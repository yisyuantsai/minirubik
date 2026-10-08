#include <stdint.h>

enum {
    CUBIES = 7,
    PERMUTATIONS = 5040,
    ORIENTATIONS = 729,
    STATES = PERMUTATIONS * ORIENTATIONS,
    MOVES = 9
};

#define IDA_MAX_DEPTH 11


/* -------------------------------------------------------------------------- */
/* Types                                                                      */
/* -------------------------------------------------------------------------- */

typedef struct {
    uint8_t p[CUBIES];
    uint8_t o[CUBIES];
} state_t;

typedef struct {
    uint16_t p;
    uint16_t o;
    uint8_t prev_index;
    uint8_t next_i;
} ida_frame_t;


/* -------------------------------------------------------------------------- */
/* Host-precomputed read-only tables                                          */
/* -------------------------------------------------------------------------- */

#include "tables_generated.h"


/* -------------------------------------------------------------------------- */
/* Target input and IDA* search data                                          */
/* -------------------------------------------------------------------------- */

/*
 * The grader can replace this string with any valid 14-character cube state.
 */
static const char input_state[] = "21345671111111";

static uint8_t solution[IDA_MAX_DEPTH];
static ida_frame_t ida_stack[IDA_MAX_DEPTH + 1];

/*
 * Each allowed-move entry packs:
 *
 *   high nibble : next face
 *   low nibble  : move number
 *
 * prev_index:
 *   0 = R
 *   1 = B
 *   2 = D
 *   3 = root
 */
static const uint8_t allowed_moves[4][MOVES] = {
    /* previous face = R */
    {0x13, 0x14, 0x15, 0x26, 0x27, 0x28, 0, 0, 0},

    /* previous face = B */
    {0x00, 0x01, 0x02, 0x26, 0x27, 0x28, 0, 0, 0},

    /* previous face = D */
    {0x00, 0x01, 0x02, 0x13, 0x14, 0x15, 0, 0, 0},

    /* root */
    {0x00, 0x01, 0x02, 0x13, 0x14, 0x15, 0x26, 0x27, 0x28}
};

static const uint8_t allowed_count[4] = {
    6, 6, 6, 9
};


/* -------------------------------------------------------------------------- */
/* State ranking                                                              */
/* -------------------------------------------------------------------------- */

/*
 * Return the Lehmer-code digit at position i.
 */
static uint8_t lehmer_digit(const state_t *state, uint8_t i)
{
    uint8_t smaller = 0;

    for (uint8_t j = (uint8_t)(i + 1U);
         j < CUBIES;
         ++j) {
        if (state->p[j] < state->p[i])
            ++smaller;
    }

    return smaller;
}


/*
 * Rank the seven movable cubies as a permutation index in [0, 5039].
 *
 * The original mixed-radix calculation uses factors:
 *
 *   7, 6, 5, 4, 3, 2, 1
 *
 * The first multiplication by 7 is unnecessary because the accumulator
 * initially equals zero. The remaining constant multiplications are written
 * explicitly with shifts and additions so they map cheaply to RV32I.
 */
static uint16_t rank_permutation(const state_t *state)
{
    uint16_t p = lehmer_digit(state, 0);

    /* p = p * 6 + digit */
    p = (uint16_t)((p << 2) +
                   (p << 1) +
                   lehmer_digit(state, 1));

    /* p = p * 5 + digit */
    p = (uint16_t)((p << 2) +
                   p +
                   lehmer_digit(state, 2));

    /* p = p * 4 + digit */
    p = (uint16_t)((p << 2) +
                   lehmer_digit(state, 3));

    /* p = p * 3 + digit */
    p = (uint16_t)((p << 1) +
                   p +
                   lehmer_digit(state, 4));

    /* p = p * 2 + digit */
    p = (uint16_t)((p << 1) +
                   lehmer_digit(state, 5));

    /*
     * The final Lehmer digit is always zero, so the original final
     * multiplication by one does not change the result.
     */
    return p;
}


/*
 * Rank the first six orientations as a base-3 number in [0, 728].
 *
 * The seventh orientation is determined by the total-twist invariant.
 *
 * x * 3 is written as:
 *
 *   (x << 1) + x
 *
 * so no multiplication instruction or helper routine is required.
 */
static uint16_t rank_orientation(const state_t *state)
{
    uint16_t o = 0;

    for (uint8_t i = 0; i < CUBIES - 1; ++i) {
        o = (uint16_t)((o << 1) +
                       o +
                       state->o[i]);
    }

    return o;
}


/* -------------------------------------------------------------------------- */
/* Heuristic                                                                  */
/* -------------------------------------------------------------------------- */

/*
 * The permutation and orientation heuristic tables contain exact distances
 * in their respective abstractions.
 *
 * Taking their maximum remains admissible.
 */
static uint8_t heuristic(uint16_t p, uint16_t o)
{
    uint8_t hp = perm_dist[p];
    uint8_t ho = ori_dist[o];

    return hp > ho ? hp : ho;
}


/* -------------------------------------------------------------------------- */
/* IDA* search                                                                */
/* -------------------------------------------------------------------------- */

/*
 * Search one IDA* bound using a fixed-size explicit DFS stack.
 *
 * No recursion and no heap allocation are required.
 */
static int ida_search_bound(uint16_t root_p,
                            uint16_t root_o,
                            uint8_t bound)
{
    uint8_t sp = 0;

    ida_stack[0].p = root_p;
    ida_stack[0].o = root_o;
    ida_stack[0].prev_index = 3;
    ida_stack[0].next_i = 0;

    for (;;) {
        ida_frame_t *frame = &ida_stack[sp];

        /*
         * Solved state.
         */
        if (frame->p == 0 && frame->o == 0)
            return 1;

        /*
         * All legal moves at this depth have been examined.
         * Backtrack, or fail if this is the root.
         */
        if (frame->next_i >= allowed_count[frame->prev_index]) {
            if (sp == 0)
                return 0;

            --sp;
            continue;
        }

        /*
         * Decode the next legal move.
         *
         * low nibble  = move
         * high nibble = next face
         */
        uint8_t entry =
            allowed_moves[frame->prev_index][frame->next_i++];

        uint8_t move =
            (uint8_t)(entry & 0x0F);

        uint8_t next_face =
            (uint8_t)(entry >> 4);

        /*
         * Apply the move using the host-precomputed transition tables.
         */
        uint16_t next_p =
            perm_move[frame->p][move];

        uint16_t next_o =
            ori_move[frame->o][move];

        uint8_t next_depth =
            (uint8_t)(sp + 1);

        uint8_t next_h =
            heuristic(next_p, next_o);

        /*
         * Prune before descending.
         */
        if ((uint8_t)(next_depth + next_h) > bound)
            continue;

        solution[sp] = move;

        ++sp;

        ida_stack[sp].p = next_p;
        ida_stack[sp].o = next_o;
        ida_stack[sp].prev_index = next_face;
        ida_stack[sp].next_i = 0;
    }
}


/*
 * Increase the IDA* bound from h(root) to the known cube diameter.
 */
static int solve_ida(uint16_t p,
                     uint16_t o,
                     uint8_t *solution_length)
{
    uint8_t bound = heuristic(p, o);

    while (bound <= IDA_MAX_DEPTH) {
        if (ida_search_bound(p, o, bound)) {
            *solution_length = bound;
            return 1;
        }

        ++bound;
    }

    return 0;
}


/* -------------------------------------------------------------------------- */
/* Input validation                                                           */
/* -------------------------------------------------------------------------- */

/*
 * Verify:
 *
 * - permutation entries are in [0, 6],
 * - permutation entries are unique,
 * - orientation entries are in [0, 2],
 * - total orientation is 0 modulo 3.
 *
 * The orientation sum is maintained modulo 3 incrementally, avoiding
 * the '%' operator.
 */
static int valid(const state_t *state)
{
    uint8_t sum_mod3 = 0;

    for (uint8_t i = 0; i < CUBIES; ++i) {
        if (state->p[i] >= CUBIES ||
            state->o[i] >= 3) {
            return 0;
        }

        /*
         * Check permutation uniqueness.
         */
        for (uint8_t j = 0; j < i; ++j) {
            if (state->p[j] == state->p[i])
                return 0;
        }

        /*
         * sum_mod3 is initially below 3, while state->o[i] <= 2.
         * Therefore the sum is at most 4 and one subtract is sufficient.
         */
        sum_mod3 =
            (uint8_t)(sum_mod3 + state->o[i]);

        if (sum_mod3 >= 3)
            sum_mod3 = (uint8_t)(sum_mod3 - 3);
    }

    return sum_mod3 == 0;
}


/*
 * Parse:
 *
 *   PPPPPPPOOOOOOO
 *
 * The input representation uses one-based digits:
 *
 *   permutation: 1..7
 *   orientation: 1..3
 *
 * The internal representation is zero-based.
 *
 * Two separate loops avoid the previous '% 7' index calculation and
 * per-iteration array-selection expression.
 */
static int parse_state(const char *input, state_t *state)
{
    /*
     * Permutation digits.
     */
    for (uint8_t i = 0; i < CUBIES; ++i) {
        char c = input[i];

        if (c < '1' || c > '7')
            return 0;

        state->p[i] =
            (uint8_t)(c - '1');
    }

    /*
     * Orientation digits.
     */
    for (uint8_t i = 0; i < CUBIES; ++i) {
        char c = input[CUBIES + i];

        if (c < '1' || c > '3')
            return 0;

        state->o[i] =
            (uint8_t)(c - '1');
    }

    /*
     * Require exactly 14 characters and a valid cube state.
     */
    return input[14] == '\0' && valid(state);
}


/* -------------------------------------------------------------------------- */
/* Target entry point                                                         */
/* -------------------------------------------------------------------------- */

int main(void)
{
    state_t state;

    /*
     * Parse the inlined 14-character cube state.
     */
    if (!parse_state(input_state, &state))
        return 2;

    /*
     * Convert directly to the factored state representation.
     *
     * No dense rank followed by /729 and %729 is required.
     */
    uint16_t p = rank_permutation(&state);
    uint16_t o = rank_orientation(&state);

    uint8_t solution_length;

    /*
     * Find an optimal solution.
     */
    if (!solve_ida(p, o, &solution_length))
        return 3;

    /*
     * Validate the returned solution on the target itself.
     *
     * Reapply every solution move using the same transition tables and
     * require the final factored state to be solved.
     */
    uint16_t check_p = p;
    uint16_t check_o = o;

    for (uint8_t i = 0; i < solution_length; ++i) {
        uint8_t move = solution[i];

        check_p = perm_move[check_p][move];
        check_o = ori_move[check_o][move];
    }

    if (check_p != 0 || check_o != 0)
        return 4;

    return 0;
}