#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

enum {
    CUBIES = 7,
    PERMUTATIONS = 5040,
    ORIENTATIONS = 729,
    STATES = PERMUTATIONS * ORIENTATIONS,
    MOVES = 9
};

static uint16_t perm_move[PERMUTATIONS][MOVES];
static uint16_t ori_move[ORIENTATIONS][MOVES];
static uint8_t perm_dist[PERMUTATIONS];
static uint8_t ori_dist[ORIENTATIONS];
static uint8_t perm_dist_packed[(PERMUTATIONS + 1) / 2];
static uint8_t ori_dist_packed[(ORIENTATIONS + 1) / 2];
static uint8_t solution[11];
static uint64_t ida_nodes;
static uint64_t ida_pruned_nodes;
static uint64_t ida_generated_children;
static const uint8_t allowed_moves[4][9] = {
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



typedef struct {
    uint8_t p[CUBIES], o[CUBIES];
} state_t;

/*@ predicate valid_state(state_t *state) =
      (\forall integer i; 0 <= i < CUBIES ==>
         state->p[i] < CUBIES && state->o[i] < 3) &&
      (\forall integer i, j; 0 <= i < j < CUBIES ==>
         state->p[i] != state->p[j]) &&
      (state->o[0] + state->o[1] + state->o[2] + state->o[3] +
       state->o[4] + state->o[5] + state->o[6]) % 3 == 0;
 */

static const char *const move_names[MOVES] = {"R",  "R2", "R'", "B", "B2",
                                              "B'", "D",  "D2", "D'"};
static const uint8_t inverse_move[MOVES] = {2, 1, 0, 5, 4, 3, 8, 7, 6};
/* Each destination takes a cubie from source[face][destination]. */
static const uint8_t source[3][CUBIES] = {
    {1, 4, 2, 0, 3, 5, 6},
    {0, 1, 2, 4, 5, 6, 3},
    {0, 2, 5, 3, 1, 4, 6},
};
static const uint8_t twist[3][CUBIES] = {
    {1, 2, 0, 2, 1, 0, 0},
    {0, 0, 0, 1, 2, 1, 2},
    {0, 0, 0, 0, 0, 0, 0},
};

/* The three quarter-turns preserve the fixed front-upper-left corner. */
/*@ requires face < 3;
    assigns \nothing;
    ensures \forall integer i; 0 <= i < CUBIES ==>
              \result.p[i] == state.p[source[face][i]];
    ensures \forall integer i; 0 <= i < CUBIES ==>
              \result.o[i] == (state.o[source[face][i]] + twist[face][i]) % 3;
 */
static state_t quarter_turn(state_t state, uint8_t face)
{
    state_t result;
    /*@ loop invariant 0 <= i <= CUBIES;
        loop invariant \forall integer j; 0 <= j < i ==>
          result.p[j] == state.p[source[face][j]];
        loop invariant \forall integer j; 0 <= j < i ==>
          result.o[j] == (state.o[source[face][j]] + twist[face][j]) % 3;
        loop assigns i, result.p[0..6], result.o[0..6];
        loop variant CUBIES - i;
    */
    for (uint8_t i = 0; i < CUBIES; ++i) {
        uint8_t from = source[face][i];
        result.p[i] = state.p[from];
        result.o[i] = (uint8_t) ((state.o[from] + twist[face][i]) % 3U);
    }
    return result;
}

static state_t apply_move(state_t state, uint8_t move)
{
    uint8_t turns = (uint8_t) (move % 3U + 1U);
    for (uint8_t i = 0; i < turns; ++i)
        state = quarter_turn(state, (uint8_t) (move / 3U));
    return state;
}

/*@ requires \valid_read(state);
    requires \forall integer i; 0 <= i < CUBIES ==>
      0 <= state->p[i] < CUBIES;
    requires \forall integer i, j; 0 <= i < j < CUBIES ==>
      state->p[i] != state->p[j];
    requires \forall integer i; 0 <= i < CUBIES ==>
      0 <= state->o[i] < 3;
    assigns \nothing;
    ensures \result < STATES;
 */
static uint32_t rank_state(const state_t *state)
{
    uint32_t p = 0, o = 0;
    /*@ loop invariant 0 <= i <= CUBIES;
        loop invariant (i == 0 ==> p == 0) && (i == 1 ==> p <= 6) &&
          (i == 2 ==> p <= 41) && (i == 3 ==> p <= 209) &&
          (i == 4 ==> p <= 839) && (i == 5 ==> p <= 2519) &&
          (i >= 6 ==> p <= 5039);
        loop assigns i, p;
        loop variant CUBIES - i;
     */
    for (uint8_t i = 0; i < CUBIES; ++i) {
        uint8_t smaller = 0;
        /*@ loop invariant i + 1 <= j <= CUBIES;
            loop invariant smaller <= j - i - 1;
            loop assigns j, smaller;
            loop variant CUBIES - j;
         */
        for (uint8_t j = (uint8_t) (i + 1U); j < CUBIES; ++j)
            if (state->p[j] < state->p[i])
                ++smaller;
        p = p * (CUBIES - i) + smaller;
    }
    /*@ loop invariant 0 <= i <= 6;
        loop invariant (i == 0 ==> o == 0) && (i == 1 ==> o < 3) &&
          (i == 2 ==> o < 9) && (i == 3 ==> o < 27) &&
          (i == 4 ==> o < 81) && (i == 5 ==> o < 243) &&
          (i == 6 ==> o < 729);
        loop assigns i, o;
        loop variant 6 - i;
     */
    for (uint8_t i = 0; i < 6; ++i)
        o = o * 3U + state->o[i];
    return p * ORIENTATIONS + o;
}

/*@ requires \valid(state); requires rank < STATES; assigns *state; */
static void unrank_state(uint32_t rank, state_t *state)
{
    uint8_t available[CUBIES] = {0, 1, 2, 3, 4, 5, 6};
    uint32_t p = rank / ORIENTATIONS, o = rank % ORIENTATIONS, f = 720;
    uint8_t sum = 0;
    for (uint8_t i = 0; i < CUBIES; ++i) {
        uint8_t q = (uint8_t) (p / f);
        p %= f;
        state->p[i] = available[q];
        for (uint8_t j = q; j + 1U < CUBIES - i; ++j)
            available[j] = available[j + 1U];
        if (i < 5)
            f /= 6U - i;
    }
    for (uint8_t i = 6; i-- > 0;) {
        state->o[i] = (uint8_t) (o % 3U);
        sum = (uint8_t) (sum + state->o[i]);
        o /= 3U;
    }
    state->o[6] = (uint8_t) ((3U - sum % 3U) % 3U);
}
static void build_transitions(void)
{
    state_t state;

    /* Build permutation transitions. */
    for (uint16_t p = 0; p < PERMUTATIONS; ++p) {
        unrank_state((uint32_t)p * ORIENTATIONS, &state);

        for (uint8_t move = 0; move < MOVES; ++move) {
            state_t next = apply_move(state, move);
            perm_move[p][move] =
                (uint16_t)(rank_state(&next) / ORIENTATIONS);
        }
    }

    /* Build orientation transitions. */
    for (uint16_t o = 0; o < ORIENTATIONS; ++o) {
        unrank_state(o, &state);

        for (uint8_t move = 0; move < MOVES; ++move) {
            state_t next = apply_move(state, move);
            ori_move[o][move] =
                (uint16_t)(rank_state(&next) % ORIENTATIONS);
        }
    }
}
static int validate_transitions(void)
{
    state_t state;

    for (uint32_t rank = 0; rank < STATES; ++rank) {
        uint16_t p = (uint16_t)(rank / ORIENTATIONS);
        uint16_t o = (uint16_t)(rank % ORIENTATIONS);

        unrank_state(rank, &state);

        for (uint8_t move = 0; move < MOVES; ++move) {
            state_t next = apply_move(state, move);
            uint32_t next_rank = rank_state(&next);

            uint16_t expected_p =
                (uint16_t)(next_rank / ORIENTATIONS);
            uint16_t expected_o =
                (uint16_t)(next_rank % ORIENTATIONS);

            if (perm_move[p][move] != expected_p ||
                ori_move[o][move] != expected_o)
                return 0;
        }
    }

    return 1;
}
static int build_heuristics(void)
{
    uint16_t queue[PERMUTATIONS];
    uint16_t head, tail;

    /* Permutation heuristic. */
    memset(perm_dist, 0xFF, sizeof perm_dist);

    head = 0;
    tail = 0;

    perm_dist[0] = 0;
    queue[tail++] = 0;

    while (head < tail) {
        uint16_t p = queue[head++];

        for (uint8_t move = 0; move < MOVES; ++move) {
            uint16_t next = perm_move[p][move];

            if (perm_dist[next] == 0xFF) {
                perm_dist[next] = (uint8_t)(perm_dist[p] + 1);
                queue[tail++] = next;
            }
        }
    }

    if (tail != PERMUTATIONS)
        return 0;

    /* Orientation heuristic. */
    memset(ori_dist, 0xFF, sizeof ori_dist);

    head = 0;
    tail = 0;

    ori_dist[0] = 0;
    queue[tail++] = 0;

    while (head < tail) {
        uint16_t o = queue[head++];

        for (uint8_t move = 0; move < MOVES; ++move) {
            uint16_t next = ori_move[o][move];

            if (ori_dist[next] == 0xFF) {
                ori_dist[next] = (uint8_t)(ori_dist[o] + 1);
                queue[tail++] = next;
            }
        }
    }

    if (tail != ORIENTATIONS)
        return 0;

    return 1;
}
static void pack_heuristics(void)
{
    memset(perm_dist_packed, 0, sizeof perm_dist_packed);
    memset(ori_dist_packed, 0, sizeof ori_dist_packed);

    for (uint16_t p = 0; p < PERMUTATIONS; ++p) {
        uint16_t byte_index = (uint16_t)(p >> 1);

        if (p & 1)
            perm_dist_packed[byte_index] |=
                (uint8_t)(perm_dist[p] << 4);
        else
            perm_dist_packed[byte_index] |=
                (uint8_t)(perm_dist[p] & 0x0F);
    }

    for (uint16_t o = 0; o < ORIENTATIONS; ++o) {
        uint16_t byte_index = (uint16_t)(o >> 1);

        if (o & 1)
            ori_dist_packed[byte_index] |=
                (uint8_t)(ori_dist[o] << 4);
        else
            ori_dist_packed[byte_index] |=
                (uint8_t)(ori_dist[o] & 0x0F);
    }
}
static uint8_t packed_get(const uint8_t *table, uint16_t index)
{
    uint8_t value = table[index >> 1];

    if (index & 1)
        return (uint8_t)(value >> 4);

    return (uint8_t)(value & 0x0F);
}
static int validate_packed_heuristics(void)
{
    for (uint16_t p = 0; p < PERMUTATIONS; ++p) {
        if (packed_get(perm_dist_packed, p) != perm_dist[p])
            return 0;
    }

    for (uint16_t o = 0; o < ORIENTATIONS; ++o) {
        if (packed_get(ori_dist_packed, o) != ori_dist[o])
            return 0;
    }

    return 1;
}

static int validate_heuristics(uint8_t *perm_max, uint8_t *ori_max)
{
    *perm_max = 0;
    *ori_max = 0;

    if (perm_dist[0] != 0 || ori_dist[0] != 0)
        return 0;

    for (uint16_t p = 0; p < PERMUTATIONS; ++p) {
        if (perm_dist[p] == 0xFF)
            return 0;

        if (perm_dist[p] > *perm_max)
            *perm_max = perm_dist[p];
    }

    for (uint16_t o = 0; o < ORIENTATIONS; ++o) {
        if (ori_dist[o] == 0xFF)
            return 0;

        if (ori_dist[o] > *ori_max)
            *ori_max = ori_dist[o];
    }

    return 1;
}
static uint8_t heuristic(uint16_t p, uint16_t o)
{
    uint8_t hp = perm_dist[p];
    uint8_t ho = ori_dist[o];

    return hp > ho ? hp : ho;
}

static int ida_dfs(uint16_t p, uint16_t o,
                   uint8_t depth, uint8_t bound,
                   int8_t previous_face)
{
    ++ida_nodes;

    if (p == 0 && o == 0)
        return 1;

    if (depth == bound)
        return 0;

    uint8_t prev_index =
        previous_face < 0 ? 3 : (uint8_t)previous_face;

    for (uint8_t i = 0; i < allowed_count[prev_index]; ++i) {
        
        uint8_t entry = allowed_moves[prev_index][i];

        uint8_t move = (uint8_t)(entry & 0x0F);
        uint8_t next_face = (uint8_t)(entry >> 4);

        ++ida_generated_children;

        uint16_t next_p = perm_move[p][move];
        uint16_t next_o = ori_move[o][move];

        uint8_t next_depth =
            (uint8_t)(depth + 1);

        uint8_t next_h =
            heuristic(next_p, next_o);

        if ((uint8_t)(next_depth + next_h) > bound) {
            ++ida_pruned_nodes;
            continue;
        }

        solution[depth] = move;

    
        if (ida_dfs(next_p, next_o,
            next_depth,
            bound,
            (int8_t)next_face))
        return 1;
    }

    return 0;
}
static int solve_ida(uint16_t p, uint16_t o, uint8_t *solution_length)
{
    ida_generated_children = 0;
    ida_nodes = 0;
    ida_pruned_nodes = 0;
    uint8_t bound = heuristic(p, o);

    while (bound <= 11) {
        if (ida_dfs(p, o, 0, bound, -1)) {
            *solution_length = bound;
            return 1;
        }

        ++bound;
    }

    return 0;
}
static uint8_t exact_distance(state_t state, const uint8_t *table)
{
    uint8_t distance = 0;

    for (uint32_t rank = rank_state(&state);
         rank != 0;
         rank = rank_state(&state)) {

        uint8_t move = table[rank];
        state = apply_move(state, move);
        ++distance;
    }

    return distance;
}
static uint8_t exact_distance_rank(uint32_t rank, const uint8_t *table)
{
    uint8_t distance = 0;

    while (rank != 0) {
        uint8_t move = table[rank];

        uint16_t p = (uint16_t)(rank / ORIENTATIONS);
        uint16_t o = (uint16_t)(rank % ORIENTATIONS);

        p = perm_move[p][move];
        o = ori_move[o][move];

        rank = (uint32_t)p * ORIENTATIONS + o;
        ++distance;
    }

    return distance;
}
/*@ requires \valid_read(state);
    requires \initialized(&state->p[0..6]) && \initialized(&state->o[0..6]);
    assigns \nothing;
    ensures \result != 0 ==> \forall integer i; 0 <= i < CUBIES ==>
      state->p[i] < CUBIES && state->o[i] < 3;
    ensures \result != 0 ==> \forall integer i, j; 0 <= i < j < CUBIES ==>
      state->p[i] != state->p[j];
    ensures \result != 0 ==>
      (state->o[0] + state->o[1] + state->o[2] + state->o[3] +
       state->o[4] + state->o[5] + state->o[6]) % 3 == 0;
    ensures complete: valid_state(state) ==> \result != 0;
 */
static int valid(const state_t *state)
{
    uint8_t sum = 0;
    /*@ loop invariant 0 <= i <= CUBIES;
        loop invariant sum <= 2 * i;
        loop invariant sum == (i > 0 ? state->o[0] : 0) +
          (i > 1 ? state->o[1] : 0) + (i > 2 ? state->o[2] : 0) +
          (i > 3 ? state->o[3] : 0) + (i > 4 ? state->o[4] : 0) +
          (i > 5 ? state->o[5] : 0) + (i > 6 ? state->o[6] : 0);
        loop invariant \forall integer j; 0 <= j < i ==>
          state->p[j] < CUBIES && state->o[j] < 3;
        loop invariant \forall integer j, k; 0 <= j < k < i ==>
          state->p[j] != state->p[k];
        loop assigns i, sum;
        loop variant CUBIES - i;
    */
    for (uint8_t i = 0; i < CUBIES; ++i) {
        if (state->p[i] >= CUBIES || state->o[i] >= 3)
            return 0;
        /*@ loop invariant 0 <= j <= i;
            loop invariant \forall integer k; 0 <= k < j ==>
              state->p[k] != state->p[i];
            loop assigns j;
            loop variant i - j;
        */
        for (uint8_t j = 0; j < i; ++j)
            if (state->p[j] == state->p[i])
                return 0;
        sum = (uint8_t) (sum + state->o[i]);
    }
    return sum % 3U == 0;
}

static uint8_t *build_table(uint8_t *diameter)
{
    uint8_t *toward_solved = malloc(STATES);
    uint32_t *queue = malloc((size_t) STATES * sizeof *queue);
    uint16_t permutation[3][PERMUTATIONS], orientation[3][ORIENTATIONS];
    uint32_t head = 0, tail = 1, level_end = 1;
    state_t state;
    if (!toward_solved || !queue) {
        free(toward_solved);
        free(queue);
        return NULL;
    }
    for (uint16_t rank = 0; rank < PERMUTATIONS; ++rank) {
        unrank_state((uint32_t) rank * ORIENTATIONS, &state);
        for (uint8_t face = 0; face < 3; ++face) {
            state_t next = quarter_turn(state, face);
            permutation[face][rank] =
                (uint16_t) (rank_state(&next) / ORIENTATIONS);
        }
    }
    for (uint16_t rank = 0; rank < ORIENTATIONS; ++rank) {
        unrank_state(rank, &state);
        for (uint8_t face = 0; face < 3; ++face) {
            state_t next = quarter_turn(state, face);
            orientation[face][rank] =
                (uint16_t) (rank_state(&next) % ORIENTATIONS);
        }
    }
    memset(toward_solved, UINT8_MAX, STATES);
    queue[0] = 0;
    toward_solved[0] = 0;
    *diameter = 0;
    while (head < tail) {
        if (head == level_end) {
            level_end = tail;
            ++*diameter;
        }
        uint32_t here = queue[head++];
        uint16_t p = (uint16_t) (here / ORIENTATIONS);
        uint16_t o = (uint16_t) (here % ORIENTATIONS);
        for (uint8_t face = 0; face < 3; ++face) {
            uint16_t next_p = p, next_o = o;
            for (uint8_t turn = 0; turn < 3; ++turn) {
                next_p = permutation[face][next_p];
                next_o = orientation[face][next_o];
                uint32_t there = (uint32_t) next_p * ORIENTATIONS + next_o;
                if (toward_solved[there] == UINT8_MAX) {
                    uint8_t move = (uint8_t) (face * 3U + turn);
                    toward_solved[there] = inverse_move[move];
                    queue[tail++] = there;
                }
            }
        }
    }
    free(queue);
    if (tail != STATES) {
        free(toward_solved);
        return NULL;
    }
    return toward_solved;
}

/*@ requires valid_read_string(input);
    requires \valid(state);
    assigns state->p[0..6], state->o[0..6];
    ensures \result != 0 ==> input[14] == '\0';
    ensures \result != 0 ==> \forall integer i; 0 <= i < CUBIES ==>
      state->p[i] < CUBIES && state->o[i] < 3;
    ensures \result != 0 ==> \forall integer i, j; 0 <= i < j < CUBIES ==>
      state->p[i] != state->p[j];
    ensures \result != 0 ==>
      (state->o[0] + state->o[1] + state->o[2] + state->o[3] +
       state->o[4] + state->o[5] + state->o[6]) % 3 == 0;
    ensures \result != 0 ==> \forall integer i; 0 <= i < CUBIES ==>
      state->p[i] == input[i] - '1';
    ensures \result != 0 ==> \forall integer i; 0 <= i < CUBIES ==>
      state->o[i] == input[i + CUBIES] - '1';
 */
static int parse_state(const char *input, state_t *state)
{
    /*@ loop invariant 0 <= i <= 14;
        loop invariant i <= strlen(input);
        loop invariant i <= 7 ==> \initialized(&state->p[0..i-1]);
        loop invariant i >= 7 ==> \initialized(&state->p[0..6]);
        loop invariant i >= 7 ==> \initialized(&state->o[0..i-8]);
        loop invariant \forall integer j; 0 <= j < i && j < CUBIES ==>
          state->p[j] == input[j] - '1';
        loop invariant \forall integer j; 0 <= j < i - CUBIES ==>
          state->o[j] == input[j + CUBIES] - '1';
        loop assigns i, state->p[0..6], state->o[0..6];
        loop variant 14 - i;
     */
    for (int i = 0; i < 14; ++i) {
        int limit = i < 7 ? 7 : 3;
        if (input[i] < '1' || input[i] > '0' + limit)
            return 0;
        (i < 7 ? state->p : state->o)[i % 7] = (uint8_t) (input[i] - '1');
    }
    return input[14] == '\0' && valid(state);
}

/* stdout is fully buffered off a terminal, so a write error surfaces at the
 * flush, not at the printf that queued the bytes. Every exit path that has
 * produced output goes through here.
 */
static int output_failed(void)
{
    return fflush(stdout) != 0 || ferror(stdout);
}

static int self_test(void)
{
    const state_t solved = {{0, 1, 2, 3, 4, 5, 6}, {0}};
    state_t state;
    for (uint8_t move = 0; move < MOVES; ++move) {
        state = solved;
        state = apply_move(state, move);
        state = apply_move(state, inverse_move[move]);
        if (memcmp(&solved, &state, sizeof solved))
            return 0;
    }
    for (uint32_t rank = 0; rank < STATES; ++rank) {
        unrank_state(rank, &state);
        if (!valid(&state) || rank_state(&state) != rank)
            return 0;
    }
    return 1;
}

int main(int argc, char **argv)
{
    state_t state;
    uint8_t diameter;

    if (argc == 2 && !strcmp(argv[1], "--transition-test")) {
        build_transitions();

        if (!validate_transitions()) {
            fputs("transition table validation failed\n", stderr);
            return 1;
        }

        puts("transition tables OK");
        return output_failed();
    }

    if (argc == 2 && !strcmp(argv[1], "--heuristic-test")) {
        uint8_t perm_max, ori_max;

        build_transitions();

        if (!build_heuristics()) {
            fputs("could not build heuristic tables\n", stderr);
            return 1;
        }

        if (!validate_heuristics(&perm_max, &ori_max)) {
            fputs("heuristic table validation failed\n", stderr);
            return 1;
        }

        printf("heuristic tables OK\n");
        printf("permutation max distance: %u\n",
               (unsigned)perm_max);
        printf("orientation max distance: %u\n",
               (unsigned)ori_max);

        return output_failed();
    }
    if (argc == 2 && !strcmp(argv[1], "--packed-test")) {
    build_transitions();

    if (!build_heuristics()) {
        fputs("could not build heuristic tables\n", stderr);
        return 1;
    }

    pack_heuristics();

    if (!validate_packed_heuristics()) {
        fputs("packed heuristic validation failed\n", stderr);
        return 1;
    }

    printf("packed heuristic validation OK\n");
    printf("unpacked heuristic bytes: %u\n",
           (unsigned)(PERMUTATIONS + ORIENTATIONS));
    printf("packed heuristic bytes: %u\n",
           (unsigned)(sizeof perm_dist_packed +
                      sizeof ori_dist_packed));

    return output_failed();
}

    if (argc == 3 && !strcmp(argv[1], "--ida-test")) {
        if (!parse_state(argv[2], &state)) {
            fputs("invalid cube state\n", stderr);
            return 2;
        }

        build_transitions();

        if (!build_heuristics()) {
            fputs("could not build heuristic tables\n", stderr);
            return 1;
        }

        uint32_t rank = rank_state(&state);

        uint16_t p =
            (uint16_t)(rank / ORIENTATIONS);

        uint16_t o =
            (uint16_t)(rank % ORIENTATIONS);

        uint8_t solution_length;

        if (!solve_ida(p, o, &solution_length)) {
            fputs("IDA* failed to find a solution\n", stderr);
            return 1;
        }

        /*
         * Verify that the IDA* solution actually solves
         * the original cube state.
         */
        state_t check = state;

        for (uint8_t i = 0; i < solution_length; ++i)
            check = apply_move(check, solution[i]);

        if (rank_state(&check) != 0) {
            fputs("IDA* solution does not solve the cube\n", stderr);
            return 1;
        }

        /*
         * Build the original exact BFS table and use it
         * as the optimal-distance oracle.
         */
        uint8_t *table = build_table(&diameter);

        if (!table) {
            fputs("could not build BFS table\n", stderr);
            return 1;
        }

        uint8_t bfs_distance =
            exact_distance(state, table);

        printf("IDA* length: %u\n",
               (unsigned)solution_length);

        printf("BFS distance: %u\n",
               (unsigned)bfs_distance);
        printf("IDA* nodes: %llu\n",
               (unsigned long long)ida_nodes);
        printf("heuristic-pruned nodes: %llu\n",
       (unsigned long long)ida_pruned_nodes);  
       printf("generated children: %llu\n",
       (unsigned long long)ida_generated_children);     

        printf("solution:");

        for (uint8_t i = 0; i < solution_length; ++i) {
            printf(" %s", move_names[solution[i]]);
        }

        putchar('\n');

        free(table);

        if (solution_length != bfs_distance) {
            fputs("optimality check failed\n", stderr);
            return 1;
        }

        puts("IDA* test OK");
        return output_failed();
    }

    if (argc == 2 && !strcmp(argv[1], "--admissibility-test")) {
        build_transitions();

        if (!build_heuristics()) {
            fputs("could not build heuristic tables\n", stderr);
            return 1;
        }

        uint8_t *table = build_table(&diameter);

        if (!table) {
            fputs("could not build BFS table\n", stderr);
            return 1;
        }

        for (uint32_t rank = 0; rank < STATES; ++rank) {
            uint16_t p =
                (uint16_t)(rank / ORIENTATIONS);

            uint16_t o =
                (uint16_t)(rank % ORIENTATIONS);

            uint8_t h = heuristic(p, o);
            uint8_t d = exact_distance_rank(rank, table);

            if (h > d) {
                fprintf(stderr,
                        "admissibility failed at rank %u: "
                        "h=%u d=%u\n",
                        (unsigned)rank,
                        (unsigned)h,
                        (unsigned)d);

                free(table);
                return 1;
            }
        }

        free(table);

        puts("heuristic admissibility OK for all 3674160 states");
        return output_failed();
    }

    if (argc == 2 && !strcmp(argv[1], "--optimality-test")) {
        build_transitions();

        if (!build_heuristics()) {
            fputs("could not build heuristic tables\n", stderr);
            return 1;
        }

        uint8_t *table = build_table(&diameter);

        if (!table) {
            fputs("could not build BFS table\n", stderr);
            return 1;
        }

        clock_t start = clock();

        for (uint32_t rank = 0; rank < STATES; ++rank) {
            uint16_t p =
                (uint16_t)(rank / ORIENTATIONS);

            uint16_t o =
                (uint16_t)(rank % ORIENTATIONS);

            uint8_t ida_length;

            if (!solve_ida(p, o, &ida_length)) {
                fprintf(stderr,
                        "IDA* failed at rank %u\n",
                        (unsigned)rank);

                free(table);
                return 1;
            }

            uint8_t bfs_distance =
                exact_distance_rank(rank, table);

            if (ida_length != bfs_distance) {
                fprintf(stderr,
                        "optimality failed at rank %u: "
                        "IDA*=%u BFS=%u\n",
                        (unsigned)rank,
                        (unsigned)ida_length,
                        (unsigned)bfs_distance);

                free(table);
                return 1;
            }

            if ((rank + 1) % 100000 == 0) {
                printf("checked %u / %u states\n",
                       (unsigned)(rank + 1),
                       (unsigned)STATES);
            }
        }

        clock_t end = clock();

        double seconds =
            (double)(end - start) / CLOCKS_PER_SEC;

        free(table);

        printf("optimality OK for all %u states\n",
               (unsigned)STATES);

        printf("wall-clock time: %.3f s\n",
               seconds);

        return output_failed();
    }
    if (argc == 2 && !strcmp(argv[1], "--depth11-stats")) {
    build_transitions();

    if (!build_heuristics()) {
        fputs("could not build heuristic tables\n", stderr);
        return 1;
    }

    uint8_t *table = build_table(&diameter);

    if (!table) {
        fputs("could not build BFS table\n", stderr);
        return 1;
    }

    uint32_t count = 0;
    uint64_t total_nodes = 0;
    uint64_t min_nodes = (uint64_t)-1;
    uint64_t max_nodes = 0;
    uint32_t worst_rank = 0;

    for (uint32_t rank = 0; rank < STATES; ++rank) {
        uint8_t distance =
            exact_distance_rank(rank, table);

        if (distance != 11)
            continue;

        uint16_t p =
            (uint16_t)(rank / ORIENTATIONS);

        uint16_t o =
            (uint16_t)(rank % ORIENTATIONS);

        uint8_t ida_length;

        if (!solve_ida(p, o, &ida_length)) {
            fprintf(stderr,
                    "IDA* failed at rank %u\n",
                    (unsigned)rank);

            free(table);
            return 1;
        }

        if (ida_length != 11) {
            fprintf(stderr,
                    "unexpected solution length at rank %u: %u\n",
                    (unsigned)rank,
                    (unsigned)ida_length);

            free(table);
            return 1;
        }

        ++count;
        total_nodes += ida_nodes;

        if (ida_nodes < min_nodes)
            min_nodes = ida_nodes;

        if (ida_nodes > max_nodes) {
            max_nodes = ida_nodes;
            worst_rank = rank;
        }
    }

    free(table);

    if (count != 2644) {
        fprintf(stderr,
                "expected 2644 distance-11 states, got %u\n",
                (unsigned)count);

        return 1;
    }

    double average_nodes =
        (double)total_nodes / (double)count;

    printf("distance-11 states: %u\n",
           (unsigned)count);

    printf("minimum IDA* nodes: %llu\n",
           (unsigned long long)min_nodes);

    printf("maximum IDA* nodes: %llu\n",
           (unsigned long long)max_nodes);

    printf("average IDA* nodes: %.2f\n",
           average_nodes);

    printf("worst-case rank: %u\n",
           (unsigned)worst_rank);

    return output_failed();
}

    if (argc == 2 && !strcmp(argv[1], "--self-test")) {
        if (!self_test()) {
            fputs("self-test failed\n", stderr);
            return 1;
        }

        uint8_t *table = build_table(&diameter);

        if (!table) {
            fputs("could not build complete state table\n",
                  stderr);
            return 1;
        }

        free(table);

        if (diameter != 11) {
            fputs("BFS check failed\n", stderr);
            return 1;
        }

        puts("3674160 states; diameter 11");
        return output_failed();
    }

    /*
     * Original baseline solving mode.
     */
    if (argc != 2 || !parse_state(argv[1], &state)) {
        fprintf(stderr,
                "usage: %s PPPPPPPOOOOOOO\n",
                argc > 0 && argv[0]
                    ? argv[0]
                    : "solver");

        return 2;
    }

    uint8_t *table = build_table(&diameter);

    if (!table) {
        fputs("could not build complete state table\n",
              stderr);
        return 1;
    }

    const char *separator = "";

    for (uint32_t rank = rank_state(&state);
         rank;
         rank = rank_state(&state)) {

        uint8_t move = table[rank];

        printf("%s%s",
               separator,
               move_names[move]);

        separator = " ";

        state = apply_move(state, move);
    }

    putchar('\n');

    free(table);

    return output_failed();
}