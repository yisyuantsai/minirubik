#define main solver_ida_original_main
#include "solver_ida.c"
#undef main

/*
 * Obtain the exact distance by following the original BFS
 * toward-solved table until rank 0.
 */
static uint8_t exact_distance_from_table(uint32_t rank,
                                         const uint8_t *table)
{
    state_t state;
    uint8_t distance = 0;

    unrank_state(rank, &state);

    while (rank != 0) {
        uint8_t move = table[rank];

        state = apply_move(state, move);
        rank = rank_state(&state);

        ++distance;

        /*
         * The known diameter is 11.  This protects the generator
         * against an accidentally corrupted BFS table.
         */
        if (distance > 11) {
            fprintf(stderr,
                    "invalid BFS path: distance exceeded 11\n");
            exit(1);
        }
    }

    return distance;
}


int main(void)
{
    uint8_t diameter;

    /*
     * build_table() is the original exact BFS oracle.
     * It does not require the later IDA* heuristic tables.
     */
    uint8_t *table = build_table(&diameter);

    if (!table) {
        fprintf(stderr, "could not build BFS table\n");
        return 1;
    }

    if (diameter != 11) {
        fprintf(stderr,
                "unexpected BFS diameter: %u\n",
                (unsigned)diameter);
        free(table);
        return 1;
    }

    unsigned count = 0;

    for (uint32_t rank = 0; rank < STATES; ++rank) {
        uint8_t distance =
            exact_distance_from_table(rank, table);

        if (distance != 11)
            continue;

        state_t state;
        unrank_state(rank, &state);

        /*
         * Assembly input format:
         *
         *   PPPPPPPOOOOOOO
         *
         * Internal values 0..6 / 0..2 are converted back
         * to printable digits 1..7 / 1..3.
         */
        for (unsigned i = 0; i < CUBIES; ++i)
            putchar((int)('1' + state.p[i]));

        for (unsigned i = 0; i < CUBIES; ++i)
            putchar((int)('1' + state.o[i]));

        printf(" %u\n", (unsigned)rank);

        ++count;
    }

    free(table);

    fprintf(stderr,
            "distance-11 states: %u\n",
            count);

    return count == 2644 ? 0 : 1;
}