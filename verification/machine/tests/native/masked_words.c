#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>

extern uint64_t probe(uint64_t words[8]);

void observe(uint64_t seed) {
    const uint64_t threshold = UINT64_C(1) << 63;
    uint64_t words[8];
    for (unsigned lane = 0; lane < 8; ++lane) {
        if ((seed >> lane) & 1)
            words[lane] = threshold;
        else
            words[lane] = ((seed >> (8 + lane)) & 1) ? threshold - 1 : UINT64_MAX;
    }
    uint64_t mask = probe(words);
    printf("%" PRIu64 " %" PRIu64, seed, mask);
    for (unsigned lane = 0; lane < 8; ++lane)
        printf(" %" PRIu64, words[lane]);
    putchar('\n');
}
