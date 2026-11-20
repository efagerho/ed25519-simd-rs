#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>

extern uint64_t probe(const uint64_t a[8], const uint64_t b[8]);

void observe(uint64_t seed) {
    uint64_t a[8], b[8];
    for (unsigned j = 0; j < 8; ++j) {
        a[j] = (seed >> j) & 1 ? UINT64_C(0x8000000000000000) : UINT64_C(0x5555555555555555);
        b[j] = (seed >> (8 + j)) & 1 ? 0 : UINT64_C(0x8000000000000001);
    }
    printf("%" PRIu64 " %" PRIu64 "\n", seed, probe(a, b));
}
