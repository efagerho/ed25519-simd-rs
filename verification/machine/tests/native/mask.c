#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>

extern uint64_t probe(const uint64_t a[8], const uint64_t b[16]);

void observe(uint64_t seed) {
    uint64_t a[8], b[16];
    for (unsigned lane = 0; lane < 8; ++lane) {
        a[lane] = (seed >> (8 + lane)) & 1;
        b[lane] = ((seed >> lane) & 1) ? -a[lane] : ((seed >> (16 + lane)) & 1) + 1;
        b[lane + 8] = UINT64_C(0x0123456789abcdef) + ((seed >> (24 + lane)) & 1);
    }
    printf("%" PRIu64 " %" PRIu64 "\n", seed, probe(a, b));
}
