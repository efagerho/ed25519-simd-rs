#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>

extern void capture(uint64_t initial_rcx, uint64_t result[3]);

void observe(uint64_t input) {
    uint64_t out[3];
    capture(input, out);
    printf("%" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 "\n",
           input, out[0], out[1], out[2]);
}
