#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
extern void capture(uint64_t *, uint64_t *, uint64_t *, uint64_t *, uint64_t);
extern const unsigned char probe[];
static uint64_t initial(uint64_t seed, size_t index) {
    return seed + UINT64_C(0x0101010101010101) * index;
}
static void print_words(const uint64_t *p, size_t n) {
    for (size_t i=0; i<n; ++i) printf(" %" PRIu64, p[i]);
}
void observe(uint64_t seed) {
    // Include signal headroom, both nested return slots, alignment padding,
    // the saved RBP and the caller return. The frame origin is 64-byte aligned.
    static _Alignas(64) uint64_t backing[8192+184];
    uint64_t *frame=backing+8192+8;
    uint64_t regs[256], status[4], output[24];
    size_t saved=160+2*(seed%4);
    for (size_t i=0; i<256; ++i) regs[i]=initial(seed,i);
    for (size_t i=0; i<184; ++i) backing[8192+i]=initial(seed,256+i);
    for (size_t i=0; i<24; ++i) output[i]=initial(seed,440+i);
    capture(output+8,regs,status,frame,seed);
    for (int i=-8; i<176; ++i) {
        if (i==-2 || i==-1 || i==(int)saved || i==(int)saved+1 ||
            (i>=0 && i<8) || (i>=80 && i<88)) continue;
        if (frame[i]!=initial(seed,264+i)) __builtin_trap();
    }
    for (size_t i=0; i<24; ++i)
        if ((i<8 || i>=16) && output[i]!=initial(seed,440+i)) __builtin_trap();
    printf("%" PRIu64,seed); print_words(status,4);
    printf(" %" PRIu64 " %" PRIu64 " %" PRIu64,frame[saved],
           frame[-1]-(uintptr_t)probe,frame[-2]-(uintptr_t)probe);
    print_words(regs,256); print_words(frame,160); print_words(output+8,8);
    putchar('\n');
}
