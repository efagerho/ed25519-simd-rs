"""Check both field kernels and their caller in a linked x86-64 Linux ELF."""
import re
import sys
from dataclasses import dataclass
from functools import cache

import z3

from spec import EXPONENT, INPUT_MAX, OUTPUT_MAX, P, RADIX, integer

from elf import address, disassemble, require


@dataclass(frozen=True)
class Word:
    value: z3.ArithRef
    maximum: int

    def __post_init__(self):
        require(0 <= self.maximum < 2**64, "possible 64-bit wraparound")


def constant(value):
    return Word(z3.IntVal(value), value)


# Treat each distinct floor division as an arbitrary integer. The same
# dividend/divisor always receives the same symbol. A ring identity valid
# for every such assignment includes the actual hardware quotient.
@cache
def quotient(value, radix):
    return z3.FreshInt("quotient")


def low(value, radix):
    # This form of Euclidean remainder lets ring normalization cancel the
    # quotient shared with the corresponding high-half instruction.
    return value - radix * quotient(value, radix)


# Private square pre/postcondition. Multiplication accepts all five
# limbs at IFMA width and establishes the stronger public output bounds.
SQUARE_MAX = (RADIX - 1, 2**52 - 1, RADIX - 1, 2**52 - 1, RADIX - 1)


def fits(actual, allowed):
    return len(actual) == len(allowed) and all(x <= y for x, y in zip(actual, allowed))


def prove_kernel(code, pc, square):
    input_max = SQUARE_MAX if square else INPUT_MAX
    output_max = SQUARE_MAX if square else OUTPUT_MAX
    lhs = [Word(z3.Int(f"x{i}"), input_max[i % 5]) for i in range(10)]
    rhs = lhs if square else [Word(z3.Int(f"y{i}"), INPUT_MAX[i % 5]) for i in range(10)]
    regs = {f"zmm{i}": v for i, v in enumerate(lhs)}
    regs.update(zmm28=constant(19), zmm29=constant(RADIX - 1))
    while True:
        pc, op, args = code[pc]
        if op == "ret" and not args:
            break
        dst, *sources = args
        require(re.fullmatch(r"zmm(?:[0-9]|[12][0-9]|3[01])", dst)
                and dst not in ("zmm28", "zmm29"), "illegal kernel destination")
        if op == "vmovdqu64":
            [mem] = sources
            base, offset = address(mem)
            require(not square and base == "r8" and offset % 64 == 0 and offset < 640,
                    "invalid kernel read")
            result = rhs[offset // 64]
        elif op == "vmovdqa64":
            [src] = sources
            result = regs[src]
        elif op == "vpxorq" and sources == [dst, dst]:
            result = constant(0)
        else:
            a, b = sources
            x = regs[a]
            if op in ("vpsllq", "vpsrlq"):
                count = int(b, 0)
                require(0 <= count < 64, "unsupported shift")
                scale = 2**count
                result = (Word(x.value * scale, x.maximum * scale) if op == "vpsllq"
                          else Word(quotient(x.value, scale), x.maximum // scale))
            else:
                y = regs[b]
                if op == "vpandq" and b == "zmm29":
                    result = Word(low(x.value, RADIX), RADIX - 1)
                elif op == "vpaddq":
                    result = Word(x.value + y.value, x.maximum + y.maximum)
                elif op == "vpmullq":
                    result = Word(x.value * y.value, x.maximum * y.maximum)
                elif op in ("vpmadd52luq", "vpmadd52huq"):
                    split = 2**52
                    require(max(x.maximum, y.maximum) < split, "IFMA truncates operand")
                    product = x.value * y.value
                    if op == "vpmadd52luq":
                        # Small products (e.g. 19 times the top carry)
                        # have no high half. Keep their exact value.
                        maximum = x.maximum * y.maximum
                        if maximum < split:
                            part, bound = product, maximum
                        else:
                            part, bound = low(product, split), split - 1
                    else:
                        part, bound = quotient(product, split), x.maximum * y.maximum // split
                    result = Word(regs[dst].value + part, regs[dst].maximum + bound)
                else:
                    raise ValueError("unsupported kernel instruction " + op)
        regs[dst] = result

    for start in (0, 5):
        out = [regs[f"zmm{i}"] for i in range(start, start + 5)]
        require(fits([x.maximum for x in out], output_max), "output bound")
        left = integer(x.value for x in lhs[start:start + 5])
        right = integer(x.value for x in rhs[start:start + 5])
        delta = integer(x.value for x in out) - left * right
        # Construct an integer witness for divisibility; Z3 checks the full
        # identity independently of the code extracting the coefficients.
        poly = z3.simplify(delta, som=True, som_blowup=4096)
        witness = z3.IntVal(0)
        for term in poly.children() if z3.is_add(poly) else [poly]:
            coeff = 1
            monomial = z3.IntVal(1)
            for factor in term.children() if z3.is_mul(term) else [term]:
                if z3.is_int_value(factor):
                    coeff *= factor.as_long()
                else:
                    monomial *= factor
            require(coeff % P == 0, f"nonzero coefficient modulo p: {term}")
            witness += (coeff // P) * monomial
        solver = z3.Solver()
        solver.set(timeout=10000)
        solver.add(z3.simplify(delta - P * witness, som=True, som_blowup=4096) != 0)
        require(solver.check() == z3.unsat, "unproved field identity")


@dataclass(frozen=True)
class Limb:
    stream: int
    exponent: int
    generation: int
    index: int


def whole_field(words, stream):
    first = words[0]
    require(words == [Limb(stream, first.exponent, first.generation, i) for i in range(5)],
            "limbs from different field values")
    return first.exponent


def prove_entry(binary):
    bounds = {0: INPUT_MAX}  # Indexed by the generation on each stored limb.
    pc, code = disassemble(binary)
    # Each private entry must independently pass the corresponding kernel proof.
    calls = sorted({int(args[0], 16) for _, op, args in code.values() if op == "call"})
    require(len(calls) == 2, "expected two arithmetic kernels")
    square, multiply = calls
    prove_kernel(code, square, True)
    prove_kernel(code, multiply, False)

    regs, memory = {}, {}
    for stream, base in enumerate(("rsi", "rdx")):
        for i in range(5):
            memory[base, i * 64] = Limb(stream, 1, 0, i)
    sp = 0
    frame = 1928
    steps = 0
    zero_flag = None
    while True:
        steps += 1
        require(steps < 5000, "public loop did not terminate")
        next_pc, op, args = code[pc]
        if op in ("sub", "add") and args == ["rsp", hex(frame)]:
            sp += frame if op == "add" else -frame
            require(sp in (0, -frame), "invalid stack adjustment")
            zero_flag = None
        elif op in ("mov", "movabs") and args[0] in ("eax", "rax", "ecx"):
            dst, imm = args
            val = int(imm, 0)
            require(0 <= val < 2**(64 if dst == "rax" else 32), "immediate width")
            regs["rax" if dst == "eax" else dst] = val
        elif op == "vpbroadcastq" and args[1] == "rax":
            regs[args[0]] = regs["rax"]
        elif op == "vmovdqu64":
            dst, src = args
            load = src.startswith("[")
            base, offset = address(src if load else dst)
            require(offset % 64 == 0, "partial limb")
            if base == "rsp":
                require(sp == -frame and offset + 64 <= frame, "stack access")
            if load:
                require(base in ("rsi", "rdx", "rsp"), "unexpected read")
                regs[dst] = memory[base, offset]
            else:
                require(base == "rsp" or (base == "rdi" and offset < 640), "unexpected write")
                memory[base, offset] = regs[src]
        elif op == "lea" and args[0] == "r8":
            base, offset = address(args[1])
            require(base == "rsp" and sp == -frame, "invalid saved pair address")
            regs["r8"] = sp + offset
        elif op == "call":
            target = int(args[0], 16)
            require(sp == -frame and regs["zmm28"] == 19 and regs["zmm29"] == RADIX - 1,
                    "kernel precondition")
            outputs = []
            for stream in (0, 1):
                base = 5 * stream
                words = [regs[f"zmm{i}"] for i in range(base, base + 5)]
                left = whole_field(words, stream)
                require(fits(bounds[words[0].generation], SQUARE_MAX if target == square else INPUT_MAX),
                        "left operand exceeds kernel input bounds")
                right = left
                if target == multiply:
                    offset = regs["r8"] - sp + base * 64
                    saved = [memory["rsp", offset + i * 64] for i in range(5)]
                    right = whole_field(saved, stream)
                    require(fits(bounds[saved[0].generation], INPUT_MAX), "right operand bounds")
                outputs.extend(Limb(stream, left + right, steps, i) for i in range(5))
            bounds[steps] = SQUARE_MAX if target == square else OUTPUT_MAX
            for i in range(32):
                if i not in (28, 29):
                    regs.pop(f"zmm{i}", None)
            regs.update({f"zmm{i}": v for i, v in enumerate(outputs)})
        elif op == "dec" and args == ["ecx"]:
            regs["ecx"] = (regs["ecx"] - 1) % 2**32
            zero_flag = regs["ecx"] == 0
        elif op == "jne" and zero_flag is not None:
            if not zero_flag:
                next_pc = int(args[0], 16)
        elif op == "vzeroupper" and not args:
            for i in range(16):
                regs.pop(f"zmm{i}", None)
        elif op == "ret" and not args:
            require(sp == 0, "stack not restored")
            break
        else:
            raise ValueError(f"unsupported caller instruction at {pc:x}: {op} {args}")
        pc = next_pc

    for stream in (0, 1):
        out = [memory["rdi", (5 * stream + i) * 64] for i in range(5)]
        require(whole_field(out, stream) == EXPONENT, "wrong output exponent")
        require(fits(bounds[out[0].generation], OUTPUT_MAX), "output lacks proved limb bounds")


if __name__ == "__main__":
    prove_entry(sys.argv[1])
    print("Checked both field kernels, limb bounds, paired exponentiation and SysV frame.")
