"""Straight-line SysV probes for the typed vector instruction subset, one child per case."""
import ctypes
import mmap
import os
from pathlib import Path
import platform
import signal
import subprocess

from case_data import GPRS, OPS, registers


def require_host(cpu):
    required = {"avx512f", "avx512dq", "avx512ifma"}
    if platform.system() != "Linux" or platform.machine() != "x86_64":
        raise ValueError("native backend requires x86-64 Linux")
    missing = required.difference(cpu.get("flags", "").split())
    if missing:
        raise ValueError("native backend requires " + ", ".join(sorted(missing)))


def asm(instruction):
    op, *args = instruction
    if op == "vmovdqu64":
        dst, base, disp = args
        return f"{op} zmm{dst}, ZMMWORD PTR [{GPRS[base]} {disp:+d}]"
    operands = [f"zmm{n}" if kind == "r" else str(n) for kind, n in zip(OPS[op][1], args)]
    return op + " " + ", ".join(operands)


def wrapper(index, ins):
    name = f"probe_{index}"
    base = GPRS[ins[2]] if ins[0] == "vmovdqu64" else None
    state, saved = [r for r in ("r10", "r11", "r9") if r != base][:2]
    yield f".global {name}, {name}_ins, {name}_end"
    yield f"{name}:"
    yield f"mov {state}, rdi"
    for i in range(32):
        yield f"vmovdqu64 zmm{i}, [{state} + {64*i}]"
    if base:
        yield f"mov {saved}, {base}"
        yield f"mov {base}, rsi"
    yield f"{name}_ins:"
    yield asm(ins)
    yield f"{name}_end:"
    if base:
        yield f"mov {base}, {saved}"
    for i in range(32):
        yield f"vmovdqu64 [{state} + {64*i}], zmm{i}"
    yield "vzeroupper"
    yield "ret"


class Native:
    def __init__(self, work, instructions, cpu):
        self.cpu = cpu
        self.index = {ins: i for i, ins in enumerate(dict.fromkeys(map(tuple, instructions)))}
        source = work / "probes.S"
        with source.open("w") as f:
            print(".intel_syntax noprefix\n.text", file=f)
            for ins, index in self.index.items():
                print(*wrapper(index, ins), sep="\n", file=f)
            print('.section .note.GNU-stack,"",@progbits', file=f)
        library = work / "probes.so"
        subprocess.run(["cc", "-shared", "-nostdlib", source, "-o", library], check=True)
        self.lib = ctypes.CDLL(str(library))

    def execute(self, case, encoded):
        ins = case["instruction"]
        name = f"probe_{self.index[tuple(ins)]}"
        begin = ctypes.addressof(ctypes.c_char.in_dll(self.lib, name + "_ins"))
        end = ctypes.addressof(ctypes.c_char.in_dll(self.lib, name + "_end"))
        assembled = ctypes.string_at(begin, end - begin)
        if assembled != encoded:
            return {"assembled_bytes": assembled.hex()}
        fn = getattr(self.lib, name)
        fn.argtypes = [ctypes.c_void_p, ctypes.c_void_p]
        fn.restype = None
        # The child writes its entire ZMM register file back through shared memory.
        # Assemble only validated typed operands; no caller-supplied bytes are executed.
        with mmap.mmap(-1, 32 * 64) as state:
            initial = registers(case)
            state[:] = b"".join(n.to_bytes(8, "little") for reg in initial for n in reg)
            state_ptr = ctypes.addressof(ctypes.c_char.from_buffer(state))
            backing = ctypes.create_string_buffer(160)
            data_ptr = ((ctypes.addressof(backing) + 63) & ~63) + 1
            data = b"".join(x.to_bytes(8, "little") for x in case.get("memory", []))
            ctypes.memmove(data_ptr, data, len(data))
            base_ptr = data_ptr - ins[3] if ins[0] == "vmovdqu64" else 0
            pid = os.fork()
            if pid == 0:
                # A load may temporarily use RSP as its test address.
                try:
                    os.sched_setaffinity(0, {self.cpu})
                    signal.pthread_sigmask(signal.SIG_BLOCK, {signal.SIGINT, signal.SIGTERM, signal.SIGHUP})
                    fn(state_ptr, base_ptr)
                except BaseException:
                    os._exit(125)
                os._exit(0)
            _, status = os.waitpid(pid, 0)
            if status:
                return {"child_exit": os.waitstatus_to_exitcode(status)}
            words = [int.from_bytes(state[i:i+8], "little") for i in range(0, len(state), 8)]
        return {"registers": [words[i:i+8] for i in range(0, len(words), 8)]}


def execute_probe(name, work, encoded, inputs, cpu):
    """Execute the fixed probe only after checking its complete linked encoding."""
    src = Path(__file__).parent
    binary = work / f"{name}-probe"
    subprocess.run(["cc", src / f"{name}.S", src / f"{name}.c", src / "probe_main.c",
                    "-o", binary], check=True)
    observed = {"bytes": subprocess.check_output([binary, "--bytes"], text=True).strip()}
    if observed["bytes"] == encoded.hex():
        counts = "".join(f"{n}\n" for n in inputs)
        try:
            result = subprocess.run([binary], input=counts, capture_output=True, text=True, timeout=10,
                                    preexec_fn=lambda: os.sched_setaffinity(0, {cpu}))
        except subprocess.TimeoutExpired:
            return {**observed, "timeout": True}
        if result.returncode:
            observed["exit"] = result.returncode
        else:
            observed["rows"] = [list(map(int, row.split())) for row in result.stdout.splitlines()]
    return observed
