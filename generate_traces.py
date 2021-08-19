#!/usr/bin/env python3

import subprocess as sp
import os

ISLA_FOOTPRINT = "./run_isla_footprint.sh"
ISLA_SNAPSHOT = os.path.abspath("../isla-snapshots/aarch64.ir")
ISLA_CONFIG = os.path.abspath("./aarch64_isla_coq.toml")
ISLA_ARGS = [
    "-A", ISLA_SNAPSHOT,
    "-C", ISLA_CONFIG,
    "-f", "isla_footprint_no_init",
    "-s",
    "--simplify-registers",
]

ISLA_COQ_FRONTEND = [ "dune", "exec", "--", "isla-coq" ]

INSTRUCTIONS_DIR = "instructions"

INSTRUCTIONS = {
    "stp" : {
        "instruction" : "stp x0, x1, [sp, #-16]!",
        "constraints" : [
            '= (bvand SP_EL2 0xfff0000000000007) 0x0000000000000000',
            'bvugt SP_EL2 0x0000000000000010'
        ]
    },
    "load" : {
        "instruction" : "ldr x0, [x1]",
        "constraints" : [
            '= (bvand R1 0xfff0000000000007) 0x0000000000000000',
        ]
    },
    "store" : {
        "instruction" : "str x9, [x1]",
        "constraints" : [
            '= (bvand R1 0xfff0000000000007) 0x0000000000000000',
        ]
    },
    "b_0x8" : {
        "instruction" : "b 0x8",
    },
    "bl_0x100" : {
        "instruction" : "bl 0x100",
    },
    # "bne_0xc" : {
        # "instruction" : "bne 0xc",
    # },
    "mov_w0_0" : {
        "instruction" : "mov w0, 0",
    },
    "mov_x0_1" : {
        "instruction" : "mov x0, 1",
    },
    "ret" : {
        "instruction" : "ret",
    },
    "mov_x28_x0" : {
        "instruction" : "mov x28, x0",
    },
    "cmp_x1_0" : {
        "instruction" : "cmp x1, 0",
    },
}

IGNORED_REGISTER_NAMES = [
    "SEE",
    "BTypeNext",
    "__unconditional",
    "__v81_implemented",
    "__v82_implemented",
    "__v83_implemented",
    "__v84_implemented",
    "__v85_implemented",
    "__trickbox_enabled",
    "__CNTControlBase",
    "__defaultRAM",
    "__isla_monomorphize_reads",
    "__isla_monomorphize_writes",
    "__highest_el_aarch32",
]
IGNORE_LINES_CONTAINING = \
    ["Cycle"] + \
    ["ReadReg \"" + r + "\"" for r in IGNORED_REGISTER_NAMES] + \
    ["WriteReg \"" + r + "\"" for r in IGNORED_REGISTER_NAMES]

def main():
    for name, data in INSTRUCTIONS.items():
        trace_file = os.path.join(INSTRUCTIONS_DIR, name + ".isla")
        original_coq_file = os.path.join(INSTRUCTIONS_DIR, name + "_original.v")
        coq_file = os.path.join(INSTRUCTIONS_DIR, name + ".v")
        definition_name = name + "_trace"

        # run isla-footprint
        with open(trace_file, "w") as f:
            sp.run([ISLA_FOOTPRINT] + ISLA_ARGS
                   + ["-i", data["instruction"]]
                   + [y for x in data.get("constraints", []) for y in ["--reset-constraint", x]],
                   stdout=f)

        # run isla-coq fronteng
        sp.run(ISLA_COQ_FRONTEND + [
            "--definition-name=" + definition_name,
            "-o", original_coq_file,
            trace_file])

        # comment out lines with irrelevant instructions
        with open(original_coq_file, "r") as fin:
            with open(coq_file, "w") as fout:
                for line in fin:
                    if any(s in line for s in IGNORE_LINES_CONTAINING):
                        fout.write("(*" + line.rstrip("\n") + "*)\n")
                    else:
                        fout.write(line)

        os.remove(original_coq_file)

if __name__ == "__main__":
    main()
