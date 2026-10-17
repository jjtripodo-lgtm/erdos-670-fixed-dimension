# Fresh-kernel replay: exact scope

The checker used is the official Lean 4.31.0-rc1 Linux x86_64 distribution's
`leanchecker`, compiler source commit `fd009949156901e6cf15b6d9bf1122294b8e697a`.
Its executable, shared libraries and relevant bundled source hashes are recorded
in `TOOLCHAIN_BINARY_HASHES.json`; the full distribution archive hash is in
`TOOLCHAIN.json`. No files were omitted from this installation.

The command is `lake env leanchecker --fresh --verbose Erdos670Bridge.Bridge`.
The bundled [LeanChecker.lean](https://github.com/leanprover/lean4/blob/fd009949156901e6cf15b6d9bf1122294b8e697a/src/LeanChecker.lean)
loads that target module and calls `mkEmptyEnvironment.replay env.constants.map₁`.
Thus the fresh option replays the loaded imported constants as well as those
defined in the final adapter, rather than trusting an already constructed
import environment as the starting kernel environment.

The bundled [Lean/Replay.lean](https://github.com/leanprover/lean4/blob/fd009949156901e6cf15b6d9bf1122294b8e697a/src/Lean/Replay.lean)
sends safe, non-partial declarations to the kernel with trust level zero,
orders dependencies, and compares constructors/recursors with regenerated
ones. It explicitly skips unsafe and partial constants. It also has a
same-name/type/parameters duplicate-theorem case for module-system private
theorems. Axioms are declarations the checker can accept; this is why the
separate endpoint-specific transitive `#print axioms` audit is indispensable.

This is an additional consistency check against malformed or modified imported
proof environments using the **same official Lean kernel implementation**.
It is not an external proof checker, independent second machine, full rebuild
of dependency sources, or a specialist mathematical review. Cache provenance
and the mismatch with current upstream Formal Conjectures versions remain
separate limitations. Success is claimed only when the execution receipt
records this exact command's exit code zero and binds its actual log.
