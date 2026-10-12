# Pinned Lean verification tooling assessment

Date: 2026-10-12. Target public repository commit: `5dc4278b24e5f10db0c006b0cb9ecf30857ffaca`.

## Confirmed executable path

The project pins `leanprover/lean4:v4.31.0-rc1`, compiler source commit `fd009949156901e6cf15b6d9bf1122294b8e697a`. The official x86_64 Linux distribution was downloaded directly from the Lean GitHub release. Its SHA-256 is `055f1780f20f9774bbe270d5d4cf7561fb26ee6734c0917ba6cfb867e33cb99e`, independently computed and matched to the digest returned by the official GitHub release API. Its `bin/leanchecker` exists.

Use this exact toolchain's bundled checker:

```
lake env leanchecker --fresh Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceFixedDimension670
```

The pinned `src/lean/LeanChecker.lean` confirms that `--fresh` loads the chosen module and replays its complete imported declaration environment into `mkEmptyEnvironment` through Lean's kernel. This is stronger than checking only newly declared project constants, but it is not a separately implemented kernel and still trusts the structural validity of `.olean` files. `#print axioms` should be performed separately on the six named deliverable declarations, rejecting everything outside `propext`, `Classical.choice`, and `Quot.sound`.

The separate lean4checker repository is now deprecated (README observed at `91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709`). Its default toolchain is v4.29.0-rc8; blindly building its default branch would be an inappropriate way to obtain the pinned project's checker.

Caution: the bundled v4.31 checker has no help switch. Unknown flags are ignored, and a flags-only invocation can trigger checking a default module set. An exploratory `leanchecker --help` outside the project was interrupted; it is not counted as a verification result.

## Stronger comparator and external checker route

An exact matching official Comparator tag exists:

- Repository: https://github.com/leanprover/comparator
- Tag: `v4.31.0-rc1`
- Commit: `3afea238d63125383110f8b59acaf11d7788c3e1`
- Its locked exporter: https://github.com/leanprover/lean4export at `cd502a76e05515e7d3e09eaefee1dfd8349ca592`, also the exporter's `v4.31.0-rc1` tag
- Its additional locked Lean4Checker library: `b7398199245524275543dec6113229c9bb4902e5`

The pinned Comparator README and manifest were inspected directly. This version uses a separately built comparator executable invoked under `lake env`; the project's Lake 5.0.0-src+fd00994 does not list a `lake comparator` command. Its documented external-kernel option is `enable_nanoda: true`. Do not assume current documentation's newer generic `external_kernels` interface works on this tag.

A meaningful full Comparator run requires:

1. An independently reviewed challenge theorem and its referenced definitions in a trusted environment, matching the intended Euclidean dimension, range of n, separation and diameter conclusions. Importing the solution into the challenge would undermine statement-independence.
2. Pinned Comparator and exporter builds without changing the research package's lockfile.
3. Real Landrun isolation for solution compilation/export, with the pinned README's additional AF_UNIX restriction. Development `fake-landrun.sh` is not equivalent protection.
4. A separately built Nanoda checker from the official repository referenced by Lean's guidance, with version/commit and export-format compatibility recorded. The pinned comparator does not itself lock Nanoda.
5. Only the three standard axioms permitted, all relevant final theorem names compared, and terminal successful logs from both checking kernels.

This workspace does not have Landrun or Cargo installed. More importantly, a direct check of the documented systemd user isolation route failed: `Failed to connect to user scope bus via local transport: Operation not permitted`. No workaround or security bypass was attempted. Therefore no malicious-proof-isolated Comparator/Nanoda result is claimed here. Constructing that independent trusted challenge and approved isolation is distinct from merely rebuilding the package.

## Sources

- Official Lean validation guidance: https://lean-lang.org/doc/reference/latest/ValidatingProofs/
- Official release: https://github.com/leanprover/lean4/releases/tag/v4.31.0-rc1
- Pinned built-in checker: https://github.com/leanprover/lean4/blob/fd009949156901e6cf15b6d9bf1122294b8e697a/src/LeanChecker.lean
- Pinned comparator instructions: https://github.com/leanprover/comparator/blob/3afea238d63125383110f8b59acaf11d7788c3e1/README.md
- Pinned comparator dependencies: https://github.com/leanprover/comparator/blob/3afea238d63125383110f8b59acaf11d7788c3e1/lake-manifest.json
- Nanoda source referenced by official guidance: https://github.com/ammkrn/nanoda_lib
