# Independent Linux verification of fixed-dimension Erdős 670

**Result: PASS. Completed 12 October 2026, 21:02 UTC.**

The public source snapshot was independently rebuilt on a separate x86_64 Linux machine. All 54 project modules compiled, all six audited declarations depended only on the three standard Lean axioms, and the official pinned Lean checker successfully replayed the entire imported declaration environment from an empty environment.

## Exact identities

- Public repository: https://github.com/jjtripodo-lgtm/erdos-670-fixed-dimension
- Verified public commit: `5dc4278b24e5f10db0c006b0cb9ecf30857ffaca`
- Exported proof-source pin recorded by the repository: `35c67a69e009c9ca27267077608864987b7e2851`
- Lean: `leanprover/lean4:v4.31.0-rc1`, compiler commit `fd009949156901e6cf15b6d9bf1122294b8e697a`
- Mathlib: `0ed37c9258f123a2c76a2175596f75c2bd50f941`
- Official Linux toolchain archive SHA-256: `055f1780f20f9774bbe270d5d4cf7561fb26ee6734c0917ba6cfb867e33cb99e`; computed locally and matched to the official GitHub release API digest

## Completed checks

1. All 154 distributed candidate files matched their recorded hashes and byte counts; the exact 54-module import closure, source hashes, dependency lock and toolchain matched
2. Nine public dependency repositories were freshly fetched at the committed hashes, with clean checkouts and initially zero compiled upstream outputs
3. The official Mathlib cache utility was built from its pinned source. It downloaded and decompressed all 3,421 requested upstream cache archives from the official Azure endpoint. SHA-256 hashes of every downloaded archive are included. The cache utility itself added six locally built upstream modules, giving 3,427 upstream `.olean` files before project replay
4. From zero project `.olean` files, all 54 module builds, the final default build, and the six-declaration trust-zero axiom audit succeeded: **56/56 commands, all exit 0**, producing exactly the 54 expected project `.olean` paths. Project replay took **870.962 seconds**
5. Every audited declaration, including `fixed_dimension_erdos_670`, reported exactly `propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx`, native-evaluation axiom, or custom axiom occurred in these dependencies
6. `lake env leanchecker --fresh Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceFixedDimension670` exited **0** after **1,510.504 seconds**. The pinned checker emits no success text by default, so its zero-byte output log is expected; the process exit, duration and log digest are recorded separately
7. Source identities and all nine dependency pins/cleanliness were rechecked after kernel replay. The public checkout remained clean at the exact verified commit. An additional receipt validator checked all 56 new log hashes, command structures, module paths and six axiom results
8. The supplied 11 negative receipt cases were rejected, and the manuscript's 34 supplementary rational-arithmetic/reference checks passed. These are supplementary checks, not substitutes for Lean verification

There were 43 distinct ordinary lint/deprecation warning locations. They concerned unused variables/simp arguments, unnecessary tactic sequencing, tactic suggestions and deprecated names. The original warnings are preserved in the build logs.

## Scope

This run used fresh project sources and fresh pinned upstream source checkouts, **with freshly downloaded official upstream compiled caches**. It was not a complete upstream source rebuild. The fresh checker replay validated the imported declaration environment through Lean's own kernel; it was not a separately implemented kernel and does not authenticate source-to-binary correspondence for the upstream cache. Comparator/Nanoda challenge comparison was not executed. See `TOOL_COMPATIBILITY.md` for the exact-version-compatible stronger route and verified isolation limitation.

## Evidence layout

- `replay/RECEIPT.json` and 56 `.log` files: original project replay record, byte-for-byte
- `FRESH_KERNEL_REPLAY_RECEIPT.json`: exact fresh-kernel command, terminal exit and toolchain identity
- `logs/fresh_kernel_replay.log`: original checker output (empty on this successful run)
- `logs/driver.log`: original orchestration progress and terminal successful exits
- `INDEPENDENT_VERIFICATION.sanitized.json`: driver metadata with only local absolute paths replaced; replacements and original-file digest are explicitly identified
- `INDEPENDENT_RECEIPT_VALIDATION.json`: post-run validation of the actual produced files and logs, including warning headers
- `source-pins/`: copied public source manifest, lock, toolchain and axiom-audit source
- `logs/official-release-provenance.json`: official release URL and digest
- `logs/downloaded-cache-sha256.json`: all 3,421 downloaded upstream cache archive hashes
- `MANIFEST_SHA256.json`: hashes and byte counts of every other file in this evidence bundle
- `validate_bundle.py`: portable artifact integrity and internal-consistency validator

All proof/build/checker logs and the original project replay receipt are unmodified. The original absolute-path driver metadata and irrelevant transport/fetch logs are retained separately. Signed release-download redirect URLs, local usernames, host identifiers and local filesystem locations are excluded from this distribution. Public GitHub repository names and ordinary public upstream URLs are retained.

## Reproduce on another Linux machine

Use a clean directory and the official Lean toolchain above. Do not run `lake update`, which can change the lock. Install/select the exact official toolchain with Elan, or extract the official Linux distribution and verify the SHA-256 above. Make its `lean`, `lake`, and `leanchecker` executables available on `PATH`.

From this bundle's directory, use a new checkout name if `repo` already exists:

```sh
git clone https://github.com/jjtripodo-lgtm/erdos-670-fixed-dimension.git repo
git -C repo checkout --detach 5dc4278b24e5f10db0c006b0cb9ecf30857ffaca
python3 repo/verify_candidate.py
python3 repo/lean-fixed670/prepare_dependencies.py --fetch
cd repo/lean-fixed670
lake --version
lake exe cache get $(cat ../../mathlib-imports.txt)
python3 prepare_dependencies.py
python3 verify_sources.py
python3 replay.py --output ../../new-replay
lake env leanchecker --fresh Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceFixedDimension670
python3 verify_sources.py
python3 prepare_dependencies.py
```

`new-replay` must not already exist, and project outputs must initially be absent. Omitting the cache step changes this to a more resource-intensive upstream source build; that is a different execution mode from the run documented here.

To validate this evidence bundle without running Lean, run `python3 validate_bundle.py`. This checks archived evidence integrity and consistency, not a new proof compilation.
