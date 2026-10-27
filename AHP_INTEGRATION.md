# AHP fidelity integration

> **Historical first integration report.** The 18-module / 58-record figures below describe the initial integration. The public snapshot also includes the two later S-1 modules and six further records, for 20 additional modules and 64 additional main records. Its core totals are 2,782 modules and 572 main records plus R7. See [RELEASE.md](RELEASE.md). No historical evidence has been promoted by this note.

Branch: `ahp-integration`. Worktree: `/home/sebastian/BalabanCoercivityLemma-integrate`.
Base: `de2ca59d80e2944ef2ca07fe340b26190377d138`.

**Status: ALL CHECKS PASSED**, 2026-10-22 21:10:37 UTC. All 58 complete new axiom records passed the full raw-output audit.

## Added

18 accepted modules, registered as roots of the new `AHPFidelity` library and in `lean/MODULES.tsv`:

| Integrated module | Accepted original source (under `AHP/`) | Check |
|---|---|---|
| `AHP.CoverageRow` | `fidelity/coverage-row/lean/CoverageRow.lean` | 9 |
| `AHP.JetBoundaryComparison` | `fidelity/s3-normalisation/lean/JetBoundaryComparison.lean` | 10 |
| `AHP.ShellComparison` | `fidelity/s1-touching/lean/ShellComparison.lean` | 10 |
| `AHP.ClassInclusion` | `fidelity/s2-inclusion/lean/ClassInclusion.lean` | 10 |
| `AHP.CollarNonStrict` | `fidelity/sheet-variants/lean/CollarNonStrict.lean` | 10 |
| `AHP.ReadingB` | `fidelity/sheet-variants/lean/ReadingB.lean` | 10 |
| `AHP.LambdaScale` | `fidelity/sheet-variants/lean/LambdaScale.lean` | 10 |
| `AHP.GlobalGauge` | `fidelity/sheet-variants/lean/GlobalGauge.lean` | 10 |
| `AHP.NormHS` | `fidelity/sheet-variants/lean/NormHS.lean` | 10 |
| `AHP.QuantifierOrder` | `fidelity/sheet-variants/lean/QuantifierOrder.lean` | 10 |
| `AHP.UthCross` | `fidelity/guarded/lean/UthCross.lean` | 10 |
| `AHP.S2Nonvacuity` | `round2/s2-nonvacuity/r1-prove/Attempt.lean` | 11 |
| `AHP.S2CornerSaturation` | `round2/s2-nonvacuity/r1-refute/Attempt.lean` | 12 |
| `AHP.S1CornerCollapse` | `round2/s1-touching/r1-prove/Attempt.lean` | 13 |
| `AHP.S1TouchingRefutation` | `round3/s1-proper/r1-refute/Attempt.lean` | 14 |
| `AHP.S3FirstTerm` | `round2/s3-normalisation/r1-prove/Attempt.lean` | 15 |
| `AHP.S3FullComparison` | `round5/s3-raw/s3raw-r1/Attempt.lean` | 16 |
| `AHP.S2OddNonvacuity` | `round7/s2-odd/r1/Attempt.lean` | 17 |

The files live under `lean/src/AHP/`. `Check9.lean`--`Check17.lean` check 58 declarations: 45 accepted Stage B records (including its three sheet helpers), plus 13 closing or strengthening declarations. There is one new `fid-*` LEAN claim row per checked declaration. The expected main output has 566 lines; its original 508 lines are unchanged. `REPRODUCE.sh` already discovers numbered Check files in version order and was not edited.

`paper/OPEN_ITEMS.md` section T records the exact results and limits. The paper TeX/PDF and all of `notes/` remain unchanged. In particular, the owner still needs to apply `AHP/fidelity/coverage-row/ROW6.md` to statement-sheet row 6.

## Source fidelity and renames

No proof, statement, import or declaration name was changed. Only standalone `#print axioms` and `#check` diagnostic lines were removed from the copied sources. The accepted Stage B and closing-declaration axiom prints are in the numbered Check files; auxiliary diagnostic inventories are not promoted to extra claims.

All 18 file-to-module path changes are recorded in `lean/RENAMES.tsv`. There are **no declaration renames**. Separate Check environments preserve repeated copied definitions, notably the round-two S-2 pin reused in three modules and the S-3 first-term definitions embedded in the full comparison. The coverage module is also isolated from the older conflicting lane environments. The raw S-3 source already contains the normalized round-three proof, so the round-three s3-rest source was not duplicated.

The provenance table below records original source and independent verification report/log hashes; integrated module hashes are in `lean/MODULES.tsv`, and selected declarations and axiom records are in the Check files and claims ledger. The AHP review paths refer to the original files in `/home/sebastian/BalabanCoercivityLemma`, not new copies of unaccepted attempts. A byte-level audit verifies that each module differs from its accepted source only by removal of diagnostic lines. Existing module/claim/rename rows and expected axiom lines are retained as unchanged prefixes. Removing diagnostics leaves existing blank separators at EOF in 12 copied modules; these are deliberately retained for byte-level source fidelity. Default `git diff --check` reports only those blank-at-EOF warnings; the check passes with `core.whitespace=-blank-at-eof`.

## Acceptance boundary

- S-1: the round-three exact unguarded touching headline is refuted at \(\ell = 2\) through a singular carrier and totalised inverses. Round-two corner-coverage collapse is a separate positive reduction. No guarded or unqualified printed refutation is claimed.
- S-2: class comparisons and proper-domain four-bond non-vacuity are included. The independently accepted round-seven result covers every \(\ell \ge 2\), including odd \(\ell > 11\), with flat depth-two witnesses. It does not identify the printed class or establish non-flat richness.
- S-3: both linked H/C conventions and both raw/normalized constraints match exactly with constant 1 and unchanged mass, under the original inverse guards and disclosed source conventions.
- Guarded all-plaquette reading: **OPEN**. The Stage B flat-path comparison is not a counterexample; `AHP/round6/RESULTS.md` remains the later record, with evidence undetermined for the statement.
- Round-seven S-1 odd: excluded because neither supplied independent verification closes the goal. No every-ell S-1 claim is integrated.
- Round-seven S-4 odd sites-only: excluded because no goal closes. The analytic odd sites-only cell remains open.
- No sources from `AHP/attempts/`, round 4, round 5 guarded, round 6, or any other unaccepted attempt are integrated. No Compact modules or other-thread lakefile changes were brought over.

## Verification

Static audit: passed (18 exact diagnostic-only copies; 58 matching checks/claims; allowed source constructs; frozen imports only; original 508 expected lines unchanged; original Lake libraries unchanged).

The reproduction was started only in this worktree, under a heavy slot, with:

```sh
cd /home/sebastian/BalabanCoercivityLemma-integrate
export PATH="$HOME/.elan/bin:$PATH"
nohup setsid "$BB_CLI" heavy run -- env MAX_LEAN=2 LEAN_NUM_THREADS=1 MIN_AVAIL_GB=6 \
  PACKAGES_FROM=/home/sebastian/BalabanCoercivityLemma-integrate/lean/.lake/packages \
  ./REPRODUCE.sh > reproduce.stdout 2>&1 < /dev/null &
```

The first full run compiled all 18 modules successfully (`lake build exit=0 after 8141 s`) but exposed an unsupported `pp.width` option in the generated Check files. A retry was aborted during legacy Check3 by the host restart at 2026-10-22 19:50 UTC; all its processes were confirmed gone before restarting. The post-restart sweep compiled every Check file successfully, exposing only five wrapped-record formatting differences. Both the unsupported option and the ineffective local `format.width` replacement were removed from the generated Checks. No accepted module, proof, statement, import or declaration name was changed.

Lean 4.31's console message serializer wraps five long new axiom records; the existing `REPRODUCE.sh` filter retains their first lines. The 58 appended expectations now follow that existing literal-output convention, including those five first lines. The original 508 lines and the reproduction script remain byte-for-byte unchanged. This is not an axiom-set relaxation: all 58 **complete** new records, including continuation lines in `Check9.raw`--`Check17.raw`, were normalized only for whitespace and checked for exact equality with the accepted independent verification records and for dependencies contained in `{propext, Classical.choice, Quot.sound}`. `paper/CLAIMS.tsv` retains the complete records. The final full reproduction and the complete-record audit both passed.

Original 508-line SHA-256: `c4dbb5335f408172921f9f958c25983f25658a00e9a0b7384ac0394b56807a65`.
Final 566-line SHA-256: `10ef33d78fc7349bcc6208ddc1393531cdea17bfdbbb493883fb82b68f52ef59`.

Final `reproduce.log` summary (2026-10-22, UTC):

```text
[21:09:35] toolchain pin: leanprover/lean4:v4.31.0
[21:09:35] lean: Lean (version 4.31.0, x86_64-unknown-linux-gnu, commit 68218e876d2a38b1985b8590fff244a83c321783, Release)
[21:09:35] offline mode: copying packages from /home/sebastian/BalabanCoercivityLemma-integrate/lean/.lake/packages
[21:09:35] lake build (MAX_LEAN=2, threads/process=1); this takes many hours on a cold tree
[21:09:40] lake build exit=0 after 5 s
[21:09:40] modules in project: 2780
[21:09:43] Check1.lean exit=0; axiom lines: 315
[21:09:46] Check2.lean exit=0; axiom lines: 2
[21:09:49] Check3.lean exit=0; axiom lines: 19
[21:09:52] Check4.lean exit=0; axiom lines: 61
[21:09:55] Check5.lean exit=0; axiom lines: 19
[21:09:58] Check6.lean exit=0; axiom lines: 14
[21:10:01] Check7.lean exit=0; axiom lines: 29
[21:10:04] Check8.lean exit=0; axiom lines: 49
[21:10:07] Check9.lean exit=0; axiom lines: 3
[21:10:10] Check10.lean exit=0; axiom lines: 42
[21:10:14] Check11.lean exit=0; axiom lines: 1
[21:10:17] Check12.lean exit=0; axiom lines: 2
[21:10:20] Check13.lean exit=0; axiom lines: 2
[21:10:22] Check14.lean exit=0; axiom lines: 1
[21:10:25] Check15.lean exit=0; axiom lines: 2
[21:10:28] Check16.lean exit=0; axiom lines: 3
[21:10:30] Check17.lean exit=0; axiom lines: 2
[21:10:34] CheckR7.lean exit=0; axiom lines: 1
[21:10:34] PASS: Check axiom output identical to axioms.expected.txt (566 lines)
[21:10:34] PASS: CheckR7 axiom output identical to axioms.r7.expected.txt (1 lines)
[21:10:37] PASS: forbidden-token scan equals expected list (5 modules; see HANDOFF.md)
[21:10:37] ALL CHECKS PASSED
```

## Commit

Integration commit: `07d1bae02873ae6cb93fb6ecc0e8a12f1e14c9bf`.

This report is committed in a documentation-only follow-up so that it can record the actual integration commit hash. Both commits remain local on `ahp-integration`; no push or merge was performed.

## Provenance hashes

Integrated module hashes and original source paths are in `lean/MODULES.tsv`. These SHA-256 values identify the exact accepted original sources and their independent review records in the main checkout.

| Module | Original source SHA-256 | Verification report SHA-256 | Independent log SHA-256 |
|---|---|---|---|
| `AHP.CoverageRow` | `9f60a35f39ecdeabf97ac3f25212997220cf070373f3a63f20c6cd31b81b12e2` | `10c17a59d65520b466df6df179fc7d1180accbbc74ac0cc3c9244073f41d9bb2` | `05d23d75181ef85e8d929e5763a1b0b416a3829fef8e0bb0a05c34338c805374` |
| `AHP.JetBoundaryComparison` | `5bb512bb0d3e40cb91213473180cc9bd1eb3e6eade9879cea36b29fbccfcf8c0` | `174e4d586b7c59a84c96a6b59dccc9f1ebdd52b9350cd0ddb36671d609274efb` | `2907ccde917a8e1da1fe9d335cd65fd80164e0b2f5e7ffdda9448fc8e3c7a478` |
| `AHP.ShellComparison` | `358c72f814cb755a50659c55603b9ef4d6faddfeafc10fddc3d2c388366923b8` | `70762116db8c702a49619001d7297ad401749d36d953d2f5f9fb70528e727954` | `d91fb2a26074c8d990b7c3c133053323332591772f0e5229960d6a1fbb16a25d` |
| `AHP.ClassInclusion` | `f3dabe1f66f069d97943debb296d6ebb23af764389b0f68f8e51c06e0dfed002` | `239f7562313336a924233d62874e3d32accf4c59880b623effecd008d8ca0e3a` | `3e78c85ff8690585d13af85189ec5a0fcab1ee4373bb21174ca09954819d8182` |
| `AHP.CollarNonStrict` | `3d37f3fd397449588c754546302e5d02db65d29316e69fae08ac97c465553fa0` | `0a1ae12676273cf93e65e893eb48d2eb044a3c9df4ef6ff595cee530f2e61bf3` | `5f1d9577cec4e1ccc2d92e3def74ed8749fde8139a3de4f37fbdde709809e864` |
| `AHP.ReadingB` | `0bb62eca78a15ad9c1f6235c7596a25735f1fc0af09db00b29fb727bc10a9b3c` | `0f033d389ccb73e83561f670f404a8cb2ce0630b301ec22af5ce1117d7c53905` | `d8298d5459635ef5c6d7a887dc4820dd31e0f81cd45d49228e97049971136c99` |
| `AHP.LambdaScale` | `0d1d59cad99bd2cd23e9a8f9280398cd72f331b93afbac83f08cbec8fa6b95d7` | `6b12449d131e2f930250149ef6ab14c1aa6888bab87624722124856694da2ca2` | `8e751e90feda9b44163a56308f55b0923df1952cd36debb253a49c69fc07131d` |
| `AHP.GlobalGauge` | `b4eb7a7b13b99e75d638dd6d4c51af7b3df34f95032a1939d9656b5b373d72f0` | `069e147f5a46997ca9160ee811b6cc39275bd1f3d3aa1ebaf9fe3f4c84fb0a1f` | `36945c48b2d2cb1b63bf5232820cc157ca0cff82f3bf0c68ba081c48b9bc1504` |
| `AHP.NormHS` | `7a19645bb0c7b5c25b5539fcdbd9451a19a8f44aea7adefb6d61150bd7ecf304` | `22067ffe808d0742a846238aed7fd1c5613d4131b57bf5c16bd0d99de27b09b5` | `acdb0168c22cd62617bd769638921f6fcbbb52db213334d1bb76509964c84ccc` |
| `AHP.QuantifierOrder` | `af934ea7d9b3e4ef592058c70ac0d110916b929b98812e44ea58488e370dc5eb` | `eb8e3a73e8d53318df861c15e3ab9903ebd588ead43fd751377681dcaaadbaa0` | `2ad09b5886d8ef279a48a0d8322b4faf6d5e159955cce8202a8b546353313629` |
| `AHP.UthCross` | `f206f691c8d56be9a6ba73c9c5992be3d34bc0ec67e076b96e99cb51f00fa63b` | `f4d137087114ee337cb6552c758babe9ee96f48a1f4eae90f63532725141f40c` | `725cc202453cfe2a657117322331aec75e7a9069db0930525e67c8ce8b944880` |
| `AHP.S2Nonvacuity` | `2e2d384afeab5a5fa1a0249c7e3960eef91078888b071463bf0228538cc07f8a` | `ab557065f27e053941ed2d2804708e2bf509f831f25e48e985d77c7e44eae6b5` | `86d57db2e18abd87b059282160b6b026cdfa7a303e3ece6212d2d584ed6498b5` |
| `AHP.S2CornerSaturation` | `c4a1d4d0614dd1fcf700219fbd12fd03349a4b7f600dea0da15d678dfb553ccd` | `161856697a1e6b9527c2e6b7705240aab9820eabd3b9512ff11f9ebed7606fa3` | `e1655d2cf3f404d10c43c6b276067885c95561679d1b535a009e9b71be67de56` |
| `AHP.S1CornerCollapse` | `d45e27d564812a3b7679b3efdaad008ba833a74604dac5dc66cf32fd78bc5d40` | `af965477c09d92b7de2c14c01d53dfe7e44d548dca9687b87f83e6017bf406eb` | `153aef38bce2a0d463ab46fd1907e808a32d11075111d53410026def37385b40` |
| `AHP.S1TouchingRefutation` | `a114b3d28b83d02b8d38df0f26cfac3d1485bb4cb72bdcd0150bd392e79a0280` | `71e48035e203fbdba3c008cddf37880dd3724f09e6b06d6fd4b38bcc6606ba32` | `fb72117ac68c0ad97b024c2bcc461adea36b2e07cd1faf9e8b3e090137849b40` |
| `AHP.S3FirstTerm` | `67908d7b3f5a0b882fdbf32376f130e800709d78e1747b43ad6cfaa116d5aa47` | `43d7411eab0a8a50578b2785d2872e9cdb8701a36ffa1251cd3fa6f72d806919` | `5c6c392d4679225a0cbaf8165cd390e9c92b79bbb2bfb93f332214d998622d99` |
| `AHP.S3FullComparison` | `33ce45abad8892fc2c522708add52f2121b07f647b8e4953b00b7a74fe3ad9e1` | `ff20d37c5d9911f63d02e6af853605aeefa0654bd070e8af6615932d90de9b4f` | `bdade3583f20d55d7b4a62c62e3b796413a01578c7d63f9ed5425b374ab528e4` |
| `AHP.S2OddNonvacuity` | `000f5c6e860d67172468f2fa762344fd17de9586943ecc9c3b9c4659723ee835` | `6cc722c95ba22098a0b67c1bbc80ede0630b30f27c1b4260f7ca91ca2d503d9c` | `f671f4866cc7c562f5338fffb1e3b4c85c484e04077dd8ab4fa6023dc091bf74` |
