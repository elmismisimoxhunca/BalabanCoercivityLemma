# ATTACK — s1-touching (stage A design review)

Reviewer pass over `AHP/fidelity/s1-touching/SPEC.md`, `numerics/shell_touch.py`, `numerics/results.json`, against `HANDOFF.md`, `paper/OPEN_ITEMS.md` (B, K–N, R, S) and `notes/statement_sheet.tex`. Nothing here was compiled; no Lean was run. All conclusions below are about fidelity and honesty of the stage-A package, not about the truth of `P428Target8Shell`.

New artifact from this review: `numerics/attack_check.py` / `numerics/attack_check.json` (reproduction of `results.json`, an eigenmode decomposition the SPEC quotes but never computes, bond-set inclusion checks, cap arithmetic, and the monotonicity core of the rewrite obstruction).

## Verdict

**Survives with one required repair and minor citation drift.** The variant says what it claims about the print; the hypothesis class provably admits a proper nonempty \(\Omega_0\); the transcribed operators match the cited Lean definitions in content; the tolerances are honest. One SPEC sentence quotes numbers (`+0.024`, \(-0.281\), `4.6`) that the recorded script cannot produce and attributes them to the wrong configuration. The prediction "unknown / counterexample more likely than a rewrite (against the literal class), shell statement undecided" is the correct epistemic state and is not oversold.

## 1. Does the variant say what it claims about the print?

Yes.

- The print sentences used are the same ones the project record uses: (3.10)/(3.11) sum over all plaquettes of \(T_\eta\) (statement sheet A9: "The print sums (3.10), (3.11) over *all* plaquettes"), and the CMP 102 p.277 convention is quoted in `OPEN_ITEMS.md` S-1 verbatim as the SPEC paraphrases it (bonds with at least one end-point, plaquettes with at least one corner).
- Frozen `plaqIn` (`ZR2Ops2.lean:74`) is both-endpoints on all four boundary edges, which is exactly "all four corners"; the script's `plaq_kind == "in"` is the same set. Frozen `CubeBond` (`ZStatementP428.lean:145`) is both-endpoints. Verified at the cited lines.
- The SPEC is explicit that `ReadBond` is **stronger** than the literal CMP 102 bond sentence and calls itself "the plaquette sentence pushed onto every bond that plaquette reads". It does not claim to be the literal S-1 reading, so it cannot be faulted for failing to be one. It correctly disclaims `CoversPlaqCorner` (the rejected predecessor's collapse mechanism, `AHP/attempts/s1-touching/SOL_VERDICT.md`, verdict "reject", confirmed on disk) and disclaims `plaqCorner = plaqIn` and any conclusion of the frozen `InstIneq`.
- The claim that class cubes sit in \(\Omega_0\): `DescribedAt` puts the box in \(B^j\cup B^{j+1}\subseteq\Omega_j\subseteq\Omega_0\), and `classCube_sub_om0` exists (at `D1Final.lean:36`; SPEC says `:35`, off by one).
- `P428Target8Shell`'s quantifier block was compared line by line against `P428Target8` (`ZT5A.lean:291`) and the `P428Core8` expansion (`ZT5A.lean:170–174`): same order \(\ell,a,m_0,m,R_0,R\), `SidePow6` conjunct in the same place, \(a_0,\gamma_0\) before \(k\ge1\), `(12:ℝ)·M·α₀ ≤ a₀`, `TorusOK`/`Admissible`/`LambdaOK2` order, \(\eta=(\ell^k)^{-1}\). Only the class hypothesis (`ClassCoupledShell`) and the selectors (`selCorner`/`selCorner`) differ, as claimed. `P428Target8S selCorner selCorner` indeed keeps frozen `ClassCoupled` (`D1Lit.lean:104–123`), so the SPEC's "that is a different statement" is right.
- `PerCubeRegularShell` is `PerCubeRegular2` (`ZR2A.lean:47–68`) with only `CubeBond → ReadBond` and `CurlReads → CurlReadsRead`: clause order, the `HT` conjunct, the `exp((ηI)•A)` gauge law, the `^1`/`^2`/`^3` power pattern, and the `periodicLatticeShiftBack` curl-guard structure all match verbatim.

## 2. Does the hypothesis class admit a proper nonempty \(\Omega_0\)?

Yes, and the argument needs no numerics:

1. `ClassCoupledShell = CoversOm0p ∧ PerCubeRegularShell` with frozen coverage. `CoversOm0p 2 M 12 2 (SlabNv 2 M R)` is the existing theorem `slab3_coversp`, used at `D1Final.lean:141` (SPEC says `:139`, off by two); the NV slab has proper nonempty \(\Omega_0\) and is `Admissible` (it is the D1 lane's own witness).
2. `PerCubeRegularShell` constrains \(U\), not the tower. \(U=1\) with \(g=\mathrm{id}\), \(A=0\) satisfies every clause for any \(\alpha_0>0\), since all Frobenius norms are \(0\) and the bounds are positive.
3. \(12M\alpha_0\le a_0\) is satisfiable for any \(a_0>0\) by taking \(\alpha_0\) small. So the class is inhabited for every prover choice of \(a_0\); the statement is not vacuous.

Direction check on the stage-B inclusion target: `CubeBond sites e → ReadBond sites e` holds because the plaquette \((x,\mu,\nu)\) (\(\nu\ne\mu\), exists in `Fin 3`) has corner \(x\in\) sites and edge \(e\). No torus-size hypothesis is needed (the stage-B plan's "at least two sites per direction" is unnecessary but harmless). Hence `PerCubeRegularShell → PerCubeRegular2` pointwise and `ClassCoupledShell → ClassCoupled`: the shell class is strictly **smaller in \(U\)** (more bonds constrained) while the operators are **larger** (\(\mathrm{plaqIn}\subset\mathrm{plaqCorner}\)). Neither direction relative to frozen `P428Target8` follows, and the SPEC says exactly that. Numerically confirmed: `CubeBond ⊆ ReadBond` and `CubeBond ⊆ TouchBond` on all five geometries (`attack_check.json`, `bond_inclusions`).

One imprecision to fix in prose: the design JSON's "That extra outer-bond clause is what admits a proper nonempty \(\Omega_0\)" is misleading. \(U=1\) inhabits the class under *any* of the three bond sets, and `CoversOm0p` is what places corners in cubes; the `ReadBond` clause is what makes the class **constrain the bonds the corner operators actually read** (it sees the \(U_\theta\) flux; `TouchBond` does not). The SPEC body says this correctly ("It is what lets a proper nonempty \(\Omega_0\) stay in the class" in the sense of staying nontrivially constrained); the one-line summary should not be read as a non-vacuity mechanism.

## 3. Do the numerical operators match the cited Lean lines?

Content: yes, everywhere checked. Line numbers: several drifts.

Verified in content against the current `lean/src` files:

- `curlValueCovariant` (`CovariantOperators.lean:315`): script's `A₀ + R(U₀)A₁ − R(U₃)A₂ − A₃` matches exactly, including which link transports which term.
- `bilPlaq` (`DeltaPrimeOperator.lean:376–400, 433`): the \(A'\) sign flips match `a1LM`–`a4LM` (`AZW=-R(U(x,\nu))A\), `AWX=-A(x,\nu)`, `AXY=A(x,\mu)`, `AYZ=R(U(x,\mu))A`); the six brackets in `DeltaPrime` order with the `i·b_i·b_j·Im` structure match `bilPlaq_atoms`, including the triple-\(i\) factor (script's `1j*bs[i]` where `bs` already carries one `1j`, matching Lean's `smulILM (b1LM …)`).
- `hsInner` (`SuTwoInner.lean:104`), `reHolonomy`/`imHolonomy` (\((H\pm H^{-1})/2\), \((H-H^{-1})/2i\)), holonomy edge order (`ClayStatement.lean:1286`, boundary edges `:1295`), `Zb`/`Uth` (`D1Path.lean:25,46`), `frobSq` (`RMapLipschitz.lean:60`), `plaqIn` (`ZR2Ops2.lean:74`), `CubeBond` (`ZStatementP428.lean:145`).
- Anchors: the unit tests check the Cartan closed form \(Q=\cos\varphi\,\mathrm{curl}^2\) internally, and the global check reproduces `BdPt.delta_pi` (`D1Geo1.lean:94`), the Lean value \(-4\langle X,X\rangle\) at \(\theta=\pi\), on four tori. `delta_form_sum` (sum of `hsInner(curl,curl) + ½ bilPlaq`) is at `D1Eval.lean:56` and its statement matches the assembled form.
- `T1 = i\,\mathrm{diag}(1,-1)\) is `suTwoWitnessVal` at `CovariantOperators.lean:128` (the script header cites this correctly).

Line-number drift to repair (content right, coordinates wrong against `lean/src`):

| citation | actual |
|---|---|
| script header `D1Eval.lean:48 delta_form_sum` | `:56` (line 48 is inside `plaq_central`'s proof) |
| script header `ClayStatement.lean:1274` (shift) | `:1281` |
| script header `DeltaPrime.lean:131 reHolonomy, :148 imHolonomy` | `:125`, `:133` |
| SPEC: witness \(T_1\) "at `SuTwoInner.lean:128`" | wrong file/line; the \(i\,\mathrm{diag}(1,-1)\) witness is `CovariantOperators.lean:128`, reused as `pauliE3` (`SuTwoInner.lean:522`); `SuTwoInner.lean:128` is inside an unrelated proof |
| SPEC: `classCube_sub_om0` `D1Final.lean:35` | `:36` |
| SPEC: `slab3_coversp` used at `D1Final.lean:139` | `:141` |

Correct as cited: `ZT5A.lean:291`, `ZR2A.lean:48`, `ZR2Ops2.lean:74`, `ZStatementP428.lean:73/131/140/145/211`, `ZR2A.lean:107/121`, `ZR6A.lean:27/33/124`, `D1Lit.lean:96/123/134`, `D1Geo1.lean:94`, `D1Eval.lean:28`, `D1Eval2.lean:65/152`, `CovariantOperators.lean:247/315`, `SuTwoInner.lean:104`, `DeltaPrime.lean:106`, `DeltaPrimeOperator.lean:433`, `ClayStatement.lean:1286/1295`, `D1Path.lean:25/46`, `RMapLipschitz.lean:60`.

## 4. Are the tolerances honest?

Yes.

- `spectrum_stats` counts negative at \(<-10^{-8}\) against `eigvalsh` errors \(\sim10^{-13}\) on these \(O(1)\) matrices; minima of order \(-5\cdot10^{-15}\) are reported as "0 up to \(10^{-14}\)", not as zeros-by-decree. `n_zero` at \(|\cdot|\le10^{-8}\) does not swallow the reported negative minima.
- `if w == 0.0: continue` in the Cartan assembler skips only exactly-zero weights, which contribute exactly nothing; the \(\theta=\pi/2\) row still reports the Rayleigh value \(2.4\cdot10^{-16}\), not 0.
- The rewrite-obstruction `extra` list is truncated at 3 by construction and is reported as "at least one", never as a count. (`attack_check.py` recomputed the full witness counts: 64 on the side-4 slab, 30 on the cube.)
- The optimizer in `max_curl_under_bounds` is documented in the script as an upper bound on negativity (real gradient fields are more constrained) and the SPEC quotes it as "the search reached", with the analytic corner next to it.
- The `a0_equals_phase_cap` row in `results.json` is genuinely mislabeled (it caps phases at \(\pi/(2\sqrt2)\) itself, not at \(a_0/\sqrt2\)); the SPEC itself flags this row as "not the threshold test". That is the right handling.
- The random-Cartan rows at caps \(\pi/8\) and \(0.3\) are analytically vacuous (pointwise alone gives \(|\varphi|\le4\theta_{\max}\le\pi/2\)); they confirm the transcription, nothing more, and the SPEC does not ask them to do more. The random row at cap \(\pi/4\) goes negative (\(-3.19\)) precisely because it violates the gradient clause; the SPEC correctly does not cite it as inside-class evidence. The honest summary is: inside the full shell cap \(\pi/4\), nonnegativity is *analytic* (\(|\varphi|\le2|\Delta\theta|\le\pi/2\), verified in `attack_check.json` `cap_arithmetic`), and the single-bond constrained search is the only numerical check of it. No lattice-wide gradient-constrained sampler exists in this package; the SPEC's "no negative Cartan spectrum was seen inside the cap" should be read with that scope.
- Reproducibility: I re-ran `shell_touch.py` (53.5 s vs recorded 57.9 s); `results.json` is bit-for-bit identical except the `seconds` field. All SPEC numbers quoted from it check out: Rayleigh \(4\cos\theta\) table, spectrum minima \(-10\), `read ∩ far` \(=64,144,144,256,72\), `touch ∩ far` \(=0\), structured-flux min \(-2.9445\), nonabelian \(-0.2233\) (105 neg), penalised \(-0.0435\) (touch) vs \(-0.0662\) (in).

## 5. Required repair: an unsupported, misattributed numbers sentence

SPEC section "Results", last paragraph of the non-abelian table:

> "The mode that realises \(-0.22\) has curl energy \(+0.024\) and \(\Delta'\) energy \(-0.281\), so the sign comes from `bilPlaq`, on a field whose flat divergence energy is about \(4.6\)."

`shell_touch.py` computes **no eigenvectors** (`eigvalsh` only) and no curl/bilPlaq decomposition anywhere, so this sentence is not reproducible from the recorded artifacts — a "do not report a number you have not just measured" violation in form. I reconstructed both recorded \(\varepsilon=0.05\) configurations (`attack_check.py`, replaying the rng; results in `attack_check.json`):

| configuration | min eig | curl part | bilPlaq part | flat div energy |
|---|---|---|---|---|
| main-sequence (the \(-0.2233\) row) | \(-0.22330\) | \(+0.0190\) | \(-0.2423\) | \(4.350\) |
| fresh seed 0 (the `gauge_penalty` raw \(-0.2573\) row) | \(-0.25726\) | \(+0.0238\) | \(-0.2811\) | \(4.632\) |

The quoted triple \((+0.024, -0.281, 4.6)\) belongs to the **seed-0 \(-0.257\)** mode, not to "the mode that realises \(-0.22\)". The qualitative claim (sign from `bilPlaq`; divergence energy \(\approx4.3\)–\(4.6\)) is true for **both** modes and is now measured and recorded. Repair options: rewrite the sentence with the correct attribution and cite `attack_check.json`, or fold the decomposition into `shell_touch.py` and re-record. Do not leave the sentence as is.

## 6. Independent confirmation of the structural claims

- **Rewrite impossibility, strengthened.** The script's check is the right witness and the argument is tighter than the SPEC states: any \(S\) with \(\mathrm{plaqIn}\,S=\mathrm{plaqCorner}\,\Omega\) must contain every corner of every touching plaquette (each is in \(\mathrm{plaqIn}\,S\)), so \(S\supseteq C\); by monotonicity \(\mathrm{plaqIn}\,S\supseteq\mathrm{plaqIn}\,C\), which contains a plaquette with no corner in \(\Omega\). Hence no \(S\) at all works — not just \(S=C\). `attack_check.json` `rewrite_monotonicity` confirms both conjuncts on two geometries. On side 4 width 2 the forced set is the *whole torus* (wrap-around; both slab boundaries are two sites apart), so the obstruction there is maximal, and the SPEC is right that block closure is not the obstruction (`forced_is_M2_block_closed: true` on that geometry, equality still fails).
- **\(U_\theta\) visibility.** `touch ∩ far = 0` is definitional (touching vs both-endpoints-out are complementary clauses) and confirmed; `read ∩ far > 0` confirmed on all five geometries. The per-cube version of the argument goes through site coverage: a touching plaquette's corner lies in some class cube, whose `ReadBond` then contains all four of its bonds. So \(U_\theta\) leaves every `TouchBond`-only class and is seen by the shell class; whether it *enters* the shell class is the smallness test, exactly as the SPEC frames it.
- **Cap arithmetic.** \(|\theta|<a_0/(\sqrt2\,\ell^j)\), \(|\Delta\theta|<a_0/(\sqrt2\,\ell^{2j})\), \(|\varphi|\le2|\Delta\theta|\): at \(j=0\), \(a_0=\pi/(2\sqrt2)\) gives \(|\varphi|<\pi/2\) strictly, so \(\cos\varphi>0\) on every shell-regular Cartan plaquette; \(a_0=\pi/\sqrt2\) and \(\pi\sqrt2\) give no such guarantee (`cap_arithmetic`). Matches SPEC predictions 2–3, including the \(a_0>\pi\sqrt2\approx4.44\) entry fee for the \(\theta=\pi\) configuration. The SPEC labels these "model thresholds … not a value of \(\gamma_0\) and not a theorem", which is the correct billing. One suppressed step the stage-B file would need: the gradient clause is per cube, so the model needs "both parallel pairs of each touching plaquette are read-bonds of one common cube" — true via site coverage at any corner, but a proof step, not a definition.

## 7. What the design claims that the evidence does not fully support (scope notes, not contradictions)

- The design JSON's "the numerics say the old counterexample still meets [`P428Target8S selCorner selCorner`]" is operator-level evidence only: the raw touching Cartan form is negative at \(U_\theta\) (verified, \(-4\) Rayleigh, agreeing with `BdPt.delta_pi`), and \(U_\theta\) lies in the frozen class. A refutation of that *statement* needs the gauge-fixed `genForm` analysis. The SPEC body is careful ("still makes the touching quadratic form negative"); the summary line should be read in that sense. The Lean refutations on record are `not_P428Target8Literal` (selAll) and `not_P428Target8LiteralBoth`, not selCorner.
- The \(\varepsilon=0.05\) nonabelian indefiniteness of raw \(\Delta\) for *both* selectors is fairly presented as not separating the readings and not touching `genForm`; the penalised minima (\(-0.0435\) touch, \(-0.0662` in`) support "the frozen plaquette set is at least as indefinite", which is all the SPEC says.
- `P428Target8Shell` remains undecided, and the SPEC's final section says so with the right reason (a counterexample must survive every \(a_0\) or the gauge fixing; a reduction needs `plaqCorner = plaqIn`, which fails on every proper domain tested). The prediction "counterexample more likely than a rewrite" is correctly scoped to the literal touching-bond class.

## 8. Stage-B plan review

Targets 1–3 are provable as scoped and correctly refuse to prove `P428Target8Shell` or derive it from `p428Target8`. Notes for whoever writes it:

- Target 1 (`CubeBond → ReadBond`, then the class implication) needs no "at least two sites per direction" hypothesis; only \(\nu\ne\mu\) in `Fin 3`. Keep the condition if it is free, but it is not load-bearing.
- Target 2 (`no_plaqIn_eq_plaqCorner`) should use the monotonicity form above (§6), which is cleaner than searching over \(S\), and must handle wrap-around: the witness face plaquette at \(x_0=W\), directions \(1,2\), needs \(2\le W\le N-2\), which the SPEC already states.
- Target 3's "record that the four `BdPt` plaquettes lie in `plaqCorner` and not in `plaqIn`" is exactly what the numerics see (touch = all = \(-4\), in = \(0\)); fine as a comparison, correctly not a re-proof of `not_P428Target8Literal`.
- The imports list is right (`ZStatementP428`, `ZR2A`, `ZR6A`, `ZR2Ops2`, `ClayStatement`, `D1Lit`; `D1Path`/`D1Geo1` optional). No edits to frozen files are needed for targets 1–3.

## Summary of actions for the designer

1. **Required:** fix or re-source the eigenmode sentence (§5); `attack_check.json` already contains the correct numbers for both configurations.
2. **Should:** repair the six citation drifts in §3 (all content-correct, coordinates stale).
3. **Should:** reword the design-JSON line "the extra outer-bond clause is what admits a proper nonempty \(\Omega_0\)" (§2) and the "old counterexample still meets it" line (§7) to their operator-level meanings.
4. **Optional:** note that random caps \(\pi/8, 0.3\) are analytically vacuous, and that no lattice-wide gradient-constrained sampler backs the cap-\(\pi/4\) nonnegativity beyond the analytic \(2\)-difference bound.

None of these change the design's prediction: rewriting is impossible on the tested domains, the old counterexamples kill the touching *operators* and the frozen-class selector variant at operator level, the shell class is nonempty with proper \(\Omega_0\), and `P428Target8Shell` is undecided.
