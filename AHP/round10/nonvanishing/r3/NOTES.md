# Nonvanishing, round 3 — a physical top jet detects the source curl

## Decision

**GoalNeg2 is NOT proved. No original round-9 cofinal coupling premise is proved.**

This round proves a new implication for the **actual frozen operators and actual dilated geometry**: a nonzero physical, transversely aggregated, direction-1 top jet forces a nonzero localized neutral curl of its constrained lift. Combined with dictionary R3's source-energy identity, this supplies a free profile with nonzero coupling to that vector.

The nonzero top jet of a crossing vector is still unproved. The entire crossing-kernel condition and the nested cofinal quantifiers are still unproved. In particular, the new conditional result must not be described as a proof of coupling nonvanishing.

Published: `AHP/round10/shared/nonvanishing/R3_DilatedFlux.lean`, **824 lines**. Original and shared publication independently compile with exit 0, no warnings/errors, and standard axioms only. Its **82 declarations** are individually audited: 66 new, 16 reused verbatim. `CHECKS.json` passes.

## 1. What changed from round 2

Round 2 proves that the finite tridiagonal source family detects any nonzero finite jet vector. Its actual physical source-column dictionary was still missing.

Dictionary R3 instead proves the exact free-profile identity

\[
\operatorname{coupling}(f,u)=2\sum_{p\subset\Omega_0}
  (\operatorname{curl} r_u)(p)(\operatorname{curl}f)(p),
\qquad
r_u(e)=\langle E_3,[i_EH_0 C^2_0(W_0i_Eu)](e)\rangle.
\]

Taking the admissible free profile to be \(r_u\) makes this twice the nonnegative curl energy. A nonzero selected curl therefore detects that vector without solving the neutral tridiagonal source system.

Our new result connects the **same nonzero physical jet condition** to this curl criterion. There is no longer a source-column or Bloch-normalization premise on this route. The missing crossing-specific jet condition itself has not been removed.

The dictionary result is independently owned: `shared/dictionary/R3_FreeSource.lean`, notably `FreeSource.profileCoupling_curl`, `adaptive_pos_iff`, `exists_profile_iff_curlDetected`, and `liftJet_Q`. I inspected its actual statements and recorded standard-axiom records; I did not recompile or modify its files. The final cross-track coupling application is left to assembly rather than claimed compiled by this track.

## 2. Exact transverse flux identity

Let T be a finite transverse section, s its tangential unit translation, and a,b the longitudinal/tangential components of a scalar bond field. Define

\[
F_b(x)=\sum_{t\in T}b(x,t),\qquad
c(x,t)=a(x,t)+b(x+1,t)-a(x,st)-b(x,t).
\]

Translation is a permutation, so exactly

\[
\sum_t c(x,t)=F_b(x+1)-F_b(x).
\]

If all these plaquette curls vanish between layers l and h, the flux is constant there. If the flux at one collar layer is zero, all these layer fluxes are zero. Thus a nonzero quantity

\[
\frac18\bigl(F_b(p)+F_b(p+1)\bigr)
\]

forces a nonzero plaquette curl at some layer \(l\le x<p+1\).

`Flux.lean` proves these finite identities. `TorusAppendix.lean.txt` identifies them with the frozen `LatticeOperators.curlValue` on the real physical torus, not a replacement cell. Both tangential directions have the scalar torus identity; the full blocking/geometry application in this deliverable uses direction 1.

## 3. The actual normalized Q rows — no assumed dictionary

For ell=2 the frozen flat `Q1jet_flat` theorem identifies the normalized first jet with

\[
(Q_1 A)(c)=\frac1{16}\sum_{x\in B(c_-)}\bigl(A(x,1)+A(x+e_1,1)\bigr).
\]

Fix an even longitudinal base p and sum over all even transverse coarse sites. The explicit equivalence `tiling` partitions the actual transverse torus into two-by-two cells. Each fine transverse tangential bond occurs twice among the two path-link positions. Therefore

\[
\sum_{\text{transverse coarse }c} (Q_1 A)(p,c,1)
=\frac18\bigl(F_A(p)+F_A(p+1)\bigr).
\]

The factor is **1/8**, with the physical transverse multiplicity already in the sum. No cell-normalized Fourier vector is used. In particular, we do not assume the previously conjectured q=1 dilation identity.

The exact chain of compiled identities is:

- `PhysicalBlocking.qOnePathSum_row`: frozen scalar blocking equals the finite-array block row;
- `sum_qOnePathSum_row`: physical transverse row sum is the displayed flux;
- `sum_Q1jet_row`: every real linear functional commutes with the genuine flat SU(2) Q1 jet;
- `Qfull_level_one`: the level-one full-tower row is exactly that normalized Q1 jet;
- `sum_Qfull_level_one`: the formula for genuine frozen `QfullOf` rows.

The cube-coordinate lemmas were copied verbatim from frozen `NsPtA`/`NsPtB`, in a new namespace and without NsPtB's unused ambient `CfData` parameter. No `CfData` premise is introduced. The source bodies and their standard axioms are audited.

## 4. All geometry and collar obligations are discharged

Put

\[
N=4q(R+1),\qquad p_j=2Rq+4q+2j,\qquad 0\le j<N.
\]

`DilatedFlux.topIdx` constructs every actual level-one direction-1 row at base \(p_j\) and the \((4q)^2\) even transverse sites. It proves membership in the actual `bondsLam`, including the exclusion of the next tower level. These are not hypothetical row identifiers in the final theorem.

`collarIdx` constructs the physical direction-1 bonds at the first Omega_0 layer \(x_0=4q\) as **level-zero rows**, for every q>0 and R>=1. The definition of `QfullOf` makes such a row the fine bond value. The actual quadratic jet is zero at every level-zero row (`C2full_level_zero`). Consequently

\[
Q_0 A=C^2_0(v)\quad\Longrightarrow\quad A(4q,t,1)=0
\]

for all transverse t. The zero collar flux used in section 2 follows; no boundary condition was added to the physical application.

Finally, `plaq01_in` proves that every plaquette produced by the flux argument is in the actual selected `plaqIn Omega_0`. It checks all four boundary bonds and their endpoints, using \(p_j+2\le10Rq+12q\). It is not merely a touching-plaquette claim.

## 5. Compiled final statements

Namespace: `AdalyFormal.Round10.Nonvanishing.DilatedFlux`.

`L q R` is the original fine dilated extent; `G q R` is `geomOf 2 1 (dilTower q R)`. The original `dilLu`, `dilTower`, and two side-length lemmas are copied verbatim in their original `Round4.Guarded.RefuteR1` namespace.

```lean
theorem localized_curl_of_jetAggregate {q R j : ℕ}
    (hq : 0 < q) (hR : 1 ≤ R) (hj : j < blockCount q R)
    (φ : SuTwo →ₗ[ℝ] ℝ) (A v : BondFnL2 (L q R))
    (hQ : QfullOf (G q R) flatCfg A = C2fullOf (G q R) flatCfg v)
    (hne : jetAggregate hq hj φ v ≠ 0) :
    ∃ p ∈ plaqIn ((dilTower q R).Om 0),
      curlValue (fun e => φ (A e)) p ≠ 0
```

Here `jetAggregate` is the physical sum of the actual `C2fullOf` top coordinates, not a replacement jet. Neither `hQ` nor `hne` is hidden: the first is the constrained-lift identity in the intended application; the second is the still-missing nondegeneracy.

The final specialized theorem is:

```lean
theorem neutral_localized_curl_of_topJet {q R : ℕ}
    (hq : 0 < q) (hR : 1 ≤ R)
    (A : BondFnL2 (L q R)) (u : ↥(bondSupp (G q R)))
    (hQ : QfullOf (G q R) flatCfg A = C2fullOf (G q R) flatCfg
      (Wop (G q R) flatCfg 1 (iE (G q R) u)))
    (hjet : TopJetDetected hq R u) :
    ∃ p ∈ plaqIn ((dilTower q R).Om 0),
      curlValue (fun e => ⟪pauliE3,A e⟫) p ≠ 0
```

In the application, choose \(A=i_EH_0\operatorname{vacJet}(u)\). Dictionary R3's `liftJet_Q` supplies the constraint identity given the actual N-unit (already proved for admissible q,R in round 9). No tridiagonal inverse is used.

## 6. Exactly what remains

The new **unproved** per-vector target is a compiled definition, not a theorem:

```lean
def TopJetDetected {q : ℕ} (hq : 0 < q) (R : ℕ)
    (u : ↥(bondSupp (G q R))) : Prop :=
  ∃ j : ℕ, ∃ hj : j < blockCount q R,
    jetAggregate hq hj neutralFunctional
      (Wop (G q R) flatCfg 1 (iE (G q R) u)) ≠ 0
```

`neutralFunctional X = inner(pauliE3,X)` with the frozen norm-one axis. We have **not proved `TopJetDetected` for any actual vacuum crossing generator**, much less a cofinal family of them.

For the proposed charged-line route, one still needs a crossing generator satisfying this predicate **and** assembly's `KernelLine`, which contains the entire vacuum crossing kernel, at nested cofinal dyadic scales and even radii. Alternatively, one needs another common-profile definiteness argument on the entire kernel. Vector-dependent adaptive profiles cannot be exchanged for one fixed profile on a multidimensional kernel; the R2 quantifier counterexample still applies.

The original sufficient premise remains exactly:

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
  ∃ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ,
    QualitativeR2.CanonicalCoupling (2^j) R (uthPath (2^j) R)
      (corrDeriv (2^j) R f)
```

This is the original `CofinalAnyProfileCoupling`, still **not proved**.

Why the proof stops here: the telescoping argument is linear in the *lift*, while the missing jet is quadratic in the *crossing vector*. Unique continuation of a nonzero linear recurrence solution alone does not imply a nonzero commutator jet. Nonzero fields lying in a common commuting Lie direction have zero second commutator jet (compare frozen `NsCvO17.C2StepX_sigma3`); they are not asserted to be the actual crossing fields. Crossing-specific polarization/phase information is still necessary. No new obstruction to the actual conjectured coupling premise was found, and it is not reported false.

## 7. Verification and files

| File | Lines / role | Final wrapper exit |
|---|---|---|
| `Flux.lean` | finite permutation flux and normalized block sums | 0 |
| `TorusFlux.lean` | scalar actual torus curl | 0 |
| `PhysicalBlocking.lean` | actual normalized Q1/Qfull rows and collar helper | 0 |
| `DilatedFlux.lean` | 824-line full deliverable, actual geometry and named target | 0 |
| `shared/nonvanishing/R3_DilatedFlux.lean` | byte-identical independently compiled publication | 0 |

All five final files have no diagnostics and every declaration has a printed dependency record contained in `{propext, Classical.choice, Quot.sound}`. The shared file has 82 such records. `CHECKS.json` verifies sources, log/exit freshness, every declaration, permitted imports, prohibited-device absence, 16 verbatim reused fragments, and shared byte identity. It explicitly records GoalNeg2, round-9 coupling, crossing jet nonvanishing, and full-kernel definiteness as **false/not proved**.

No numerical solve was run in this round. No numerical result is used as a proof step. Failed development compilations were ordinary elaboration/indexing/tactic errors; all final sources were repaired and recompiled. No compiler timeout, memory kill, pending job, or missing exit record remains. The short temporary name-check file and its outputs were removed from this track directory.

Reproduction, from the repository root:

```sh
python3 AHP/round10/nonvanishing/r3/copy_coordinates.py
python3 AHP/round10/nonvanishing/r3/build.py
AHP/round3/lean1.sh AHP/round10/nonvanishing/r3/Flux.lean
AHP/round3/lean1.sh AHP/round10/nonvanishing/r3/TorusFlux.lean
AHP/round3/lean1.sh AHP/round10/nonvanishing/r3/PhysicalBlocking.lean
AHP/round3/lean1.sh AHP/round10/nonvanishing/r3/DilatedFlux.lean
AHP/round3/lean1.sh AHP/round10/shared/nonvanishing/R3_DilatedFlux.lean
python3 AHP/round10/nonvanishing/r3/audit.py
```

Only this round's track directory and its own shared nonvanishing files were written. No earlier AHP round, other track's files, frozen source, lakefile, protected directory, integration checkout, or worktree was modified. No build/REPRODUCE, commit, push, or removal outside this track.

### Integration follow-up: robust neutral-functional proof

Assembly subsequently reported that `neutralFunctional.map_smul'` failed in its combined compact harness; the retained `assembly/r3/history/JetCompact.v2.log` shows the unsolved scalar-inner-product goal. The physical theorem and all indexing were unaffected. I replaced the simplifier-based proof with the direct term `inner_smul_right _ _ _`, and used anonymous binders in the additive proof to avoid unused-variable warnings. No definition's mathematical content or theorem statement changed.

The original and shared full deliverables were recompiled with clean exit 0, and the audit again passes all 82 declaration records. The purposeful compatibility test `AfterDictionary.lean`, generated by `regression.py`, places the exact neutral-functional declaration after the published dictionary prefix; its final compilation is also clean and standard-axiom-only. `REGRESSION.json` records the prefix hash, and `CHECKS.json` checks the resulting log/exit. **That smaller prefix test passed before the change too**, so it is not claimed to reproduce the assembly-only failure or prove a red/green regression. The retained assembly failure plus direct proof and fresh compatibility compilations are the verification evidence. Full assembly recompilation remains owned by assembly.

Commands for this additional compatibility check:

```sh
python3 AHP/round10/nonvanishing/r3/regression.py
AHP/round3/lean1.sh AHP/round10/nonvanishing/r3/AfterDictionary.lean
python3 AHP/round10/nonvanishing/r3/audit.py
```
