# Guarded all-plaquette reading — round 4, refutation route, pass 1

**closedGoal: `none`. Neither pinned negative goal is proved.**

The new partial result removes the previous candidate's fixed-m limitation and strengthens base-bond nonidentity to **exact nontrivial holonomy on a fully interior plaquette**, together with failure of every global flattening gauge. It supplies the cofinal class/geometry/smallness/competitor obligations. It supplies **neither** the all-plaquette carrier guard nor corrected singularity.

## Main compiled result

**`AdalyFormal.Round4.Guarded.RefuteR1.cofinal_in_class_curved_competitor`**, `Attempt.lean:1599`.

Its actual binders are:

\[
\forall m_0\;\exists m\ge\max(m_0,1)\;\forall R_0\;\exists R\ge R_0,
\quad 34\le R2^m,
\quad \forall a_0>0\;\exists(k,L_u,\alpha,S,\Lambda,U,\widetilde B).
\]

The conclusion contains all of:

- positive capped smallness: \(\alpha>0\), \(12\,2^m\alpha\le a_0\);
- `TorusOK`, all six `Admissible` clauses, and `LambdaOK2`;
- the **actual frozen `ClassCoupled`**, including both coverage clauses and every per-cube regularity clause;
- both admissible-test restrictions and strictly positive `bondEnergy`;
- a nonidentity bond based in \(\Omega_0\);
- a plaquette in **`plaqIn (S.Om 0)`** with nonidentity `periodicPlaquetteHolonomy`;
- no global gauge transformation making U identically one.

The witnesses are \(m=m_0+1\), \(q=2^{m_0}\), \(M=2q=2^m\), \(R=2(R_0+18)\), and \(k=1\). Thus **R is chosen before every positive cap**, and the reduction's room condition is genuinely included. The parameter a does not enter this nonspectral theorem; it has not been used to assert any operator statement.

This is not the pin's `CofinalPencilFailure`: its two spectral clauses remain missing. The complete pin and its goals are unchanged; no weaker proposition is presented as a replacement goal.

## Scaled single-defect family

The entire round-3 refutation attempt is a verbatim prefix of `Attempt.lean`; therefore the complete round-3 pin is also an exact prefix. New declarations start at line 986. Only frozen `DrEquiv` is imported; no AHP file is imported.

For any positive integer q and every even \(R\ge6\), the new geometric family has

\[
L_f+1=((12R+16)q,8q,8q),\qquad L_u+1=((6R+8)q,4q,4q),
\]
\[
\Omega_0=[4q,(12R+12)q)\times T^2,
\quad \Omega_1=[(2R+4)q,(10R+12)q)\times T^2,
\quad \Omega_j=\varnothing\quad(j\ge2),
\]
\[
\Lambda=[(3R+4)q,(3R+6)q)\times T_u^2.
\]

Here \(\ell=2\), \(M=2q\), \(k=1\), \(\eta=1/2\). At q=1 these formulas are the round-3 wide-top geometry. The longitudinal interval argument has been generalized, not replaced by the unrelated frozen three-stratum non-vacuity example. This is a geometric extension, **not a claim of operator equivalence under dilation**.

The background `dilU q R epsilon V` equals V on bonds with neither endpoint in \(\Omega_0\). On the remaining bonds it is `Ug epsilon` exactly when

- the base longitudinal coordinate is \((2R+4)q\);
- both transverse coordinates are even;
- the bond direction is 1.

It is identity on the other non-exterior bonds. The transverse period remains two; enlarging the torus repeats the motif rather than making an operator-conjugacy assertion.

**`dil_in_class_nonflat_competitor` (`:1423`) allows every exterior V**, not only an exterior chosen before the cap or a diagonal one. It constructs

\[
\alpha=\frac12\min\left(\frac{a_0}{24q},1\right),
\qquad \varepsilon=\frac{\alpha}{160}.
\]

This gives \(0<\varepsilon<1\), the cap, and regularity via the frozen `ufield_perCubeRegular2` and `perCubeRegular2_congr`. No pointwise, difference, curl-of-curl, or cube-index obligation was dropped. The final existential cofinal theorem uses V=1 merely to package nonspectral existence; the parameterized family theorem retains arbitrary exterior links for a future spectral construction.

### Exact curvature, not a numerical diagnostic

At \(x=((2R+4)q,0,0)\), let p be the oriented (0,1)-plaquette. The new exact statements prove

\[
p\in\operatorname{plaqIn}(\Omega_0),\qquad
\operatorname{Hol}_{U}(p)=\operatorname{Ug}(\varepsilon)^{-1}\ne1.
\]

The three other links in this word are identity and the final link is `Ug epsilon`. The whole plaquette's boundary endpoints lie in \(\Omega_0\), so this computation is independent of V. `Ug_ne_one` gives the strict nonidentity for \(0<\varepsilon<1\). The frozen gauge-conjugation identity for the plaquette word then excludes any global flattening gauge.

This strengthens round 3's nonidentity-bond theorem. **Curvature still does not prove nonzero assembled `Delta2`, boundary return, or spectral separation.**

## New declarations of interest

All names below have prefix `AdalyFormal.Round4.Guarded.RefuteR1.`.

| Declaration | Line | Proved scope |
|---|---:|---|
| `dil_torus` | 1012 | Actual torus compatibility for M=2q |
| `dil_admissible` | 1024 | All six admissibility clauses |
| `dil_lambda` | 1111 | Actual `LambdaOK2` |
| `dil_competitor` | 1156 | Explicit free-bond competitor and positive energy |
| `dil_coverage` | 1342 | Both frozen factor-12 coverage clauses, every positive q and even R>=6 |
| `dil_regular` | 1388 | Full per-cube regularity with arbitrary exterior V |
| `dil_in_class_nonflat_competitor` | 1423 | Combined capped family certificate for every q>0, even R>=6, cap>0, and V |
| `dil_holonomy` | 1486 | Exact interior plaquette word = `Ug epsilon` inverse |
| `dil_plaq_in` | 1519 | That plaquette is fully interior, not merely touching |
| `dilU_curved` | 1551 | A fully interior plaquette has nonidentity holonomy |
| `dilU_not_pure_gauge` | 1558 | No global gauge makes U identity |
| `cofinal_in_class_curved_competitor` | 1599 | Correct cofinal m/R/cap order, room, class, competitor and curvature |

## The concrete remaining obstruction

No exact spectral separation has been constructed, even at one instance of this family. To complete the refutation one must choose the exterior V (and any other allowed parameters), at each cofinal scale/radius and under every positive cap, and prove simultaneously

\[
\operatorname{IsUnit}(A),\qquad z\ne0,\qquad(A-D)z=0,
\]

where A is the **full carrier** `Ginv_all`, D is the genuine localized `Delta2`, and z belongs to the actual carrier. Neither an explicit such z nor a full-carrier unit certificate is present here. There is also no exact demonstration that this curved family's assembled correction or inverse-propagated boundary return is nonzero. A nontrivial plaquette word alone does not settle those operator quantities.

The prior floating-point crossings are not promoted to exact kernels. Their finite-difference discrepancies exceed their sampled small carrier gaps, and their fixed-radius amplitudes do not establish the arbitrary-cap quantifier. No numerical sweep was rerun here. Geometric scaling does not establish a Fourier/intertwining dictionary or preserve a spectral crossing.

### What the mined estimates do and do not exclude

Read `AHP/round4/guarded/MINE.md`'s scope/constant-order analysis and the frozen signatures used in this construction. The mined coercivity and units are for **localized** B and C; the ordinary norm coercivity constant also carries a depth factor. They are not an all-plaquette lower gap for A or the guarded boundary response. The carrier guard alone is not the missing uniform lower-bound statement. `GapAt` is an implication of units, not a numerical gap.

Consequently, this attempt proves **no impossibility result** from a supposed all-plaquette uniform gap. Such a gap is not supplied by the mine. The missing spectral step is open, not contradicted by the localized estimates. All pin qualifications about selectors, totalized inverses, class bonds, geometry and printed fidelity are retained.

## Verification

Only the shared serialization wrapper was used for compilation:

```sh
AHP/round3/lean1.sh AHP/round4/guarded/refute-r1/Attempt.lean
python3 AHP/round4/guarded/refute-r1/validate.py
```

Final exit **0**, no errors or warnings. Evidence: `Attempt.lean.log`, `Attempt.lean.exit`, `CHECKS.json`. All **100 local declarations** have individual dependency records. There are **120 dependency records** including inherited frozen roots, all subsets of the permitted three. Main record:

```text
'AdalyFormal.Round4.Guarded.RefuteR1.cofinal_in_class_curved_competitor' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Final source SHA-256:

```text
df30c794c74bda3d1fbbc66c8cf13bcd1b0045d29a0a07cd78733e4bb4b735e1
```

`validate.py` verifies both verbatim prefixes, frozen-only import, forbidden-token absence, final exit, source/log/exit ordering, diagnostic absence, complete local dependency prints and allowed dependency sets. This is an artifact audit, not an independent second-agent recompile or a proof of any spectral assertion.

The first foreground invocation was interrupted with an empty log and no exit record; two process-table checks found no surviving compiler/wrapper before work continued. It was not counted as successful. Subsequent compilations used persistent terminals, with wrapper completion/exit records checked before any further compile. Intermediate syntax/type errors were repaired; failed scratch compilation artifacts were removed from this directory after the clean final result. No simultaneous duplicate compile was launched.

The required two judgements and PIN.md were read in full; inherited source-reading qualifications remain. All authored files are under `AHP/round4/guarded/refute-r1/`. No protected source, other AHP item, lakefile, paper, notes, expected output, or extras were edited. No direct Lean/Lake command, reproduction, dependency update, numerical computation, commit, push, or deletion outside this directory was run.
