# Dictionary round 4 — exact color selection and an actual zero-jet obstruction

**GoalNeg2 remains OPEN. No original round-9 cofinal coupling premise is proved or refuted.** This final round supplies exact selection rules for the actual flat dressed quadratic jet and its propagated source response. It also constructs a nonzero charged physical field with zero full jet and zero coupling to every profile. That field is **not asserted to lie in a crossing kernel**. Consequently the construction refutes a proposed shortcut from “nonzero and charged” to jet nonvanishing, not the guarded reading or its coupling premise.

## 1. Compiled deliverables and verification

| Local file | Shared publication | Lines | New declarations | Axiom records |
|---|---|---:|---:|---:|
| `Color.lean` | `AHP/round10/shared/dictionary/R4_ColorSelection.lean` | 299 | 22 | 22 |
| `Actual.lean` | `AHP/round10/shared/dictionary/R4_ColorResponse.lean` | 2185 | 61 | 194 |

Each local file and each shared copy has an independent clean wrapper compilation, exit **0**. The full shared publication was additionally recompiled after recovery of this round's interrupted thread, through `bb heavy run -- AHP/round3/lean1.sh ...`, with exit **0**. No warning or error occurs in any final log. Every one of the **61 new declarations** has an individual axiom print; all records use only `propext`, `Classical.choice`, `Quot.sound` (or no axioms). `CHECKS.json` passes.

The sole import is frozen `DrEquiv`. The complete R3 `R3_FreeSource.lean` is an unchanged byte prefix of `Actual.lean`. Four reused source fragments, including the original round-9 flip element and the original dilated-size lemmas, are checked verbatim by `COPIES.json` and `audit.py`. Local/shared publications are byte-identical. There are no replacement operators or weakened copies of operative definitions.

New namespaces, all under `AdalyFormal.Round10.Dictionary`:

- `Color`: quadratic algebra and global-color covariance, 22 declarations;
- `ColorResponse`: actual neutral/charged projections and response identities, 28 declarations;
- `ColorObstruction`: an explicit physical zero-jet charged field, 11 declarations.

Main printed records include:

```text
'AdalyFormal.Round10.Dictionary.ColorResponse.vacJet_chargedPart_component' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round10.Dictionary.ColorObstruction.exists_charged_invisible' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 2. Exact full-color covariance at the flat interior

For any frozen tower geometry G and mass a, define

\[
z(u)=C^2_G(1)\bigl(W_G(1,a)i_Eu\bigr).
\]

This is `Color.flatJet`, not a surrogate jet. It is quadratic (`flatJet_quad`) and satisfies, for every constant \(g\in SU(2)\),

\[
z(\operatorname{Ad}_g u)=\operatorname{Ad}_g z(u).
\]

`flatJet_gauge` follows directly from the frozen `Wop_gauge`, `iE_adEL` and `C2fullOf_gauge`: every constant gauge fixes the trivial background. `ColorResponse.vacJet_constant` specializes it to the actual dilated family, and `flatH_constant` proves the corresponding covariance of the **full** flat constrained lift H, using the frozen assembled gauge equivalence. These identities hold without added unit hypotheses; they are algebraic covariance identities for the defined operators, not claims that every totalized inverse is a unit at arbitrary parameters.

This is full SU(2) covariance of the **flat interior W/C2/H**, not full SU(2) commutation of the exterior-twisted carrier. A diagonal exterior twist preserves only the already-proved diagonal U(1), and the flip below changes that background. No crossing-kernel flip invariance is inferred.

Put

\[
S=\operatorname{Ad}_{\mathrm{diag}(i,-i)},\qquad
F=\operatorname{Ad}_{\left(\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right)},\qquad
E_3=\mathrm{diag}(i,-i).
\]

Here E3 is the norm-one frozen `pauliE3`. The exact matrix calculations show that S fixes the neutral axis, negates the charged plane, and F negates E3. Quadratic evenness and covariance then give:

1. **Neutral inputs have zero full jet:** \(Su=u\Rightarrow z(u)=0\) (`flatJet_neutral_zero`). Indeed z(u) is fixed by S; F sends u to -u, so evenness also makes z(u) fixed by F. A neutral vector fixed by F is zero.
2. **Charged inputs have neutral jets:** \(Su=-u\Rightarrow z(u)(p)=\langle E_3,z(u)(p)\rangle E_3\) (`flatJet_charged_neutral`). This is quadratic equivariance, not linear sector preservation.
3. **A charged single real color has zero full jet:** if additionally \(Fu=u\) or \(Fu=-u\), then z(u)=0 (`flatJet_single_color_zero`). Again both S and F fix the output.

No local blocking-path formula, Fourier character, spectral hypothesis or numerical approximation is used for these results.

## 3. Charged projection preserves all free-profile information

Define the exact orthogonal projections on the physical carrier:

\[
u_+=\tfrac12(u+Su),\qquad u_-=\tfrac12(u-Su).
\]

`color_decomposition`, `neutralPart_fixed`, `chargedPart_neg`, `color_orthogonal` prove \(u=u_++u_-\), \(Su_+=u_+\), \(Su_-=-u_-\), and \(\langle u_+,u_-\rangle=0\). The neutral projection is pointwise \(u_+(b)=\langle E_3,u(b)\rangle E_3\).

Let \(n(z)(p)=\langle E_3,z(p)\rangle\). This is a quadratic S-invariant map. Its neutral self-term vanishes by section 2, and the quadratic parallelogram identity kills its mixed neutral/charged term. Thus

\[
n(z(u_-))=n(z(u)),\qquad z(u_-)(p)=n(z(u))(p)E_3.
\]

The second equality is the main actual-family theorem:

```lean
theorem vacJet_chargedPart_component (q R : ℕ) (u : TwistSpace q R)
    (p : BIdx (geomOf 2 1 (dilTower q R))) :
    vacJet q R (chargedPart (geomOf 2 1 (dilTower q R)) u) p =
      neutralCoord (vacJet q R u p) • pauliE3
```

It applies componentwise before any physical transverse sum, so no Bloch-cell normalization is needed.

Recall R3's actual response profile and explicit coupling:

\[
r_u(b)=\langle E_3,(i_EH_0z(u))(b)\rangle,\qquad
F_f(u)=2\langle H_0z(u),J'[f]\rangle
      =2\sum_{p\in\mathrm{plaqIn}(\Omega_0)}c_{r_u}(p)c_f(p).
\]

Using covariance of full H gives the exact identities

\[
r_{\operatorname{Ad}_{g_\alpha}u}=r_u,\qquad r_{Fu}=-r_u,
\qquad r_{u_+}=0,\qquad r_{u_-}=r_u.
\]

These are `responseProfile_rot`, `responseProfile_flip`, `responseProfile_neutralPart_zero`, and `responseProfile_chargedPart`. Consequently:

```lean
curlDetected_chargedPart_iff :
  CurlDetected q R (chargedPart (geomOf 2 1 (dilTower q R)) u) ↔ CurlDetected q R u

profileCoupling_chargedPart :
  profileCoupling q R f (chargedPart (geomOf 2 1 (dilTower q R)) u) =
    profileCoupling q R f u
```

A flip eigenvector is invisible to every diagonal profile, whether or not it is purely charged (`responseProfile_flip_eigen_zero`, `profileCoupling_zero_of_flip_eigen`). For opposite flip eigenspaces, the response is purely mixed:

\[
Fx=x,\quad Fy=-y\quad\Longrightarrow\quad
r_{ax+by}=ab\,r_{x+y}.
\]

This is `responseProfile_mixed`, derived from the actual quadratic map and its vanishing self-terms. It is not a proof that the mixed term of a crossing vector is nonzero, nor a full spatial alternating-form or transfer-matrix dictionary.

The explicit form is the same H0-C2-J' form as before. Identification with the original arbitrary-profile `corrDeriv` uses assembly R3's compiled `corrDeriv_profile_form` with visible known regularity inputs; this round does not recompile the long historical regularity join or silently drop those inputs.

## 4. A concrete obstruction to nonzero-plus-charged detection

For every q>0 and every R, choose the fine site

\[
x=(4q,0,0)\in\Omega_0
\]

and the direction-0 bond at x. Put the frozen charged generator `pauliE1` on that bond and zero elsewhere. `ColorObstruction.oneColor` is this actual touching-bond carrier element, built with frozen `sing` and `sing_mem_bondSupp`.

The construction checks the physical torus bounds and membership in Omega0, proves the field is nonzero using the Pauli norm, and computes

\[
Su=-u,\qquad Fu=-u.
\]

Section 2 therefore gives zero **full dressed quadratic jet**, not merely a vanishing aggregate. Section 3 gives zero coupling to every profile. The exact compiled conclusion is:

```lean
theorem exists_charged_invisible {q : ℕ} (hq : 0 < q) (R : ℕ) :
    ∃ u : TwistSpace q R, u ≠ 0 ∧ halfE (geomOf 2 1 (dilTower q R)) u = -u ∧
      vacJet q R u = 0 ∧ (∀ f, profileCoupling q R f u = 0)
```

**This does not refute any actual coupling premise.** There is no assertion that this u solves the exterior vacuum kernel equation at any angle. Rather, it proves that a crossing-specific argument is indispensable: neither a nonzero linear field nor being charged forces a nonzero quadratic jet, even for the actual frozen operators in every admissible geometry.

Similarly, a free-profile coupling vanishes on neutral kernel directions. To prove definiteness on a full crossing kernel one must exclude such directions (or prove the relevant kernel is charged); projecting a selected vector to its charged part does not eliminate other vectors from the kernel.

## 5. Exact remaining targets — unproved

The unchanged R3 actual-operator path is

\[
\mathrm{TopJetDetected}\Longrightarrow\mathrm{CurlDetected}
\Longrightarrow F_{r_u}(u)>0,
\]

with the known full flat constraint-unit premise explicit in the first implication. This round preserves the neutral jet and response under charged projection but proves neither detection condition for a genuine crossing vector.

One precise sufficient remaining premise is the already-defined
`AdalyFormal.Round10.Assembly.R3.CofinalAnyPathCurlLine`. Its exact definition, with the same namespace opens as `assembly/r3/EnergyGlue.lean`, is:

```lean
def CofinalAnyPathCurlLine : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)),
      AdalyFormal.D1Literal.ContFam V ∧ AnFam V ∧ V 0 = (fun _ => 1) ∧
      (∃ w, ⟪w, vacA (2^j) R V 1 Real.pi w⟫ < 0) ∧
      ∃ u : TwistSpace (2^j) R, KernelLine (2^j) R V u ∧ CurlDetected (2^j) R u
```

`KernelLine` is `AdalyFormal.Round10.Assembly.R2.KernelLine`, not merely selected-sector simplicity:

```lean
def KernelLine (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (u₀ : TwistSpace q R) : Prop :=
  u₀ ≠ 0 ∧ vacA q R V 1 (vacEdge q R V) u₀ = 0 ∧
  adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R))
    (adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)) u₀) = -u₀ ∧
  (∀ u, vacA q R V 1 (vacEdge q R V) u = 0 →
    u ∈ Submodule.span ℝ {u₀,
      adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)) u₀})
```

The other predicate is exactly R3's

```lean
def CurlDetected (q R : ℕ) (u : TwistSpace q R) : Prop :=
  ∃ p ∈ plaqIn ((dilTower q R).Om 0),
    circulation (responseProfile q R u) p ≠ 0
```

The fixed canonical-path version `CofinalCurlLine` drops the free-path clauses and uses `uthPath`. Either still requires:

1. crossing-specific nonzero physical jet aggregate or localized response curl;
2. containment of the **entire** crossing kernel in the charged line, or a valid alternative single-profile definiteness argument on the entire kernel;
3. arbitrarily large dyadic exponents and, at each selected exponent, arbitrarily large even radii, not just one radius per scale.

Assembly R4 is separately developing the full-kernel response-convex-hull alternative. This dictionary does not prove its no-cancellation hypothesis. Nonvanishing R4 supplies an abstract polynomial/Bezout cofinal certificate, but no certificate is identified with the actual operators. Its published status was inspected, not independently recompiled here.

**Still not proved by the dictionary track:** full spatial W/Q/T covariance; transverse character decomposition and block dimensions; crossing-kernel character concentration/simplicity; actual cofinal coupling. R1 proves only the differential/Hessian translation layer. A quadratic C2 must not be treated as a linear character-preserving operator. R1's precise collar/core-length obstruction to a canonical q=1 radius identification remains; no canonical dilation isometry is used or claimed.

### Question for a future nonvanishing round

Can the crossing equation rule out all flip-eigenvector/one-real-color cancellations and force a nonzero physical mixed-color jet? Please specify whether you need a local C2 path stencil, a W boundary-transfer identity, or spectral exclusion for an already identified left-only crossing. The current global-color rules do not supply that nondegeneracy. If using assembly's whole-kernel alternative, which actual kernel property prevents cancellation among the response gradients of distinct unit vectors? No further round is started by this hand-off.

## 6. Reproduction, recovery and hygiene

The original round-4 execution had already written and compiled the final Lean artifacts before its thread failed. The continuation inspected those actual files rather than overwriting them, reran `audit.py`, independently recompiled the strongest shared publication, and completed these notes and `shared/dictionary/R4_STATUS.md`. It does not present the earlier thread's termination as a mathematical failure or a goal proof.

From the repository root:

```sh
python3 AHP/round10/dictionary/r4/build.py
bb heavy run -- AHP/round3/lean1.sh AHP/round10/dictionary/r4/Color.lean
bb heavy run -- AHP/round3/lean1.sh AHP/round10/dictionary/r4/Actual.lean
bb heavy run -- AHP/round3/lean1.sh AHP/round10/shared/dictionary/R4_ColorSelection.lean
bb heavy run -- AHP/round3/lean1.sh AHP/round10/shared/dictionary/R4_ColorResponse.lean
python3 AHP/round10/dictionary/r4/audit.py
```

`build.py` writes only the local harnesses. Publication files are already byte-identical; if changing the appendices later, publish new names rather than overwrite a consumed hand-off. For a combined assembly, use the three appendix fragments after their dependencies, not two complete harnesses with duplicate declarations.

No new numerical experiment, large historical compilation, `lake build`, `REPRODUCE.sh`, git commit/push, worktree operation or deletion was performed. Authored proof/notes/audit files are confined to `dictionary/r4/` and `shared/dictionary/`. No protected source, earlier-round file, another track's file or integration checkout was edited. The final successful compilation records and axiom audit are evidence for the stated selection rules only, not for GoalNeg2.
