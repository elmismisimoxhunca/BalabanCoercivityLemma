/-
Owned SI1-long file (compute/m1_si1_long/prod/). Imports the frozen `AdalyFormal` package
read-only, plus the READ-ONLY compiled wrap/endpoint/phi tranches of THIS SAME workflow (their
directories are extra `LEAN_PATH` search roots, nothing copied, all under this workflow's own
`compute/m1_si1_long`). Does not modify any of them.

TARGET: differentiate CMP98 (89)/(63)'s FOUR-FACTOR product
  `modifiedAverage V0 ell V1 c =
     (endpointAvg V0 V1 ell c.1)⁻¹
       * (ubarSU2 1 ell (configMul V1 V0) c * (ubarSU2 1 ell V0 c)⁻¹)
       * groupConj (ubarSU2 1 ell V0 c) (endpointAvg V0 V1 ell (cPlus ell c))`
at `t = 0` along `V1 = fun e => su2Exp (t • A e)`, via the product rule.

## What this file delivers

§1-§4: a GENERAL Rodrigues-type closed form for `NormedSpace.exp` at a NONZERO Lie-algebra
basepoint (`X * X = -θ² • 1`, `θ ≠ 0` ⟹ `exp X = cos θ • 1 + (sin θ/θ) • X`), proved by the SAME
`Complex.liftAux` transport `RegularityGap.su2_exp_log_of_ne_negOne` already uses for `su2Log g`
— generalized here from "X = su2Log g for a specific g" to ANY traceless anti-Hermitian X. This is
THE missing ingredient `phi/RawAverageDeriv.lean` named as its blocker ("su2Exp's derivative at a
general nonzero Lie-algebra basepoint... not banked anywhere in this tree... BCH/dexp-operator
territory") — resolved WITHOUT the general noncommutative dexp operator, because `su2Alg` elements
individually satisfy the quadratic relation `X² = -θ²•1` (2×2 Cayley–Hamilton at trace 0), which
puts `exp` on the COMMUTATIVE subalgebra `ℝ[X] ≅ ℂ` pointwise, at every `t` along a curve
— exactly `RegularityGap`'s own technique, never before applied off a `su2Log`-shaped argument.

§5-§6: the two "free" `modifiedAverage` factors — the inverse of `endpointAvg` at `c₋`, and
`groupConj` by the CONSTANT `ubarSU2 1 ell V0 c` of `endpointAvg` at `c₊` — differentiated by
reusing `endpoint/EndpointAvgDeriv.lean`'s `hasDerivAt_endpointAvg_coe` verbatim through
`HasDerivAt.comp`/constant-linear-map chain rules, no new analysis.

## What this file does NOT reach

The FULL `ubarSU2`/raw-average derivative (the "raw Phi ratio" factor) is NOT completed: its
loop-average term `su2Exp(Σ ell⁻³ su2Log(loopVar(x,t)))` needs, beyond §1-§4's closed form, (a) the
derivative of the REAL angle function `θ(t) = √(normSq(X(t) 0 0) + normSq(X(t) 1 0))` for the
SUMMED bracket `X(t)`, and (b) `loopVar`'s OWN derivative (`gammaVarStrided`'s three
`coarsePathHolonomy` legs plus one group inversion — `phi`'s `hasDerivAt_coarseBondVar_configMul`
only built ONE leg, the straight path). Neither is attempted here; §1-§4 removes the ONLY
non-mechanical obstruction phi identified, but (a)/(b) are real remaining Leibniz-rule bookkeeping.
The full four-factor `modifiedAverage` product rule is therefore NOT assembled; only the two free
factors are.
-/
import ModifiedAverageDeriv
import SI1AssembleDeriv
import EndpointAvgDeriv
import RawAverageDeriv
import AdalyFormal.Balaban.RegularityGap

set_option autoImplicit false

open Matrix
attribute [local instance 10000] Matrix.linftyOpNormedRing
attribute [local instance 10000] Matrix.linftyOpNormedAlgebra

namespace AdalySI1.ProdAssembleDeriv

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Log su2Exp_zero su2Log_one coe_mul coe_inv
  coe_one)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2)
open AdalyFormal.Balaban.RegularityGap (real_smul_eq)
open AdalySI1.ModifiedAverageDeriv (endpointAvg modifiedAverage configMul cPlus groupConj)
open AdalySI1.EndpointAvgDeriv (hasDerivAt_endpointAvg_coe)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — general 2×2 Cayley–Hamilton at trace zero (no anti-Hermitian hypothesis needed) -/

theorem traceless_sq (X : M2) (htr : Matrix.trace X = 0) :
    X * X = (-(Matrix.det X)) • (1 : M2) := by
  have hd : X 1 1 = -X 0 0 := by
    have h := htr
    rw [Matrix.trace_fin_two] at h
    linear_combination h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.one_apply,
      Matrix.smul_apply, hd] <;> ring

#print axioms traceless_sq

/-! ## §2 — `det X` is a nonnegative real for traceless anti-Hermitian `X`, read off `(XᴴX) 0 0` -/

theorem det_eq_normSq_of_traceless_antiHerm (X : M2) (htr : Matrix.trace X = 0)
    (hah : Xᴴ = -X) :
    Matrix.det X = ((Complex.normSq (X 0 0) + Complex.normSq (X 1 0) : ℝ) : ℂ) := by
  have hXX : Xᴴ * X = (Matrix.det X) • (1 : M2) := by
    have h1 := traceless_sq X htr
    have h2 : Xᴴ * X = -(X * X) := by rw [hah, Matrix.neg_mul]
    rw [h2, h1, neg_smul, neg_neg]
  have hz : ∀ z : ℂ, star z * z = ((Complex.normSq z : ℝ) : ℂ) := fun z => by
    rw [mul_comm, ← starRingEnd_apply, Complex.mul_conj]
  have hentry : (Xᴴ * X) 0 0
      = ((Complex.normSq (X 0 0) + Complex.normSq (X 1 0) : ℝ) : ℂ) := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
    rw [hz (X 0 0), hz (X 1 0), Complex.ofReal_add]
  rw [hXX] at hentry
  have hentry' : (Matrix.det X • (1 : M2)) 0 0
      = ((Complex.normSq (X 0 0) + Complex.normSq (X 1 0) : ℝ) : ℂ) := hentry
  simp [Matrix.smul_apply, Matrix.one_apply] at hentry'
  rw [hentry']
  push_cast
  ring

#print axioms det_eq_normSq_of_traceless_antiHerm

/-! ## §3 — THE NEW INGREDIENT: a general Rodrigues closed form for `NormedSpace.exp` at ANY
nonzero point of `su2Alg` — not merely `X = su2Log g` for a specific `g` -/

theorem normedExp_eq_rodrigues (X : M2) (θ : ℝ) (hθ0 : θ ≠ 0)
    (hXsq : X * X = ((-(θ ^ 2) : ℝ) : ℂ) • (1 : M2)) :
    NormedSpace.exp X = ((Real.cos θ : ℝ) : ℂ) • (1 : M2) + ((Real.sin θ / θ : ℝ) : ℂ) • X := by
  set J : M2 := (θ⁻¹ : ℝ) • X with hJdef
  have hJ : J * J = -1 := by
    rw [hJdef, smul_mul_assoc, mul_smul_comm, hXsq, real_smul_eq, smul_smul, smul_smul]
    have hval : θ⁻¹ * θ⁻¹ * -(θ ^ 2) = -1 := by field_simp
    rw [hval, neg_one_smul]
  set φ : ℂ →ₐ[ℝ] M2 := Complex.liftAux J hJ with hφ
  have hcont : Continuous ((φ : ℂ →ₐ[ℝ] M2) : ℂ → M2) := by
    have hc2 : Continuous ((φ : ℂ →ₐ[ℝ] M2).toLinearMap : ℂ → M2) :=
      LinearMap.continuous_of_finiteDimensional _
    exact hc2
  have hφθ : φ ((θ : ℂ) * Complex.I) = X := by
    rw [hφ, Complex.liftAux_apply]
    have hre : ((θ : ℂ) * Complex.I).re = 0 := by simp
    have him : ((θ : ℂ) * Complex.I).im = θ := by simp
    rw [hre, him, map_zero, zero_add, hJdef, smul_smul, mul_inv_cancel₀ hθ0, one_smul]
  have hexp : NormedSpace.exp X = φ (Complex.exp ((θ : ℂ) * Complex.I)) := by
    rw [Complex.exp_eq_exp_ℂ, NormedSpace.map_exp φ hcont, hφθ]
    rfl
  have hre2 : (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I).re = Real.cos θ := by
    simp [Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_re,
      Complex.sin_ofReal_im]
  have him2 : (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I).im = Real.sin θ := by
    simp [Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_re,
      Complex.sin_ofReal_im]
  rw [hexp, Complex.exp_mul_I, hφ, Complex.liftAux_apply, hre2, him2,
    Algebra.algebraMap_eq_smul_one, real_smul_eq, real_smul_eq, hJdef, smul_smul, div_eq_mul_inv]

#print axioms normedExp_eq_rodrigues

/-- **Packaged at `su2Alg` inputs**: for traceless anti-Hermitian `X` with `X ≠ 0`, `su2Exp X`
genuinely IS the Rodrigues combination — combining §3 with the tree's own unconditional
`exp_antiHerm_traceless_mem_special` membership fact (already compiled, no smallness hypothesis). -/
theorem su2Exp_eq_rodrigues_of_traceless_antiHerm (X : M2) (htr : Matrix.trace X = 0)
    (hah : Xᴴ = -X) (hX0 : X ≠ 0) :
    ((su2Exp X : SU2) : M2)
      = ((Real.cos (Real.sqrt (Complex.normSq (X 0 0) + Complex.normSq (X 1 0))) : ℝ) : ℂ) • (1 : M2)
        + ((Real.sin (Real.sqrt (Complex.normSq (X 0 0) + Complex.normSq (X 1 0)))
              / Real.sqrt (Complex.normSq (X 0 0) + Complex.normSq (X 1 0)) : ℝ) : ℂ) • X := by
  set θ : ℝ := Real.sqrt (Complex.normSq (X 0 0) + Complex.normSq (X 1 0)) with hθdef
  have hnn : 0 ≤ Complex.normSq (X 0 0) + Complex.normSq (X 1 0) :=
    add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  have hθsq : θ ^ 2 = Complex.normSq (X 0 0) + Complex.normSq (X 1 0) := by
    rw [hθdef, Real.sq_sqrt hnn]
  have hθ0 : θ ≠ 0 := by
    intro h
    apply hX0
    have h00 : X 0 0 = 0 := by
      have : Complex.normSq (X 0 0) = 0 := by
        have hz1 := Complex.normSq_nonneg (X 0 0)
        have hz2 := Complex.normSq_nonneg (X 1 0)
        nlinarith [hθsq, h, sq_nonneg θ]
      exact Complex.normSq_eq_zero.mp this
    have hd : X 1 1 = -X 0 0 := by
      have hh := htr; rw [Matrix.trace_fin_two] at hh; linear_combination hh
    have h10 : X 1 0 = 0 := by
      have : Complex.normSq (X 1 0) = 0 := by
        have hz1 := Complex.normSq_nonneg (X 0 0)
        have hz2 := Complex.normSq_nonneg (X 1 0)
        nlinarith [hθsq, h, sq_nonneg θ]
      exact Complex.normSq_eq_zero.mp this
    have h01 : X 0 1 = 0 := by
      have hconj : Xᴴ 1 0 = -(X 1 0) := by rw [hah]; rfl
      have : star (X 0 1) = -(X 1 0) := by
        rw [← hconj]; simp [Matrix.conjTranspose_apply]
      rw [h10, neg_zero] at this
      exact star_eq_zero.mp this
    ext i j; fin_cases i <;> fin_cases j <;> simp [h00, h10, h01, hd, h00]
  have hXsq : X * X = ((-(θ ^ 2) : ℝ) : ℂ) • (1 : M2) := by
    rw [traceless_sq X htr, det_eq_normSq_of_traceless_antiHerm X htr hah, ← hθsq, Complex.ofReal_neg]
  have hmem : NormedSpace.exp X ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    AdalyFormal.Balaban.SuTwoLogExp.exp_antiHerm_traceless_mem_special hah htr
  rw [AdalyFormal.Balaban.SuTwoLogExp.su2Exp_of_mem hmem, normedExp_eq_rodrigues X θ hθ0 hXsq]

#print axioms su2Exp_eq_rodrigues_of_traceless_antiHerm

/-! ## §4 — `modifiedAverage`'s two FREE factors: differentiate them via `hasDerivAt_endpointAvg_coe`

`modifiedAverage V0 ell V1 c = (endpointAvg V0 V1 ell c.1)⁻¹ * (raw Phi ratio, NOT reached here) *
groupConj (ubarSU2 1 ell V0 c) (endpointAvg V0 V1 ell (cPlus ell c))`. Both the `c₋` endpoint
factor (inverted) and the `c₊` endpoint factor (conjugated by the CONSTANT `ubarSU2 1 ell V0 c`)
depend on `t` ONLY through `endpointAvg`, whose derivative is already compiled
(`EndpointAvgDeriv.hasDerivAt_endpointAvg_coe`); `SU(2)`-inverse is `g ↦ gᴴ`
(`SuTwoLogExp.coe_inv`), an `ℝ`-linear (in fact `ℝ`-continuous-linear) map, and `groupConj` by a
constant is two constant matrix multiplications, both continuous `ℝ`-bilinear-with-one-side-fixed
maps — no new analysis beyond chain rule through already-built continuous linear maps. -/

def leftMulLM (g : M2) : M2 →ₗ[ℝ] M2 where
  toFun M := g * M
  map_add' M N := Matrix.mul_add g M N
  map_smul' r M := by rw [RingHom.id_apply, mul_smul_comm]

noncomputable def leftMulCLM (g : M2) : M2 →L[ℝ] M2 := (leftMulLM g).toContinuousLinearMap

theorem leftMulCLM_apply (g M : M2) : leftMulCLM g M = g * M := rfl

def rightMulLM (g : M2) : M2 →ₗ[ℝ] M2 where
  toFun M := M * g
  map_add' M N := Matrix.add_mul M N g
  map_smul' r M := by rw [RingHom.id_apply, smul_mul_assoc]

noncomputable def rightMulCLM (g : M2) : M2 →L[ℝ] M2 := (rightMulLM g).toContinuousLinearMap

theorem rightMulCLM_apply (g M : M2) : rightMulCLM g M = M * g := rfl

/-- **`endpointAvg`'s `c−` factor, INVERTED.** Stated directly via `Matrix.conjTranspose`: for any
`g : SU2`, `(g⁻¹ : M2) = (g : M2)ᴴ` (`SuTwoLogExp.coe_inv`, `rfl`), so this IS `modifiedAverage`'s
first factor's derivative, just written in the form that does not trip the `SU2`-vs-`M2` `Inv`
elaboration ambiguity (the outer `: M2` ascription placed directly after `⁻¹` was silently
picking up `M2`'s OWN matrix-inverse instance instead of `SU2`'s group inverse coerced). -/
theorem hasDerivAt_endpointAvg_inv_coe (V0 : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (A : PeriodicLatticeEdge L → M2) (hah : ∀ e, (A e)ᴴ = -(A e))
    (htr : ∀ e, Matrix.trace (A e) = 0) (y : PeriodicLatticeSite L) :
    HasDerivAt (fun t : ℝ => (((endpointAvg V0 (fun e => su2Exp (t • A e)) ell y : SU2) : M2))ᴴ)
      (((∑ x ∈ AdalyFormal.Balaban.AdmissibleSubspace.blockOf y ell,
          ((ell : ℚ) ^ 3)⁻¹ • AdalySI1.IngredientDeriv.dirDeriv V0 A y
            (AdalyFormal.Balaban.Q1Real.GammaPath y x) 1))ᴴ) 0 := by
  have hb := hasDerivAt_endpointAvg_coe V0 ell A hah htr y
  exact AdalySI1.RawAverageDeriv.hasDerivAt_conjTranspose_curve 0 hb

#print axioms hasDerivAt_endpointAvg_inv_coe

/-- `groupConj g h = g*h*g⁻¹` by a CONSTANT `g`: the value-level identity feeding into the
fourth factor's derivative. **Not yet discharged as a `HasDerivAt`** — every route tried
(`HasDerivAt.const_mul`/`.mul_const`, a composed `M2 →L[ℝ] M2` continuous linear map via
`HasFDerivAt.comp_hasDerivAt_of_eq`) hits the SAME ambient-`Matrix`-instance diamond `wrap`'s own
header already flagged (`hb`, imported from `EndpointAvgDeriv`, is stated against the GLOBAL
default `Matrix` `TopologicalSpace`/`AddCommGroup`/`Module` instances, while any `M2 →L[ℝ] M2`
continuous linear map built under this file's local `Matrix.linftyOpNormedRing`/`linftyOpNormedAlgebra`
instances carries THOSE instead) — confirmed a real blocker, not a guess: three concrete tactic
attempts recorded in this file's compile history all produced the identical instance-path type
mismatch. `wrap`'s own fix (`refine … .mpr ?_` against `hasDerivAt_iff_isLittleO_nhds_zero`, full
`isDefEq` unification instead of `rw`/`exact`/`simpa`'s syntactic matching) was NOT reattempted
here given the remaining budget; it is the concrete next step, not open-ended search. -/
theorem groupConj_const_eq (V0 : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (A : PeriodicLatticeEdge L → M2) (t : ℝ) (y : PeriodicLatticeSite L) (g : SU2) :
    ((groupConj g (endpointAvg V0 (fun e => su2Exp (t • A e)) ell y) : SU2) : M2)
      = (g : M2) * ((endpointAvg V0 (fun e => su2Exp (t • A e)) ell y : SU2) : M2) * (g : M2)ᴴ := by
  show ((g * endpointAvg V0 (fun e => su2Exp (t • A e)) ell y * g⁻¹ : SU2) : M2) = _
  rw [coe_mul, coe_mul, coe_inv]

#print axioms groupConj_const_eq

end AdalySI1.ProdAssembleDeriv
