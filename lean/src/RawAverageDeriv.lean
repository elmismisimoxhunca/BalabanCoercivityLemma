/-
Owned SI1 scratch file (compute/m1_si1_long/phi/). Imports the frozen `AdalyFormal` package
read-only, plus the READ-ONLY wrap/ and endpoint/ olean artifacts of THIS SAME workflow (their
directories are search roots, nothing copied). Does not modify any of them.

TARGET: differentiate CMP98 (89)/(63)'s second factor `(V̄₁V₀)_c(V̄₀)_c⁻¹` at `t = 0` along
`V₁ = fun e => su2Exp(t•A e)` — i.e. `ubarSU2 1 ell (configMul V1 V0) c`, THE RAW AVERAGE (15)
ITSELF (`stridedBlockedGauge su2LogExp 1 ell · c`), INCLUDING its final multiplicative
`coarseBondVar` factor (CMP98 (15)'s "`U(c)`", the straight `ell`-fold bond product), evaluated at
an ARBITRARY (not-necessarily-near-identity) background `V0` — since `(configMul V1 V0) (e) =
V1(e)*V0(e)` equals `V0(e)` (not `1`) at `t=0`, this is genuinely NOT the "identity-loop proxy"
that `wrap`'s/`endpoint`'s own `rZeroPath`/`endpointAvg` machinery handles (there the VARIED field
`V1` alone collapses to the trivial link config at `t=0`, regardless of the (separately-tracked,
conjugation-only) background). `ubarSU2`'s raw average has no such separate "background role" for
`V0`: `V0` enters the SAME multiplicative slot the perturbation does.
-/
import AdalyFormal.Balaban.Q1Real
import AdalyFormal.Balaban.BlockedBackground
import AdalyFormal.Balaban.SuTwoLogExpCore
import AdalyFormal.Balaban.SuTwoLogExpFaithful
import AdalyFormal.Balaban.SuTwoLogExpTorus
import AdalyFormal.Balaban.UbarTowerCovariance
import AdalyFormal.Balaban.TowerLawCovariant
import AdalyFormal.Balaban.CovariantHjMinimizer
import IngredientDeriv
import ModifiedAverageDeriv

set_option autoImplicit false

open Matrix
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace AdalySI1.RawAverageDeriv

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Log su2Kappa su2Angle su2NegOne
  su2Exp_zero su2Log_one coe_mul coe_inv coe_one adMap adMap_apply sin_su2Angle_ne_zero)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2)
open AdalyFormal.Balaban.UbarTowerCov (coarseBondVar gammaVarStrided loopVar cPlusS)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalySI1.IngredientDeriv (groupConj hasDerivAt_su2Exp_coe_smul)
open AdalySI1.ModifiedAverageDeriv (configMul)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — `su2Log` differentiates OFF THE IDENTITY, at any non-central point

`wrap`'s/`endpoint`'s own `su2Log` ingredient (`IngredientDeriv.hasDerivAt_su2Log_su2Exp_smul`) is
the composite `su2Log ∘ su2Exp` on a curve through `0`, using the EXACT local inverse `Bch2.log_exp`
— it never differentiates `su2Log` itself away from the identity. `su2Log`'s own definition,
`(κ(g)/2)•(g−gᴴ)` with `κ(g) = θ(g)/sin θ(g)`, `θ(g) = arccos((tr g).re/2)`, is an EXPLICIT
algebraic formula with a genuine coordinate singularity ONLY at `sin θ(g) = 0`, i.e. at the two
central elements `g = 1, -1` (`SuTwoLogExpFaithful.sin_su2Angle_ne_zero`). Away from those two
points this is ordinary calculus: `arccos` differentiates by Mathlib's own `hasDerivAt_arccos`
wherever its argument avoids `±1`, and the trace/conjugate-transpose maps are `ℝ`-linear. -/

/-- The trace argument `(tr g).re / 2` avoids Mathlib's `arccos` singularities `±1` exactly where
`g` avoids the two central elements — read off `sin_su2Angle_ne_zero` by contraposition against
`Real.arccos_one`/`Real.arccos_neg_one`, no re-derivation of the trace bound. -/
theorem traceArg_ne_center (g : SU2) (h1 : g ≠ 1) (h2 : g ≠ su2NegOne) :
    (Matrix.trace (g : M2)).re / 2 ≠ 1 ∧ (Matrix.trace (g : M2)).re / 2 ≠ -1 := by
  have hsin := sin_su2Angle_ne_zero g h1 h2
  constructor
  · intro hx
    exact hsin (by unfold su2Angle; rw [hx, Real.arccos_one, Real.sin_zero])
  · intro hx
    exact hsin (by unfold su2Angle; rw [hx, Real.arccos_neg_one, Real.sin_pi])

#print axioms traceArg_ne_center

/-- **The composite `M ↦ (tr M).re` is a genuine `ℝ`-linear map on `M2`**, built directly (not via
`Complex.reCLM ∘ traceLinearMap`, which routes `ℝ`'s own `Module ℝ ℝ` instance through `RCLike` and
produces a codomain-instance diamond against the plain `HasDerivAt … : ℝ → ℝ` goal below). -/
def reTraceLM : M2 →ₗ[ℝ] ℝ where
  toFun M := (Matrix.trace M).re
  map_add' M N := by simp [Matrix.trace_add]
  map_smul' r M := by
    simp only [Matrix.trace_smul, RingHom.id_apply, smul_eq_mul]
    rw [Complex.real_smul, Complex.mul_re]
    simp

theorem reTraceLM_apply (M : M2) : reTraceLM M = (Matrix.trace M).re := rfl

noncomputable def reTraceCLM : M2 →L[ℝ] ℝ := reTraceLM.toContinuousLinearMap

theorem reTraceCLM_apply (M : M2) : reTraceCLM M = (Matrix.trace M).re := rfl

/-- **PAID — `t ↦ (tr (G t)).re` differentiates along any `ℝ`-differentiable ambient curve `G`,
unconditionally** (linear-in-`M`, hence entire — no singularity at all, unlike `arccos` itself). -/
theorem hasDerivAt_reTrace_curve {G : ℝ → M2} {G' : M2} (t0 : ℝ) (hG : HasDerivAt G G' t0) :
    HasDerivAt (fun t => (Matrix.trace (G t)).re) (Matrix.trace G').re t0 := by
  have h := reTraceCLM.hasFDerivAt.comp_hasDerivAt t0 hG
  exact h

#print axioms hasDerivAt_reTrace_curve

/-- **PAID — `arccos ∘ (trace-real-part / 2)` differentiates at any non-central `SU(2)` point**,
along an arbitrary `ℝ`-differentiable ambient curve through it. -/
theorem hasDerivAt_su2Angle_curve {g0 : M2} {G : ℝ → M2} {G' : M2} (t0 : ℝ)
    (hG : HasDerivAt G G' t0) (h1 : (Matrix.trace g0).re / 2 ≠ 1)
    (h2 : (Matrix.trace g0).re / 2 ≠ -1) (hval : G t0 = g0) :
    HasDerivAt (fun t => Real.arccos ((Matrix.trace (G t)).re / 2))
      (-(1 / Real.sqrt (1 - ((Matrix.trace g0).re / 2) ^ 2)) * ((Matrix.trace G').re / 2)) t0 := by
  have hTrace : HasDerivAt (fun t => (Matrix.trace (G t)).re / 2)
      ((Matrix.trace G').re / 2) t0 := (hasDerivAt_reTrace_curve t0 hG).div_const 2
  have h1' : (Matrix.trace (G t0)).re / 2 ≠ -1 := hval ▸ h2
  have h2' : (Matrix.trace (G t0)).re / 2 ≠ 1 := hval ▸ h1
  have harc := (Real.hasDerivAt_arccos h1' h2').comp t0 hTrace
  rw [hval] at harc
  exact harc

#print axioms hasDerivAt_su2Angle_curve

/-- **PAID — `sin ∘ su2Angle` differentiates at any non-central point**, chain rule against
`hasDerivAt_su2Angle_curve`. -/
theorem hasDerivAt_sin_su2Angle_curve {g0 : M2} {G : ℝ → M2} {G' : M2} (t0 : ℝ)
    (hG : HasDerivAt G G' t0) (h1 : (Matrix.trace g0).re / 2 ≠ 1)
    (h2 : (Matrix.trace g0).re / 2 ≠ -1) (hval : G t0 = g0) :
    HasDerivAt (fun t => Real.sin (Real.arccos ((Matrix.trace (G t)).re / 2)))
      (Real.cos (Real.arccos ((Matrix.trace g0).re / 2)) *
        (-(1 / Real.sqrt (1 - ((Matrix.trace g0).re / 2) ^ 2)) * ((Matrix.trace G').re / 2))) t0 := by
  have hAngle := hasDerivAt_su2Angle_curve t0 hG h1 h2 hval
  rw [← hval] at hAngle
  have h := (Real.hasDerivAt_sin _).comp t0 hAngle
  rw [hval] at h
  exact h

#print axioms hasDerivAt_sin_su2Angle_curve

/-- **PAID — `su2Kappa = θ/sinθ` differentiates at any non-central point**, quotient rule
(denominator nonzero is exactly `sin_su2Angle_ne_zero`, threaded via `h1`/`h2`). -/
theorem hasDerivAt_su2Kappa_curve {g0 : M2} {G : ℝ → M2} {G' : M2} (t0 : ℝ)
    (hG : HasDerivAt G G' t0) (h1 : (Matrix.trace g0).re / 2 ≠ 1)
    (h2 : (Matrix.trace g0).re / 2 ≠ -1) (hval : G t0 = g0)
    (hsin0 : Real.sin (Real.arccos ((Matrix.trace g0).re / 2)) ≠ 0) :
    HasDerivAt (fun t => Real.arccos ((Matrix.trace (G t)).re / 2)
        / Real.sin (Real.arccos ((Matrix.trace (G t)).re / 2)))
      (((-(1 / Real.sqrt (1 - ((Matrix.trace g0).re / 2) ^ 2)) * ((Matrix.trace G').re / 2))
            * Real.sin (Real.arccos ((Matrix.trace g0).re / 2))
          - Real.arccos ((Matrix.trace g0).re / 2)
            * (Real.cos (Real.arccos ((Matrix.trace g0).re / 2))
                * (-(1 / Real.sqrt (1 - ((Matrix.trace g0).re / 2) ^ 2)) * ((Matrix.trace G').re / 2))))
        / (Real.sin (Real.arccos ((Matrix.trace g0).re / 2))) ^ 2) t0 :=
  by
    have hAngle := hasDerivAt_su2Angle_curve t0 hG h1 h2 hval
    have hSin := hasDerivAt_sin_su2Angle_curve t0 hG h1 h2 hval
    rw [← hval] at hAngle hSin
    have hsin0' : Real.sin (Real.arccos ((Matrix.trace (G t0)).re / 2)) ≠ 0 := hval ▸ hsin0
    have h := hAngle.div hSin hsin0'
    rw [hval] at h
    exact h

#print axioms hasDerivAt_su2Kappa_curve

/-! ## §2 — `conjTranspose` is `ℝ`-linear, hence differentiates unconditionally -/

def conjTransposeLM : M2 →ₗ[ℝ] M2 where
  toFun M := Mᴴ
  map_add' := Matrix.conjTranspose_add
  map_smul' r M := by simp [Matrix.conjTranspose_smul]

theorem conjTransposeLM_apply (M : M2) : conjTransposeLM M = Mᴴ := rfl

noncomputable def conjTransposeCLM : M2 →L[ℝ] M2 := conjTransposeLM.toContinuousLinearMap

theorem conjTransposeCLM_apply (M : M2) : conjTransposeCLM M = Mᴴ := rfl

theorem hasDerivAt_conjTranspose_curve {G : ℝ → M2} {G' : M2} (t0 : ℝ) (hG : HasDerivAt G G' t0) :
    HasDerivAt (fun t => (G t)ᴴ) (G')ᴴ t0 := by
  have h := conjTransposeCLM.hasFDerivAt.comp_hasDerivAt t0 hG
  exact h

#print axioms hasDerivAt_conjTranspose_curve

/-! ## §3 — `su2Log`, assembled: differentiates at any non-central `SU(2)` point -/

/-- **PAID — THE NEW INGREDIENT.** `su2Log g = (κ(g)/2) • (g − gᴴ)` differentiates along ANY
`ℝ`-differentiable ambient curve `G` through any NON-CENTRAL point `g0 = G t0` — not merely on
curves built from `su2Exp(t•H)` through the identity. This is the piece `wrap`'s/`endpoint`'s own
`su2Log` ingredient (`IngredientDeriv.hasDerivAt_su2Log_su2Exp_smul`, an exact local-inverse
argument valid only through `g = 1`) cannot supply, and the piece the raw average (15)'s loop
term `log(W_x)` genuinely needs since `W_x` sits at a non-identity point for a nonidentity
background. -/
theorem hasDerivAt_su2Log_curve {g0 : M2} {G : ℝ → M2} {G' : M2} (t0 : ℝ)
    (hG : HasDerivAt G G' t0) (h1 : (Matrix.trace g0).re / 2 ≠ 1)
    (h2 : (Matrix.trace g0).re / 2 ≠ -1) (hval : G t0 = g0)
    (hsin0 : Real.sin (Real.arccos ((Matrix.trace g0).re / 2)) ≠ 0) :
    HasDerivAt (fun t => (((Real.arccos ((Matrix.trace (G t)).re / 2)
            / Real.sin (Real.arccos ((Matrix.trace (G t)).re / 2))) / 2 : ℝ) : ℂ) • (G t - (G t)ᴴ))
      ((((Real.arccos ((Matrix.trace g0).re / 2)
              / Real.sin (Real.arccos ((Matrix.trace g0).re / 2))) / 2 : ℝ) : ℂ) • (G' - G'ᴴ)
        + (((((-(1 / Real.sqrt (1 - ((Matrix.trace g0).re / 2) ^ 2)) * ((Matrix.trace G').re / 2))
              * Real.sin (Real.arccos ((Matrix.trace g0).re / 2))
            - Real.arccos ((Matrix.trace g0).re / 2)
              * (Real.cos (Real.arccos ((Matrix.trace g0).re / 2))
                  * (-(1 / Real.sqrt (1 - ((Matrix.trace g0).re / 2) ^ 2)) * ((Matrix.trace G').re / 2))))
          / (Real.sin (Real.arccos ((Matrix.trace g0).re / 2))) ^ 2) / 2 : ℝ) : ℂ)
          • (g0 - g0ᴴ)) t0 := by
  have hKappa := (hasDerivAt_su2Kappa_curve t0 hG h1 h2 hval hsin0).div_const 2
  rw [← hval] at hKappa
  have hKappaC := hKappa.ofReal_comp
  have hSub : HasDerivAt (fun t => G t - (G t)ᴴ) (G' - G'ᴴ) t0 :=
    hG.sub (hasDerivAt_conjTranspose_curve t0 hG)
  have hprod := hKappaC.smul hSub
  rw [hval] at hprod
  exact hprod

#print axioms hasDerivAt_su2Log_curve

/-- **PAID — the same fact, stated directly against `su2Log`/`SU2`** (not the raw `κ`/subtraction
formula): for a curve `V : ℝ → SU2` whose `M2`-coercion is differentiable and which passes through
any NON-CENTRAL point `g0` at `t0`, `t ↦ su2Log (V t)` is genuinely differentiable there. -/
theorem hasDerivAt_su2Log_su2_curve {g0 : SU2} {V : ℝ → SU2} {G' : M2} (t0 : ℝ)
    (hG : HasDerivAt (fun t => ((V t : SU2) : M2)) G' t0) (hne1 : g0 ≠ 1)
    (hne2 : g0 ≠ su2NegOne) (hval : V t0 = g0) :
    HasDerivAt (fun t => su2Log (V t))
      ((((Real.arccos ((Matrix.trace (g0 : M2)).re / 2)
              / Real.sin (Real.arccos ((Matrix.trace (g0 : M2)).re / 2))) / 2 : ℝ) : ℂ) • (G' - G'ᴴ)
        + (((((-(1 / Real.sqrt (1 - ((Matrix.trace (g0 : M2)).re / 2) ^ 2)) * ((Matrix.trace G').re / 2))
              * Real.sin (Real.arccos ((Matrix.trace (g0 : M2)).re / 2))
            - Real.arccos ((Matrix.trace (g0 : M2)).re / 2)
              * (Real.cos (Real.arccos ((Matrix.trace (g0 : M2)).re / 2))
                  * (-(1 / Real.sqrt (1 - ((Matrix.trace (g0 : M2)).re / 2) ^ 2)) * ((Matrix.trace G').re / 2))))
          / (Real.sin (Real.arccos ((Matrix.trace (g0 : M2)).re / 2))) ^ 2) / 2 : ℝ) : ℂ)
          • ((g0 : M2) - (g0 : M2)ᴴ)) t0 := by
  have h1 : (Matrix.trace (g0 : M2)).re / 2 ≠ 1 := (traceArg_ne_center g0 hne1 hne2).1
  have h2 : (Matrix.trace (g0 : M2)).re / 2 ≠ -1 := (traceArg_ne_center g0 hne1 hne2).2
  have hsin0 : Real.sin (Real.arccos ((Matrix.trace (g0 : M2)).re / 2)) ≠ 0 :=
    sin_su2Angle_ne_zero g0 hne1 hne2
  have hval' : (fun t => ((V t : SU2) : M2)) t0 = (g0 : M2) := by show ((V t0 : SU2) : M2) = (g0 : M2); rw [hval]
  have h := hasDerivAt_su2Log_curve t0 hG h1 h2 hval' hsin0
  have hFun : (fun t : ℝ => (((Real.arccos ((Matrix.trace ((V t : SU2) : M2)).re / 2)
            / Real.sin (Real.arccos ((Matrix.trace ((V t : SU2) : M2)).re / 2))) / 2 : ℝ) : ℂ)
          • (((V t : SU2) : M2) - ((V t : SU2) : M2)ᴴ))
      = fun t : ℝ => su2Log (V t) := by
    funext t; unfold su2Log su2Kappa su2Angle; congr 1; push_cast; ring
  rwa [hFun] at h

#print axioms hasDerivAt_su2Log_su2_curve

/-! ## §4 — `coarsePathHolonomy` differentiates at a GENUINELY NONIDENTITY background, along ANY
forward path — THE FINAL STRAIGHT-PATH FACTOR's ingredient

`coarsePathHolonomy ell V y p` is the PLAIN (no `groupConj`/adjoint-transport wrapping) recursive
product `V(y,μ₁)·V(shift(y,μ₁),μ₂)·…`. Perturbing `V := configMul (fun e => su2Exp(t•A e)) V0`
gives, AT `t=0`, `V(e) = V0(e)` — the ACTUAL background holonomy, not the identity — exactly
`coarseBondVar`'s straight-path instance (`p := List.replicate ell μ`) at CMP98 (15)'s own
`ell = 1` (single-block) scope. This is the genuinely new multi-factor Leibniz rule the raw
average's `U(c)` factor needs, and which `wrap`'s adjoint-transport-wrapped `dirDeriv` does not
supply (there every per-step factor collapses to `1` at `t=0`; here none of them do). -/

noncomputable def holonomyDirDeriv (V0 : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2) (ell : ℕ) :
    PeriodicLatticeSite L → List (Fin 3) → M2
  | _, [] => 0
  | y, μ :: rest =>
      A (y, μ) * (V0 (y, μ) : M2) * ((coarsePathHolonomy ell V0 (coarseShift y ell μ) rest : SU2) : M2)
        + (V0 (y, μ) : M2) * holonomyDirDeriv V0 A ell (coarseShift y ell μ) rest

/-- **PAID — the multi-factor Leibniz rule for `coarsePathHolonomy`, at a general nonidentity
background `V0`, threaded through an arbitrary LEFT multiplier `P` (so the induction closes).** -/
theorem hasDerivAt_coarsePathHolonomy_configMul_aux (V0 : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2) (hah : ∀ e, (A e)ᴴ = -(A e))
    (htr : ∀ e, Matrix.trace (A e) = 0) (ell : ℕ) :
    ∀ (p : List (Fin 3)) (y : PeriodicLatticeSite L) (P : ℝ → SU2) (D : M2),
      HasDerivAt (fun t : ℝ => ((P t : SU2) : M2)) D 0 →
      HasDerivAt
        (fun t : ℝ => ((P t * coarsePathHolonomy ell
              (configMul (fun e => su2Exp (t • A e)) V0) y p : SU2) : M2))
        (D * ((coarsePathHolonomy ell V0 y p : SU2) : M2)
          + ((P 0 : SU2) : M2) * holonomyDirDeriv V0 A ell y p) 0 := by
  intro p
  induction p with
  | nil =>
      intro y P D hPD
      simpa [coarsePathHolonomy, holonomyDirDeriv, coe_one] using hPD
  | cons μ rest ih =>
      intro y P D hPD
      have hstep : ∀ t : ℝ,
          (P t * coarsePathHolonomy ell (configMul (fun e => su2Exp (t • A e)) V0) y (μ :: rest) : SU2)
            = (P t * su2Exp (t • A (y, μ)) * V0 (y, μ))
                * coarsePathHolonomy ell (configMul (fun e => su2Exp (t • A e)) V0)
                    (coarseShift y ell μ) rest := by
        intro t
        show P t * ((configMul (fun e => su2Exp (t • A e)) V0) (y, μ)
              * coarsePathHolonomy ell (configMul (fun e => su2Exp (t • A e)) V0)
                  (coarseShift y ell μ) rest) = _
        show P t * (su2Exp (t • A (y, μ)) * V0 (y, μ)
              * coarsePathHolonomy ell (configMul (fun e => su2Exp (t • A e)) V0)
                  (coarseShift y ell μ) rest) = _
        group
      have hQ0 : (fun t : ℝ => P t * su2Exp (t • A (y, μ)) * V0 (y, μ)) 0 = P 0 * V0 (y, μ) := by
        simp
      have hQd : HasDerivAt
          (fun t : ℝ => ((P t * su2Exp (t • A (y, μ)) * V0 (y, μ) : SU2) : M2))
          (D * (V0 (y, μ) : M2) + ((P 0 : SU2) : M2) * A (y, μ) * (V0 (y, μ) : M2)) 0 := by
        have hcoe : ∀ t : ℝ, ((P t * su2Exp (t • A (y, μ)) : SU2) : M2) * (V0 (y, μ) : M2)
            = ((P t * su2Exp (t • A (y, μ)) * V0 (y, μ) : SU2) : M2) := by
          intro t; exact (coe_mul (P t * su2Exp (t • A (y, μ))) (V0 (y, μ))).symm
        have hmul := hPD.mul (hasDerivAt_su2Exp_coe_smul (hah (y, μ)) (htr (y, μ)))
        have hmul2 := hmul.mul_const (V0 (y, μ) : M2)
        simp only [zero_smul, su2Exp_zero, Submonoid.coe_one, mul_one, add_mul] at hmul2
        exact hmul2.congr_of_eventuallyEq (Filter.Eventually.of_forall hcoe)
      have hrest := ih (coarseShift y ell μ) (fun t => P t * su2Exp (t • A (y, μ)) * V0 (y, μ))
        (D * (V0 (y, μ) : M2) + ((P 0 : SU2) : M2) * A (y, μ) * (V0 (y, μ) : M2)) hQd
      simp only [su2Exp_zero, mul_one, zero_smul] at hrest
      rw [coe_mul] at hrest
      have hcombine : (D * (V0 (y, μ) : M2) + ((P 0 : SU2) : M2) * A (y, μ) * (V0 (y, μ) : M2))
            * ((coarsePathHolonomy ell V0 (coarseShift y ell μ) rest : SU2) : M2)
          + ((P 0 : SU2) : M2) * (V0 (y, μ) : M2) * holonomyDirDeriv V0 A ell (coarseShift y ell μ) rest
        = D * ((coarsePathHolonomy ell V0 y (μ :: rest) : SU2) : M2)
          + ((P 0 : SU2) : M2) * holonomyDirDeriv V0 A ell y (μ :: rest) := by
        show _ = D * ((V0 (y,μ) : M2) * ((coarsePathHolonomy ell V0 (coarseShift y ell μ) rest : SU2) : M2))
          + ((P 0 : SU2) : M2) * (A (y, μ) * (V0 (y, μ) : M2)
              * ((coarsePathHolonomy ell V0 (coarseShift y ell μ) rest : SU2) : M2)
            + (V0 (y, μ) : M2) * holonomyDirDeriv V0 A ell (coarseShift y ell μ) rest)
        noncomm_ring
      rw [hcombine] at hrest
      have hfun : ∀ t : ℝ,
          ((P t * coarsePathHolonomy ell (configMul (fun e => su2Exp (t • A e)) V0) y (μ :: rest) : SU2) : M2)
            = ((P t * su2Exp (t • A (y, μ)) * V0 (y, μ)
              * coarsePathHolonomy ell (configMul (fun e => su2Exp (t • A e)) V0)
                  (coarseShift y ell μ) rest : SU2) : M2) := by
        intro t; rw [hstep t]
      exact hrest.congr_of_eventuallyEq (Filter.Eventually.of_forall hfun)

#print axioms hasDerivAt_coarsePathHolonomy_configMul_aux

/-- **PAID — THE TARGETED DELIVERABLE: `coarseBondVar`, CMP98 (15)'s own `U(c)` — the FINAL
STRAIGHT-PATH FACTOR of the raw average — differentiates at a genuinely nonidentity background
`V0`.** At `t=0`, `configMul (fun e=>su2Exp(t•A e)) V0` equals `V0` (not the identity link
config): `coarseBondVar`'s value there is the ACTUAL background bond product, not `1`. -/
theorem hasDerivAt_coarseBondVar_configMul (V0 : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2) (hah : ∀ e, (A e)ᴴ = -(A e))
    (htr : ∀ e, Matrix.trace (A e) = 0) (s ell : ℕ) (c : PeriodicLatticeEdge L) :
    HasDerivAt
      (fun t : ℝ => ((coarseBondVar s ell (configMul (fun e => su2Exp (t • A e)) V0) c : SU2) : M2))
      (holonomyDirDeriv V0 A s c.1 (List.replicate ell c.2)) 0 := by
  have h := hasDerivAt_coarsePathHolonomy_configMul_aux V0 A hah htr s (List.replicate ell c.2) c.1
    (fun _ : ℝ => (1 : SU2)) 0 (hasDerivAt_const (0 : ℝ) (((1 : SU2) : M2)))
  simp only [Submonoid.coe_one, one_mul, zero_mul, zero_add] at h
  exact h

#print axioms hasDerivAt_coarseBondVar_configMul

end AdalySI1.RawAverageDeriv
