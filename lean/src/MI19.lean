import MI18

/-!
# MI19 -- the curvature sandwich (M1 lane E, 2026-10-13)

For a bond field `B`, `λ_B = G'(T B)`:
`F(B) = ‖χ_P C(B − Dm λ_B)‖² + Δ'(B − Dm λ_B) + ‖TB‖² + ‖√w Q B‖²` (`Fform`; `= ⟪A, Ginv A⟫` for `B = ιA`, MI18 `ginv_form`),
`G0(B) = ‖χ_P C B‖² + ‖TB‖² + ‖√w Q B‖²` (`G0form`), `N(B) = ‖e^{−σ} B‖²`.
* `sandwich` : `(1−η) G0 − 2ν N ≤ F ≤ (1+η) G0 + 2ν N`, `η = ε₁ + (1+1/ε₁) κ₂ + 2ν g5²`, `κ₂ = 12 ρ² ℓ⁸ (4ℓ/cs)²`,
  `ν = (17/√2)·12 ρ ℓ⁴`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.M1IMS

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer
open AdalyFormal.M1Site
open AdalyFormal.StatementLane (Tower Admissible bigSide scaleUp)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap BondFnL2 curlValueCovariant)
open AdalyFormal.Balaban.CovariantHjMinimizer (PlaqFnL2)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.StatementLaneR6 (plaqMask plaqMask_apply deltaPrimeBilL2NormLoc)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantLM_L2)

variable {L : PeriodicLatticeExtent}

section sand
variable {Lf : PeriodicLatticeExtent} {ell M R k : ℕ} {S : Tower Lf}
  (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hR1 : 1 ≤ R) (hM1 : 1 ≤ M) {W : ℕ} (hW : 1 ≤ W)
  (hWR : W ≤ R * M * ell)
include hS hell hR1 hM1 hW hWR

/-- the curvature-coupled form `F`. -/
noncomputable def Fform (S : Tower Lf) (ell k : ℕ) (U : Cfg Lf) (a : ℝ) (B : BondFnL2 Lf) : ℝ :=
  ‖plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U (B - Dm (geomOf ell k S) U
      (Gp (geomOf ell k S) U a (Tfull (geomOf ell k S) U B))))‖ ^ 2
    + deltaPrimeBilL2NormLoc U (plaqIn (S.Om 0))
        (B - Dm (geomOf ell k S) U (Gp (geomOf ell k S) U a (Tfull (geomOf ell k S) U B)))
        (B - Dm (geomOf ell k S) U (Gp (geomOf ell k S) U a (Tfull (geomOf ell k S) U B)))
    + ‖Tfull (geomOf ell k S) U B‖ ^ 2 + ‖Ymass (geomOf ell k S) U a B‖ ^ 2

/-- the decoupled form `G0`. -/
noncomputable def G0form (S : Tower Lf) (ell k : ℕ) (U : Cfg Lf) (a : ℝ) (B : BondFnL2 Lf) : ℝ :=
  ‖plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U B)‖ ^ 2 + ‖Tfull (geomOf ell k S) U B‖ ^ 2
    + ‖Ymass (geomOf ell k S) U a B‖ ^ 2

/-- **the curvature sandwich**. -/
theorem sandwich (U : Cfg Lf) (a cs : ℝ) (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hreg : HolRegime S ell k U ρ) (ε1 : ℝ) (hε1 : 0 < ε1) (B : BondFnL2 Lf) :
    (1 - (ε1 + (1 + 1 / ε1) * (12 * ρ ^ 2 * (ell : ℝ) ^ 8 * (4 * ell / cs) ^ 2)
        + 2 * ((17 / Real.sqrt 2) * 12 * (ρ * (ell : ℝ) ^ 4)) *
          ((ell : ℝ) * (Real.sqrt (12 / cs) + Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1) * (4 / cs))) ^ 2))
        * G0form S ell k U a B
      - 2 * ((17 / Real.sqrt 2) * 12 * (ρ * (ell : ℝ) ^ 4)) * ‖bondWt (-sigG (geomOf ell k S)) B‖ ^ 2
      ≤ Fform S ell k U a B ∧
    Fform S ell k U a B
      ≤ (1 + (ε1 + (1 + 1 / ε1) * (12 * ρ ^ 2 * (ell : ℝ) ^ 8 * (4 * ell / cs) ^ 2)
        + 2 * ((17 / Real.sqrt 2) * 12 * (ρ * (ell : ℝ) ^ 4)) *
          ((ell : ℝ) * (Real.sqrt (12 / cs) + Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1) * (4 / cs))) ^ 2))
        * G0form S ell k U a B
      + 2 * ((17 / Real.sqrt 2) * 12 * (ρ * (ell : ℝ) ^ 4)) * ‖bondWt (-sigG (geomOf ell k S)) B‖ ^ 2 := by
  set G := geomOf ell k S
  set ν := (17 / Real.sqrt 2) * 12 * (ρ * (ell : ℝ) ^ 4)
  set g5c := (ell : ℝ) * (Real.sqrt (12 / cs) + Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1) * (4 / cs))
  set κ2 := 12 * ρ ^ 2 * (ell : ℝ) ^ 8 * (4 * ell / cs) ^ 2
  set lam := Gp G U a (Tfull G U B)
  set x := plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U B)
  set y := plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U (Dm G U lam))
  set TT := ‖Tfull G U B‖ ^ 2
  set MM := ‖Ymass G U a B‖ ^ 2
  set NN := ‖bondWt (-sigG G) B‖ ^ 2
  have hcs := hp.hcs
  have hν0 : 0 ≤ ν := by have : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num); positivity
  have hg50 : 0 ≤ g5c := by
    have := dD_nonneg hS hW hell hR1 hM1 hWR; positivity
  have hκ0 : 0 ≤ κ2 := by positivity
  have hTT : 0 ≤ TT := sq_nonneg _
  have hMM : 0 ≤ MM := sq_nonneg _
  have hNN : 0 ≤ NN := sq_nonneg _
  -- the curvature coupling
  have hxy : plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U (B - Dm G U lam)) = x - y := by
    rw [map_sub, map_sub]
  have hy : ‖y‖ ^ 2 ≤ κ2 * TT := by
    have h1 := curv_strat hS hell hR1 hM1 U ρ hρ hreg lam
    have h2 := g1' hS hW hell hR1 hM1 hWR U a cs hp (siteMask G.Om0 (Tfull G U B))
    have h3 := siteMask_norm_le G.Om0 (Tfull G U B)
    have hlam : lam = LinvP G U a (siteMask G.Om0 (Tfull G U B)) := rfl
    rw [← hlam] at h2
    have h4 : ‖siteWt (-(sigG G + sigG G)) lam‖ ≤ (4 * ell / cs) * ‖Tfull G U B‖ :=
      h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
    have h5 := pow_le_pow_left₀ (norm_nonneg _) h4 2
    rw [mul_pow] at h5
    calc ‖y‖ ^ 2 ≤ 12 * ρ ^ 2 * (ell : ℝ) ^ 8 * ‖siteWt (-(sigG G + sigG G)) lam‖ ^ 2 := h1
      _ ≤ 12 * ρ ^ 2 * (ell : ℝ) ^ 8 * ((4 * ell / cs) ^ 2 * ‖Tfull G U B‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = κ2 * TT := by ring
  -- the Δ' coupling
  have hD : |deltaPrimeBilL2NormLoc U (plaqIn (S.Om 0)) (B - Dm G U lam) (B - Dm G U lam)| ≤ ν * (2 * NN + 2 * g5c ^ 2 * TT) := by
    have h1 := deltaPrime_strat hS hell hR1 hM1 U ρ hρ hreg (B - Dm G U lam)
    have h2 : ‖bondWt (-sigG G) (B - Dm G U lam)‖ ≤ ‖bondWt (-sigG G) B‖ + g5c * ‖Tfull G U B‖ := by
      rw [map_sub]
      refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
      have := g5 hS hW hell hR1 hM1 hWR U a cs hp (siteMask G.Om0 (Tfull G U B))
      exact this.trans (mul_le_mul_of_nonneg_left (siteMask_norm_le _ _) hg50)
    have h3 : ‖bondWt (-sigG G) (B - Dm G U lam)‖ ^ 2 ≤ 2 * NN + 2 * g5c ^ 2 * TT := by
      have h0 := norm_nonneg (bondWt (-sigG G) (B - Dm G U lam))
      have h4 := pow_le_pow_left₀ h0 h2 2
      nlinarith [sq_nonneg (‖bondWt (-sigG G) B‖ - g5c * ‖Tfull G U B‖), norm_nonneg (bondWt (-sigG G) B),
        norm_nonneg (Tfull G U B)]
    exact h1.trans (mul_le_mul_of_nonneg_left h3 hν0)
  have hD' := abs_le.mp hD
  obtain ⟨hup, hlow⟩ := norm_sub_sq_bounds x y ε1 hε1
  have hFdef : Fform S ell k U a B = ‖x - y‖ ^ 2
      + deltaPrimeBilL2NormLoc U (plaqIn (S.Om 0)) (B - Dm G U lam) (B - Dm G U lam) + TT + MM := by
    unfold Fform; rw [hxy]
  have hG0 : G0form S ell k U a B = ‖x‖ ^ 2 + TT + MM := rfl
  rw [hFdef, hG0]
  have hx0 := sq_nonneg ‖x‖
  have hyy : (1 + 1 / ε1) * ‖y‖ ^ 2 ≤ (1 + 1 / ε1) * (κ2 * TT) := mul_le_mul_of_nonneg_left hy (by positivity)
  have hyy' : (1 / ε1) * ‖y‖ ^ 2 ≤ (1 + 1 / ε1) * (κ2 * TT) := by
    have : (1 / ε1) * ‖y‖ ^ 2 ≤ (1 + 1 / ε1) * ‖y‖ ^ 2 := by nlinarith [sq_nonneg ‖y‖]
    linarith
  have hε1' : 0 ≤ 1 / ε1 := by positivity
  have hA0 : 0 ≤ (1 + 1 / ε1) * κ2 := mul_nonneg (by linarith) hκ0
  have hB0 : 0 ≤ ν * g5c ^ 2 := mul_nonneg hν0 (sq_nonneg _)
  have p1 := mul_nonneg hA0 hx0
  have p2 := mul_nonneg hB0 hx0
  have p3 := mul_nonneg hε1.le hTT
  have p4 := mul_nonneg hε1.le hMM
  have p5 := mul_nonneg hA0 hMM
  have p6 := mul_nonneg hB0 hMM
  have p7 := mul_nonneg hε1.le hx0
  have p8 := mul_nonneg hA0 hTT
  have p9 := mul_nonneg hB0 hTT
  have hDl := hD'.1
  have hDu := hD'.2
  constructor
  · nlinarith
  · nlinarith

end sand

end AdalyFormal.M1IMS

#print axioms AdalyFormal.M1IMS.sandwich
#print axioms AdalyFormal.M1IMS.Fform
#print axioms AdalyFormal.M1IMS.G0form
