import DLR48

/-!
# DL49 -- the SMOOTH right inverse of the CURVED bond map at M0, and its scaled `G⁻¹`-energy (the competitor of `extN`)

* `Qdrift_M0` : `‖Q_U x − Q₁ x‖² ≤ φ_C²/n³ ‖x‖²` (`φ_C = phiC ℓ (3600ℓρ)`; MF7 `hC1_M0`, every index at level `k`).
* `Sop = Q_U ∘ Eop` : `‖Sop u − u‖ ≤ δ‖u‖`, `δ = (81/4)φ_C`, and `δ < 1` at M0 (`phi_sq_small`: `φ_C² < 1/1000`);
  hence `Sop` is coercive with constant `1 − δ` and invertible (`Sinv`).
* **`bondExtM0`** (DL50) : for the scaled genuine instance `I = ginvM0 ..` (DL42) and every `u`:
  `∃ g, I.Qb g = u ∧ ⟪g, I.Ginv g⟫ ≤ bNS ℓ a ρ δ ‖u‖²`, with the k-FREE
  `bNS = (cN + κS dN/cS)² + νS (gN + dN/√cS)² + dN² + 1`, `A0 = 1/((1−δ)√a)`, `gN = (81/4)A0`,
  `cN = (3888 + 243ρ)A0`, `dN = (1944 + (81√3/2)ρ)A0`.
  (`g = Eop(Sinv(u/√(a n³)))`; `Ginv_upper` (DL47) + smoothness `Eop_grad` (DL48) + `curl/div` bounds (DL46).)
-/
set_option autoImplicit false
set_option maxHeartbeats 128000000
set_option maxRecDepth 200000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU PlaqFnL2)
open AdalyFormal.SliceCoerc (coarseC Qtop GF)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.AsmM0 (M0RegimeR rhoM0 Mc KhatM0 phiC ThetaM0)
open AdalyFormal.BondComposite (rr TowerClass thetaOf bidx_level)

/-- the k-free constants of the competitor -/
noncomputable def A0S (a δ : ℝ) : ℝ := 1 / ((1 - δ) * Real.sqrt a)
noncomputable def gNS (a δ : ℝ) : ℝ := (81 / 4) * A0S a δ
noncomputable def cNS (a ρ δ : ℝ) : ℝ := (3888 + 243 * ρ) * A0S a δ
noncomputable def dNS (a ρ δ : ℝ) : ℝ := (1944 + (81 * Real.sqrt 3 / 2) * ρ) * A0S a δ
noncomputable def bNS (a ρ δ : ℝ) : ℝ :=
  (cNS a ρ δ + κS ρ * (dNS a ρ δ / cS a ρ)) ^ 2 + νS ρ * (gNS a δ + dNS a ρ δ / Real.sqrt (cS a ρ)) ^ 2
    + dNS a ρ δ ^ 2 + 1

/-- the drift parameter -/
noncomputable def δS (ell : ℕ) (ρ : ℝ) : ℝ := (81 / 4) * phiC ell (3600 * (ell : ℝ) * ρ)

section
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) (a t e q0 : ℝ)
  (R : M0RegimeR ell k Lu U a t e q0) (H : AdalyFormal.RegBgKU.KUSmall ell (rhoM0 ell k e q0))

include R in
theorem δS_nonneg : 0 ≤ δS ell (rhoM0 ell k e q0) := by
  unfold δS phiC
  have hρ := m0_rho_nonneg ell k Lu U a t e q0 R
  have hr : 0 < rr ell := Real.sqrt_pos.mpr (by have := R.hell; positivity)
  have : 0 ≤ 3600 * (ell : ℝ) * rhoM0 ell k e q0 := by positivity
  positivity

include R in
theorem δS_lt : δS ell (rhoM0 ell k e q0) < 1 := by
  have h := AdalyFormal.M0Finish.phi_sq_small ell a t (rhoM0 ell k e q0) R.ha R.ht (m0_rho_nonneg ell k Lu U a t e q0 R)
    R.hsmallU
  have h0 := δS_nonneg ell k Lu U a t e q0 R
  unfold δS at h0 ⊢
  have hφ0 : 0 ≤ phiC ell (3600 * (ell : ℝ) * rhoM0 ell k e q0) := by
    have := h0; nlinarith
  nlinarith

include R H in
/-- the bond drift in operator form -/
theorem Qdrift_M0 (x : BondFnL2 (scaleUp ell k Lu)) :
    ‖(bondSectorOf (GF ell k Lu) U).Qfull x - (bondSectorOf (GF ell k Lu) (trivialU _)).Qfull x‖ ^ 2
      ≤ phiC ell (3600 * (ell : ℝ) * rhoM0 ell k e q0) ^ 2 / ((ell : ℝ) ^ k) ^ 3 * ‖x‖ ^ 2 := by
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := by have := R.hell; positivity
  have ha := R.ha
  have h := AdalyFormal.M0Finish.hC1_M0 ell k Lu U a t e q0 R H x
  have hlev : ∀ p : BIdx (GF ell k Lu), a * ((GF ell k Lu).ell : ℝ) ^ (p.1 : ℕ) = a * (ell : ℝ) ^ k := by
    intro p
    have hk := bidx_level ell k Lu p
    show a * (ell : ℝ) ^ (p.1 : ℕ) = a * (ell : ℝ) ^ k
    rw [hk]
  simp only [hlev] at h
  rw [← Finset.mul_sum] at h
  have hsum : ‖(bondSectorOf (GF ell k Lu) U).Qfull x - (bondSectorOf (GF ell k Lu) (trivialU _)).Qfull x‖ ^ 2
      = ∑ p : BIdx (GF ell k Lu), ‖(bondSectorOf (GF ell k Lu) (trivialU _)).Qfull x p
          - (bondSectorOf (GF ell k Lu) U).Qfull x p‖ ^ 2 := by
    rw [norm_sub_rev, PiLp.norm_sq_eq_of_L2]; rfl
  rw [hsum]
  have e1 : (Real.sqrt a * phiC ell (3600 * (ell : ℝ) * rhoM0 ell k e q0) / (ell : ℝ) ^ k) ^ 2
      = a * phiC ell (3600 * (ell : ℝ) * rhoM0 ell k e q0) ^ 2 / ((ell : ℝ) ^ k) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt ha.le]
  rw [e1] at h
  have han : 0 < a * (ell : ℝ) ^ k := by positivity
  set S := ∑ p : BIdx (GF ell k Lu), ‖(bondSectorOf (GF ell k Lu) (trivialU _)).Qfull x p
          - (bondSectorOf (GF ell k Lu) U).Qfull x p‖ ^ 2 with hS
  have key : S ≤ (a * phiC ell (3600 * (ell : ℝ) * rhoM0 ell k e q0) ^ 2 / ((ell : ℝ) ^ k) ^ 2 * ‖x‖ ^ 2)
      / (a * (ell : ℝ) ^ k) := by
    rw [le_div_iff₀ han]; linarith [h]
  refine key.trans (le_of_eq ?_)
  field_simp

/-- `S = Q_U ∘ Eop` -/
noncomputable def Sop : FSp (GF ell k Lu) →L[ℝ] FSp (GF ell k Lu) :=
  (bondSectorOf (GF ell k Lu) U).Qfull ∘L Eop ell k Lu (by have := R.hell; omega)

include H in
theorem Sop_near (u : FSp (GF ell k Lu)) :
    ‖Sop ell k Lu U a t e q0 R u - u‖ ≤ δS ell (rhoM0 ell k e q0) * ‖u‖ := by
  have hell0 : 0 < ell := by have := R.hell; omega
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := by positivity
  set x := Eop ell k Lu hell0 u with hx
  have e1 : Sop ell k Lu U a t e q0 R u - u
      = (bondSectorOf (GF ell k Lu) U).Qfull x - (bondSectorOf (GF ell k Lu) (trivialU _)).Qfull x := by
    rw [Eop_rightInv ell k Lu hell0 u]; rfl
  rw [e1]
  have h1 := Qdrift_M0 ell k Lu U a t e q0 R H x
  have h2 := Eop_norm_sq ell k Lu hell0 u
  have hφ0 : 0 ≤ phiC ell (3600 * (ell : ℝ) * rhoM0 ell k e q0) := by
    have := δS_nonneg ell k Lu U a t e q0 R; unfold δS at this; linarith
  have h3 : ‖(bondSectorOf (GF ell k Lu) U).Qfull x - (bondSectorOf (GF ell k Lu) (trivialU _)).Qfull x‖ ^ 2
      ≤ (δS ell (rhoM0 ell k e q0) * ‖u‖) ^ 2 := by
    refine h1.trans ?_
    unfold δS
    have h4 : phiC ell (3600 * (ell : ℝ) * rhoM0 ell k e q0) ^ 2 / ((ell : ℝ) ^ k) ^ 3 * ‖x‖ ^ 2
        ≤ phiC ell (3600 * (ell : ℝ) * rhoM0 ell k e q0) ^ 2 / ((ell : ℝ) ^ k) ^ 3
          * ((81 / 4) ^ 2 * ((ell : ℝ) ^ k) ^ 3 * ‖u‖ ^ 2) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    refine h4.trans (le_of_eq ?_)
    field_simp
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by have := δS_nonneg ell k Lu U a t e q0 R; positivity)
    two_ne_zero).mp h3

include H in
theorem Sop_coer (u : FSp (GF ell k Lu)) :
    (1 - δS ell (rhoM0 ell k e q0)) * ‖u‖ ^ 2 ≤ ⟪u, Sop ell k Lu U a t e q0 R u⟫ := by
  have h := Sop_near ell k Lu U a t e q0 R H u
  have e1 : ⟪u, Sop ell k Lu U a t e q0 R u⟫ = ‖u‖ ^ 2 + ⟪u, Sop ell k Lu U a t e q0 R u - u⟫ := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq]; ring
  have h2 : -(‖u‖ * ‖Sop ell k Lu U a t e q0 R u - u‖) ≤ ⟪u, Sop ell k Lu U a t e q0 R u - u⟫ := by
    have := abs_real_inner_le_norm u (Sop ell k Lu U a t e q0 R u - u)
    linarith [neg_abs_le ⟪u, Sop ell k Lu U a t e q0 R u - u⟫]
  have h3 : ‖u‖ * ‖Sop ell k Lu U a t e q0 R u - u‖ ≤ ‖u‖ * (δS ell (rhoM0 ell k e q0) * ‖u‖) :=
    mul_le_mul_of_nonneg_left h (norm_nonneg _)
  rw [e1]; nlinarith

end

#print axioms δS_nonneg
#print axioms δS_lt
#print axioms Qdrift_M0
#print axioms Sop_near
#print axioms Sop_coer

end AdalyFormal.DLayer
