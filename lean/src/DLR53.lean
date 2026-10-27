import DLR52

/-!
# DL53 -- **`hHcol_M0`: the ℓ¹ columns of the genuine `H` are `≤ C_H n³`, C_H k- and volume-free** (premise `hHcol` of DL5)

* `NopM0_eq` : `N' = (s²/n²) N_f` (`s = √(a n³)`); `Nf_isUnit`; **`dataH_scaled`** : `ι(data.H w) = s · H'w` (`H'` = `(nM0 ..).H`).
* `phiP θ' z x = θ' Σ_μ cycd(x_μ − z_μ)` : `phiP_lip` (one fine step changes it by `≤ θ'`), `phiP_self` (`= 0` at `z`),
  `phiP_sum` (`Σ_x e^{−2 phiP} ≤ (2/(1−e^{−2θ'}))³`), `geom_le` (`2/(1−e^{−2θ/n}) ≤ n(1/θ + 2)`).
* **`hHcol_M0`** : `Σ_b ‖ι(data.H δ_{p,v})(b)‖ ≤ CHfree · n³ · ‖v‖`,
  `CHfree = √3·√a·(1/θ+2)^{3/2} · 2K̂(qBS + δBS)/(1/bNS − ENfree)` — a function of `(ℓ, a, t, ρ, θ)` only.
-/
set_option autoImplicit false
set_option maxHeartbeats 128000000
set_option maxRecDepth 200000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU PlaqFnL2)
open AdalyFormal.SliceCoerc (coarseC Qtop GF)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.AsmM0 (M0RegimeR rhoM0 Mc KhatM0 phiC ThetaM0)
open AdalyFormal.BondComposite (rr TowerClass thetaOf)
open AdalyFormal.M0Finish (PU)

/-! ## the distance weight -/

theorem cycd_step {N : ℕ} [NeZero N] (d : Fin N) : |((cycd (d + 1) : ℕ) : ℝ) - ((cycd d : ℕ) : ℝ)| ≤ 1 := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hv : (d + 1).val = (d.val + 1) % N := by
    rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  unfold cycd
  rw [hv]
  have hd := d.isLt
  by_cases h : d.val + 1 < N
  · rw [Nat.mod_eq_of_lt h]
    rw [abs_le]
    constructor
    · have : (min d.val (N - d.val) : ℕ) ≤ min (d.val + 1) (N - (d.val + 1)) + 1 := by omega
      have h2 : ((min d.val (N - d.val) : ℕ) : ℝ) ≤ ((min (d.val + 1) (N - (d.val + 1)) : ℕ) : ℝ) + 1 := by
        exact_mod_cast this
      linarith
    · have : (min (d.val + 1) (N - (d.val + 1)) : ℕ) ≤ min d.val (N - d.val) + 1 := by omega
      have h2 : ((min (d.val + 1) (N - (d.val + 1)) : ℕ) : ℝ) ≤ ((min d.val (N - d.val) : ℕ) : ℝ) + 1 := by
        exact_mod_cast this
      linarith
  · have hdN : d.val + 1 = N := by omega
    rw [hdN, Nat.mod_self]
    have e1 : min 0 (N - 0) = 0 := by simp
    have e2 : min d.val (N - d.val) ≤ 1 := by omega
    rw [e1]
    have h3 : ((min d.val (N - d.val) : ℕ) : ℝ) ≤ 1 := by exact_mod_cast e2
    have h4 : (0 : ℝ) ≤ ((min d.val (N - d.val) : ℕ) : ℝ) := by positivity
    rw [Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg h4]
    exact h3

variable {L : PeriodicLatticeExtent}

/-- the distance weight centred at `z` -/
noncomputable def phiP (θ' : ℝ) (z x : PeriodicLatticeSite L) : ℝ := θ' * ∑ μ : Fin 3, ((cycd (x μ - z μ) : ℕ) : ℝ)

theorem phiP_self (θ' : ℝ) (z : PeriodicLatticeSite L) : phiP θ' z z = 0 := by
  unfold phiP; simp [cycd]

theorem phiP_lip (θ' : ℝ) (hθ : 0 ≤ θ') (z : PeriodicLatticeSite L) : WtLip θ' (phiP θ' z) := by
  intro x ν
  unfold phiP
  rw [← mul_sub, ← Finset.sum_sub_distrib, Fintype.sum_eq_single ν]
  · rw [abs_mul, abs_of_nonneg hθ]
    have e : (periodicLatticeShift x ν) ν - z ν = (x ν - z ν) + 1 := by
      unfold periodicLatticeShift; rw [Function.update_self]; abel
    rw [e]
    have := cycd_step (x ν - z ν)
    nlinarith [abs_nonneg ((((cycd (x ν - z ν + 1)) : ℕ) : ℝ) - ((cycd (x ν - z ν) : ℕ) : ℝ))]
  · intro μ hμ
    have e : (periodicLatticeShift x ν) μ = x μ := by
      unfold periodicLatticeShift; rw [Function.update_of_ne hμ]
    rw [e, sub_self]

theorem phiP_sum (θ' : ℝ) (hθ : 0 < θ') (z : PeriodicLatticeSite L) :
    ∑ x : PeriodicLatticeSite L, Real.exp (-(2 * phiP θ' z x)) ≤ (2 / (1 - Real.exp (-(2 * θ')))) ^ 3 := by
  have h1 : ∀ x : PeriodicLatticeSite L, Real.exp (-(2 * phiP θ' z x))
      = ∏ μ : Fin 3, Real.exp (-((2 * θ') * ((cycd (x μ - z μ) : ℕ) : ℝ))) := by
    intro x
    rw [← Real.exp_sum]
    congr 1
    unfold phiP
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    ring
  simp only [h1]
  · have h2 : ∀ μ : Fin 3, ∑ t : Fin (L μ + 1), Real.exp (-((2 * θ') * ((cycd (t - z μ) : ℕ) : ℝ)))
        ≤ 2 / (1 - Real.exp (-(2 * θ'))) := by
      intro μ
      have e : ∑ t : Fin (L μ + 1), Real.exp (-((2 * θ') * ((cycd (t - z μ) : ℕ) : ℝ)))
          = ∑ t : Fin (L μ + 1), Real.exp (-((2 * θ') * ((cycd t : ℕ) : ℝ))) :=
        Fintype.sum_equiv (Equiv.subRight (z μ)) _ _ (fun t => rfl)
      rw [e]
      exact cyc_geom_sum (L μ + 1) (2 * θ') (by positivity)
    rw [show ∑ x : PeriodicLatticeSite L, ∏ μ : Fin 3, Real.exp (-((2 * θ') * ((cycd (x μ - z μ) : ℕ) : ℝ)))
        = ∏ μ : Fin 3, ∑ t : Fin (L μ + 1), Real.exp (-((2 * θ') * ((cycd (t - z μ) : ℕ) : ℝ))) by
      rw [Finset.prod_univ_sum, Fintype.piFinset_univ]]
    calc ∏ μ : Fin 3, ∑ t : Fin (L μ + 1), Real.exp (-((2 * θ') * ((cycd (t - z μ) : ℕ) : ℝ)))
        ≤ ∏ _μ : Fin 3, 2 / (1 - Real.exp (-(2 * θ'))) :=
          Finset.prod_le_prod (fun μ _ => Finset.sum_nonneg (fun t _ => (Real.exp_pos _).le)) (fun μ _ => h2 μ)
      _ = (2 / (1 - Real.exp (-(2 * θ')))) ^ 3 := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem geom_le (n θ : ℝ) (hn : 1 ≤ n) (hθ : 0 < θ) :
    2 / (1 - Real.exp (-(2 * (θ / n)))) ≤ n * (1 / θ + 2) := by
  have hn0 : 0 < n := by linarith
  set x := 2 * (θ / n) with hx
  have hx0 : 0 < x := by positivity
  have h1 : Real.exp (-x) * (1 + x) ≤ 1 := by
    have := Real.add_one_le_exp x
    have h2 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-x)]
  have h3 : x / (1 + x) ≤ 1 - Real.exp (-x) := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have h4 : 0 < x / (1 + x) := by positivity
  calc 2 / (1 - Real.exp (-x)) ≤ 2 / (x / (1 + x)) := div_le_div_of_nonneg_left (by norm_num) h4 h3
    _ = n / θ + 2 := by rw [hx]; field_simp
    _ ≤ n * (1 / θ + 2) := by
        have : 2 ≤ 2 * n := by linarith
        rw [mul_add, mul_one_div]; linarith

/-! ## the genuine `H` and the scaled one -/

section
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) (a t e q0 : ℝ)
  (R : M0RegimeR ell k Lu U a t e q0) (H : AdalyFormal.RegBgKU.KUSmall ell (rhoM0 ell k e q0))
  (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (θ : ℝ)
  (hφ : WtLip (θ / (ell : ℝ) ^ k) φ) (hc : CondM0 ell a (rhoM0 ell k e q0) θ)
include R H hφ hc

theorem NopM0_eq (u : FSp (GF ell k Lu)) :
    NopM0 ell k Lu U a t e q0 R H φ θ hφ hc u
      = (Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3) ^ 2 / ((ell : ℝ) ^ k) ^ 2) • Nf ell k Lu U a u := by
  show (Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3) • (bondSectorOf (GF ell k Lu) U).Qfull)
      (GiM0 ell k Lu U a (ContinuousLinearMap.adjoint
        (Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3) • (bondSectorOf (GF ell k Lu) U).Qfull) u)) = _
  rw [adjoint_smul_real]
  simp only [GiM0, Nf, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, map_smul, smul_smul]
  congr 1
  ring

theorem Nf_coer (u : FSp (GF ell k Lu)) :
    ((((ell : ℝ) ^ k) ^ 2 / Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3) ^ 2) * (1 / bNS a (rhoM0 ell k e q0) (δS ell (rhoM0 ell k e q0))))
      * ‖u‖ ^ 2 ≤ ⟪u, Nf ell k Lu U a u⟫ := by
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := by have := R.hell; positivity
  have hs : 0 < Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3) := Real.sqrt_pos.mpr (by have := R.ha; positivity)
  have h := NopM0_coer ell k Lu U a t e q0 R H φ θ hφ hc u
  rw [NopM0_eq, real_inner_smul_right] at h
  have hc2 : 0 < Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3) ^ 2 / ((ell : ℝ) ^ k) ^ 2 := by positivity
  have e1 : (((ell : ℝ) ^ k) ^ 2 / Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3) ^ 2)
      = (Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3) ^ 2 / ((ell : ℝ) ^ k) ^ 2)⁻¹ := by rw [inv_div]
  rw [e1, mul_assoc, inv_mul_le_iff₀ hc2]
  linarith

theorem Nf_isUnit : IsUnit (Nf ell k Lu U a) := by
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := by have := R.hell; positivity
  have hs : 0 < Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3) := Real.sqrt_pos.mpr (by have := R.ha; positivity)
  have hb := bNS_pos a (rhoM0 ell k e q0) (δS ell (rhoM0 ell k e q0)) hc.νS_nonneg
  exact coercive_isUnit _ (by positivity) (Nf_coer ell k Lu U a t e q0 R H φ θ hφ hc)

/-- **the genuine `H` is `√(a n³)` times the scaled one** -/
theorem dataH_scaled (hEG : 4 * EGM0 ell a (rhoM0 ell k e q0) θ hc ≤ 1 / KhatM0 ell a t (rhoM0 ell k e q0))
    (Lam : Set (PeriodicLatticeSite Lu)) (w : FSp (GF ell k Lu)) :
    iE (GF ell k Lu) ((PU ell k Lu (by have := R.hell; omega) U a Lam).data.H w)
      = Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3) • (nM0 ell k Lu U a t e q0 R H φ θ hφ hc hEG).H w := by
  have hell0 : 0 < ell := by have := R.hell; omega
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := by positivity
  set s := Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3) with hsdef
  have hs : 0 < s := Real.sqrt_pos.mpr (by have := R.ha; positivity)
  have hu := GinvFull_isUnit ell k Lu U a t e q0 R H
  have hNu := Nf_isUnit ell k Lu U a t e q0 R H φ θ hφ hc
  set c := s ^ 2 / ((ell : ℝ) ^ k) ^ 2 with hcdef
  have hc0 : 0 < c := by positivity
  have hNop : NopM0 ell k Lu U a t e q0 R H φ θ hφ hc = c • Nf ell k Lu U a := by
    ext1 u; rw [NopM0_eq]; rfl
  have hinv : Ring.inverse (NopM0 ell k Lu U a t e q0 R H φ θ hφ hc) = c⁻¹ • Ring.inverse (Nf ell k Lu U a) := by
    rw [hNop]
    apply ring_inverse_eq_of
    · ext1 u
      have h1 : Nf ell k Lu U a (Ring.inverse (Nf ell k Lu U a) u) = u := by
        rw [← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel _ hNu, ContinuousLinearMap.one_apply]
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, map_smul, smul_smul, h1,
        ContinuousLinearMap.one_apply]
      simp [hc0.ne']
    · ext1 u
      have h1 : Ring.inverse (Nf ell k Lu U a) (Nf ell k Lu U a u) = u := by
        rw [← ContinuousLinearMap.mul_apply, Ring.inverse_mul_cancel _ hNu, ContinuousLinearMap.one_apply]
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, map_smul, smul_smul, h1,
        ContinuousLinearMap.one_apply]
      simp [hc0.ne']
  rw [dataH_eq ell k Lu hell0 U a Lam hu w]
  show _ = s • (GiM0 ell k Lu U a (ContinuousLinearMap.adjoint (s • (bondSectorOf (GF ell k Lu) U).Qfull)
      (Ring.inverse (NopM0 ell k Lu U a t e q0 R H φ θ hφ hc) w)))
  rw [hinv, adjoint_smul_real]
  simp only [GiM0, ContinuousLinearMap.smul_apply, map_smul, smul_smul]
  symm
  convert one_smul ℝ _ using 2
  rw [hcdef]; field_simp

end

/-- the k-free column constant -/
noncomputable def CHfree (ell : ℕ) (a t ρ θ : ℝ) (hc : CondM0 ell a ρ θ) (hK : 0 < KhatM0 ell a t ρ)
    (hEG : 4 * EGM0 ell a ρ θ hc ≤ 1 / KhatM0 ell a t ρ) : ℝ :=
  Real.sqrt 3 * Real.sqrt a * ((1 / θ + 2) * Real.sqrt (1 / θ + 2))
    * ((2 * KhatM0 ell a t ρ) * (qBS ell a ρ + δBS ell a ρ θ) / (1 / bNS a ρ (δS ell ρ) - ENfree ell a t ρ θ hc hK hEG))

section
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) (a t e q0 : ℝ)
  (R : M0RegimeR ell k Lu U a t e q0) (H : AdalyFormal.RegBgKU.KUSmall ell (rhoM0 ell k e q0))
include R H

/-- **`hHcol` at M0, with a k- and volume-free constant** -/
theorem hHcol_M0 (θ : ℝ) (hθ : 0 < θ) (hc : CondM0 ell a (rhoM0 ell k e q0) θ)
    (hEG : 4 * EGM0 ell a (rhoM0 ell k e q0) θ hc ≤ 1 / KhatM0 ell a t (rhoM0 ell k e q0))
    (hN : ENfree ell a t (rhoM0 ell k e q0) θ hc (KhatM0_pos ell k Lu U a t e q0 R) hEG
      < 1 / bNS a (rhoM0 ell k e q0) (δS ell (rhoM0 ell k e q0)))
    (Lam : Set (PeriodicLatticeSite Lu)) (p : BIdx (GF ell k Lu)) (v : SuTwo) :
    ∑ b, ‖(iE (GF ell k Lu) ((PU ell k Lu (by have := R.hell; omega) U a Lam).data.H
        (WithLp.toLp 2 (Pi.single p v) : FSp (GF ell k Lu)))) b‖
      ≤ CHfree ell a t (rhoM0 ell k e q0) θ hc (KhatM0_pos ell k Lu U a t e q0 R) hEG * ((ell : ℝ) ^ k) ^ 3 * ‖v‖ := by
  have hell0 : 0 < ell := by have := R.hell; omega
  have hn1 : (1 : ℝ) ≤ (ell : ℝ) ^ k := m0_n_ge_one ell k Lu U a t e q0 R
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := by linarith
  set n := (ell : ℝ) ^ k with hndef
  set z := p.2.1.1 with hz
  set ψ := phiP (θ / n) z with hψ
  have hψl : WtLip (θ / n) ψ := phiP_lip (θ / n) (by positivity) z
  set J := nM0 ell k Lu U a t e q0 R H ψ θ hψl hc hEG with hJ
  set δv : FSp (GF ell k Lu) := WithLp.toLp 2 (Pi.single p v) with hδv
  set CH := (2 * KhatM0 ell a t (rhoM0 ell k e q0)) * (qBS ell a (rhoM0 ell k e q0) + δBS ell a (rhoM0 ell k e q0) θ)
    / (1 / bNS a (rhoM0 ell k e q0) (δS ell (rhoM0 ell k e q0))
        - ENfree ell a t (rhoM0 ell k e q0) θ hc (KhatM0_pos ell k Lu U a t e q0 R) hEG) with hCH
  have hK := KhatM0_pos ell k Lu U a t e q0 R
  have hCH0 : 0 ≤ CH := by
    rw [hCH]
    have : 0 ≤ qBS ell a (rhoM0 ell k e q0) := by unfold qBS; positivity
    have := hc.δBS_nonneg
    have : 0 < 1 / bNS a (rhoM0 ell k e q0) (δS ell (rhoM0 ell k e q0))
        - ENfree ell a t (rhoM0 ell k e q0) θ hc (KhatM0_pos ell k Lu U a t e q0 R) hEG := by linarith
    positivity
  -- the weighted bound at the column
  have hW := H_CT_M0 ell k Lu U a t e q0 R H ψ θ hψl hc hEG hN δv
  have hδn : ‖δv‖ = ‖v‖ := by
    rw [hδv, PiLp.norm_toLp_single]
  have hfix : (fspWP ell k Lu ψ).wi δv = δv := by
    refine PiLp.ext (fun q => ?_)
    show Real.exp (-ψ q.2.1.1) • (δv q) = δv q
    by_cases hq : q = p
    · subst hq; rw [hψ, phiP_self]; simp
    · have : δv q = 0 := by rw [hδv]; simp [Pi.single_apply, hq]
      rw [this, smul_zero]
  have hcj : cjp (fspWP ell k Lu ψ) (bondWP ψ) J.H δv = bondWt ψ (J.H δv) := by
    rw [cjp_apply, hfix]; rfl
  rw [hcj, hδn] at hW
  -- ℓ¹ from the weighted ℓ²
  set X := J.H δv with hX
  have hsum : ∑ b, ‖X b‖ ≤ Real.sqrt (∑ b : Bond (scaleUp ell k Lu), (Real.exp (ψ b.1))⁻¹ ^ 2)
      * Real.sqrt (∑ b : Bond (scaleUp ell k Lu), (Real.exp (ψ b.1) * ‖X b‖) ^ 2) :=
    sum_le_weighted Finset.univ (fun b => ‖X b‖) (fun b => Real.exp (ψ b.1)) (fun b _ => Real.exp_pos _)
  have hS2 : ∑ b : Bond (scaleUp ell k Lu), (Real.exp (ψ b.1) * ‖X b‖) ^ 2 = ‖bondWt ψ X‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    show (Real.exp (ψ b.1) * ‖X b‖) ^ 2 = ‖Real.exp (ψ b.1) • X b‖ ^ 2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hS1 : ∑ b : Bond (scaleUp ell k Lu), (Real.exp (ψ b.1))⁻¹ ^ 2 ≤ 3 * (n * (1 / θ + 2)) ^ 3 := by
    have e1 : ∑ b : Bond (scaleUp ell k Lu), (Real.exp (ψ b.1))⁻¹ ^ 2
        = 3 * ∑ x : PeriodicLatticeSite (scaleUp ell k Lu), Real.exp (-(2 * ψ x)) := by
      rw [show (∑ b : Bond (scaleUp ell k Lu), (Real.exp (ψ b.1))⁻¹ ^ 2)
          = ∑ x : PeriodicLatticeSite (scaleUp ell k Lu), ∑ _μ : Fin 3, (Real.exp (ψ x))⁻¹ ^ 2 from
        Fintype.sum_prod_type _]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Real.exp_neg, ← Real.exp_nat_mul]
      push_cast; ring_nf
    rw [e1]
    have h2 := phiP_sum (θ / n) (by positivity) z
    have h3 := geom_le n θ hn1 hθ
    have h4 : (2 / (1 - Real.exp (-(2 * (θ / n))))) ^ 3 ≤ (n * (1 / θ + 2)) ^ 3 := by
      have h5 : 0 ≤ 2 / (1 - Real.exp (-(2 * (θ / n)))) := by
        have : Real.exp (-(2 * (θ / n))) < 1 := by
          have h0 : 0 < θ / n := by positivity
          have := Real.exp_lt_exp.mpr (show -(2 * (θ / n)) < 0 by linarith)
          rwa [Real.exp_zero] at this
        have : 0 < 1 - Real.exp (-(2 * (θ / n))) := by linarith
        positivity
      exact pow_le_pow_left₀ h5 h3 3
    linarith
  have hfinal : ∑ b, ‖X b‖ ≤ Real.sqrt (3 * (n * (1 / θ + 2)) ^ 3) * (CH * ‖v‖) := by
    refine hsum.trans ?_
    rw [hS2, Real.sqrt_sq (norm_nonneg _)]
    exact mul_le_mul (Real.sqrt_le_sqrt hS1) hW (norm_nonneg _) (Real.sqrt_nonneg _)
  -- the genuine column
  have hgen : ∀ b, ‖(iE (GF ell k Lu) ((PU ell k Lu hell0 U a Lam).data.H δv)) b‖
      = Real.sqrt (a * n ^ 3) * ‖X b‖ := by
    intro b
    rw [dataH_scaled ell k Lu U a t e q0 R H ψ θ hψl hc hEG Lam δv]
    show ‖Real.sqrt (a * n ^ 3) • X b‖ = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  simp only [hgen]
  rw [← Finset.mul_sum]
  have hsq : Real.sqrt (3 * (n * (1 / θ + 2)) ^ 3) = Real.sqrt 3 * (n * Real.sqrt n) * ((1 / θ + 2) * Real.sqrt (1 / θ + 2)) := by
    have hθ2 : 0 ≤ 1 / θ + 2 := by positivity
    rw [mul_pow, Real.sqrt_mul (by norm_num), Real.sqrt_mul (by positivity), sqrt_cube n hn.le, sqrt_cube _ hθ2]
    ring
  have hsa : Real.sqrt (a * n ^ 3) = Real.sqrt a * (n * Real.sqrt n) := by
    rw [Real.sqrt_mul (by have := R.ha; positivity), sqrt_cube n hn.le]
  have hsn2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn.le
  calc Real.sqrt (a * n ^ 3) * ∑ b, ‖X b‖
      ≤ Real.sqrt (a * n ^ 3) * (Real.sqrt (3 * (n * (1 / θ + 2)) ^ 3) * (CH * ‖v‖)) :=
        mul_le_mul_of_nonneg_left hfinal (Real.sqrt_nonneg _)
    _ = CHfree ell a t (rhoM0 ell k e q0) θ hc (KhatM0_pos ell k Lu U a t e q0 R) hEG * n ^ 3 * ‖v‖ := by
        rw [hsq, hsa]
        unfold CHfree
        rw [← hCH]
        have e : n * Real.sqrt n * (n * Real.sqrt n) = n ^ 3 := by nlinarith [hsn2]
        calc Real.sqrt a * (n * Real.sqrt n)
              * (Real.sqrt 3 * (n * Real.sqrt n) * ((1 / θ + 2) * Real.sqrt (1 / θ + 2)) * (CH * ‖v‖))
            = Real.sqrt 3 * Real.sqrt a * ((1 / θ + 2) * Real.sqrt (1 / θ + 2)) * CH
                * (n * Real.sqrt n * (n * Real.sqrt n)) * ‖v‖ := by ring
          _ = _ := by rw [e]

end

#print axioms cycd_step
#print axioms phiP_self
#print axioms phiP_lip
#print axioms phiP_sum
#print axioms geom_le
#print axioms NopM0_eq
#print axioms Nf_coer
#print axioms Nf_isUnit
#print axioms dataH_scaled
#print axioms CHfree
#print axioms hHcol_M0

end AdalyFormal.DLayer
