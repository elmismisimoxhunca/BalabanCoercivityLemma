import MI2
import MI8

/-!
# MI9 -- local commutators of the masked gradient with the G4 partition (M1 lane E, 2026-10-13)

`siteMul h`, `bondMul h` : multiplication operators.  `h_p = hpart p` (lane B G4) on sites, `hbond p` (MI2) on bonds.
`KG = 4 · 6(3(2c+1))³ · (ℓ²/((c−4)κM))²` (so the G4 bound per bond of `Ω₀` is `Σ_p (h_p y − h_p y')² ≤ KG / ℓ^{2 strat y}`).
* `cD_sum`   : `Σ_p ‖ℓ^{strat(tail)} (h_p Dm f − Dm (h_p f))‖² ≤ 3 KG ‖f‖²`;
* `cDs_sum`  : `Σ_p ‖ℓ^{2 strat} (h_p Dm* w − Dm* (h_p w))‖² ≤ 3 ℓ⁴ KG ‖ℓ^{strat(tail)} w‖²`;
* `cDs_sum0` : `Σ_p ‖h_p Dm* A − Dm* (h_p A)‖² ≤ 3 KG ‖ℓ^{−strat(tail)} A‖²`.
All constants are free of `k`, the torus, the tower and `κ`-independent up to `1/(κM)²`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.M1IMS

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer
open AdalyFormal.M1Site
open AdalyFormal.StatementLane (Tower Admissible bigSide)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack
  periodicLatticeShiftBack_shift gradCovariantAdjointValue)

variable {L : PeriodicLatticeExtent}

/-! ## 0. multiplication operators -/

noncomputable def siteMul (h : PeriodicLatticeSite L → ℝ) : SiteL2 L →L[ℝ] SiteL2 L :=
  LinearMap.toContinuousLinearMap
    { toFun := fun f => WithLp.toLp 2 (fun x => h x • f x)
      map_add' := fun f g => by refine PiLp.ext (fun x => ?_); simp [smul_add]
      map_smul' := fun c f => by
        refine PiLp.ext (fun x => ?_)
        simp only [PiLp.smul_apply, RingHom.id_apply]
        exact smul_comm _ _ _ }

theorem siteMul_apply (h : PeriodicLatticeSite L → ℝ) (f : SiteL2 L) (x : PeriodicLatticeSite L) :
    siteMul h f x = h x • f x := rfl

noncomputable def bondMul (h : Bond L → ℝ) : BondFnL2 L →L[ℝ] BondFnL2 L :=
  LinearMap.toContinuousLinearMap
    { toFun := fun f => WithLp.toLp 2 (fun b => h b • f b)
      map_add' := fun f g => by refine PiLp.ext (fun x => ?_); simp [smul_add]
      map_smul' := fun c f => by
        refine PiLp.ext (fun x => ?_)
        simp only [PiLp.smul_apply, RingHom.id_apply]
        exact smul_comm _ _ _ }

theorem bondMul_apply (h : Bond L → ℝ) (f : BondFnL2 L) (b : Bond L) : bondMul h f b = h b • f b := rfl

theorem siteMask_siteMul (S : Set (PeriodicLatticeSite L)) (h : PeriodicLatticeSite L → ℝ) (f : SiteL2 L) :
    siteMask S (siteMul h f) = siteMul h (siteMask S f) := by
  classical
  refine PiLp.ext (fun x => ?_)
  rw [siteMul_apply, siteMask_apply, siteMask_apply, siteMul_apply]
  split_ifs <;> simp

/-- reindexing by the backward shift. -/
theorem sum_shiftBack {β : Type*} [AddCommMonoid β] (μ : Fin 3) (g : PeriodicLatticeSite L → β) :
    ∑ x, g (periodicLatticeShiftBack x μ) = ∑ z, g z := by
  have hbij : Function.Bijective (fun x : PeriodicLatticeSite L => periodicLatticeShiftBack x μ) := by
    rw [Function.bijective_iff_has_inverse]
    exact ⟨fun z => periodicLatticeShift z μ, fun x => periodicLatticeShift_shiftBack x μ,
      fun z => periodicLatticeShiftBack_shift z μ⟩
  exact Function.Bijective.sum_comp hbij g

/-! ## 1. the G4 constant -/

/-- `KG = 4 m (ℓ²/((c−4)κM))²`, `m = 6 (3(2c+1))³`. -/
noncomputable def KG (ell M κ c : ℕ) : ℝ :=
  4 * ((6 * (3 * (2 * c + 1)) ^ 3 : ℕ) : ℝ) * ((ell : ℝ) ^ 2 / (((c : ℝ) - 4) * κ * M)) ^ 2

theorem KG_nonneg (ell M κ c : ℕ) : 0 ≤ KG ell M κ c := by unfold KG; positivity

section geo
variable {Lf : PeriodicLatticeExtent} {ell M R k κ c : ℕ} {S : Tower Lf}

/-- the G4 bound per bond of `Ω₀`, in the form `KG / ℓ^{2 strat}`. -/
theorem hpart_step (hA : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M) (hell : 1 ≤ ell) (hR1 : 1 ≤ R)
    (hR : (c + 3) * κ * ell ≤ R) (hc : 5 ≤ c) {y : PeriodicLatticeSite Lf} (hy : y ∈ S.Om 0) (μ : Fin 3)
    (hy' : periodicLatticeShift y μ ∈ S.Om 0) :
    ∑ p, (AdalyFormal.M1.hpart ell M k κ c S p y - AdalyFormal.M1.hpart ell M k κ c S p (periodicLatticeShift y μ)) ^ 2
      ≤ KG ell M κ c / ((ell : ℝ) ^ AdalyFormal.M1.strat S k y) ^ 2 := by
  have h := AdalyFormal.M1.hpart_grad_sq hA hκ hM hell hR1 hR hc hy μ hy'
  refine h.trans (le_of_eq ?_)
  unfold KG
  have hc5 : (5 : ℝ) ≤ c := by exact_mod_cast hc
  have hc4 : (0 : ℝ) < (c : ℝ) - 4 := by linarith
  have hκr : (0 : ℝ) < κ := by exact_mod_cast hκ
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hlr : (0 : ℝ) < (ell : ℝ) ^ AdalyFormal.M1.strat S k y := by
    have : (0 : ℝ) < ell := by exact_mod_cast hell
    positivity
  field_simp

end geo

/-! ## 2. the gradient commutator -/

section comm
variable {Lf : PeriodicLatticeExtent} {ell M R k κ c : ℕ} {S : Tower Lf}
  (hS : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M) (hell : 2 ≤ ell) (hR1 : 1 ≤ R)
  (hR : (c + 3) * κ * ell ≤ R) (hc : 5 ≤ c)
include hS hκ hM hell hR1 hR hc

/-- the step bound in `stratG` form with the weight `ℓ^{2 stratG}` cleared. -/
theorem hpart_step_w {y : PeriodicLatticeSite Lf} (hy : y ∈ S.Om 0) (μ : Fin 3)
    (hy' : periodicLatticeShift y μ ∈ S.Om 0) :
    ((ell : ℝ) ^ stratG (geomOf ell k S) y) ^ 2 *
      ∑ p, (AdalyFormal.M1.hpart ell M k κ c S p y - AdalyFormal.M1.hpart ell M k κ c S p (periodicLatticeShift y μ)) ^ 2
      ≤ KG ell M κ c := by
  have h := hpart_step hS hκ hM (by omega) hR1 hR hc hy μ hy'
  rw [strat_eq_stratG (by omega) hS] at h
  have hlr : (0 : ℝ) < ((ell : ℝ) ^ stratG (geomOf ell k S) y) ^ 2 := by
    have : (0 : ℝ) < ell := by exact_mod_cast (show 0 < ell by omega)
    positivity
  rw [le_div_iff₀ hlr] at h
  linarith

/-- pointwise form of the gradient commutator. -/
theorem cD_pt (U : Cfg Lf) (f : SiteL2 Lf) (b : Bond Lf) :
    ∑ p, ‖bondWt (sigG (geomOf ell k S)) (bondMul (hbond ell M k κ c S p) (Dm (geomOf ell k S) U f)
        - Dm (geomOf ell k S) U (siteMul (AdalyFormal.M1.hpart ell M k κ c S p) f)) b‖ ^ 2
      ≤ KG ell M κ c * ‖f (periodicLatticeShift b.1 b.2)‖ ^ 2 := by
  classical
  set G := geomOf ell k S
  set t := b.1
  set hd := periodicLatticeShift b.1 b.2
  have hval : ∀ p, (bondWt (sigG G) (bondMul (hbond ell M k κ c S p) (Dm G U f)
        - Dm G U (siteMul (AdalyFormal.M1.hpart ell M k κ c S p) f))) b
      = Real.exp (sigG G t) • (hbond ell M k κ c S p b • (RMap (U b) (siteMask G.Om0 f hd) - siteMask G.Om0 f t)
          - (RMap (U b) (siteMask G.Om0 (siteMul (AdalyFormal.M1.hpart ell M k κ c S p) f) hd) - siteMask G.Om0 (siteMul (AdalyFormal.M1.hpart ell M k κ c S p) f) t)) := by
    intro p
    rw [bondWt_apply, PiLp.sub_apply, bondMul_apply]
    simp only [Dm, ContinuousLinearMap.comp_apply, gradL2_apply']
    rfl
  have hKG := KG_nonneg ell M κ c
  by_cases ht : t ∈ G.Om0
  · by_cases hh : hd ∈ G.Om0
    · have e : ∀ p, (bondWt (sigG G) (bondMul (hbond ell M k κ c S p) (Dm G U f)
            - Dm G U (siteMul (AdalyFormal.M1.hpart ell M k κ c S p) f))) b
          = Real.exp (sigG G t) • ((AdalyFormal.M1.hpart ell M k κ c S p t - AdalyFormal.M1.hpart ell M k κ c S p hd) • RMap (U b) (f hd)) := by
        intro p
        rw [hval p]
        have hb : hbond ell M k κ c S p b = AdalyFormal.M1.hpart ell M k κ c S p t := by
          show (if b.1 ∈ S.Om 0 then _ else _) = _
          exact if_pos ht
        rw [hb, siteMask_on _ _ _ hh, siteMask_on _ _ _ ht, siteMask_on _ _ _ hh, siteMask_on _ _ _ ht,
          siteMul_apply, siteMul_apply]
        congr 1
        rw [map_smul, smul_sub, sub_smul]
        abel
      simp only [e, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap, mul_pow, sq_abs]
      rw [exp_sig G (by show 0 < ell; omega)]
      have hs := hpart_step_w hS hκ hM hell hR1 hR hc ht b.2 hh
      calc ∑ p, ((ell : ℝ) ^ stratG G t) ^ 2 * ((AdalyFormal.M1.hpart ell M k κ c S p t - AdalyFormal.M1.hpart ell M k κ c S p hd) ^ 2 * ‖f hd‖ ^ 2)
          = (((ell : ℝ) ^ stratG G t) ^ 2 * ∑ p, (AdalyFormal.M1.hpart ell M k κ c S p t - AdalyFormal.M1.hpart ell M k κ c S p hd) ^ 2) * ‖f hd‖ ^ 2 := by
            rw [Finset.mul_sum, Finset.sum_mul]; refine Finset.sum_congr rfl (fun p _ => ?_); ring
        _ ≤ KG ell M κ c * ‖f hd‖ ^ 2 := mul_le_mul_of_nonneg_right hs (sq_nonneg _)
    · have e : ∀ p, (bondWt (sigG G) (bondMul (hbond ell M k κ c S p) (Dm G U f)
            - Dm G U (siteMul (AdalyFormal.M1.hpart ell M k κ c S p) f))) b = 0 := by
        intro p
        rw [hval p]
        have hb : hbond ell M k κ c S p b = AdalyFormal.M1.hpart ell M k κ c S p t := by
          show (if b.1 ∈ S.Om 0 then _ else _) = _
          exact if_pos ht
        rw [hb, siteMask_off _ _ _ hh, siteMask_off _ _ _ hh, siteMask_on _ _ _ ht, siteMask_on _ _ _ ht,
          siteMul_apply, map_zero]
        simp
      simp only [e, norm_zero]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
      positivity
  · have e : ∀ p, (bondWt (sigG G) (bondMul (hbond ell M k κ c S p) (Dm G U f)
          - Dm G U (siteMul (AdalyFormal.M1.hpart ell M k κ c S p) f))) b = 0 := by
      intro p
      rw [hval p]
      have hb : hbond ell M k κ c S p b = AdalyFormal.M1.hpart ell M k κ c S p hd := by
        show (if b.1 ∈ S.Om 0 then _ else _) = _
        exact if_neg ht
      rw [hb, siteMask_off _ _ _ ht, siteMask_off _ _ _ ht, sub_zero, sub_zero]
      by_cases hh : hd ∈ G.Om0
      · rw [siteMask_on _ _ _ hh, siteMask_on _ _ _ hh, siteMul_apply, map_smul, sub_self, smul_zero]
      · rw [siteMask_off _ _ _ hh, siteMask_off _ _ _ hh, map_zero, smul_zero, sub_zero, smul_zero]
    simp only [e, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
    positivity

/-- **(L1) the gradient commutator, summed over the partition**: `Σ_p ‖ℓ^{strat} c_p(Dm) f‖² ≤ 3 KG ‖f‖²`. -/
theorem cD_sum (U : Cfg Lf) (f : SiteL2 Lf) :
    ∑ p, ‖bondWt (sigG (geomOf ell k S)) (bondMul (hbond ell M k κ c S p) (Dm (geomOf ell k S) U f)
        - Dm (geomOf ell k S) U (siteMul (AdalyFormal.M1.hpart ell M k κ c S p) f))‖ ^ 2
      ≤ 3 * KG ell M κ c * ‖f‖ ^ 2 := by
  simp only [PiLp.norm_sq_eq_of_L2]
  rw [Finset.sum_comm]
  calc ∑ b : Bond Lf, ∑ p, ‖(bondWt (sigG (geomOf ell k S)) (bondMul (hbond ell M k κ c S p) (Dm (geomOf ell k S) U f)
        - Dm (geomOf ell k S) U (siteMul (AdalyFormal.M1.hpart ell M k κ c S p) f))) b‖ ^ 2
      ≤ ∑ b : Bond Lf, KG ell M κ c * ‖f (periodicLatticeShift b.1 b.2)‖ ^ 2 :=
        Finset.sum_le_sum (fun b _ => cD_pt hS hκ hM hell hR1 hR hc U f b)
    _ = KG ell M κ c * (3 * ‖f‖ ^ 2) := by rw [← Finset.mul_sum, sum_shift_sq]
    _ = 3 * KG ell M κ c * ∑ x, ‖f x‖ ^ 2 := by rw [PiLp.norm_sq_eq_of_L2]; ring

/-! ## 3. the divergence commutator -/

theorem Dm_adjoint' (U : Cfg Lf) :
    ContinuousLinearMap.adjoint (Dm (geomOf ell k S) U) = siteMask (geomOf ell k S).Om0 ∘L gradAdj U := by
  unfold Dm gradAdj
  rw [ContinuousLinearMap.adjoint_comp, siteMask_adjoint]

open Classical in
theorem Dm_adj_apply (U : Cfg Lf) (w : BondFnL2 Lf) (x : PeriodicLatticeSite Lf) :
    ContinuousLinearMap.adjoint (Dm (geomOf ell k S) U) w x
      = if x ∈ (geomOf ell k S).Om0 then gradCovariantAdjointValue U (WithLp.ofLp w) x else 0 := by
  rw [Dm_adjoint' hS hκ hM hell hR1 hR hc, ContinuousLinearMap.comp_apply, siteMask_apply]
  split_ifs
  · show (WithLp.ofLp (gradAdj U w)) x = _
    rw [gradAdj_apply]
  · rfl

open Classical in
/-- pointwise form of the divergence commutator: only the bonds ENTERING `x` from `Ω₀` contribute. -/
theorem cDs_pt (U : Cfg Lf) (w : BondFnL2 Lf) (x : PeriodicLatticeSite Lf) :
    ∑ p, ‖siteMul (AdalyFormal.M1.hpart ell M k κ c S p) (ContinuousLinearMap.adjoint (Dm (geomOf ell k S) U) w) x
        - ContinuousLinearMap.adjoint (Dm (geomOf ell k S) U) (bondMul (hbond ell M k κ c S p) w) x‖ ^ 2
      ≤ 3 * ∑ μ : Fin 3, (if x ∈ S.Om 0 ∧ periodicLatticeShiftBack x μ ∈ S.Om 0 then
          (∑ p, (AdalyFormal.M1.hpart ell M k κ c S p (periodicLatticeShiftBack x μ)
            - AdalyFormal.M1.hpart ell M k κ c S p x) ^ 2) * ‖w (periodicLatticeShiftBack x μ, μ)‖ ^ 2 else 0) := by
  classical
  set G := geomOf ell k S
  by_cases hx : x ∈ G.Om0
  · have e : ∀ p, siteMul (AdalyFormal.M1.hpart ell M k κ c S p) (ContinuousLinearMap.adjoint (Dm G U) w) x
          - ContinuousLinearMap.adjoint (Dm G U) (bondMul (hbond ell M k κ c S p) w) x
        = ∑ μ : Fin 3, (if periodicLatticeShiftBack x μ ∈ S.Om 0 then
            (AdalyFormal.M1.hpart ell M k κ c S p x - AdalyFormal.M1.hpart ell M k κ c S p (periodicLatticeShiftBack x μ)) •
              RMap (U (periodicLatticeShiftBack x μ, μ))⁻¹ (w (periodicLatticeShiftBack x μ, μ)) else 0) := by
      intro p
      rw [siteMul_apply, Dm_adj_apply hS hκ hM hell hR1 hR hc, Dm_adj_apply hS hκ hM hell hR1 hR hc, if_pos hx, if_pos hx]
      unfold gradCovariantAdjointValue
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun μ _ => ?_)
      have hb1 : hbond ell M k κ c S p (x, μ) = AdalyFormal.M1.hpart ell M k κ c S p x := by
        show (if x ∈ S.Om 0 then _ else _) = _
        exact if_pos hx
      have e1 : (WithLp.ofLp (bondMul (hbond ell M k κ c S p) w)) (x, μ) = AdalyFormal.M1.hpart ell M k κ c S p x • w (x, μ) := by
        show bondMul _ w (x, μ) = _; rw [bondMul_apply, hb1]
      have e2 : (WithLp.ofLp (bondMul (hbond ell M k κ c S p) w)) (periodicLatticeShiftBack x μ, μ)
          = hbond ell M k κ c S p (periodicLatticeShiftBack x μ, μ) • w (periodicLatticeShiftBack x μ, μ) := rfl
      rw [e1, e2]
      have ew : (WithLp.ofLp w) (periodicLatticeShiftBack x μ, μ) = w (periodicLatticeShiftBack x μ, μ) := rfl
      have ew2 : (WithLp.ofLp w) (x, μ) = w (x, μ) := rfl
      rw [ew, ew2, map_smul]
      split_ifs with hz
      · have hb2 : hbond ell M k κ c S p (periodicLatticeShiftBack x μ, μ) = AdalyFormal.M1.hpart ell M k κ c S p (periodicLatticeShiftBack x μ) := by
          show (if periodicLatticeShiftBack x μ ∈ S.Om 0 then _ else _) = _
          rw [if_pos hz]
        rw [hb2, smul_sub, sub_smul]; abel
      · have hb2 : hbond ell M k κ c S p (periodicLatticeShiftBack x μ, μ) = AdalyFormal.M1.hpart ell M k κ c S p x := by
          show (if periodicLatticeShiftBack x μ ∈ S.Om 0 then _ else _) = _
          rw [if_neg hz]
          show AdalyFormal.M1.hpart ell M k κ c S p (periodicLatticeShift (periodicLatticeShiftBack x μ) μ) = AdalyFormal.M1.hpart ell M k κ c S p x
          rw [periodicLatticeShift_shiftBack]
        rw [hb2, smul_sub]; abel
    simp only [e]
    -- Cauchy–Schwarz over the three directions, then exchange the sums
    have hcs : ∀ p, ‖∑ μ : Fin 3, (if periodicLatticeShiftBack x μ ∈ S.Om 0 then
            (AdalyFormal.M1.hpart ell M k κ c S p x - AdalyFormal.M1.hpart ell M k κ c S p (periodicLatticeShiftBack x μ)) •
              RMap (U (periodicLatticeShiftBack x μ, μ))⁻¹ (w (periodicLatticeShiftBack x μ, μ)) else 0)‖ ^ 2
        ≤ 3 * ∑ μ : Fin 3, (if periodicLatticeShiftBack x μ ∈ S.Om 0 then
            (AdalyFormal.M1.hpart ell M k κ c S p (periodicLatticeShiftBack x μ) - AdalyFormal.M1.hpart ell M k κ c S p x) ^ 2 * ‖w (periodicLatticeShiftBack x μ, μ)‖ ^ 2 else 0) := by
      intro p
      have h1 := norm_sum_le (Finset.univ : Finset (Fin 3)) (fun μ => (if periodicLatticeShiftBack x μ ∈ S.Om 0 then
            (AdalyFormal.M1.hpart ell M k κ c S p x - AdalyFormal.M1.hpart ell M k κ c S p (periodicLatticeShiftBack x μ)) •
              RMap (U (periodicLatticeShiftBack x μ, μ))⁻¹ (w (periodicLatticeShiftBack x μ, μ)) else 0))
      have h2 : ∀ μ : Fin 3, ‖(if periodicLatticeShiftBack x μ ∈ S.Om 0 then
            (AdalyFormal.M1.hpart ell M k κ c S p x - AdalyFormal.M1.hpart ell M k κ c S p (periodicLatticeShiftBack x μ)) •
              RMap (U (periodicLatticeShiftBack x μ, μ))⁻¹ (w (periodicLatticeShiftBack x μ, μ)) else (0 : SuTwo))‖ ^ 2
          = (if periodicLatticeShiftBack x μ ∈ S.Om 0 then
            (AdalyFormal.M1.hpart ell M k κ c S p (periodicLatticeShiftBack x μ) - AdalyFormal.M1.hpart ell M k κ c S p x) ^ 2 * ‖w (periodicLatticeShiftBack x μ, μ)‖ ^ 2 else 0) := by
        intro μ
        split_ifs
        · rw [norm_smul, AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap, mul_pow, Real.norm_eq_abs, sq_abs]
          ring
        · simp
      have h3 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 3)))
        (f := fun μ => ‖(if periodicLatticeShiftBack x μ ∈ S.Om 0 then
            (AdalyFormal.M1.hpart ell M k κ c S p x - AdalyFormal.M1.hpart ell M k κ c S p (periodicLatticeShiftBack x μ)) •
              RMap (U (periodicLatticeShiftBack x μ, μ))⁻¹ (w (periodicLatticeShiftBack x μ, μ)) else (0 : SuTwo))‖)
      simp only [Finset.card_univ, Fintype.card_fin] at h3
      simp only [h2] at h3
      have h4 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      push_cast at h3
      linarith
    refine (Finset.sum_le_sum (fun p _ => hcs p)).trans (le_of_eq ?_)
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    have hx0 : x ∈ S.Om 0 := hx
    by_cases hz : periodicLatticeShiftBack x μ ∈ S.Om 0
    · simp only [if_pos hz, if_pos (And.intro hx0 hz)]
      rw [Finset.sum_mul]
    · simp only [if_neg hz, Finset.sum_const_zero]
      rw [if_neg (fun h' => hz h'.2)]
  · have e : ∀ p, siteMul (AdalyFormal.M1.hpart ell M k κ c S p) (ContinuousLinearMap.adjoint (Dm G U) w) x
          - ContinuousLinearMap.adjoint (Dm G U) (bondMul (hbond ell M k κ c S p) w) x = 0 := by
      intro p
      rw [siteMul_apply, Dm_adj_apply hS hκ hM hell hR1 hR hc, Dm_adj_apply hS hκ hM hell hR1 hR hc, if_neg hx, if_neg hx, smul_zero, sub_zero]
    simp only [e, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
    have : ∀ μ : Fin 3, 0 ≤ (if x ∈ S.Om 0 ∧ periodicLatticeShiftBack x μ ∈ S.Om 0 then
          (∑ p, (AdalyFormal.M1.hpart ell M k κ c S p (periodicLatticeShiftBack x μ)
            - AdalyFormal.M1.hpart ell M k κ c S p x) ^ 2) * ‖w (periodicLatticeShiftBack x μ, μ)‖ ^ 2 else 0) := by
      intro μ; split_ifs
      · exact mul_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (sq_nonneg _)
      · exact le_rfl
    have := Finset.sum_nonneg (fun μ (_ : μ ∈ Finset.univ) => this μ)
    linarith

open Classical in
/-- **(L2') divergence commutator, unweighted target**: `Σ_p ‖c_p(Dm*) A‖² ≤ 3 KG ‖ℓ^{−strat(tail)} A‖²`. -/
theorem cDs_sum0 (U : Cfg Lf) (A : BondFnL2 Lf) :
    ∑ p, ‖siteMul (AdalyFormal.M1.hpart ell M k κ c S p) (ContinuousLinearMap.adjoint (Dm (geomOf ell k S) U) A)
        - ContinuousLinearMap.adjoint (Dm (geomOf ell k S) U) (bondMul (hbond ell M k κ c S p) A)‖ ^ 2
      ≤ 3 * KG ell M κ c * ‖bondWt (-sigG (geomOf ell k S)) A‖ ^ 2 := by
  classical
  set G := geomOf ell k S
  simp only [PiLp.norm_sq_eq_of_L2]
  rw [Finset.sum_comm]
  have hpt := fun x => cDs_pt hS hκ hM hell hR1 hR hc U A x
  simp only [PiLp.sub_apply] at hpt
  refine (Finset.sum_le_sum (fun x _ => hpt x)).trans ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hstep : ∀ μ : Fin 3, ∀ x : PeriodicLatticeSite Lf,
      (if x ∈ S.Om 0 ∧ periodicLatticeShiftBack x μ ∈ S.Om 0 then
        (∑ p, (AdalyFormal.M1.hpart ell M k κ c S p (periodicLatticeShiftBack x μ)
          - AdalyFormal.M1.hpart ell M k κ c S p x) ^ 2) * ‖A (periodicLatticeShiftBack x μ, μ)‖ ^ 2 else 0)
      ≤ KG ell M κ c * ‖(bondWt (-sigG G) A) (periodicLatticeShiftBack x μ, μ)‖ ^ 2 := by
    intro μ x
    split_ifs with h
    · set z := periodicLatticeShiftBack x μ
      have hzx : periodicLatticeShift z μ = x := periodicLatticeShift_shiftBack x μ
      have hs := hpart_step_w hS hκ hM hell hR1 hR hc h.2 μ (by rw [hzx]; exact h.1)
      rw [hzx] at hs
      rw [bondWt_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
      have he : Real.exp ((-sigG G) (z, μ).1) = ((ell : ℝ) ^ stratG G z)⁻¹ := by
        show Real.exp (-(sigG G z)) = _
        rw [Real.exp_neg, exp_sig G (by show 0 < ell; omega)]
        rfl
      rw [he]
      have hlr : (0 : ℝ) < ((ell : ℝ) ^ stratG G z) ^ 2 := by
        have : (0 : ℝ) < ell := by exact_mod_cast (show 0 < ell by omega)
        positivity
      rw [inv_pow]
      have hKs : (∑ p, (AdalyFormal.M1.hpart ell M k κ c S p z - AdalyFormal.M1.hpart ell M k κ c S p x) ^ 2)
          ≤ KG ell M κ c * (((ell : ℝ) ^ stratG G z) ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hlr]; linarith
      exact mul_le_mul_of_nonneg_right hKs (sq_nonneg _) |>.trans (le_of_eq (by ring))
    · have := KG_nonneg ell M κ c; positivity
  calc 3 * ∑ μ : Fin 3, ∑ x, (if x ∈ S.Om 0 ∧ periodicLatticeShiftBack x μ ∈ S.Om 0 then
        (∑ p, (AdalyFormal.M1.hpart ell M k κ c S p (periodicLatticeShiftBack x μ)
          - AdalyFormal.M1.hpart ell M k κ c S p x) ^ 2) * ‖A (periodicLatticeShiftBack x μ, μ)‖ ^ 2 else 0)
      ≤ 3 * ∑ μ : Fin 3, ∑ x, KG ell M κ c * ‖(bondWt (-sigG G) A) (periodicLatticeShiftBack x μ, μ)‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun μ _ => Finset.sum_le_sum (fun x _ => hstep μ x)))
          (by norm_num)
    _ = 3 * KG ell M κ c * ∑ b : Bond Lf, ‖(bondWt (-sigG G) A) b‖ ^ 2 := by
        rw [Fintype.sum_prod_type_right]
        simp only [← Finset.mul_sum]
        rw [mul_assoc]
        congr 2
        refine Finset.sum_congr rfl (fun μ _ => ?_)
        exact sum_shiftBack μ (fun z => ‖(bondWt (-sigG G) A) (z, μ)‖ ^ 2)

open Classical in
/-- **(L2) divergence commutator, weighted**: `Σ_p ‖ℓ^{2 strat} c_p(Dm*) w‖² ≤ 3 ℓ⁴ KG ‖ℓ^{strat(tail)} w‖²`. -/
theorem cDs_sum (U : Cfg Lf) (w : BondFnL2 Lf) :
    ∑ p, ‖siteWt (sigG (geomOf ell k S) + sigG (geomOf ell k S))
        (siteMul (AdalyFormal.M1.hpart ell M k κ c S p) (ContinuousLinearMap.adjoint (Dm (geomOf ell k S) U) w)
          - ContinuousLinearMap.adjoint (Dm (geomOf ell k S) U) (bondMul (hbond ell M k κ c S p) w))‖ ^ 2
      ≤ 3 * (ell : ℝ) ^ 4 * KG ell M κ c * ‖bondWt (sigG (geomOf ell k S)) w‖ ^ 2 := by
  classical
  set G := geomOf ell k S
  have hell0 : 0 < ell := by omega
  have hellr : (0 : ℝ) < ell := by exact_mod_cast hell0
  simp only [PiLp.norm_sq_eq_of_L2]
  rw [Finset.sum_comm]
  have hpt : ∀ x, ∑ p, ‖(siteWt (sigG G + sigG G)
        (siteMul (AdalyFormal.M1.hpart ell M k κ c S p) (ContinuousLinearMap.adjoint (Dm G U) w)
          - ContinuousLinearMap.adjoint (Dm G U) (bondMul (hbond ell M k κ c S p) w))) x‖ ^ 2
      ≤ ((ell : ℝ) ^ stratG G x) ^ 4 * (3 * ∑ μ : Fin 3, (if x ∈ S.Om 0 ∧ periodicLatticeShiftBack x μ ∈ S.Om 0 then
          (∑ p, (AdalyFormal.M1.hpart ell M k κ c S p (periodicLatticeShiftBack x μ)
            - AdalyFormal.M1.hpart ell M k κ c S p x) ^ 2) * ‖w (periodicLatticeShiftBack x μ, μ)‖ ^ 2 else 0)) := by
    intro x
    have h0 := cDs_pt hS hκ hM hell hR1 hR hc U w x
    have e : ∀ p, ‖(siteWt (sigG G + sigG G)
        (siteMul (AdalyFormal.M1.hpart ell M k κ c S p) (ContinuousLinearMap.adjoint (Dm G U) w)
          - ContinuousLinearMap.adjoint (Dm G U) (bondMul (hbond ell M k κ c S p) w))) x‖ ^ 2
        = ((ell : ℝ) ^ stratG G x) ^ 4 * ‖siteMul (AdalyFormal.M1.hpart ell M k κ c S p)
            (ContinuousLinearMap.adjoint (Dm G U) w) x
          - ContinuousLinearMap.adjoint (Dm G U) (bondMul (hbond ell M k κ c S p) w) x‖ ^ 2 := by
      intro p
      rw [siteWt_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, PiLp.sub_apply]
      congr 1
      rw [Pi.add_apply, Real.exp_add, exp_sig G (by show 0 < ell; omega)]
      show ((ell : ℝ) ^ stratG G x * (ell : ℝ) ^ stratG G x) ^ 2 = ((ell : ℝ) ^ stratG G x) ^ 4
      ring
    simp only [e]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left h0 (by positivity)
  refine (Finset.sum_le_sum (fun x _ => hpt x)).trans ?_
  have hstep : ∀ μ : Fin 3, ∀ x : PeriodicLatticeSite Lf,
      ((ell : ℝ) ^ stratG G x) ^ 4 * (if x ∈ S.Om 0 ∧ periodicLatticeShiftBack x μ ∈ S.Om 0 then
        (∑ p, (AdalyFormal.M1.hpart ell M k κ c S p (periodicLatticeShiftBack x μ)
          - AdalyFormal.M1.hpart ell M k κ c S p x) ^ 2) * ‖w (periodicLatticeShiftBack x μ, μ)‖ ^ 2 else 0)
      ≤ (ell : ℝ) ^ 4 * KG ell M κ c * ‖(bondWt (sigG G) w) (periodicLatticeShiftBack x μ, μ)‖ ^ 2 := by
    intro μ x
    split_ifs with h
    · set z := periodicLatticeShiftBack x μ
      have hzx : periodicLatticeShift z μ = x := periodicLatticeShift_shiftBack x μ
      have hs := hpart_step_w hS hκ hM hell hR1 hR hc h.2 μ (by rw [hzx]; exact h.1)
      rw [hzx] at hs
      -- strata of adjacent sites differ by at most one
      have hadj := (AdalyFormal.M1.strat_adj hS hR1 (by omega) (by omega) z μ).1
      rw [hzx, strat_eq_stratG hell0 hS, strat_eq_stratG hell0 hS] at hadj
      rw [bondWt_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
      have he : Real.exp (sigG G (z, μ).1) = (ell : ℝ) ^ stratG G z := exp_sig G (by show 0 < ell; omega) z
      rw [he]
      set sz := stratG G z
      set sx := stratG G x
      have hpow : ((ell : ℝ) ^ sx) ^ 4 ≤ (ell : ℝ) ^ 4 * ((ell : ℝ) ^ sz) ^ 2 * ((ell : ℝ) ^ sz) ^ 2 := by
        simp only [← pow_mul, ← pow_add]
        exact pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ ell by omega)) (by omega)
      have hS0 : 0 ≤ ∑ p, (AdalyFormal.M1.hpart ell M k κ c S p z - AdalyFormal.M1.hpart ell M k κ c S p x) ^ 2 :=
        Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have hw0 := sq_nonneg ‖w (z, μ)‖
      calc ((ell : ℝ) ^ sx) ^ 4 * ((∑ p, (AdalyFormal.M1.hpart ell M k κ c S p z
              - AdalyFormal.M1.hpart ell M k κ c S p x) ^ 2) * ‖w (z, μ)‖ ^ 2)
          ≤ ((ell : ℝ) ^ 4 * ((ell : ℝ) ^ sz) ^ 2 * ((ell : ℝ) ^ sz) ^ 2) * ((∑ p, (AdalyFormal.M1.hpart ell M k κ c S p z
              - AdalyFormal.M1.hpart ell M k κ c S p x) ^ 2) * ‖w (z, μ)‖ ^ 2) :=
            mul_le_mul_of_nonneg_right hpow (mul_nonneg hS0 hw0)
        _ = (ell : ℝ) ^ 4 * (((ell : ℝ) ^ sz) ^ 2 * ∑ p, (AdalyFormal.M1.hpart ell M k κ c S p z
              - AdalyFormal.M1.hpart ell M k κ c S p x) ^ 2) * (((ell : ℝ) ^ sz) ^ 2 * ‖w (z, μ)‖ ^ 2) := by ring
        _ ≤ (ell : ℝ) ^ 4 * KG ell M κ c * (((ell : ℝ) ^ sz) ^ 2 * ‖w (z, μ)‖ ^ 2) := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by positivity)) (by positivity)
    · rw [mul_zero]; have := KG_nonneg ell M κ c; positivity
  have hx : ∀ x : PeriodicLatticeSite Lf, ((ell : ℝ) ^ stratG G x) ^ 4 * (3 * ∑ μ : Fin 3,
        (if x ∈ S.Om 0 ∧ periodicLatticeShiftBack x μ ∈ S.Om 0 then
          (∑ p, (AdalyFormal.M1.hpart ell M k κ c S p (periodicLatticeShiftBack x μ)
            - AdalyFormal.M1.hpart ell M k κ c S p x) ^ 2) * ‖w (periodicLatticeShiftBack x μ, μ)‖ ^ 2 else 0))
      ≤ 3 * ∑ μ : Fin 3, (ell : ℝ) ^ 4 * KG ell M κ c * ‖(bondWt (sigG G) w) (periodicLatticeShiftBack x μ, μ)‖ ^ 2 := by
    intro x
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum (fun μ _ => ?_)
    have h1 := hstep μ x
    calc ((ell : ℝ) ^ stratG G x) ^ 4 * (3 * (if x ∈ S.Om 0 ∧ periodicLatticeShiftBack x μ ∈ S.Om 0 then
          (∑ p, (AdalyFormal.M1.hpart ell M k κ c S p (periodicLatticeShiftBack x μ)
            - AdalyFormal.M1.hpart ell M k κ c S p x) ^ 2) * ‖w (periodicLatticeShiftBack x μ, μ)‖ ^ 2 else 0))
        = 3 * (((ell : ℝ) ^ stratG G x) ^ 4 * (if x ∈ S.Om 0 ∧ periodicLatticeShiftBack x μ ∈ S.Om 0 then
          (∑ p, (AdalyFormal.M1.hpart ell M k κ c S p (periodicLatticeShiftBack x μ)
            - AdalyFormal.M1.hpart ell M k κ c S p x) ^ 2) * ‖w (periodicLatticeShiftBack x μ, μ)‖ ^ 2 else 0)) := by ring
      _ ≤ 3 * ((ell : ℝ) ^ 4 * KG ell M κ c * ‖(bondWt (sigG G) w) (periodicLatticeShiftBack x μ, μ)‖ ^ 2) := by
          linarith
  refine (Finset.sum_le_sum (fun x _ => hx x)).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hμ : ∀ μ : Fin 3, ∑ x : PeriodicLatticeSite Lf,
      (ell : ℝ) ^ 4 * KG ell M κ c * ‖(bondWt (sigG G) w) (periodicLatticeShiftBack x μ, μ)‖ ^ 2
      = (ell : ℝ) ^ 4 * KG ell M κ c * ∑ z : PeriodicLatticeSite Lf, ‖(bondWt (sigG G) w) (z, μ)‖ ^ 2 := by
    intro μ
    rw [← Finset.mul_sum]
    congr 1
    exact sum_shiftBack μ (fun z => ‖(bondWt (sigG G) w) (z, μ)‖ ^ 2)
  rw [Finset.sum_congr rfl (fun μ _ => hμ μ), ← Finset.mul_sum]
  rw [show ∑ μ : Fin 3, ∑ z : PeriodicLatticeSite Lf, ‖(bondWt (sigG G) w) (z, μ)‖ ^ 2
      = ∑ b : Bond Lf, ‖(bondWt (sigG G) w) b‖ ^ 2 from (Fintype.sum_prod_type_right (fun b : Bond Lf => ‖(bondWt (sigG G) w) b‖ ^ 2)).symm]
  ring

end comm

end AdalyFormal.M1IMS

#print axioms AdalyFormal.M1IMS.siteMul_apply
#print axioms AdalyFormal.M1IMS.bondMul_apply
#print axioms AdalyFormal.M1IMS.siteMask_siteMul
#print axioms AdalyFormal.M1IMS.sum_shiftBack
#print axioms AdalyFormal.M1IMS.KG_nonneg
#print axioms AdalyFormal.M1IMS.hpart_step
#print axioms AdalyFormal.M1IMS.hpart_step_w
#print axioms AdalyFormal.M1IMS.cD_pt
#print axioms AdalyFormal.M1IMS.cD_sum
#print axioms AdalyFormal.M1IMS.Dm_adjoint'
#print axioms AdalyFormal.M1IMS.Dm_adj_apply
#print axioms AdalyFormal.M1IMS.cDs_pt
#print axioms AdalyFormal.M1IMS.cDs_sum0
#print axioms AdalyFormal.M1IMS.cDs_sum
#print axioms AdalyFormal.M1IMS.siteMul
#print axioms AdalyFormal.M1IMS.bondMul
#print axioms AdalyFormal.M1IMS.KG
