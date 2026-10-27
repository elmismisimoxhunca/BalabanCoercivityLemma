import ZXR2Ops3

/-!
# CvOX1 -- the Dirichlet unit `DelpA + (1 - mask)` for EVERY link configuration (lane omega, extra)

`delpA_unit`: if `a > 0`, `ell >= 2` and some site lies outside `Om0`, then `IsUnit (DelpA G U a + (1 - siteMask G.Om0))`
for every `U`.  Proof: `<f, X f> >= |D (m f)|^2 + |f - m f|^2` (the mass term `Qpa` is positive), so `X f = 0` forces
`f = m f` with `D f = 0`; covariantly constant fields have constant `hsInner (f x) (f x)` on the (connected) torus, and
`f` vanishes off `Om0`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap gradValueCovariant)
open AdalyFormal.Balaban.SuTwoInner (hsInner hsInner_RMap hsInner_self_nonneg hsInner_self_eq_zero)

open Fin.NatCast

variable {L : PeriodicLatticeExtent}

theorem ajSeq_pos {a : ℝ} (ha : 0 < a) {ell : ℕ} (hell : 2 ≤ ell) (j : ℕ) : 0 < ajSeq a ell j := by
  unfold ajSeq
  split_ifs with h
  · exact ha
  · unfold AdalyFormal.Balaban.ConstantA.aSeq
    have hl : (2 : ℝ) ≤ ell := by exact_mod_cast hell
    have hpos : (0 : ℝ) < (ell : ℝ) * ell := by positivity
    have hd : 0 < a / ((ell : ℝ) * ell) := by positivity
    have h4 : (4 : ℝ) ≤ (ell : ℝ) * ell := by nlinarith
    have hda : a / ((ell : ℝ) * ell) < a := by
      rw [div_lt_iff₀ hpos]; nlinarith [mul_le_mul_of_nonneg_left h4 ha.le]
    exact AdalyFormal.Balaban.ConstantA.aSeqAux_pos a _ ha hd hda _

theorem Qpa_nonneg (G : TowerGeom L) (U : Cfg L) {a : ℝ} (ha : 0 < a) (hell : 2 ≤ G.ell) (f : SiteL2 L) :
    0 ≤ ⟪f, Qpa G U a f⟫ := by
  rw [inner_Qpa]
  refine Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun y _ => ?_))
  split_ifs
  · exact mul_nonneg (mul_nonneg (ajSeq_pos ha hell j).le (pow_nonneg (Nat.cast_nonneg _) _)) (sq_nonneg _)
  · exact le_rfl


theorem delpA_inner_ge (G : TowerGeom L) (U : Cfg L) {a : ℝ} (ha : 0 < a) (hell : 2 ≤ G.ell) (f : SiteL2 L) :
    ‖gradL2 U (siteMask G.Om0 f)‖ ^ 2 + ‖f - siteMask G.Om0 f‖ ^ 2 ≤ ⟪f, (DelpA G U a + (1 - siteMask G.Om0)) f⟫ := by
  set m := siteMask G.Om0 with hm
  have hsym : ∀ u v : SiteL2 L, ⟪m u, v⟫ = ⟪u, m v⟫ := fun u v => siteMask_symm _ u v
  have hidem : ∀ u : SiteL2 L, m (m u) = m u := fun u => siteMask_idem _ u
  have e1 : ⟪f, DelpA G U a f⟫ = ⟪m f, lapFull U (m f)⟫ + ⟪m f, Qpa G U a (m f)⟫ := by
    unfold DelpA
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply]
    rw [← hsym, inner_add_right]
  have e2 : ⟪f, ((1 : SiteL2 L →L[ℝ] SiteL2 L) - m) f⟫ = ‖f - m f‖ ^ 2 := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    rw [← real_inner_self_eq_norm_sq]
    have h0 : ⟪m f, f - m f⟫ = 0 := by
      rw [inner_sub_right]
      have a1 : ⟪m f, m f⟫ = ⟪f, m f⟫ := by rw [hsym, hidem]
      have a2 : ⟪m f, f⟫ = ⟪f, m f⟫ := real_inner_comm _ _
      rw [a1, a2, sub_self]
    have hdec : f = (f - m f) + m f := by abel
    calc ⟪f, f - m f⟫ = ⟪(f - m f) + m f, f - m f⟫ := by rw [← hdec]
      _ = ⟪f - m f, f - m f⟫ := by rw [inner_add_left, h0, add_zero]
  have e3 : ⟪m f, lapFull U (m f)⟫ = ‖gradL2 U (m f)‖ ^ 2 := by
    unfold lapFull gradAdj
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
  have e4 := Qpa_nonneg G U ha hell (m f)
  show _ ≤ ⟪f, DelpA G U a f + ((1 : SiteL2 L →L[ℝ] SiteL2 L) - m) f⟫
  rw [inner_add_right, e1, e2, e3]
  linarith

/-- covariantly constant site fields have constant `hsInner (f x) (f x)`. -/
theorem covConst_norm (U : Cfg L) (f : SiteL2 L) (h : gradL2 U f = 0) (x y : PeriodicLatticeSite L) :
    hsInner (f x) (f x) = hsInner (f y) (f y) := by
  have hb : ∀ b : AdalyFormal.Balaban.AdmissibleSubspace.Bond L, RMap (U b) (f (periodicLatticeShift b.1 b.2)) = f b.1 := by
    intro b
    have := congrFun (congrArg WithLp.ofLp h) b
    rw [gradL2_apply] at this
    simp only [gradValueCovariant] at this
    exact sub_eq_zero.mp this
  have hstep : ∀ (z : PeriodicLatticeSite L) (μ : Fin 3), hsInner (f (periodicLatticeShift z μ)) (f (periodicLatticeShift z μ)) = hsInner (f z) (f z) := by
    intro z μ
    have := hb (z, μ)
    simp only [] at this
    rw [← hsInner_RMap (U (z, μ)) (f (periodicLatticeShift z μ)) (f (periodicLatticeShift z μ)), this]
  have hiter : ∀ (z : PeriodicLatticeSite L) (μ : Fin 3) (j : ℕ),
      hsInner (f (Function.update z μ (z μ + (Nat.cast j : Fin (L μ + 1))))) (f (Function.update z μ (z μ + (Nat.cast j : Fin (L μ + 1))))) = hsInner (f z) (f z) := by
    intro z μ j
    induction j with
    | zero => simp
    | succ j ih =>
      have : Function.update z μ (z μ + (Nat.cast (j + 1) : Fin (L μ + 1))) =
          periodicLatticeShift (Function.update z μ (z μ + (Nat.cast j : Fin (L μ + 1)))) μ := by
        unfold periodicLatticeShift
        rw [Function.update_self, Function.update_idem]
        congr 1
        rw [Nat.cast_succ]
        abel
      rw [this, hstep, ih]
  have hupd : ∀ (z : PeriodicLatticeSite L) (μ : Fin 3) (v : Fin (L μ + 1)),
      hsInner (f (Function.update z μ v)) (f (Function.update z μ v)) = hsInner (f z) (f z) := by
    intro z μ v
    have := hiter z μ (v - z μ).val
    rw [Fin.cast_val_eq_self, add_sub_cancel] at this
    exact this
  have hall : ∀ z w : PeriodicLatticeSite L, hsInner (f w) (f w) = hsInner (f z) (f z) := by
    intro z w
    have hw : w = Function.update (Function.update (Function.update z 0 (w 0)) 1 (w 1)) 2 (w 2) := by
      funext ν
      fin_cases ν <;> simp [Function.update]
    rw [hw, hupd, hupd, hupd]
  exact (hall x y).symm

theorem delpA_unit (G : TowerGeom L) (U : Cfg L) {a : ℝ} (ha : 0 < a) (hell : 2 ≤ G.ell)
    (hout : ∃ x : PeriodicLatticeSite L, x ∉ G.Om0) :
    IsUnit (DelpA G U a + (1 - siteMask G.Om0)) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  set X : SiteL2 L →L[ℝ] SiteL2 L := DelpA G U a + (1 - siteMask G.Om0) with hX
  have hinj : Function.Injective X := by
    refine (injective_iff_map_eq_zero X).mpr (fun f hf => ?_)
    have h1 := delpA_inner_ge G U ha hell f
    rw [hf, inner_zero_right] at h1
    have hs1 := sq_nonneg ‖gradL2 U (siteMask G.Om0 f)‖
    have hs2 := sq_nonneg ‖f - siteMask G.Om0 f‖
    have hD : ‖gradL2 U (siteMask G.Om0 f)‖ ^ 2 = 0 := by linarith
    have hR : ‖f - siteMask G.Om0 f‖ ^ 2 = 0 := by linarith
    have hfm : f = siteMask G.Om0 f :=
      sub_eq_zero.mp (norm_eq_zero.mp ((pow_eq_zero_iff (two_ne_zero)).mp hR))
    have hDm : gradL2 U (siteMask G.Om0 f) = 0 := norm_eq_zero.mp ((pow_eq_zero_iff (two_ne_zero)).mp hD)
    have hDf : gradL2 U f = 0 := by rw [← hfm] at hDm; exact hDm
    obtain ⟨x0, hx0⟩ := hout
    have hx0f : f x0 = 0 := by
      have : (siteMask G.Om0 f) x0 = 0 := by rw [siteMask_apply, if_neg hx0]
      rw [← hfm] at this; exact this
    ext x
    have := covConst_norm U f hDf x x0
    rw [hx0f] at this
    have h0 : hsInner (f x) (f x) = 0 := by
      rw [this]; exact AdalyFormal.Balaban.DeltaKU.hsInner_zero_right _
    have := hsInner_self_eq_zero h0
    simp [this]
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := (X : SiteL2 L →ₗ[ℝ] SiteL2 L))).mp hinj⟩

#print axioms ajSeq_pos
#print axioms delpA_inner_ge
#print axioms covConst_norm
#print axioms delpA_unit

end AdalyFormal.CoverOmega
