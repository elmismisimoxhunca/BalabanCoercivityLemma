import CvN3

/-!
# CvN4 -- `G' = (Ω₀Δ'_aΩ₀)⁻¹` exists at EVERY configuration, and `θ ↦ Ginv(1[b ↦ vPath θ])` is continuous
(lane cover_necessary_20261016)

* `forall_of_shift`: a property of sites closed under every forward shift and true at one site is true everywhere (torus
  connectivity).
* `DelpA_unit`: on any height-1 tower with `Ω₀ ≠` torus and `a > 0`, the operator `Ω₀(Δ_U + Q'*aQ')Ω₀ + (1 - Ω₀)` whose
  `Ring.inverse` defines `G'` (`ZR2Ops2.Gp`) is invertible for EVERY `U` (energy identity + covariant-constant fields vanish).
* `Ginv_path_continuous`: if the moving bond `b` is based farther than `9 ell` from `Ω₁`, then
  `θ ↦ (gparams ell 1 Lu _ S (Upath b θ) a Λ).data.Ginv` (3.122) is continuous.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.CoverNec

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLaneR8
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap gradValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

variable {L : PeriodicLatticeExtent}

open Fin.NatCast

/-! ## 1. connectivity of the torus -/

theorem shift_iter (P : PeriodicLatticeSite L → Prop) (h : ∀ x μ, P x → P (periodicLatticeShift x μ))
    (x : PeriodicLatticeSite L) (μ : Fin 3) (hx : P x) :
    ∀ n : ℕ, P (Function.update x μ (x μ + (n : Fin (L μ + 1)))) := by
  intro n
  induction n with
  | zero => simpa using hx
  | succ n ih =>
      have h1 := h _ μ ih
      unfold periodicLatticeShift at h1
      simp only [Function.update_self, Function.update_idem] at h1
      rw [Nat.cast_succ, ← add_assoc]
      exact h1

theorem forall_of_shift (P : PeriodicLatticeSite L → Prop) (h : ∀ x μ, P x → P (periodicLatticeShift x μ))
    {x0 : PeriodicLatticeSite L} (h0 : P x0) (y : PeriodicLatticeSite L) : P y := by
  have step : ∀ (x : PeriodicLatticeSite L) (μ : Fin 3) (c : Fin (L μ + 1)), P x → P (Function.update x μ c) := by
    intro x μ c hx
    have := shift_iter P h x μ hx (c - x μ).val
    rwa [Fin.cast_val_eq_self, add_sub_cancel] at this
  have e : y = Function.update (Function.update (Function.update x0 0 (y 0)) 1 (y 1)) 2 (y 2) := by
    funext μ
    fin_cases μ <;> simp
  rw [e]
  exact step _ _ _ (step _ _ _ (step _ _ _ h0))

/-! ## 2. `G'` exists at every configuration -/

theorem RMap_eq_zero {V : Matrix.specialUnitaryGroup (Fin 2) ℂ} {Z : SuTwo} (h : RMap V Z = 0) : Z = 0 := by
  have h1 : inner ℝ (RMap V Z) (RMap V Z) = inner ℝ Z Z := AdalyFormal.Balaban.SuTwoInner.inner_RMap V Z Z
  rw [h, inner_zero_left] at h1
  exact inner_self_eq_zero.mp h1.symm

theorem ajSeq_le1 (a : ℝ) (ell j : ℕ) (hj : j ≤ 1) : ajSeq a ell j = a := by
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
  · simp [ajSeq]
  · simp [ajSeq, AdalyFormal.Balaban.ConstantA.aSeq, AdalyFormal.Balaban.ConstantA.aSeqAux]

open Classical in
theorem Qpa_nonneg {ell : ℕ} (S : Tower L) (U : Cfg L) {a : ℝ} (ha : 0 < a) (g : SiteL2 L) :
    0 ≤ ⟪g, Qpa (geomOf ell 1 S) U a g⟫ := by
  rw [inner_Qpa]
  refine Finset.sum_nonneg (fun j hj => Finset.sum_nonneg (fun y _ => ?_))
  split_ifs
  · have hj1 : j ≤ 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [ajSeq_le1 a _ j hj1]
    positivity
  · exact le_rfl

theorem DelpA_unit {ell : ℕ} (S : Tower L) (U : Cfg L) {a : ℝ} (ha : 0 < a) (hne : ∃ x, x ∉ S.Om 0) :
    IsUnit (DelpA (geomOf ell 1 S) U a + (1 - siteMask (geomOf ell 1 S).Om0)) := by
  set G := geomOf ell 1 S with hGdef
  set X : SiteL2 L →L[ℝ] SiteL2 L := DelpA G U a + (1 - siteMask G.Om0) with hX
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  have hinj : Function.Injective X := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    set g := siteMask G.Om0 f with hg
    have hQ := Qpa_nonneg (ell := ell) S U ha g
    have hE : ⟪f, X f⟫ = ‖gradL2 U g‖ ^ 2 + ⟪g, Qpa G U a g⟫ + ‖f - g‖ ^ 2 := by
      have e1 : ⟪f, DelpA G U a f⟫ = ‖gradL2 U g‖ ^ 2 + ⟪g, Qpa G U a g⟫ := by
        unfold DelpA
        simp only [ContinuousLinearMap.comp_apply, add_apply]
        rw [← siteMask_symm, inner_add_right, inner_lapFull]
      have e2 : ⟪f, (1 - siteMask G.Om0) f⟫ = ‖f - g‖ ^ 2 := by
        rw [sub_apply, one_apply_eq_self, ← real_inner_self_eq_norm_sq]
        have h3 : ⟪g, f - g⟫ = 0 := by
          rw [inner_sub_right, hg, siteMask_symm _ f (siteMask _ f), siteMask_idem, real_inner_comm, sub_self]
        have : ⟪f, f - g⟫ = ⟪f - g, f - g⟫ + ⟪g, f - g⟫ := by rw [← inner_add_left, sub_add_cancel]
        rw [this, h3, add_zero]
      rw [hX, add_apply, inner_add_right, e1, e2]
    rw [hf, inner_zero_right] at hE
    have hn1 : 0 ≤ ‖gradL2 U g‖ ^ 2 := sq_nonneg _
    have hn3 : 0 ≤ ‖f - g‖ ^ 2 := sq_nonneg _
    have hD : ‖gradL2 U g‖ ^ 2 = 0 := by linarith
    have hfg : ‖f - g‖ ^ 2 = 0 := by linarith
    have hD0 : gradL2 U g = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hD
      exact norm_eq_zero.mp this
    have hfg0 : f = g := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hfg
      exact sub_eq_zero.mp (norm_eq_zero.mp this)
    -- `g` is covariantly constant and vanishes off `Ω₀`, hence everywhere
    obtain ⟨x0, hx0⟩ := hne
    have hg0 : (WithLp.ofLp g) x0 = 0 := by
      show (siteMask G.Om0 f) x0 = 0
      rw [siteMask_apply, if_neg (show x0 ∉ G.Om0 from hx0)]
    have hall : ∀ y, (WithLp.ofLp g) y = 0 := by
      refine forall_of_shift (fun x => (WithLp.ofLp g) x = 0) (fun x μ hx => ?_) hg0
      have hb : (WithLp.ofLp (gradL2 U g)) (x, μ) = 0 := by rw [hD0]; rfl
      rw [gradL2_apply] at hb
      unfold gradValueCovariant at hb
      simp only at hx hb
      rw [hx, sub_zero] at hb
      exact RMap_eq_zero hb
    rw [hfg0]
    exact PiLp.ext hall
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := (X : SiteL2 L →ₗ[ℝ] SiteL2 L))).mp hinj⟩

/-! ## 3. continuity of `Ginv` along the path -/

theorem adjoint_continuous {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] {X : Type*} [TopologicalSpace X]
    {A : X → E →L[ℝ] F} (hA : Continuous A) : Continuous fun t => ContinuousLinearMap.adjoint (A t) :=
  (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := F)).continuous.comp hA

/-- `Ginv` (3.122) at `(ell, k = 1, Lu, S, U, a, Λ)`, typed on the `U`-independent carrier `E₀` of `geomOf ell 1 S`. -/
noncomputable def GinvAt (ell : ℕ) (hell : 0 < ell) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell 1 Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (U : Cfg (scaleUp ell 1 Lu)) :
    ↥(bondSupp (geomOf ell 1 S)) →L[ℝ] ↥(bondSupp (geomOf ell 1 S)) :=
  (gparams ell 1 Lu hell S U a Lam).data.Ginv

theorem Ginv_path_continuous {ell : ℕ} (hell : 0 < ell) {Lu : PeriodicLatticeExtent} (S : Tower (scaleUp ell 1 Lu))
    {a : ℝ} (ha : 0 < a) (Lam : Set (PeriodicLatticeSite Lu)) (b : Bond (scaleUp ell 1 Lu))
    (hfar : ∀ y ∈ S.Om 1, 9 * ell < pdist y b.1) (hne : ∃ x, x ∉ S.Om 0) :
    Continuous fun t => GinvAt ell hell Lu S a Lam (Upath b t) := by
  set G := geomOf ell 1 S with hGdef
  set U0 : Cfg (scaleUp ell 1 Lu) := fun _ => 1 with hU0
  have hFA : ∀ t, FarAgree S (9 * ell) (Upath b t) U0 := fun t => farAgree_update S _ U0 b (vPath t) hfar
  have hFA8 : ∀ t, FarAgree S (8 * ell) (Upath b t) U0 := fun t => (hFA t).mono (by omega)
  set T0 := Tfull G U0 with hT0
  set Ms0 := MassFull G a (bondSectorOf G U0) with hMs0
  set Qp0 := Qpa G U0 a with hQp0
  set m := siteMask G.Om0 with hm
  let X : ℝ → SiteL2 (scaleUp ell 1 Lu) →L[ℝ] SiteL2 (scaleUp ell 1 Lu) := fun t =>
    (m.comp ((ContinuousLinearMap.adjoint (gradL2 (Upath b t))).comp (gradL2 (Upath b t)) + Qp0)).comp m + (1 - m)
  have hXeq : ∀ t, X t = DelpA G (Upath b t) a + (1 - siteMask G.Om0) := by
    intro t
    show (m.comp ((ContinuousLinearMap.adjoint (gradL2 (Upath b t))).comp (gradL2 (Upath b t)) + Qp0)).comp m + (1 - m)
      = DelpA G (Upath b t) a + (1 - siteMask G.Om0)
    rw [hQp0, ← Qpa_congr_far hell (hFA8 t) a]
    rfl
  have hXu : ∀ t, IsUnit (X t) := fun t => by rw [hXeq]; exact DelpA_unit S _ ha hne
  have hgc := gradL2_continuous (Upath_cont b)
  have hXc : Continuous X := by
    refine Continuous.add (Continuous.clm_comp (Continuous.clm_comp continuous_const
      (Continuous.add (Continuous.clm_comp (adjoint_continuous hgc) hgc) continuous_const)) continuous_const) continuous_const
  have hIc : Continuous fun t => Ring.inverse (X t) := by
    refine continuous_iff_continuousAt.2 (fun t => ?_)
    have h1 : ContinuousAt Ring.inverse (X t) := by
      rw [← (hXu t).unit_spec]
      exact NormedRing.inverse_continuousAt (R := SiteL2 (scaleUp ell 1 Lu) →L[ℝ] SiteL2 (scaleUp ell 1 Lu))
        (hXu t).unit
    exact h1.comp hXc.continuousAt
  let W : ℝ → BondFnL2 (scaleUp ell 1 Lu) →L[ℝ] BondFnL2 (scaleUp ell 1 Lu) := fun t =>
    1 - (gradL2 (Upath b t)).comp (((Ring.inverse (X t)).comp m).comp T0)
  have hWeq : ∀ t, W t = Wop G (Upath b t) a := by
    intro t
    have hT : (Rproj G (Upath b t)).comp (gradAdj (Upath b t)) = T0 := by
      rw [hT0, ← Tfull_congr_far hell (hFA8 t)]; rfl
    show 1 - (gradL2 (Upath b t)).comp (((Ring.inverse (X t)).comp m).comp T0) = Wop G (Upath b t) a
    unfold Wop Gp
    (rw [← hT, hXeq t]) <;> rfl
  have hWc : Continuous W :=
    continuous_const.sub (Continuous.clm_comp hgc (Continuous.clm_comp (Continuous.clm_comp hIc continuous_const)
      continuous_const))
  have hDc := Delta_continuous G (Upath_cont b)
  have hGeq : ∀ t, GinvAt ell hell Lu S a Lam (Upath b t) =
      (pE G).comp (((ContinuousLinearMap.adjoint (W t)).comp ((Delta G (Upath b t)).comp (W t))).comp (iE G)) +
        (ContinuousLinearMap.adjoint (T0.comp (iE G))).comp (T0.comp (iE G)) + (pE G).comp (Ms0.comp (iE G)) := by
    intro t
    have hTt : Tfull G (Upath b t) = T0 := Tfull_congr_far hell (hFA8 t)
    have hMt : MassFull G a (bondSectorOf G (Upath b t)) = Ms0 := MassFull_congr_far hell (hFA t) a
    rw [hWeq t]
    show (pE G).comp ((DpiFull G (Upath b t) a).comp (iE G)) +
        (ContinuousLinearMap.adjoint ((Tfull G (Upath b t)).comp (iE G))).comp ((Tfull G (Upath b t)).comp (iE G)) +
        (pE G).comp ((MassFull G a (bondSectorOf G (Upath b t))).comp (iE G)) = _
    (rw [hTt, hMt]) <;> rfl
  simp only [hGeq]
  refine Continuous.add (Continuous.add ?_ continuous_const) continuous_const
  exact Continuous.clm_comp continuous_const (Continuous.clm_comp (Continuous.clm_comp (adjoint_continuous hWc)
    (Continuous.clm_comp hDc hWc)) continuous_const)

#print axioms forall_of_shift
#print axioms RMap_eq_zero
#print axioms Qpa_nonneg
#print axioms DelpA_unit
#print axioms GinvAt
#print axioms Ginv_path_continuous

end AdalyFormal.CoverNec
