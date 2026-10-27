import CvS3a

/-!
# CvS3b -- on the tip instance, `G⁻¹` (3.122) changes with the tip link only on the level-0 (pinned) bonds
(lane cover_strong_20261016)

Configurations `Ut v = 1[b_t ↦ v]` on the tip instance (CvN6), compared with the constant configuration `1`.
* `Gp_lapDir`: `G' (Δ_U|Ω₀ h) = h` for `h ∈ N(Q')` (any `U`, `a > 0`, `Ω₀ ≠` torus): `Q'*aQ' h = 0`.
* **`tip_Wop_eq`**: `W = I − D G' R D*` is THE SAME operator for every `v` (`R D*` is far-local (CvN2); `G' R D* x ∈ N(Q')`
  vanishes off `Ω₁` (CvN2 `NQp_vanish`) and is the same element; its gradient is far-local).
* `TipBond e`: `e` is a boundary bond of a plaquette of `plaqIn Ω₀` through `b_t`.  `tipBond_far`, `tipBond_lvl0`.
* `plaq_term_zero`: a field vanishing on `∂p` has zero curl and zero `Δ'` bilinear term at `p` (every `U`).
* `tip_W_vanish`: `W` preserves "vanishes on every tip bond".
* **`tip_Delta_bil`**: `⟪w', Δ_{Ut v} w⟫ = ⟪w', Δ_1 w⟫` for `w, w'` vanishing on every tip bond.
* **`tip_Ginv_compress`**: for `x, x' ∈ E₀` vanishing on every level-0 bond of `𝔅`, `⟪x', G⁻¹(Ut v) x⟫ = ⟪x', G⁻¹(1) x⟫`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.CoverStrong

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.StatementLaneR6 (edge_mem curlValue_congr bilPlaq_congr deltaKLocCLM_symm)
open AdalyFormal.NoCover
open AdalyFormal.GeneralClass
open AdalyFormal.CoverNec (FarAgree farAgree_update Tfull_congr_far NQp_congr_far lapDir_congr_NQp grad_congr_near
  NQp_vanish nearOm1_of_vanish QfullOf_congr_far MassFull_congr_far Delta_form_sum DelpA_unit tip_far9 tip_outside)

/-! ## generic -/

section Generic
variable {L : PeriodicLatticeExtent}

theorem Gp_lapDir {ell : ℕ} {S : Tower L} (U : Cfg L) {a : ℝ} (ha : 0 < a) (hne : ∃ x, x ∉ S.Om 0)
    {h : SiteL2 L} (hh : h ∈ NQp (geomOf ell 1 S) U) :
    Gp (geomOf ell 1 S) U a (lapDir (geomOf ell 1 S) U h) = h := by
  set G := geomOf ell 1 S with hG
  have hX := DelpA_unit (ell := ell) S U ha hne
  have hmask : siteMask G.Om0 h = h := by
    refine PiLp.ext (fun x => ?_)
    rw [siteMask_apply]
    split_ifs with hx
    · rfl
    · exact (hh.1 x hx).symm
  have hQ : Qpa G U a h = 0 := by
    unfold Qpa
    simp only [ContinuousLinearMap.sum_apply]
    refine Finset.sum_eq_zero (fun j hj => Finset.sum_eq_zero (fun y _ => ?_))
    split_ifs with hy
    · simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
      have hj' : j ≤ G.k := by
        have := Finset.mem_range.mp hj
        omega
      rw [hh.2 j hj' y hy]
      simp
    · simp
  have hXh : (DelpA G U a + (1 - siteMask G.Om0)) h = lapDir G U h := by
    show siteMask G.Om0 ((lapFull U + Qpa G U a) (siteMask G.Om0 h)) + (h - siteMask G.Om0 h)
      = siteMask G.Om0 (lapFull U (siteMask G.Om0 h))
    rw [hmask, ContinuousLinearMap.add_apply, hQ, add_zero, sub_self, add_zero]
  have hm2 : siteMask G.Om0 (lapDir G U h) = lapDir G U h := by
    show siteMask G.Om0 (siteMask G.Om0 (lapFull U (siteMask G.Om0 h))) = siteMask G.Om0 (lapFull U (siteMask G.Om0 h))
    rw [siteMask_idem]
  show Ring.inverse (DelpA G U a + (1 - siteMask G.Om0)) (siteMask G.Om0 (lapDir G U h)) = h
  rw [hm2, ← hXh, inverse_apply_of_unit hX]

/-- a field vanishing on the four boundary bonds of `p` has zero curl and zero `Δ'` term at `p`, for every `U`. -/
theorem plaq_term_zero (U : Cfg L) (p : PeriodicLatticePlaquette L) (w : Bond L → SuTwo)
    (hw : ∀ e ∈ periodicPlaquetteBoundaryEdges p, w e = 0) :
    curlValueCovariant U w p = 0 ∧ bilPlaq U p w w = 0 := by
  have h1 := hw _ ((edge_mem p _).mpr (Or.inl rfl))
  have h2 := hw _ ((edge_mem p _).mpr (Or.inr (Or.inl rfl)))
  have h3 := hw _ ((edge_mem p _).mpr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 := hw _ ((edge_mem p _).mpr (Or.inr (Or.inr (Or.inr rfl))))
  have hc : curlValueCovariant U w p = 0 := by
    unfold curlValueCovariant
    rw [h1, h2, h3, h4]
    simp
  refine ⟨hc, ?_⟩
  have ha1 : a1LM U p w = 0 := by
    rw [a1LM_apply]; unfold AprimeZW; rw [h3]; simp
  have ha2 : a2LM p w = 0 := by
    rw [a2LM_apply]; unfold AprimeWX; rw [h4]; simp
  have ha3 : a3LM p w = 0 := by
    rw [a3LM_apply]; unfold AprimeXY; rw [h1]; simp
  have ha4 : a4LM U p w = 0 := by
    rw [a4LM_apply]; unfold AprimeYZ; rw [h2]; simp
  have hcm : curlMatLM U p w = 0 := by
    rw [curlMatLM_apply, hc]; simp
  rw [bilPlaq_apply, firstBilPlaq_apply, secondBilPlaq_apply]
  simp only [pairBil_apply, b1LM, b2LM, b3LM, b4LM, LinearMap.comp_apply, ha1, ha2, ha3, ha4, hcm, map_zero,
    zero_mul, mul_zero, Matrix.trace_zero, Complex.zero_re, sub_zero, add_zero]

/-- the bilinear form of `G⁻¹` (3.122) on `E₀`: `⟪W x', Δ W x⟫ + ⟪T x', T x⟫ + ⟪x', Q*aQ x⟫`. -/
theorem Ginv_bil (P : IngrBParams) (x x' : ↥(bondSupp P.G)) :
    ⟪x', P.data.Ginv x⟫ =
      ⟪Wop P.G P.U P.a (iE P.G x'), Delta P.G P.U (Wop P.G P.U P.a (iE P.G x))⟫ +
        ⟪Tfull P.G P.U (iE P.G x'), Tfull P.G P.U (iE P.G x)⟫ +
        ⟪iE P.G x', MassFull P.G P.a P.sector (iE P.G x)⟫ := by
  have e1 : ⟪x', P.data.Ginv x⟫ = ⟪x', P.data.Dpi x⟫ + ⟪P.data.T x', P.data.T x⟫ + ⟪x', P.data.Mass x⟫ := by
    simp only [BaseDataS.Ginv, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, inner_add_right]
    rw [← P.data.T_adj]
  have e2 : ⟪x', P.data.Dpi x⟫ =
      ⟪Wop P.G P.U P.a (iE P.G x'), Delta P.G P.U (Wop P.G P.U P.a (iE P.G x))⟫ := by
    have : P.data.Dpi x = pE P.G (DpiFull P.G P.U P.a (iE P.G x)) := rfl
    rw [this, pE_inner_right]
    simp only [DpiFull, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  have e3 : ⟪P.data.T x', P.data.T x⟫ = ⟪Tfull P.G P.U (iE P.G x'), Tfull P.G P.U (iE P.G x)⟫ := rfl
  have e4 : ⟪x', P.data.Mass x⟫ = ⟪iE P.G x', MassFull P.G P.a P.sector (iE P.G x)⟫ := by
    have : P.data.Mass x = pE P.G (MassFull P.G P.a P.sector (iE P.G x)) := rfl
    rw [this, pE_inner_right]
  rw [e1, e2, e3, e4]

end Generic

/-! ## the tip instance -/

/-- the tip configuration `1[b_t ↦ v]`. -/
abbrev Ut (ell M R : ℕ) (hell0 : 0 < ell) (hM : 0 < M) (v : SU2c) : Cfg (scaleUp ell 1 (ncLu M R)) :=
  Function.update (fun _ => 1) ((xtG ell M R hell0 hM, 1) : Bond _) v

theorem Ut_one (ell M R : ℕ) (hell0 : 0 < ell) (hM : 0 < M) : Ut ell M R hell0 hM 1 = fun _ => 1 := by
  unfold Ut
  exact Function.update_eq_self _ _

/-- `e` is a boundary bond of a plaquette of `plaqIn Ω₀` that contains the tip bond. -/
def TipBond (ell M R : ℕ) (hell0 : 0 < ell) (hM : 0 < M) (e : Bond (scaleUp ell 1 (ncLu M R))) : Prop :=
  ∃ q ∈ plaqIn ((gcS ell M R).Om 0), ((xtG ell M R hell0 hM, 1) : Bond _) ∈ periodicPlaquetteBoundaryEdges q ∧
    e ∈ periodicPlaquetteBoundaryEdges q

section Tip
variable {ell M R : ℕ} (hell : 3 ≤ ell) (hell0 : 0 < ell) (hM : 0 < M) (hR : 9 * ell + 1 ≤ R)
include hell hR

theorem tip_farAgree {r : ℕ} (hr : r ≤ 9 * ell) (v : SU2c) :
    FarAgree (gcS ell M R) r (Ut ell M R hell0 hM v) (fun _ => 1) :=
  farAgree_update _ r _ _ v (fun y hy => lt_of_le_of_lt hr (tip_far9 hell hell0 hM hR y hy))

theorem tipBond_far (e : Bond (scaleUp ell 1 (ncLu M R))) (he : TipBond ell M R hell0 hM e) :
    e.1 ∉ (gcS ell M R).Om 1 ∧ periodicLatticeShift e.1 e.2 ∉ (gcS ell M R).Om 1 := by
  obtain ⟨q, -, hbtq, heq⟩ := he
  have hfar := tip_far9 (R := R) hell hell0 hM hR
  have hqt : pdist q.1 (xtG ell M R hell0 hM) ≤ 2 := (plaq_corner_dist q _ hbtq).1
  have hqb := plaq_corner_dist q e heq
  have hnot : ∀ z, pdist q.1 z ≤ 2 → z ∉ (gcS ell M R).Om 1 := by
    intro z hz hz1
    have h1 := hfar z hz1
    have h2 := AdalyFormal.StatementLaneR8.pdist_triangle z q.1 (xtG ell M R hell0 hM)
    rw [AdalyFormal.StatementLaneR8.pdist_comm z q.1] at h2
    omega
  exact ⟨hnot _ hqb.1, hnot _ hqb.2⟩

theorem tipBond_lvl0 (e : Bond (scaleUp ell 1 (ncLu M R))) (he : TipBond ell M R hell0 hM e) :
    e ∈ bondsLam (geomOf ell 1 (gcS ell M R)) 0 := by
  have hfar := tipBond_far hell hell0 hM hR e he
  obtain ⟨q, hq, -, heq⟩ := he
  have hin : e.1 ∈ (gcS ell M R).Om 0 ∧ periodicLatticeShift e.1 e.2 ∈ (gcS ell M R).Om 0 := hq e heq
  have hadm := gc_admissible (R := R) hell0 hM
  have hcs : AdalyFormal.Balaban.CoarseCurl.coarseShift e.1 (ell ^ 0) e.2 = periodicLatticeShift e.1 e.2 := by
    rw [pow_zero]; rfl
  refine ⟨Or.inl ⟨fun μ => by simp, hin.1, hfar.1⟩, ?_⟩
  show ¬ (OmGe (geomOf ell 1 (gcS ell M R)) (0 + 1) e.1 ∨
    OmGe (geomOf ell 1 (gcS ell M R)) (0 + 1) (AdalyFormal.Balaban.CoarseCurl.coarseShift e.1 (ell ^ 0) e.2))
  rw [hcs]
  rintro (h | h)
  · exact hfar.1 ((omGe_iff_om ell M R 1 hell0 _ hadm 1 _).mp h)
  · exact hfar.2 ((omGe_iff_om ell M R 1 hell0 _ hadm 1 _).mp h)

/-- `W` is the same operator for every value of the tip link. -/
theorem tip_Wop_eq {a : ℝ} (ha : 0 < a) (v : SU2c) :
    Wop (geomOf ell 1 (gcS ell M R)) (Ut ell M R hell0 hM v) a = Wop (geomOf ell 1 (gcS ell M R)) (fun _ => 1) a := by
  set G := geomOf ell 1 (gcS ell M R) with hG
  have hF8 := tip_farAgree hell hell0 hM hR (r := 8 * ell) (by omega) v
  have hF2 := tip_farAgree hell hell0 hM hR (r := 2) (by omega) v
  have hne := tip_outside hell hell0 hM (R := R) (by omega)
  have hT := Tfull_congr_far hell0 hF8
  ext1 x
  set f := Tfull G (fun _ => 1) x with hf
  have hfm : f ∈ RImage G (fun _ => 1) := Submodule.starProjection_apply_mem _ _
  obtain ⟨h, hh, hfh⟩ := Submodule.mem_map.mp hfm
  have hh' : h ∈ NQp G (Ut ell M R hell0 hM v) := by rw [NQp_congr_far hell0 hF8]; exact hh
  have hfh' : lapDir G (fun _ => 1) h = f := hfh
  have g1 : Gp G (fun _ => 1) a f = h := by rw [← hfh']; exact Gp_lapDir _ ha hne hh
  have gv : Gp G (Ut ell M R hell0 hM v) a f = h := by
    rw [← hfh', ← lapDir_congr_NQp hF2 hh]
    exact Gp_lapDir _ ha hne hh'
  have hgrad := grad_congr_near hF2 (nearOm1_of_vanish (fun z hz => NQp_vanish hh z hz))
  have hTx : Rproj G (Ut ell M R hell0 hM v) (gradAdj (Ut ell M R hell0 hM v) x) = f := by
    show Tfull G (Ut ell M R hell0 hM v) x = Tfull G (fun _ => 1) x
    rw [hT]
  have hT1 : Rproj G (fun _ => 1) (gradAdj (fun _ => 1) x) = f := rfl
  simp only [Wop, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, ContinuousLinearMap.comp_apply]
  rw [hTx, hT1, gv, g1, hgrad]

/-- `W` preserves "vanishes on every tip bond". -/
theorem tip_W_vanish {a : ℝ} (ha : 0 < a) (u : BondFnL2 (scaleUp ell 1 (ncLu M R)))
    (hu : ∀ e, TipBond ell M R hell0 hM e → (WithLp.ofLp u) e = 0) :
    ∀ e, TipBond ell M R hell0 hM e → (WithLp.ofLp (Wop (geomOf ell 1 (gcS ell M R)) (fun _ => 1) a u)) e = 0 := by
  intro e he
  set G := geomOf ell 1 (gcS ell M R) with hG
  have hne := tip_outside hell hell0 hM (R := R) (by omega)
  set f := Tfull G (fun _ => 1) u with hf
  have hfm : f ∈ RImage G (fun _ => 1) := Submodule.starProjection_apply_mem _ _
  obtain ⟨h, hh, hfh⟩ := Submodule.mem_map.mp hfm
  have hfh' : lapDir G (fun _ => 1) h = f := hfh
  have g1 : Gp G (fun _ => 1) a f = h := by rw [← hfh']; exact Gp_lapDir _ ha hne hh
  have hT1 : Rproj G (fun _ => 1) (gradAdj (fun _ => 1) u) = f := rfl
  have hfar := tipBond_far hell hell0 hM hR e he
  simp only [Wop, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, ContinuousLinearMap.comp_apply]
  rw [hT1, g1, PiLp.sub_apply, hu e he, gradL2_apply]
  unfold AdalyFormal.Balaban.CovariantOperators.gradValueCovariant
  rw [NQp_vanish hh _ hfar.1, NQp_vanish hh _ hfar.2]
  simp

theorem tip_Delta_form (v : SU2c) (w : BondFnL2 (scaleUp ell 1 (ncLu M R)))
    (hw : ∀ e, TipBond ell M R hell0 hM e → (WithLp.ofLp w) e = 0) :
    ⟪w, Delta (geomOf ell 1 (gcS ell M R)) (Ut ell M R hell0 hM v) w⟫ =
      ⟪w, Delta (geomOf ell 1 (gcS ell M R)) (fun _ => 1) w⟫ := by
  rw [Delta_form_sum, Delta_form_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  split_ifs with hp
  · by_cases hbt : ((xtG ell M R hell0 hM, 1) : Bond _) ∈ periodicPlaquetteBoundaryEdges p
    · have hz : ∀ e ∈ periodicPlaquetteBoundaryEdges p, (WithLp.ofLp w) e = 0 :=
        fun e he => hw e ⟨p, hp, hbt, he⟩
      obtain ⟨c1, b1⟩ := plaq_term_zero (Ut ell M R hell0 hM v) p _ hz
      obtain ⟨c2, b2⟩ := plaq_term_zero (fun _ => 1) p _ hz
      rw [c1, b1, c2, b2]
    · have hag : ∀ e ∈ periodicPlaquetteBoundaryEdges p, (Ut ell M R hell0 hM v) e = (fun _ => (1 : SU2c)) e := by
        intro e he
        refine Function.update_of_ne (fun h => hbt ?_) _ _
        rw [← h]
        exact he
      rw [curlValue_congr hag, bilPlaq_congr hag]
  · rfl

/-- bilinear form of `Δ` on fields vanishing on every tip bond: independent of `v`. -/
theorem tip_Delta_bil (v : SU2c) (w w' : BondFnL2 (scaleUp ell 1 (ncLu M R)))
    (hw : ∀ e, TipBond ell M R hell0 hM e → (WithLp.ofLp w) e = 0)
    (hw' : ∀ e, TipBond ell M R hell0 hM e → (WithLp.ofLp w') e = 0) :
    ⟪w', Delta (geomOf ell 1 (gcS ell M R)) (Ut ell M R hell0 hM v) w⟫ =
      ⟪w', Delta (geomOf ell 1 (gcS ell M R)) (fun _ => 1) w⟫ := by
  have hpol : ∀ U : Cfg (scaleUp ell 1 (ncLu M R)),
      ⟪w', Delta (geomOf ell 1 (gcS ell M R)) U w⟫ =
        (⟪w + w', Delta (geomOf ell 1 (gcS ell M R)) U (w + w')⟫ - ⟪w, Delta (geomOf ell 1 (gcS ell M R)) U w⟫
          - ⟪w', Delta (geomOf ell 1 (gcS ell M R)) U w'⟫) / 2 := by
    intro U
    have hs : ⟪w, Delta (geomOf ell 1 (gcS ell M R)) U w'⟫ = ⟪w', Delta (geomOf ell 1 (gcS ell M R)) U w⟫ := by
      rw [real_inner_comm]
      exact deltaKLocCLM_symm U _ w' w
    rw [map_add, inner_add_left, inner_add_right, inner_add_right, hs]
    ring
  have hsum : ∀ e, TipBond ell M R hell0 hM e → (WithLp.ofLp (w + w')) e = 0 := by
    intro e he
    rw [PiLp.add_apply, hw e he, hw' e he, add_zero]
  rw [hpol, hpol (fun _ => 1), tip_Delta_form hell hell0 hM hR v _ hsum, tip_Delta_form hell hell0 hM hR v _ hw,
    tip_Delta_form hell hell0 hM hR v _ hw']

/-- **compression of `G⁻¹` (3.122) to fields vanishing on the level-0 bonds: independent of the tip link.** -/
theorem tip_Ginv_compress {a : ℝ} (ha : 0 < a) (v : SU2c) (Lam : Set (PeriodicLatticeSite (ncLu M R)))
    (x x' : ↥(bondSupp (geomOf ell 1 (gcS ell M R))))
    (hx : ∀ b, b ∈ bondsLam (geomOf ell 1 (gcS ell M R)) 0 → (WithLp.ofLp (iE _ x)) b = 0)
    (hx' : ∀ b, b ∈ bondsLam (geomOf ell 1 (gcS ell M R)) 0 → (WithLp.ofLp (iE _ x')) b = 0) :
    ⟪x', (tipP ell M R hell0 hM v a Lam).data.Ginv x⟫ = ⟪x', (tipP ell M R hell0 hM 1 a Lam).data.Ginv x⟫ := by
  have hF8 := tip_farAgree hell hell0 hM hR (r := 8 * ell) (by omega) v
  have hF9 := tip_farAgree hell hell0 hM hR (r := 9 * ell) le_rfl v
  have hU1 : Ut ell M R hell0 hM 1 = fun _ => 1 := Ut_one ell M R hell0 hM
  have hT := Tfull_congr_far hell0 hF8
  have hMass := MassFull_congr_far hell0 hF9 a
  have hW := tip_Wop_eq hell hell0 hM hR ha v
  have hvx : ∀ e, TipBond ell M R hell0 hM e → (WithLp.ofLp (iE (geomOf ell 1 (gcS ell M R)) x)) e = 0 :=
    fun e he => hx e (tipBond_lvl0 hell hell0 hM hR e he)
  have hvx' : ∀ e, TipBond ell M R hell0 hM e → (WithLp.ofLp (iE (geomOf ell 1 (gcS ell M R)) x')) e = 0 :=
    fun e he => hx' e (tipBond_lvl0 hell hell0 hM hR e he)
  have h1 : ⟪x', (tipP ell M R hell0 hM v a Lam).data.Ginv x⟫ =
      ⟪Wop (geomOf ell 1 (gcS ell M R)) (Ut ell M R hell0 hM v) a (iE _ x'),
        Delta (geomOf ell 1 (gcS ell M R)) (Ut ell M R hell0 hM v)
          (Wop (geomOf ell 1 (gcS ell M R)) (Ut ell M R hell0 hM v) a (iE _ x))⟫ +
      ⟪Tfull (geomOf ell 1 (gcS ell M R)) (Ut ell M R hell0 hM v) (iE _ x'),
        Tfull (geomOf ell 1 (gcS ell M R)) (Ut ell M R hell0 hM v) (iE _ x)⟫ +
      ⟪iE _ x', MassFull (geomOf ell 1 (gcS ell M R)) a
        (bondSectorOf (geomOf ell 1 (gcS ell M R)) (Ut ell M R hell0 hM v)) (iE _ x)⟫ :=
    Ginv_bil (tipP ell M R hell0 hM v a Lam) x x'
  have h2 : ⟪x', (tipP ell M R hell0 hM 1 a Lam).data.Ginv x⟫ =
      ⟪Wop (geomOf ell 1 (gcS ell M R)) (Ut ell M R hell0 hM 1) a (iE _ x'),
        Delta (geomOf ell 1 (gcS ell M R)) (Ut ell M R hell0 hM 1)
          (Wop (geomOf ell 1 (gcS ell M R)) (Ut ell M R hell0 hM 1) a (iE _ x))⟫ +
      ⟪Tfull (geomOf ell 1 (gcS ell M R)) (Ut ell M R hell0 hM 1) (iE _ x'),
        Tfull (geomOf ell 1 (gcS ell M R)) (Ut ell M R hell0 hM 1) (iE _ x)⟫ +
      ⟪iE _ x', MassFull (geomOf ell 1 (gcS ell M R)) a
        (bondSectorOf (geomOf ell 1 (gcS ell M R)) (Ut ell M R hell0 hM 1)) (iE _ x)⟫ :=
    Ginv_bil (tipP ell M R hell0 hM 1 a Lam) x x'
  rw [h1, h2, hU1, hW, hT, hMass,
    tip_Delta_bil hell hell0 hM hR v _ _ (tip_W_vanish hell hell0 hM hR ha _ hvx) (tip_W_vanish hell hell0 hM hR ha _ hvx')]

end Tip

#print axioms Ut_one
#print axioms Gp_lapDir
#print axioms plaq_term_zero
#print axioms Ginv_bil
#print axioms tip_farAgree
#print axioms tipBond_far
#print axioms tipBond_lvl0
#print axioms tip_Wop_eq
#print axioms tip_W_vanish
#print axioms tip_Delta_form
#print axioms tip_Delta_bil
#print axioms tip_Ginv_compress

end AdalyFormal.CoverStrong
