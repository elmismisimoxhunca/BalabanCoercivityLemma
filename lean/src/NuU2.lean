import NuU1

/-!
# NuU2 -- units along the dir-0 staggered path at `ell = 2`: nesting, `gOf ≠ 0`, analytic proxy, `WellDefG` off a discrete set (lane ncwdh_ell2_20261018)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3

namespace AdalyFormal.NcwdhTwo

open scoped Matrix Matrix.Norms.Frobenius RealInnerProductSpace
open Filter Topology Set
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverOmega
open AdalyFormal.CoverOmega.Struct
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (scaleUp Tower)
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG

section
variable [CfData]
variable {ell M R : ℕ}

theorem neS_nested_two (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) :
    ∀ j j', j' ≤ j → (neS ell M R).Om j ⊆ (neS ell M R).Om j' := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin_two hell hM hR
  intro j j' hjj x hx
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ 3 ≤ j by omega) with rfl | rfl | rfl | h3
  · have : j' = 0 := by omega
    subst this; exact hx
  · rcases (show j' = 0 ∨ j' = 1 by omega) with rfl | rfl
    · rw [neS_om1] at hx; rw [neS_om0]
      simp only [neP0, neP1, neQ0, neQ1, neA', neB, neB', neA] at hx ⊢; omega
    · exact hx
  · rcases (show j' = 0 ∨ j' = 1 ∨ j' = 2 by omega) with rfl | rfl | rfl
    · rw [neS_om2] at hx; rw [neS_om0]
      simp only [neP0, neP1, neQ0, neQ1, neA', neB, neB', neA] at hx ⊢; omega
    · rw [neS_om2] at hx; rw [neS_om1]
      simp only [neP0, neP1, neQ0, neQ1, neA', neB, neB', neA] at hx ⊢; omega
    · exact hx
  · exact absurd hx (tw3_omHi j h3 x)

theorem out_nested_two (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) :
    ∃ x : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)), x ∉ (geomOf ell 2 (neS ell M R)).Om0 := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin_two hell hM hR
  refine ⟨fun _ => 0, fun hmem => ?_⟩
  simp only [geomOf, Set.mem_setOf_eq] at hmem
  have h0 := ((neS_om0 (ell := ell) (M := M) (R := R) (fun _ => 0)).mp hmem).1
  have hp : 1 ≤ neP0 ell M R := by simp only [neP0, neP1, neA']; omega
  simp at h0
  omega

theorem gOf_ne_zero_two (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) (U : Cfg (scaleUp ell 2 (neLu M R))) :
    gOf (geomOf ell 2 (neS ell M R)) U ≠ 0 := by
  obtain ⟨hal, h0, hdisj⟩ := geomOf_conds ell 2 (neS ell M R) (neS_nested_two hell hM hR)
  exact gOf_ne_zero _ _ (show 0 < ell by omega) hal h0 hdisj (out_nested_two hell hM hR)

/-- the structural proxy along the dir-0 staggered path. -/
noncomputable def DsP (ell M R : ℕ) (hell : 0 < ell) (a t : ℝ) : ℝ :=
  DstructP (gparams ell 2 (neLu M R) hell (neS ell M R) (stag0Cfg (neC0 ell M R) t) a (neLam M R))

theorem dsP_analytic (hell2 : 2 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) {a : ℝ} (ha : 0 < a) :
    AnalyticOnNhd ℝ (DsP ell M R (by omega) a) (Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
  intro t0 ht0
  have htπ : |t0| < Real.pi / 2 := abs_lt.2 ⟨ht0.1, ht0.2⟩
  have S := nested_z0Setup hell2 hE hdvd hM hR t0 htπ
  have hell : 0 < ell := by omega
  have hNN : ell * ell ≤ scaleUp ell 2 (neLu M R) 0 + 1 := by have := S.z.hc2; omega
  have hxs2' : neC0 ell M R + ell ≤ scaleUp ell 2 (neLu M R) 0 + 1 := by
    have := S.z.hc2; nlinarith [Nat.le_mul_self ell]
  have hT := tower_stag0_ana (Lu := neLu M R) (neS ell M R) hell hE S.z.hc1 hxs2' hNN htπ
  have hU : LinkEA (fun t => stag0Cfg (L := scaleUp ell 2 (neLu M R)) (neC0 ell M R) t) t0 :=
    LinkEA_of_AnaFam (hT.1 0 (by norm_num))
  have hJ := JfOf_analytic hU (plaqIn (geomOf ell 2 (neS ell M R)).Om0)
  have hout := out_nested_two hell2 hM hR
  exact DstructG_analytic (geomOf ell 2 (neS ell M R)) (fun t => stag0Cfg (L := scaleUp ell 2 (neLu M R)) (neC0 ell M R) t) hT
    (le_refl 2) ha (by show 2 ≤ ell; omega) hout _ hJ

theorem dsP_ne_zero_of_units (hell2 : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) (a t : ℝ)
    (hu : UnitsFour (gparams ell 2 (neLu M R) (by omega) (neS ell M R) (stag0Cfg (neC0 ell M R) t) a (neLam M R))) :
    DsP ell M R (by omega) a t ≠ 0 :=
  (DstructP_ne_iff _ (out_nested_two hell2 hM hR)).mpr ⟨gOf_ne_zero_two hell2 hM hR _, hu⟩

theorem units_of_dsP_ne_zero (hell2 : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) (a t : ℝ) (h : DsP ell M R (by omega) a t ≠ 0) :
    UnitsFour (gparams ell 2 (neLu M R) (by omega) (neS ell M R) (stag0Cfg (neC0 ell M R) t) a (neLam M R)) :=
  ((DstructP_ne_iff _ (out_nested_two hell2 hM hR)).mp h).2

/-- `H0` is bijective along the whole path (the unit background is temporal with zero angles). -/
theorem H0_bij_path (hell2 : 2 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (t a : ℝ) (ht : |t| < Real.pi / 2) :
    Function.Bijective (H0 (neLam M R) (gparams ell 2 (neLu M R) (by omega) (neS ell M R) (stag0Cfg (neC0 ell M R) t) a (neLam M R)).Q1) := by
  have hell : 0 < ell := by omega
  have S := nested_z0Setup hell2 hE hdvd hM hR t ht
  have hNN : ell ≤ scaleUp ell 2 (neLu M R) 0 + 1 := by have := S.z.hc2; nlinarith [Nat.le_mul_self ell]
  have hxs2' : neC0 ell M R + ell ≤ scaleUp ell 2 (neLu M R) 0 + 1 := by
    have := S.z.hc2; nlinarith [Nat.le_mul_self ell]
  have hT := unit_temporal_stag0 (Lu := neLu M R) hell hE t ht S.z.hc1 hxs2' hNN
  exact H0_temporal_bijective hell (unit_hdiv hdvd hM) (neLam M R) hT (by simp)

theorem wellDefG_of_dsP (hell2 : 2 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) {a : ℝ} (ha : 0 < a) (t : ℝ)
    (ht : |t| < Real.pi / 2) (h : DsP ell M R (by omega) a t ≠ 0) :
    GenP.WellDefG (gparams ell 2 (neLu M R) (by omega) (neS ell M R) (stag0Cfg (neC0 ell M R) t) a (neLam M R)) := by
  have hu := units_of_dsP_ne_zero hell2 hM hR a t h
  have hH := H0_bij_path hell2 hE hdvd hM hR t a ht
  exact ⟨⟨hH, hu.1, hu.2.1⟩, delpA_unit (geomOf ell 2 (neS ell M R)) (stag0Cfg (neC0 ell M R) t) ha (by show 2 ≤ ell; omega)
    (out_nested_two hell2 hM hR), hu.2.2.1, hu.2.2.2⟩

/-- **units off a discrete set**: if `DsP` is nonzero at `t = 0`, then around every `ts ∈ (-π/2, π/2)` there is a punctured neighbourhood
on which the printed objects exist. -/
theorem wellDefG_punctured (hell2 : 2 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) {a : ℝ} (ha : 0 < a)
    (h0 : UnitsFour (gparams ell 2 (neLu M R) (by omega) (neS ell M R) (stag0Cfg (neC0 ell M R) 0) a (neLam M R)))
    {ts : ℝ} (hts : |ts| < Real.pi / 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, t ≠ ts → |t - ts| < δ →
      |t| < Real.pi / 2 ∧ GenP.WellDefG (gparams ell 2 (neLu M R) (by omega) (neS ell M R) (stag0Cfg (neC0 ell M R) t) a (neLam M R)) := by
  have hana := dsP_analytic hell2 hE hdvd hM hR ha
  have hD0 : DsP ell M R (by omega) a 0 ≠ 0 := dsP_ne_zero_of_units hell2 hM hR a 0 h0
  have hI : IsOpen (Ioo (-(Real.pi / 2)) (Real.pi / 2)) := isOpen_Ioo
  have hmem : ts ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := abs_lt.1 hts
  have h00 : (0 : ℝ) ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by constructor <;> linarith [Real.pi_pos]
  rcases (hana ts hmem).eventually_eq_zero_or_eventually_ne_zero with hz | hnz
  · exfalso
    have := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Ioo hmem hz
    exact hD0 (this h00)
  · have h1 : ∀ᶠ t in 𝓝 ts, t ≠ ts → DsP ell M R (by omega) a t ≠ 0 := by
      filter_upwards [eventually_nhdsWithin_iff.mp hnz] with t ht hne
      exact ht hne
    have h2 : ∀ᶠ t in 𝓝 ts, t ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := hI.mem_nhds hmem
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp (h1.and h2)
    refine ⟨δ, hδ, fun t hne hlt => ?_⟩
    have hb := hδ' (by simpa [Real.dist_eq] using hlt)
    have htI := hb.2
    have htabs : |t| < Real.pi / 2 := abs_lt.2 ⟨htI.1, htI.2⟩
    exact ⟨htabs, wellDefG_of_dsP hell2 hE hdvd hM hR ha t htabs (hb.1 hne)⟩

end

end AdalyFormal.NcwdhTwo
