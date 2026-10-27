import SoZ1
import NuU2
import NuU1

/-!
# NuU2 -- units along the dir-0 staggered path at `ell = 2`: nesting, `gOf ≠ 0`, analytic proxy, `WellDefG` off a discrete set (lane ncwdh_ell2_20261018)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3

namespace AdalyFormal.SitesOnly

open AdalyFormal.NcwdhTwo

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
variable {C : ℕ} (hCp : CPos ell M R C)
include hCp

omit hCp in
/-- the structural proxy along the dir-0 staggered path. -/
noncomputable def DsP (ell M R C : ℕ) (hell : 0 < ell) (a t : ℝ) : ℝ :=
  DstructP (gparams ell 2 (neLu M R) hell (neS ell M R) (stag0Cfg (C) t) a (neLam M R))

theorem dsP_analytic (hell2 : 2 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) {a : ℝ} (ha : 0 < a) :
    AnalyticOnNhd ℝ (DsP ell M R C (by omega) a) (Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
  intro t0 ht0
  have htπ : |t0| < Real.pi / 2 := abs_lt.2 ⟨ht0.1, ht0.2⟩
  have S := nested_z0Setup_S hCp hell2 hE hdvd hM hR t0 htπ
  have hell : 0 < ell := by omega
  have hNN : ell * ell ≤ scaleUp ell 2 (neLu M R) 0 + 1 := by have := S.z.hc2; omega
  have hxs2' : C + ell ≤ scaleUp ell 2 (neLu M R) 0 + 1 := by
    have := S.z.hc2; nlinarith [Nat.le_mul_self ell]
  have hT := tower_stag0_ana (Lu := neLu M R) (neS ell M R) hell hE S.z.hc1 hxs2' hNN htπ
  have hU : LinkEA (fun t => stag0Cfg (L := scaleUp ell 2 (neLu M R)) (C) t) t0 :=
    LinkEA_of_AnaFam (hT.1 0 (by norm_num))
  have hJ := JfOf_analytic hU (plaqIn (geomOf ell 2 (neS ell M R)).Om0)
  have hout := out_nested_two hell2 hM hR
  exact DstructG_analytic (geomOf ell 2 (neS ell M R)) (fun t => stag0Cfg (L := scaleUp ell 2 (neLu M R)) (C) t) hT
    (le_refl 2) ha (by show 2 ≤ ell; omega) hout _ hJ

theorem dsP_ne_zero_of_units (hell2 : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) (a t : ℝ)
    (hu : UnitsFour (gparams ell 2 (neLu M R) (by omega) (neS ell M R) (stag0Cfg (C) t) a (neLam M R))) :
    DsP ell M R C (by omega) a t ≠ 0 :=
  (DstructP_ne_iff _ (out_nested_two hell2 hM hR)).mpr ⟨gOf_ne_zero_two hell2 hM hR _, hu⟩

theorem units_of_dsP_ne_zero (hell2 : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) (a t : ℝ) (h : DsP ell M R C (by omega) a t ≠ 0) :
    UnitsFour (gparams ell 2 (neLu M R) (by omega) (neS ell M R) (stag0Cfg (C) t) a (neLam M R)) :=
  ((DstructP_ne_iff _ (out_nested_two hell2 hM hR)).mp h).2

/-- `H0` is bijective along the whole path (the unit background is temporal with zero angles). -/
theorem H0_bij_path (hell2 : 2 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (t a : ℝ) (ht : |t| < Real.pi / 2) :
    Function.Bijective (H0 (neLam M R) (gparams ell 2 (neLu M R) (by omega) (neS ell M R) (stag0Cfg (C) t) a (neLam M R)).Q1) := by
  have hell : 0 < ell := by omega
  have S := nested_z0Setup_S hCp hell2 hE hdvd hM hR t ht
  have hNN : ell ≤ scaleUp ell 2 (neLu M R) 0 + 1 := by have := S.z.hc2; nlinarith [Nat.le_mul_self ell]
  have hxs2' : C + ell ≤ scaleUp ell 2 (neLu M R) 0 + 1 := by
    have := S.z.hc2; nlinarith [Nat.le_mul_self ell]
  have hT := unit_temporal_stag0 (Lu := neLu M R) hell hE t ht S.z.hc1 hxs2' hNN
  exact H0_temporal_bijective hell (unit_hdiv hdvd hM) (neLam M R) hT (by simp)

theorem wellDefG_of_dsP (hell2 : 2 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) {a : ℝ} (ha : 0 < a) (t : ℝ)
    (ht : |t| < Real.pi / 2) (h : DsP ell M R C (by omega) a t ≠ 0) :
    GenP.WellDefG (gparams ell 2 (neLu M R) (by omega) (neS ell M R) (stag0Cfg (C) t) a (neLam M R)) := by
  have hu := units_of_dsP_ne_zero hCp hell2 hM hR a t h
  have hH := H0_bij_path hCp hell2 hE hdvd hM hR t a ht
  exact ⟨⟨hH, hu.1, hu.2.1⟩, delpA_unit (geomOf ell 2 (neS ell M R)) (stag0Cfg (C) t) ha (by show 2 ≤ ell; omega)
    (out_nested_two hell2 hM hR), hu.2.2.1, hu.2.2.2⟩

/-- **units off a discrete set**: if `DsP` is nonzero at `t = 0`, then around every `ts ∈ (-π/2, π/2)` there is a punctured neighbourhood
on which the printed objects exist. -/
theorem wellDefG_punctured (hell2 : 2 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) {a : ℝ} (ha : 0 < a)
    (h0 : UnitsFour (gparams ell 2 (neLu M R) (by omega) (neS ell M R) (stag0Cfg (C) 0) a (neLam M R)))
    {ts : ℝ} (hts : |ts| < Real.pi / 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, t ≠ ts → |t - ts| < δ →
      |t| < Real.pi / 2 ∧ GenP.WellDefG (gparams ell 2 (neLu M R) (by omega) (neS ell M R) (stag0Cfg (C) t) a (neLam M R)) := by
  have hana := dsP_analytic hCp hell2 hE hdvd hM hR ha
  have hD0 : DsP ell M R C (by omega) a 0 ≠ 0 := dsP_ne_zero_of_units hCp hell2 hM hR a 0 h0
  have hI : IsOpen (Ioo (-(Real.pi / 2)) (Real.pi / 2)) := isOpen_Ioo
  have hmem : ts ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := abs_lt.1 hts
  have h00 : (0 : ℝ) ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by constructor <;> linarith [Real.pi_pos]
  rcases (hana ts hmem).eventually_eq_zero_or_eventually_ne_zero with hz | hnz
  · exfalso
    have := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Ioo hmem hz
    exact hD0 (this h00)
  · have h1 : ∀ᶠ t in 𝓝 ts, t ≠ ts → DsP ell M R C (by omega) a t ≠ 0 := by
      filter_upwards [eventually_nhdsWithin_iff.mp hnz] with t ht hne
      exact ht hne
    have h2 : ∀ᶠ t in 𝓝 ts, t ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := hI.mem_nhds hmem
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp (h1.and h2)
    refine ⟨δ, hδ, fun t hne hlt => ?_⟩
    have hb := hδ' (by simpa [Real.dist_eq] using hlt)
    have htI := hb.2
    have htabs : |t| < Real.pi / 2 := abs_lt.2 ⟨htI.1, htI.2⟩
    exact ⟨htabs, wellDefG_of_dsP hCp hell2 hE hdvd hM hR ha t htabs (hb.1 hne)⟩

end

#print axioms DsP
#print axioms dsP_analytic
#print axioms dsP_ne_zero_of_units
#print axioms units_of_dsP_ne_zero
#print axioms H0_bij_path
#print axioms wellDefG_of_dsP
#print axioms wellDefG_punctured

end AdalyFormal.SitesOnly
