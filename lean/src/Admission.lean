import CurvedReproduced
set_option autoImplicit false
noncomputable section
namespace HConstruction.NfRepair
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL)
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.RMapLipschitz
open AdalyFormal.Balaban.SuTwoLogExp (M2 SU2)
open AdalyFormal.Balaban.RegularityHolonomy
open Reproduced

/-- The bridge norm and the frozen regularity defect agree exactly, not just up to a constant. -/
theorem frobSq_sub_one (X : SU2) :
    frobSq ((X : M2) - 1) = 4 - 2 * (Matrix.trace (X : M2)).re := by
  have hu : (X : M2) * (X : M2).conjTranspose = 1 := by
    have h := (Matrix.mem_specialUnitaryGroup_iff.mp X.property).1
    simpa only [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] using h
  rw [frobSq_eq_trace, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    sub_mul, mul_sub, mul_sub, hu]
  simp [Matrix.trace_sub, Matrix.trace_conjTranspose]
  ring

theorem frobNorm_holonomy (U : PeriodicLinkConfiguration SU2 witnessL)
    (p : PeriodicLatticePlaquette witnessL) :
    frobNorm ((holonomyElem U p : M2) - 1) = Real.sqrt (holonomyDefectSq U p) := by
  rw [frobNorm, frobSq_sub_one]
  rfl

/-- A gauge change cannot shrink the plaquette defect. -/
theorem defect_gauge (U : PeriodicLinkConfiguration SU2 witnessL)
    (g : PeriodicLatticeSite witnessL → SU2) (p : PeriodicLatticePlaquette witnessL) :
    holonomyDefectSq (periodicGaugeTransform g U) p = holonomyDefectSq U p := by
  unfold holonomyDefectSq
  rw [holonomyElem_periodicGaugeTransform]
  have ht : Matrix.trace (((g p.1 * holonomyElem U p * (g p.1)⁻¹ : SU2) : M2)) =
      Matrix.trace ((holonomyElem U p : SU2) : M2) := by
    change Matrix.trace (((g p.1 : SU2) : M2) * (holonomyElem U p : M2) *
      (((g p.1)⁻¹ : SU2) : M2)) = _
    rw [Matrix.trace_mul_cycle]
    have h : ((((g p.1)⁻¹ : SU2) : M2) * ((g p.1 : SU2) : M2)) = 1 := by
      exact congrArg (fun x : SU2 => (x : M2)) (inv_mul_cancel (g p.1))
    rw [h, one_mul]
  rw [ht]

theorem regular_gauge_iff (U : PeriodicLinkConfiguration SU2 witnessL)
    (g : PeriodicLatticeSite witnessL → SU2) (m : ℝ) :
    IsRegularHolonomy (periodicGaugeTransform g U) m ↔ IsRegularHolonomy U m := by
  unfold IsRegularHolonomy
  simp only [defect_gauge]

theorem witness_regular_gauge_iff (g : PeriodicLatticeSite witnessL → SU2) (m : ℝ) :
    IsRegularHolonomy (periodicGaugeTransform g witnessU) m ↔ 4 ≤ m := by
  rw [regular_gauge_iff, HConstruction.Nonflat.witness_regular_iff]

/-- This names exactly the certified bridge's global plaquette input. -/
def PlaquetteBound (U : PeriodicLinkConfiguration SU2 witnessL) (eps : ℝ) : Prop :=
  ∀ p, frobNorm ((periodicPlaquetteHolonomy (G := SU2) U p : M2) - 1) ≤ eps

theorem plaquetteBound_gauge_iff (U : PeriodicLinkConfiguration SU2 witnessL)
    (g : PeriodicLatticeSite witnessL → SU2) (eps : ℝ) :
    PlaquetteBound (periodicGaugeTransform g U) eps ↔ PlaquetteBound U eps := by
  change (∀ p, frobNorm ((holonomyElem (periodicGaugeTransform g U) p : M2) - 1) ≤ eps) ↔
    (∀ p, frobNorm ((holonomyElem U p : M2) - 1) ≤ eps)
  simp only [frobNorm_holonomy, defect_gauge]

/-- Two is not merely a lower bound: it is the attained optimal uniform bound. -/
theorem witness_plaquetteBound_iff (eps : ℝ) : PlaquetteBound witnessU eps ↔ 2 ≤ eps := by
  constructor
  · exact HConstruction.Nonflat.witness_plaquette_bound_requires_two eps
  · intro he p
    change frobNorm ((holonomyElem witnessU p : M2) - 1) ≤ eps
    rw [frobNorm_holonomy]
    have hr : holonomyDefectSq witnessU p ≤ 4 :=
      (HConstruction.Nonflat.witness_regular_iff 4).mpr le_rfl p
    have hs := Real.sqrt_le_sqrt hr
    norm_num at hs
    exact hs.trans he

theorem witness_gauge_plaquetteBound_iff (g : PeriodicLatticeSite witnessL → SU2) (eps : ℝ) :
    PlaquetteBound (periodicGaugeTransform g witnessU) eps ↔ 2 ≤ eps := by
  rw [plaquetteBound_gauge_iff, witness_plaquetteBound_iff]

theorem cap_radius_iff (eps : ℝ) :
    HConstruction.Nonflat.Reproduced.loopRhoPlaqCap eps 2 < Real.pi / 2 ↔ eps < 1/3 := by
  norm_num [HConstruction.Nonflat.Reproduced.loopRhoPlaqCap,
    HConstruction.Nonflat.Reproduced.loopSurfaceBound]
  constructor <;> intro h <;> nlinarith [Real.pi_pos]

theorem radius_iff (eps : ℝ) :
    HConstruction.Nonflat.Reproduced.loopRhoPlaq eps 2 < Real.pi / 2 ↔
      6 * eps < Real.sqrt 2 := by
  norm_num [HConstruction.Nonflat.Reproduced.loopRhoPlaq,
    HConstruction.Nonflat.Reproduced.loopSurfaceBound]
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hp := Real.pi_pos
  constructor <;> intro h
  · have h' : Real.pi * (6 * eps) / (2 * Real.sqrt 2) < Real.pi / 2 := by
      convert h using 1 <;> ring
    have hh := (div_lt_iff₀ (by positivity : 0 < 2 * Real.sqrt (2 : ℝ))).mp h'
    nlinarith
  · have h' : Real.pi * (6 * eps) / (2 * Real.sqrt 2) < Real.pi / 2 := by
      apply (div_lt_iff₀ (by positivity : 0 < 2 * Real.sqrt (2 : ℝ))).mpr
      nlinarith
    convert h' using 1 <;> ring

/-- Changing the gauge cannot repair either of witnessU's certified radius inputs. -/
theorem witness_no_gauge_admission :
    ¬ ∃ (g : PeriodicLatticeSite witnessL → SU2) (eps : ℝ),
      PlaquetteBound (periodicGaugeTransform g witnessU) eps ∧
      (HConstruction.Nonflat.Reproduced.loopRhoPlaqCap eps 2 < Real.pi / 2 ∨
       HConstruction.Nonflat.Reproduced.loopRhoPlaq eps 2 < Real.pi / 2) := by
  rintro ⟨g, eps, hb, hc | hu⟩
  · have he := (witness_gauge_plaquetteBound_iff g eps).mp hb
    have hs := (cap_radius_iff eps).mp hc
    linarith
  · have he := (witness_gauge_plaquetteBound_iff g eps).mp hb
    have hs := (radius_iff eps).mp hu
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]

/-- Exact uniform Frobenius threshold throughout the frozen single-bond family. -/
theorem nonflatU_plaquetteBound_iff (t eps : ℝ) :
    PlaquetteBound (nonflatU t) eps ↔ Real.sqrt (8 * t^2 / (1+t^2)) ≤ eps := by
  constructor
  · intro h
    have hp := h witnessPlaquette
    change frobNorm ((holonomyElem (nonflatU t) witnessPlaquette : M2) - 1) ≤ eps at hp
    rwa [holonomyElem_nonflatU_witnessPlaquette, frobNorm, rotElem_coe,
      frobSq_rotM_sub_one] at hp
  · intro h p
    change frobNorm ((holonomyElem (nonflatU t) p : M2) - 1) ≤ eps
    rw [frobNorm_holonomy]
    exact (Real.sqrt_le_sqrt (nonflatU_isRegularHolonomy t p)).trans h

/-- Sharp parameter interval for this certificate, NOT for coercivity. -/
theorem nonflatU_cap_admission_iff (t : ℝ) :
    (∃ eps : ℝ, PlaquetteBound (nonflatU t) eps ∧
      HConstruction.Nonflat.Reproduced.loopRhoPlaqCap eps 2 < Real.pi / 2) ↔
      71 * t^2 < 1 := by
  have hd : 0 < 1 + t^2 := by positivity
  have hn : 0 ≤ 8 * t^2 / (1+t^2) := by positivity
  have hs := Real.sq_sqrt hn
  have hz := Real.sqrt_nonneg (8 * t^2 / (1+t^2))
  constructor
  · rintro ⟨eps, hb, hr⟩
    have hb' := (nonflatU_plaquetteBound_iff t eps).mp hb
    have he := (cap_radius_iff eps).mp hr
    have hsmall : 8 * t^2 / (1+t^2) < (1/9 : ℝ) := by nlinarith
    have hmul := (div_lt_iff₀ hd).mp hsmall
    nlinarith
  · intro ht
    have hsmall : 8 * t^2 / (1+t^2) < (1/9 : ℝ) := by
      apply (div_lt_iff₀ hd).mpr
      nlinarith
    refine ⟨Real.sqrt (8 * t^2 / (1+t^2)),
      (nonflatU_plaquetteBound_iff t _).mpr le_rfl, ?_⟩
    rw [cap_radius_iff]
    nlinarith

/-- The uncapped route's smaller sharp interval, with no unspecified smallness. -/
theorem nonflatU_admission_iff (t : ℝ) :
    (∃ eps : ℝ, PlaquetteBound (nonflatU t) eps ∧
      HConstruction.Nonflat.Reproduced.loopRhoPlaq eps 2 < Real.pi / 2) ↔
      143 * t^2 < 1 := by
  have hd : 0 < 1 + t^2 := by positivity
  have hn : 0 ≤ 8 * t^2 / (1+t^2) := by positivity
  have hs := Real.sq_sqrt hn
  have hz := Real.sqrt_nonneg (8 * t^2 / (1+t^2))
  have h2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hz2 := Real.sqrt_nonneg (2 : ℝ)
  constructor
  · rintro ⟨eps, hb, hr⟩
    have hb' := (nonflatU_plaquetteBound_iff t eps).mp hb
    have he := (radius_iff eps).mp hr
    have he0 : 0 ≤ eps := hz.trans hb'
    have hsmall : 8 * t^2 / (1+t^2) < (1/18 : ℝ) := by nlinarith
    have hmul := (div_lt_iff₀ hd).mp hsmall
    nlinarith
  · intro ht
    have hsmall : 8 * t^2 / (1+t^2) < (1/18 : ℝ) := by
      apply (div_lt_iff₀ hd).mpr
      nlinarith
    refine ⟨Real.sqrt (8 * t^2 / (1+t^2)),
      (nonflatU_plaquetteBound_iff t _).mpr le_rfl, ?_⟩
    rw [radius_iff]
    nlinarith

theorem nonflatU_one_eq_witnessU : nonflatU 1 = witnessU := by
  have hr : rotElem 1 = witnessMElem := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [rotElem, rotM, rotA, rotB, witnessMElem, witnessM]
  rw [nonflatU, hr]
  exact AdalyFormal.Balaban.NormalizedCounterexampleSearch.singleBondU_witnessMElem_eq_witnessU

/-- A separate, explicitly changed background. This is NOT witnessU. -/
noncomputable def smallCurvedU : PeriodicLinkConfiguration SU2 witnessL := nonflatU (1/16)

theorem smallCurvedU_curved : holonomyElem smallCurvedU witnessPlaquette ≠ (1 : SU2) :=
  nonflatU_curvature_ne_one (by norm_num : (1/16 : ℝ) ≠ 0)

theorem smallCurvedU_regular : IsRegularHolonomy smallCurvedU (8/257 : ℝ) := by
  have h := nonflatU_isRegularHolonomy (1/16 : ℝ)
  norm_num at h
  exact h

theorem smallCurvedU_plaquette_bound : PlaquetteBound smallCurvedU (1/5 : ℝ) := by
  intro p
  change frobNorm ((holonomyElem smallCurvedU p : M2) - 1) ≤ (1/5 : ℝ)
  rw [frobNorm_holonomy]
  have h := Real.sqrt_le_sqrt (smallCurvedU_regular p)
  have hs : Real.sqrt (8/257 : ℝ) ≤ (1/5 : ℝ) := by
    have he := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8/257)
    nlinarith [Real.sqrt_nonneg (8/257 : ℝ)]
  exact h.trans hs

/-- Both numeric bridge gates have a concrete small curved input on the same lattice.
No claim here of (3.35)-(3.36), a physical covariance, or coercivity at this different U. -/
theorem smallCurvedU_radius_admission :
    PlaquetteBound smallCurvedU (1/5 : ℝ) ∧
    (0 : ℝ) < 1/5 ∧ (1/5 : ℝ) ≤ 2 ∧
    HConstruction.Nonflat.Reproduced.loopRhoPlaqCap (1/5 : ℝ) 2 < Real.pi / 2 ∧
    HConstruction.Nonflat.Reproduced.loopRhoPlaq (1/5 : ℝ) 2 < Real.pi / 2 := by
  refine ⟨smallCurvedU_plaquette_bound, by norm_num, by norm_num, ?_, ?_⟩
  · rw [cap_radius_iff]; norm_num
  · rw [radius_iff]
    have he := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]

theorem smallCurvedU_not_witnessU : smallCurvedU ≠ witnessU := by
  intro h
  have hb := smallCurvedU_plaquette_bound
  rw [h, witness_plaquetteBound_iff] at hb
  norm_num at hb
end HConstruction.NfRepair
