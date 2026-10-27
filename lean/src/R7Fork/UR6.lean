import R7Fork.UR5
import R7Fork.UR2
import R7Fork.TargetContract

/-!
# UR6 -- the refutation pinned to the FROZEN contract file and propagated to every named variant.

* `frozen_P428Target6_false : ¬ TargetContract.P428Target6` (the export of `r7/fork/TargetContract.lean`).
* at every slab point `(2, 2^m, 2h)`, `m ≥ 1`, `h ≥ 6`, every `a > 0`: `¬ P428Genuine6`, `¬ P428Genuine6Print`,
  `¬ P428Genuine6Both`, `¬ P428Genuine6AllC`, `¬ P428Genuine6WD`; and `¬ P428Target6Unif`.
The core is `slab_coerc_false`: `CoercG6At 2 (2^m) (2h) 1 _ a (LuF ..) 12 α₀ γ₀` is false for every `α₀ > 0`, `γ₀ > 0`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.URLocality

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.FullReparamC (freeBond freeBond_coord_zero)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

theorem slabP_of (m h : ℕ) (hm : 1 ≤ m) (hh : 6 ≤ h) : SlabP (2 ^ m) h (12 * (h * 2 ^ m) + 16 * 2 ^ m) := by
  have hM2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  exact ⟨hM2, dvd_pow_self 2 (by omega), hh, rfl⟩

/-- the tower data of the slab point, common to all variants -/
theorem slab_data (m h : ℕ) (hm : 1 ≤ m) (hh : 6 ≤ h) {α₀ : ℝ} (hα : 0 < α₀) :
    let M := 2 ^ m
    TorusOK 2 M (LuF M h) ∧ Admissible 2 M (2 * h) 1 (SlabT (scaleUp 2 1 (LuF M h)) M (h * M)) ∧
    LambdaOK2 (Lu := LuF M h) 2 M (2 * h) 1 (SlabT (scaleUp 2 1 (LuF M h)) M (h * M)) (LamF (LuF M h) M h) ∧
    ClassCoupled 2 M 12 1 (SlabT (scaleUp 2 1 (LuF M h)) M (h * M)) α₀ (((2 : ℕ) : ℝ) ^ 1)⁻¹ (cfg1 su2NegOne) ∧
    (∀ μ, 4 ≤ scaleUp 2 1 (LuF M h) μ + 1) ∧
    ∃ p1 : BIdx (geomOf 2 1 (SlabT (scaleUp 2 1 (LuF M h)) M (h * M))), (p1.1 : ℕ) = 1 := by
  intro M
  have P := slabP_of m h hm hh
  have hf := fine_ext P
  have hadm := slab_admissible P hf
  have hb : (o0 : PeriodicLatticeSite (scaleUp 2 1 (LuF M h))) ∉ (SlabT (scaleUp 2 1 (LuF M h)) M (h * M)).Om 0 := by
    rw [slab_om0]; simp only [slabOm, Set.mem_setOf_eq, o0]; have := P.hM; omega
  refine ⟨slab_torusOK P, hadm, slab_lambdaOK2 P,
    classCoupled_bad_gen (ell := 2) (k := 1) (c := 12) hα (by norm_num) (by have := P.hM; omega) (by norm_num)
      (slab_coversp P hf) hadm.1 hb, fun μ => by rw [hf μ]; have := P.hM; omega, slab_level1 P⟩

theorem slab_coerc_false (m h : ℕ) (hm : 1 ≤ m) (hh : 6 ≤ h) {a α₀ γ₀ : ℝ} (ha : 0 < a) (hα : 0 < α₀) (hγ : 0 < γ₀) :
    ¬ CoercG6At 2 (2 ^ m) (2 * h) 1 (by norm_num) a (LuF (2 ^ m) h) 12 α₀ γ₀ := by
  intro hc
  obtain ⟨hT, hadm, hLam, hcl, h4, p1, hp1⟩ := slab_data m h hm hh hα
  obtain ⟨Bt, h1, h2, -, hE⟩ := slab_seed (slabP_of m h hm hh)
  exact instIneq_bad_false_gen h4 _ a _ (by norm_num) p1 hp1 ha hγ Bt h1 h2 hE (hc hT _ hadm _ hLam _ hcl)

theorem slab_coercBoth_false (m h : ℕ) (hm : 1 ≤ m) (hh : 6 ≤ h) {a α₀ γ₀ : ℝ} (ha : 0 < a) (hα : 0 < α₀) (hγ : 0 < γ₀) :
    ¬ CoercG6AtBoth 2 (2 ^ m) (2 * h) 1 (by norm_num) a (LuF (2 ^ m) h) 12 α₀ γ₀ := by
  intro hc
  obtain ⟨hT, hadm, hLam, hcl, h4, p1, hp1⟩ := slab_data m h hm hh hα
  obtain ⟨Bt, h1, -, h3, hE⟩ := slab_seed (slabP_of m h hm hh)
  have hI := hc hT _ hadm _ hLam _ hcl Bt h1 h3
  have hg := genForm_bad_gen h4 _ a (LamF (LuF (2 ^ m) h) (2 ^ m) h) (by norm_num) p1 hp1
    (WithLp.toLp 2 (GenP.genC (Pg (SlabT (scaleUp 2 1 (LuF (2 ^ m) h)) (2 ^ m) (h * 2 ^ m)) a
      (LamF (LuF (2 ^ m) h) (2 ^ m) h) (by norm_num)) Bt))
  have hpos := real_inner_self_nonneg (x := (WithLp.toLp 2 (GenP.genC (Pg (SlabT (scaleUp 2 1 (LuF (2 ^ m) h))
      (2 ^ m) (h * 2 ^ m)) a (LamF (LuF (2 ^ m) h) (2 ^ m) h) (by norm_num)) Bt) : BondFnL2 (LuF (2 ^ m) h)))
  have hb : GenP.genForm (Pg (SlabT (scaleUp 2 1 (LuF (2 ^ m) h)) (2 ^ m) (h * 2 ^ m)) a (LamF (LuF (2 ^ m) h) (2 ^ m) h)
      (by norm_num)) (WithLp.toLp 2 (GenP.genC (Pg (SlabT (scaleUp 2 1 (LuF (2 ^ m) h)) (2 ^ m) (h * 2 ^ m)) a
      (LamF (LuF (2 ^ m) h) (2 ^ m) h) (by norm_num)) Bt)) ≤ 0 := by rw [hg]; nlinarith
  have : 0 < γ₀ * bondEnergy Bt := mul_pos hγ hE
  exact absurd (lt_of_lt_of_le this hI) (not_lt.mpr hb)

/-- unpack the `a₀`, take `α₀ = a₀ / (12 M)` -/
theorem alpha_ok (m : ℕ) {a₀ : ℝ} (ha₀ : 0 < a₀) :
    0 < a₀ / (12 * ((2 ^ m : ℕ) : ℝ)) ∧ (12 : ℝ) * ((2 ^ m : ℕ) : ℝ) * (a₀ / (12 * ((2 ^ m : ℕ) : ℝ))) ≤ a₀ := by
  have hM : (0 : ℝ) < ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast pow_pos (by norm_num : 0 < 2) m
  have h12 : (0 : ℝ) < 12 * ((2 ^ m : ℕ) : ℝ) := mul_pos (by norm_num) hM
  refine ⟨div_pos ha₀ h12, le_of_eq ?_⟩
  field_simp

theorem not_Print_slab (m h : ℕ) (hm : 1 ≤ m) (hh : 6 ≤ h) (a : ℝ) (ha : 0 < a) :
    ¬ P428Genuine6Print 2 (2 ^ m) (2 * h) (by norm_num) a := by
  rintro ⟨-, a₀, ha₀, hL⟩
  obtain ⟨γ₀, hγ, hc⟩ := hL (LuF (2 ^ m) h)
  obtain ⟨hα, hαb⟩ := alpha_ok m ha₀
  exact slab_coerc_false m h hm hh ha hα hγ (hc 1 le_rfl _ hα (by exact_mod_cast hαb))

theorem not_Both_slab (m h : ℕ) (hm : 1 ≤ m) (hh : 6 ≤ h) (a : ℝ) (ha : 0 < a) :
    ¬ P428Genuine6Both 2 (2 ^ m) (2 * h) (by norm_num) a := by
  rintro ⟨-, a₀, ha₀, γ₀, hγ, hc⟩
  obtain ⟨hα, hαb⟩ := alpha_ok m ha₀
  exact slab_coercBoth_false m h hm hh ha hα hγ (hc 1 le_rfl _ _ hα (by exact_mod_cast hαb))

theorem not_AllC_slab (m h : ℕ) (hm : 1 ≤ m) (hh : 6 ≤ h) (a : ℝ) (ha : 0 < a) :
    ¬ P428Genuine6AllC 2 (2 ^ m) (2 * h) (by norm_num) a :=
  fun H => not_P428Genuine6_slab m h hm hh a ha H.toHead

theorem not_WD_slab (m h : ℕ) (hm : 1 ≤ m) (hh : 6 ≤ h) (a : ℝ) (ha : 0 < a) :
    ¬ P428Genuine6WD 2 (2 ^ m) (2 * h) (by norm_num) a :=
  fun H => not_P428Genuine6_slab m h hm hh a ha H.toHead

theorem not_P428Target6Unif : ¬ P428Target6Unif := fun H => not_P428Target6 H.toTarget

/-- **pinned to the frozen contract file** (`statement_lane_20261009_r7/fork/TargetContract.lean`, `export`) -/
theorem frozen_P428Target6_false : ¬ TargetContract.P428Target6 := not_P428Target6

theorem frozen_P428Genuine6_false_TT (a : ℝ) (ha : 0 < a) : ¬ TargetContract.P428Genuine6 2 2 6 (by norm_num) a :=
  not_P428Genuine6_TT a ha

#print axioms slab_coerc_false
#print axioms slab_coercBoth_false
#print axioms not_Print_slab
#print axioms not_Both_slab
#print axioms not_AllC_slab
#print axioms not_WD_slab
#print axioms not_P428Target6Unif
#print axioms frozen_P428Target6_false
#print axioms frozen_P428Genuine6_false_TT

end AdalyFormal.URLocality
