import R7Fork.UR4
import R7Fork.DM14

/-!
# UR5 -- the refutation for ALL large `M`, `R`: `¬ P428Target6`.

Generic part (any unit torus `Lu` whose fine torus has `≥ 4` sites per direction, any tower `S` of height `k = 1` with a level-1
bond in `𝔅`, any `Λ`): at `Ubad = cfg1 (−1)` the level-1 rows of `Q` vanish (`QlinB_one_bad_gen`, from `UR3`), `N` is not a unit
(`Nmat_bad_not_unit_gen`) and `genForm B = −a⟪B,B⟫` for every `B` (`genForm_bad_gen`).
Slab part (UR4 towers): `TorusOK`, `LambdaOK2`, a nonzero `B̃ ∈ Λ̃`, a level-1 bond, the class for `Ubad`.
Conclusion: `not_P428Genuine6_slab` (every `M = 2^m`, `m ≥ 1`, every even `R ≥ 12`) and `not_P428Target6`.
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
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice mem_blockOf mem_CoarseLattice staircasePath)
open AdalyFormal.Balaban.FullReparamC (freeBond freeBond_not_mem_staircase freeBond_not_dropped freeBond_coord_zero)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

/-! ## 1. generic: the junk at any `k = 1` tower -/

section generic
variable {Lu : PeriodicLatticeExtent} (h4 : ∀ μ, 4 ≤ scaleUp 2 1 Lu μ + 1)
include h4

theorem QlinCompX_one_bad_gen (S : Tower (scaleUp 2 1 Lu)) :
    QlinCompX (geomOf 2 1 S).ell (bgTower (geomOf 2 1 S) (cfg1 su2NegOne)) 1 = 0 := by
  show fderiv ℝ (qStepX (2 ^ 0) 2 (cfg1 su2NegOne) ∘ id) 0 = 0
  rw [Function.comp_id, pow_zero]
  exact QlinStepX_bad_eq_zero_gen h4

theorem QlinB_one_bad_gen (S : Tower (scaleUp 2 1 Lu)) : QlinB (geomOf 2 1 S) (cfg1 su2NegOne) 1 = 0 := by
  ext1 A
  rw [QlinB_apply, QlinCompX_one_bad_gen h4]
  simp

variable (S : Tower (scaleUp 2 1 Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (hell : 0 < 2)

/-- the parameters at `Ubad` -/
noncomputable abbrev Pg : IngrBParams := gparams 2 1 Lu hell S (cfg1 su2NegOne) a Lam

theorem Qs_kills_gen (p1 : BIdx (geomOf 2 1 S)) (hp1 : (p1.1 : ℕ) = 1) :
    (Pg S a Lam hell).data.Qs (WithLp.toLp 2 (Pi.single p1 suTwoWitness)) = 0 := by
  refine ext_inner_left ℝ (fun x => ?_)
  rw [inner_zero_right]
  show ⟪x, ContinuousLinearMap.adjoint ((QfullOf (geomOf 2 1 S) (cfg1 su2NegOne)).comp (iE (geomOf 2 1 S)))
      (WithLp.toLp 2 (Pi.single p1 suTwoWitness))⟫ = 0
  rw [ContinuousLinearMap.adjoint_inner_right, PiLp.inner_apply]
  rw [Finset.sum_eq_single p1]
  · show ⟪(((2 : ℕ) : ℝ) ^ (p1.1 : ℕ))⁻¹ • (WithLp.ofLp (QlinB (geomOf 2 1 S) (cfg1 su2NegOne) p1.1
        (iE (geomOf 2 1 S) x))) p1.2.1, (Pi.single p1 suTwoWitness : BIdx _ → SuTwo) p1⟫ = 0
    have hz : QlinB (geomOf 2 1 S) (cfg1 su2NegOne) (p1.1 : ℕ) = 0 := by rw [hp1]; exact QlinB_one_bad_gen h4 S
    rw [hz]
    simp
  · intro p _ hp
    simp [Pi.single_apply, hp]
  · intro hh; exact absurd (Finset.mem_univ _) hh

theorem Nmat_bad_not_unit_gen (p1 : BIdx (geomOf 2 1 S)) (hp1 : (p1.1 : ℕ) = 1) :
    ¬ IsUnit (GenP.Nmat (Pg S a Lam hell)) := by
  intro hu
  have hinj := (ContinuousLinearMap.isUnit_iff_bijective.mp hu).1
  have h0 : GenP.Nmat (Pg S a Lam hell) (WithLp.toLp 2 (Pi.single p1 suTwoWitness)) = GenP.Nmat (Pg S a Lam hell) 0 := by
    rw [map_zero]
    show ((Pg S a Lam hell).data.Q.comp ((Pg S a Lam hell).data.G1 (Pg S a Lam hell).G1inv))
      ((Pg S a Lam hell).data.Qs _) = 0
    rw [Qs_kills_gen h4 S a Lam hell p1 hp1, map_zero]
  have := congrArg (fun f : FSp (geomOf 2 1 S) => (WithLp.ofLp f) p1) (hinj h0)
  simp at this
  exact suTwoWitness_ne_zero this

theorem genForm_bad_gen (p1 : BIdx (geomOf 2 1 S)) (hp1 : (p1.1 : ℕ) = 1) (B : BondFnL2 Lu) :
    GenP.genForm (Pg S a Lam hell) B = -a * ⟪B, B⟫ := by
  have hinv : Ring.inverse (GenP.Nmat (Pg S a Lam hell)) = 0 :=
    Ring.inverse_non_unit _ (Nmat_bad_not_unit_gen h4 S a Lam hell p1 hp1)
  have hH : (Pg S a Lam hell).H1in = 0 := by
    show (iE (Pg S a Lam hell).G).comp (((Pg S a Lam hell).data.H1 (Pg S a Lam hell).G1inv).comp
      (ContinuousLinearMap.adjoint (Pg S a Lam hell).tau)) = 0
    have : (Pg S a Lam hell).data.H1 (Pg S a Lam hell).G1inv
        = (((Pg S a Lam hell).data.G1 (Pg S a Lam hell).G1inv).comp (Pg S a Lam hell).data.Qs).comp
          (Ring.inverse (GenP.Nmat (Pg S a Lam hell))) := rfl
    rw [this, hinv]
    simp
  unfold GenP.genForm GenP.firstTerm
  rw [hinv, hH]
  simp

theorem instIneq_bad_false_gen (p1 : BIdx (geomOf 2 1 S)) (hp1 : (p1.1 : ℕ) = 1) {γ₀ : ℝ} (ha : 0 < a) (hγ : 0 < γ₀)
    (Bt : Bond Lu → SuTwo) (h1 : OnLambdaTildeIn Lam 2 Bt) (h2 : OnLambdaT Lam Bt) (hE : 0 < bondEnergy Bt) :
    ¬ InstIneq 2 1 hell a Lu γ₀ S Lam (cfg1 su2NegOne) := by
  intro hI
  have hI' := hI Bt h1 h2
  have hg := genForm_bad_gen h4 S a Lam hell p1 hp1 (WithLp.toLp 2 (GenP.genC (Pg S a Lam hell) Bt))
  have hpos : 0 ≤ ⟪(WithLp.toLp 2 (GenP.genC (Pg S a Lam hell) Bt) : BondFnL2 Lu),
      WithLp.toLp 2 (GenP.genC (Pg S a Lam hell) Bt)⟫ := real_inner_self_nonneg
  have hb : GenP.genForm (Pg S a Lam hell) (WithLp.toLp 2 (GenP.genC (Pg S a Lam hell) Bt)) ≤ 0 := by
    rw [hg]; nlinarith
  have : 0 < γ₀ * bondEnergy Bt := mul_pos hγ hE
  exact absurd (lt_of_lt_of_le this hI') (not_lt.mpr hb)

end generic

/-- the class at `Ubad` for any tower whose `Ω₀` avoids the two endpoints of `b1` -/
theorem classCoupled_bad_gen {L : PeriodicLatticeExtent} {ell M c k : ℕ} {S : Tower L} {α₀ : ℝ} (hα : 0 < α₀)
    (hell : 1 ≤ ell) (hM : 1 ≤ M) (hc : 10 ≤ c)
    (hcov : CoversOm0p ell M c k S) (hS : ∀ j, S.Om (j + 1) ⊆ S.Om j) (hb : (o0 : PeriodicLatticeSite L) ∉ S.Om 0) :
    ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ (cfg1 su2NegOne) := by
  refine ⟨hcov, perCubeRegular2_congr hS (U := flatCfg) (fun e he => ?_)
    (flat_perCubeRegular2cG ell M c k hell hM hc hα S)⟩
  have hne : e ≠ b1 := by rintro rfl; exact hb he.1
  show (1 : SU2) = if e = b1 then su2NegOne else 1
  rw [if_neg hne]

/-! ## 2. the slab instance -/

section slabinst

/-- unit torus `Nu = 6H + 8M` -/
abbrev LuF (M h : ℕ) : PeriodicLatticeExtent := fun _ => 6 * (h * M) + 8 * M - 1

theorem fine_ext {M h N : ℕ} (P : SlabP M h N) : ∀ μ, scaleUp 2 1 (LuF M h) μ + 1 = N := by
  intro μ
  have := P.hM; have hN := P.hN
  simp only [scaleUp, LuF, pow_one]
  omega

theorem unit_ext {M h N : ℕ} (P : SlabP M h N) : ∀ μ, LuF M h μ + 1 = 6 * (h * M) + 8 * M := by
  intro μ; have := P.hM; simp only [LuF]; omega

def LamF (Lu : PeriodicLatticeExtent) (M h : ℕ) : Set (PeriodicLatticeSite Lu) :=
  {y | 3 * (h * M) + 3 * M ≤ (y 0).val ∧ (y 0).val < 3 * (h * M) + 5 * M}

theorem slab_torusOK {M h N : ℕ} (P : SlabP M h N) : TorusOK 2 M (LuF M h) := by
  have hu := unit_ext P
  have hM2 := P.hM
  refine ⟨fun μ => ?_, fun μ => ?_, fun μ => ?_⟩ <;> rw [hu μ]
  · exact ⟨3 * (h * M) + 4 * M, by ring⟩
  · omega
  · exact ⟨6 * h + 8, by ring⟩

theorem slab_lambdaOK {M h N : ℕ} (P : SlabP M h N) :
    LambdaOK (Lu := LuF M h) (Lf := scaleUp 2 1 (LuF M h)) 2 M (2 * h) 1 (SlabT (scaleUp 2 1 (LuF M h)) M (h * M))
      (LamF (LuF M h) M h) := by
  have hf := fine_ext P; have hu := unit_ext P
  have hNv := P.hN; have hH := P.H_ge; have hM0 := P.Mpos
  have hemb : ∀ (y : PeriodicLatticeSite (LuF M h)) (μ : Fin 3), 2 ^ 1 * (y μ).val < scaleUp 2 1 (LuF M h) μ + 1 := by
    intro y μ
    have h1 : (y μ).val < 6 * (h * M) + 8 * M := lt_of_lt_of_eq (y μ).isLt (hu μ)
    exact lt_of_lt_of_eq (by rw [pow_one]; omega) (hf μ).symm
  refine ⟨?_, fun y μ => ⟨2 ^ 1 * (y μ).val, hemb y μ⟩, ?_, ?_, ?_⟩
  · intro x hx y hy
    have h0 := hy 0
    simp only [LamF, Set.mem_setOf_eq] at hx ⊢
    have e1 : 3 * (h * M) + 3 * M = (3 * h + 3) * M := by ring
    have e2 : 3 * (h * M) + 5 * M = (3 * h + 5) * M := by ring
    rw [e1, e2] at hx ⊢
    exact ⟨(blk_le hM0 h0.symm).mp hx.1, (blk_lt hM0 h0.symm).mp hx.2⟩
  · intro y μ; rfl
  · intro y hy
    simp only [LamF, Set.mem_setOf_eq] at hy
    rw [slab_om1]
    show 2 * (h * M) + 4 * M ≤ 2 * (y 0).val ∧ 2 * (y 0).val < 10 * (h * M) + 12 * M
    omega
  · intro y hy y' hy'
    simp only [LamF, Set.mem_setOf_eq] at hy
    rw [slab_om1] at hy'
    simp only [slabOm, Set.mem_setOf_eq, not_and_or, not_le, not_lt] at hy'
    change (2 * (y' 0).val < 2 * (h * M) + 4 * M) ∨ (10 * (h * M) + 12 * M ≤ 2 * (y' 0).val) at hy'
    have hy'l : (y' 0).val < 6 * (h * M) + 8 * M := lt_of_lt_of_eq (y' 0).isLt (hu 0)
    have hyl : (y 0).val < 6 * (h * M) + 8 * M := lt_of_lt_of_eq (y 0).isLt (hu 0)
    have hR : 2 * h * M = 2 * (h * M) := by ring
    rw [hR]
    have hc : 2 * (h * M) < pcd (LuF M h 0 + 1) (y 0).val (y' 0).val := by
      have := hu 0; unfold pcd; split_ifs <;> omega
    exact lt_of_lt_of_le hc (pdist_ge_coord0 y y')

theorem slab_blockSum {M h N : ℕ} (P : SlabP M h N) : LamBlockSum 2 (LamF (LuF M h) M h) := by
  have hM2 : M % 2 = 0 := Nat.mod_eq_zero_of_dvd P.hMe
  have hH2 : (h * M) % 2 = 0 := Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_left P.hMe h)
  intro x hx
  simp only [LamF, Set.mem_setOf_eq] at hx
  let y : PeriodicLatticeSite (LuF M h) := fun μ => ⟨(x μ).val - (x μ).val % 2, by have := (x μ).isLt; omega⟩
  refine ⟨y, ⟨?_, ?_⟩, ?_⟩
  · rw [mem_CoarseLattice]
    intro μ
    show ((x μ).val - (x μ).val % 2) % 2 = 0
    omega
  · intro x' hx'
    rw [mem_blockOf] at hx'
    have := hx' 0
    simp only [LamF, Set.mem_setOf_eq]
    have h0 : (y 0).val = (x 0).val - (x 0).val % 2 := rfl
    omega
  · rw [mem_blockOf]
    intro μ
    show (x μ).val - (x μ).val % 2 ≤ (x μ).val ∧ (x μ).val < (x μ).val - (x μ).val % 2 + 2
    omega

theorem slab_lambdaOK2 {M h N : ℕ} (P : SlabP M h N) :
    LambdaOK2 (Lu := LuF M h) (Lf := scaleUp 2 1 (LuF M h)) 2 M (2 * h) 1 (SlabT (scaleUp 2 1 (LuF M h)) M (h * M))
      (LamF (LuF M h) M h) :=
  ⟨slab_lambdaOK P, slab_blockSum P⟩

/-- the seed site `(3H+3M, 0, 0)` -/
def ySeed (M h : ℕ) (hM : 2 ≤ M) : PeriodicLatticeSite (LuF M h) :=
  fun μ => ⟨if μ = 0 then 3 * (h * M) + 3 * M else 0, by
    simp only [LuF]; split_ifs <;> omega⟩

theorem slab_seed {M h N : ℕ} (P : SlabP M h N) :
    ∃ Bt : Bond (LuF M h) → SuTwo, OnLambdaTildeIn (LamF (LuF M h) M h) 2 Bt ∧ OnLambdaT (LamF (LuF M h) M h) Bt ∧
      OnLambda (LamF (LuF M h) M h) Bt ∧ 0 < bondEnergy Bt := by
  have hu := unit_ext P
  have hM2 : M % 2 = 0 := Nat.mod_eq_zero_of_dvd P.hMe
  have hH2 : (h * M) % 2 = 0 := Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_left P.hMe h)
  have hdvd : ∀ μ : Fin 3, 2 ∣ LuF M h μ + 1 := fun μ => by rw [hu μ]; exact ⟨3 * (h * M) + 4 * M, by ring⟩
  set y := ySeed M h P.hM with hydef
  have hy0 : (y 0).val = 3 * (h * M) + 3 * M := by simp [y, ySeed]
  have hyc : y ∈ CoarseLattice (LuF M h) 2 := by
    rw [mem_CoarseLattice]
    intro μ
    by_cases hμ : μ = 0
    · subst hμ; rw [hy0]; omega
    · show (if μ = 0 then 3 * (h * M) + 3 * M else 0) % 2 = 0
      rw [if_neg hμ]
  let Bt : Bond (LuF M h) → SuTwo := Pi.single (freeBond 2 y) suTwoWitness
  have hoff : ∀ b : Bond (LuF M h), b ≠ freeBond 2 y → Bt b = 0 := fun b hb => Pi.single_eq_of_ne hb _
  have hOn : OnLambdaT (LamF (LuF M h) M h) Bt := by
    intro b hb
    by_cases hbe : b = freeBond 2 y
    · exfalso
      apply hb
      have hfit : (y 0).val + 2 ≤ LuF M h 0 + 1 := by rw [hy0, hu 0]; have := P.hM; omega
      have h0 := freeBond_coord_zero y hfit (le_refl 2)
      subst hbe
      left
      show 3 * (h * M) + 3 * M ≤ ((freeBond 2 y).1 0).val ∧ ((freeBond 2 y).1 0).val < 3 * (h * M) + 5 * M
      have := P.hM
      omega
    · exact hoff b hbe
  have hBoth : OnLambda (LamF (LuF M h) M h) Bt := by
    intro b hb
    by_cases hbe : b = freeBond 2 y
    · exfalso
      apply hb
      have hfit : (y 0).val + 2 ≤ LuF M h 0 + 1 := by rw [hy0, hu 0]; have := P.hM; omega
      have h0 := freeBond_coord_zero y hfit (le_refl 2)
      have hL2 : ∀ μ, 2 ≤ LuF M h μ + 1 := fun μ => by rw [hu μ]; have := P.hM; omega
      subst hbe
      have hsh := fshift_val hL2 (freeBond 2 y).1 0 0
      rw [if_pos rfl] at hsh
      have hu0 := hu 0
      have := P.hM
      refine ⟨?_, ?_⟩
      · show 3 * (h * M) + 3 * M ≤ ((freeBond 2 y).1 0).val ∧ ((freeBond 2 y).1 0).val < 3 * (h * M) + 5 * M
        omega
      · show 3 * (h * M) + 3 * M ≤ ((periodicLatticeShift (freeBond 2 y).1 (0 : Fin 3)) 0).val ∧
          ((periodicLatticeShift (freeBond 2 y).1 (0 : Fin 3)) 0).val < 3 * (h * M) + 5 * M
        rw [hsh, Nat.mod_eq_of_lt (by omega)]
        omega
    · exact hoff b hbe
  refine ⟨Bt, ⟨?_, ?_⟩, hOn, hBoth, ?_⟩
  · intro y' hy' x hx b hb
    refine hoff b ?_
    rintro rfl
    exact freeBond_not_mem_staircase (by norm_num) hdvd y hyc y' hy'.1 x hx hb
  · intro b hb
    refine hoff b ?_
    rintro rfl
    obtain ⟨c, hc1, hc2⟩ := hb
    exact freeBond_not_dropped (by norm_num) hdvd y hyc ⟨c, hc2⟩
  · have hpos : 0 < ‖Bt (freeBond 2 y)‖ ^ 2 := by
      have : Bt (freeBond 2 y) = suTwoWitness := Pi.single_eq_same _ _
      rw [this]
      have : suTwoWitness ≠ 0 := suTwoWitness_ne_zero
      positivity
    have hle : ‖Bt (freeBond 2 y)‖ ^ 2 ≤ ∑ b : Bond (LuF M h), ‖Bt b‖ ^ 2 :=
      Finset.single_le_sum (f := fun b : Bond (LuF M h) => ‖Bt b‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ _)
    unfold bondEnergy
    linarith

/-- the level-1 index `(1, ((2H+4M, 0, 0), e₀))` of `𝔅` on the slab tower -/
theorem slab_level1 {M h N : ℕ} (P : SlabP M h N) :
    ∃ p1 : BIdx (geomOf 2 1 (SlabT (scaleUp 2 1 (LuF M h)) M (h * M))), (p1.1 : ℕ) = 1 := by
  have hf := fine_ext P
  have hNv := P.hN; have hH := P.H_ge; have hM2 := P.hM
  let s : PeriodicLatticeSite (scaleUp 2 1 (LuF M h)) :=
    fun μ => ⟨if μ = 0 then 2 * (h * M) + 4 * M else 0, by rw [hf μ]; split_ifs <;> omega⟩
  have hs0 : (s 0).val = 2 * (h * M) + 4 * M := by simp [s]
  have hmem : ((s, 0) : Bond (scaleUp 2 1 (LuF M h))) ∈ bondsLam (geomOf 2 1 (SlabT (scaleUp 2 1 (LuF M h)) M (h * M))) 1 := by
    refine ⟨Or.inl ⟨?_, ?_, ?_⟩, ?_⟩
    · intro μ
      by_cases hμ : μ = 0
      · subst hμ; rw [hs0]; exact ⟨h * M + 2 * M, by ring⟩
      · show 2 ^ 1 ∣ (if μ = 0 then 2 * (h * M) + 4 * M else 0); rw [if_neg hμ]; exact dvd_zero _
    · show s ∈ (SlabT (scaleUp 2 1 (LuF M h)) M (h * M)).Om 1
      rw [slab_om1]; simp only [slabOm, Set.mem_setOf_eq, hs0]; omega
    · show s ∉ (SlabT (scaleUp 2 1 (LuF M h)) M (h * M)).Om (1 + 1)
      rw [slab_omj M (h * M) (1 + 1) le_rfl]; exact fun h => h
    · rintro (hh | hh) <;> exact not_OmGe_of_lt (G := geomOf 2 1 (SlabT (scaleUp 2 1 (LuF M h)) M (h * M)))
        (by show 1 < 2; omega) _ hh
  exact ⟨⟨⟨1, by show 1 < 1 + 1; omega⟩, ⟨(s, 0), hmem⟩⟩, rfl⟩

/-- **THE FROZEN HEADLINE IS FALSE AT EVERY `(ell, M, R) = (2, 2^m, 2h)`, `m ≥ 1`, `h ≥ 6`, EVERY `a > 0`.** -/
theorem not_P428Genuine6_slab (m h : ℕ) (hm : 1 ≤ m) (hh : 6 ≤ h) (a : ℝ) (ha : 0 < a) :
    ¬ P428Genuine6 2 (2 ^ m) (2 * h) (by norm_num) a := by
  have hM2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hMe : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  have P : SlabP (2 ^ m) h (12 * (h * 2 ^ m) + 16 * 2 ^ m) := ⟨hM2, hMe, hh, rfl⟩
  rintro ⟨-, a₀, ha₀, γ₀, hγ₀, hcore⟩
  set M := 2 ^ m with hMdef
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have h12 : (0 : ℝ) < 12 * (M : ℝ) := mul_pos (by norm_num) hMpos
  have hα : 0 < a₀ / (12 * (M : ℝ)) := div_pos ha₀ h12
  have hαb : ((12 : ℕ) : ℝ) * ((M : ℕ) : ℝ) * (a₀ / (12 * (M : ℝ))) ≤ a₀ := by
    apply le_of_eq
    push_cast
    field_simp
  have hc := hcore 1 le_rfl (LuF M h) (a₀ / (12 * (M : ℝ))) hα hαb
  have hf := fine_ext P
  have h4 : ∀ μ, 4 ≤ scaleUp 2 1 (LuF M h) μ + 1 := fun μ => by rw [hf μ]; omega
  have hadm := slab_admissible P hf
  have hcov := slab_coversp P hf
  have hb : (o0 : PeriodicLatticeSite (scaleUp 2 1 (LuF M h))) ∉ (SlabT (scaleUp 2 1 (LuF M h)) M (h * M)).Om 0 := by
    rw [slab_om0]; simp only [slabOm, Set.mem_setOf_eq, o0]; omega
  have hcl := classCoupled_bad_gen (ell := 2) (k := 1) (c := 12) (α₀ := a₀ / (12 * (M : ℝ))) hα (by norm_num) (by omega)
    (by norm_num) hcov hadm.1 hb
  have hI := hc (slab_torusOK P) _ hadm _ (slab_lambdaOK2 P) (cfg1 su2NegOne) hcl
  obtain ⟨Bt, h1, h2, -, hE⟩ := slab_seed P
  obtain ⟨p1, hp1⟩ := slab_level1 P
  exact instIneq_bad_false_gen h4 _ a _ (by norm_num) p1 hp1 ha hγ₀ Bt h1 h2 hE hI

/-- **THE FROZEN HEADLINE `P428Target6` IS FALSE.** -/
theorem not_P428Target6 : ¬ P428Target6 := by
  intro hT
  obtain ⟨m₀, hm₀, hT⟩ := hT 2 le_rfl 1 one_pos
  obtain ⟨R₀, hR⟩ := hT m₀ le_rfl
  have hG := hR (2 * (R₀ + 6)) (by omega)
  exact not_P428Genuine6_slab m₀ (R₀ + 6) hm₀ (by omega) 1 one_pos hG

end slabinst

#print axioms QlinB_one_bad_gen
#print axioms Nmat_bad_not_unit_gen
#print axioms genForm_bad_gen
#print axioms instIneq_bad_false_gen
#print axioms classCoupled_bad_gen
#print axioms slab_torusOK
#print axioms slab_lambdaOK2
#print axioms slab_seed
#print axioms slab_level1
#print axioms not_P428Genuine6_slab
#print axioms not_P428Target6

end AdalyFormal.URLocality
