import R8UR4


/-!
# R8UR5s -- r8 port of the SLAB INSTANCE of `compute/u_reads_omega0_20261012/UR5.lean` (UR lane), compiled against the r8 fork.
Ported verbatim (namespace `AdalyFormal.URLocality` -> `AdalyFormal.URLocalityR8`, headline names `…6` -> `…8`): `classCoupled_bad_gen`
and the slab facts `slab_torusOK`, `slab_lambdaOK2`, `slab_seed`, `slab_level1`.  These do not involve the jets.  NOT ported here: the
generic junk section and the refutation `not_P428Genuine6_slab` (their verbatim port is `R8UR5.lean`, a must-fire control: it must
FAIL against the repaired jets).
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.URLocalityR8

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

end slabinst

#print axioms classCoupled_bad_gen
#print axioms slab_torusOK
#print axioms slab_lambdaOK2
#print axioms slab_seed
#print axioms slab_level1

end AdalyFormal.URLocalityR8
