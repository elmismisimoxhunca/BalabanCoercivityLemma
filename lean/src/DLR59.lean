import DLR58

/-!
# DL59 -- **`hJs_class`: the source `J` is `O(β n⁻³)` on the printed class `PerCubeRegular2` at the full tower** (premise hJs of DL5)

For `U` with `PerCubeRegular2 ℓ M f k (fullTower ℓ k Lu) α₀ (ℓ^k)⁻¹ U` (printed (3.35)-(3.36), curl form, the headline's `η`),
`4 ≤ f`, `0 < M`, `4β ≤ 1` (`β = fMα₀`):
  `‖Jf(b)‖ ≤ JSfree β / n³`,  `JSfree β = (β + 40β² + 4144β³ + 8192β⁴)/√2`  — k-, volume- and U-free.
Route: for `x = b.1` the class cube `siteBox (cubeCorner x) (f·Mℓ^k)` (index `k`: `classCube_full`) contains the 3×3×3
neighbourhood of `x` (`near_mem_box`); its gauge `g` and field `A` give `LocRep` for `U^g` (clauses 1, 2) and clause 3 at `x`;
`J_local_bound` (DL58) bounds `J(U^g)(x,μ)`; gauge covariance (GCb7 `JfieldLoc_gauge`) transfers it to `J(U)`;
`‖Jf b‖ = frobNorm(J)/√2` (`norm_sq_eq_half_frobSq`), `plaqIn Ω₀ = univ` on the full tower.
-/
set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 20000

namespace AdalyFormal.DLayer

open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.RMapLipschitz (frobSq frobNorm frobSq_nonneg frobNorm_nonneg frobNorm_sq norm_sq_eq_half_frobSq)
open AdalyFormal.Balaban.SourceJ (Jfield)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack
  periodicLatticeShiftBack_shift)
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.StatementLane (IsClassCube DescribedAt CubeBond HT siteBox towerBj GridCorner bigSide scaleUp)
open AdalyFormal.StatementLane2 (curlA ddA CurlReads PerCubeRegular2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)

local notation "Mt" => Matrix (Fin 2) (Fin 2) ℂ

variable {L : PeriodicLatticeExtent}

/-! ## sites near `x` -/

theorem shiftF_apply (y : PeriodicLatticeSite L) (a c : Fin 3) :
    (periodicLatticeShift y a) c = if c = a then y c + 1 else y c := by
  unfold periodicLatticeShift
  by_cases h : c = a
  · subst h; rw [Function.update_self, if_pos rfl]
  · rw [Function.update_of_ne h, if_neg h]

theorem shiftBack_apply (y : PeriodicLatticeSite L) (a c : Fin 3) :
    (periodicLatticeShiftBack y a) c = if c = a then y c - 1 else y c := by
  unfold periodicLatticeShiftBack
  by_cases h : c = a
  · subst h; rw [Function.update_self, if_pos rfl]
  · rw [Function.update_of_ne h, if_neg h]

/-- `y` is within one step of `x` in every coordinate -/
def Near (x y : PeriodicLatticeSite L) : Prop := ∀ c, y c = x c - 1 ∨ y c = x c ∨ y c = x c + 1

/-- the grid corner of the class cube around `x` -/
def cubeCorner (g : ℕ) (x : PeriodicLatticeSite L) : PeriodicLatticeSite L :=
  fun c => ⟨((x c - 1).val / g) * g, lt_of_le_of_lt (Nat.div_mul_le_self _ _) (x c - 1).isLt⟩

theorem cubeCorner_grid (g : ℕ) (x : PeriodicLatticeSite L) : GridCorner g (cubeCorner g x) :=
  fun c => Nat.mul_mod_left _ _

theorem fin_val_add_le {N : ℕ} [NeZero N] (a b : Fin N) : (a + b).val ≤ a.val + b.val := by
  rw [Fin.val_add]; exact Nat.mod_le _ _

theorem fin_val_one_le {n : ℕ} : (1 : Fin (n + 1)).val ≤ 1 := by
  rw [Fin.val_one']; exact Nat.mod_le _ _

theorem near_mem_box (g s : ℕ) (hg : 0 < g) (hs : g + 2 < s) (x y : PeriodicLatticeSite L) (hy : Near x y) :
    y ∈ siteBox (cubeCorner g x) s := by
  intro c
  set a : Fin (L c + 1) := x c - 1 with ha
  set z : Fin (L c + 1) := cubeCorner g x c with hz
  have hzv : z.val = (a.val / g) * g := rfl
  have hza : z.val ≤ a.val := by rw [hzv]; exact Nat.div_mul_le_self _ _
  have hlhs : ((y c).val + (L c + 1) - z.val) % (L c + 1) = (y c - z).val := by
    rw [Fin.sub_def]
    show ((y c).val + (L c + 1) - z.val) % (L c + 1) = ((L c + 1) - z.val + (y c).val) % (L c + 1)
    congr 1
    have := z.isLt
    omega
  rw [hlhs]
  have hsplit : y c - z = (y c - a) + (a - z) := by abel
  rw [hsplit]
  refine lt_of_le_of_lt (fin_val_add_le _ _) ?_
  have h1 : (a - z).val < g := by
    rw [Fin.coe_sub_iff_le.mpr hza, hzv]
    have := Nat.mod_add_div a.val g
    have := Nat.mod_lt a.val hg
    have e : a.val / g * g = g * (a.val / g) := Nat.mul_comm _ _
    omega
  have h2 : (y c - a).val ≤ 2 := by
    rcases hy c with h | h | h
    · rw [h, ha, sub_self]; simp
    · have e : y c - a = 1 := by rw [h, ha]; abel
      rw [e]; exact le_trans fin_val_one_le (by norm_num)
    · have e : y c - a = 1 + 1 := by rw [h, ha]; abel
      rw [e]
      exact le_trans (fin_val_add_le _ _) (by have := (fin_val_one_le (n := L c)); omega)
  omega

/-! ## the class cube around `x` at the full tower -/

theorem towerBj_full_k (ell k : ℕ) (Lu : PeriodicLatticeExtent) :
    towerBj (fullTower ell k Lu) k = Set.univ := by
  ext y; simp [towerBj, fullTower]

theorem towerBj_full_lt (ell k : ℕ) (Lu : PeriodicLatticeExtent) (i : ℕ) (hi : i < k) :
    towerBj (fullTower ell k Lu) i = ∅ := by
  ext y; simp [towerBj, fullTower, hi.le, show i + 1 ≤ k by omega]

theorem near_self (x : PeriodicLatticeSite L) : Near x x := fun c => Or.inr (Or.inl rfl)

theorem classCube_full (ell M f k : ℕ) (Lu : PeriodicLatticeExtent) (hg : 0 < bigSide M ell k)
    (hs : bigSide M ell k + 2 < f * bigSide M ell k) (x : PeriodicLatticeSite (scaleUp ell k Lu)) :
    IsClassCube ell M f k (fullTower ell k Lu) (siteBox (cubeCorner (bigSide M ell k) x) (f * bigSide M ell k)) k := by
  refine ⟨⟨le_rfl, ⟨cubeCorner (bigSide M ell k) x, cubeCorner_grid _ x, rfl⟩, ?_, ?_⟩, ?_⟩
  · intro y _; left; rw [towerBj_full_k]; trivial
  · exact ⟨x, near_mem_box _ _ hg hs x x (near_self x), by rw [towerBj_full_k]; trivial⟩
  · intro i hi
    obtain ⟨hik, -, -, hne⟩ := hi
    by_contra hne'
    have hlt : i < k := lt_of_le_of_ne hik hne'
    rw [towerBj_full_lt ell k Lu i hlt, Set.inter_empty] at hne
    exact Set.not_nonempty_empty hne

/-! ## the needed sites are near `x` -/

theorem near_of (x y : PeriodicLatticeSite L) (h : ∀ c, y c = x c - 1 ∨ y c = x c ∨ y c = x c + 1) : Near x y := h

section
variable (x : PeriodicLatticeSite L) (ν μ : Fin 3) (hνμ : ν ≠ μ)
include hνμ

theorem near_list :
    Near x x ∧ Near x (periodicLatticeShiftBack x ν) ∧ Near x (periodicLatticeShift x ν)
    ∧ Near x (periodicLatticeShift x μ) ∧ Near x (periodicLatticeShift (periodicLatticeShiftBack x ν) μ)
    ∧ Near x (periodicLatticeShift (periodicLatticeShift x ν) μ)
    ∧ Near x (periodicLatticeShift (periodicLatticeShift x μ) ν) := by
  refine ⟨near_self x, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro c <;>
    simp only [shiftF_apply, shiftBack_apply] <;> split_ifs <;> simp_all

end

/-! ## from the class to the local representation -/

theorem frobNorm_cjM (g : SU2) (X : Mt) : frobNorm (AdalyFormal.GaugeCov.cjM g X) = frobNorm X := by
  unfold AdalyFormal.GaugeCov.cjM
  have h1 : (g : Mt)ᴴ * (g : Mt) = 1 := AdalyFormal.Balaban.SuTwoInner.conjTranspose_mul_self g
  rw [fN_mul_unitary _ _ (by rw [Matrix.conjTranspose_conjTranspose]; exact h1)]
  exact AdalyFormal.Balaban.RegularUQChain.frobNorm_mul_left_iso _ _ h1

/-- the `J` constant of the class -/
noncomputable def JSfree (β : ℝ) : ℝ := (β + 40 * β ^ 2 + 4144 * β ^ 3 + 8192 * β ^ 4) / Real.sqrt 2

theorem J_class_frob (ell M f k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu))
    (α₀ : ℝ) (hM : 0 < M) (hf : 4 ≤ f)
    (hP : PerCubeRegular2 ell M f k (fullTower ell k Lu) α₀ ((ell : ℝ) ^ k)⁻¹ U)
    (hsm : 4 * ((f : ℝ) * M * α₀) ≤ 1) (x : PeriodicLatticeSite (scaleUp ell k Lu)) (μ : Fin 3) :
    frobNorm (Jfield U x μ)
      ≤ (((ell : ℝ) ^ k)⁻¹) ^ 3 * ((f * M * α₀) + 40 * (f * M * α₀) ^ 2 + 4144 * (f * M * α₀) ^ 3
          + 8192 * (f * M * α₀) ^ 4) := by
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := by positivity
  have hn1 : (1 : ℝ) ≤ (ell : ℝ) ^ k := one_le_pow₀ (by exact_mod_cast hell)
  set η := ((ell : ℝ) ^ k)⁻¹ with hηdef
  have hη : 0 < η := by positivity
  have hη1 : η ≤ 1 := by rw [hηdef]; exact inv_le_one_of_one_le₀ hn1
  set β := (f : ℝ) * M * α₀ with hβ
  have hg : 0 < bigSide M ell k := by unfold bigSide; positivity
  have hs : bigSide M ell k + 2 < f * bigSide M ell k := by
    have : 4 * bigSide M ell k ≤ f * bigSide M ell k := Nat.mul_le_mul_right _ hf
    omega
  set sites := siteBox (cubeCorner (bigSide M ell k) x) (f * bigSide M ell k) with hsites
  have hcube := classCube_full ell M f k Lu hg hs x
  obtain ⟨g, A, hA, hD, hLap⟩ := hP sites k hcube
  have hone : ((ell : ℝ) ^ k * η)⁻¹ = 1 := by rw [hηdef, mul_inv_cancel₀ hn.ne', inv_one]
  have hnear : ∀ y, Near x y → y ∈ sites := fun y hy => near_mem_box _ _ hg hs x y hy
  -- the local representation of `U^g`
  have hloc : LocRep (periodicGaugeTransform g U) η A β β (CubeBond sites) := by
    refine ⟨hη, fun e he => (hA e he).2.1, fun e he => (hA e he).1, fun e he => ?_, fun z d d' h0 h1 => ?_, ?_⟩
    · have := (hA e he).2.2; rw [hone, one_pow, mul_one] at this; exact this.le
    · have := hD d' d z h0 h1; rw [hone, one_pow, mul_one] at this; exact this.le
    · have hβ0 : 0 ≤ β := by
        have hb : CubeBond sites ((x, μ) : Bond (scaleUp ell k Lu)) := by
          refine ⟨hnear x (near_self x), hnear _ ?_⟩
          intro c; simp only [shiftF_apply]; split_ifs <;> simp_all
        have := (hA _ hb).2.2
        rw [hone, one_pow, mul_one] at this
        exact le_trans (frobNorm_nonneg _) this.le
      nlinarith
  -- bonds near `x`
  have hcb : ∀ y d, Near x y → Near x (periodicLatticeShift y d) → CubeBond sites (y, d) :=
    fun y d h1 h2 => ⟨hnear y h1, hnear _ h2⟩
  have hneed : ∀ ν, ν ≠ μ → NeedBonds (CubeBond sites) (periodicLatticeShiftBack x ν) ν μ := by
    intro ν hν
    obtain ⟨n0, n1, n2, n3, n4, n5, n6⟩ := near_list x ν μ hν
    have e1 : periodicLatticeShift (periodicLatticeShiftBack x ν) ν = x := periodicLatticeShift_shiftBack x ν
    have e2 : periodicLatticeShift (periodicLatticeShift (periodicLatticeShiftBack x ν) μ) ν = periodicLatticeShift x μ := by
      rw [shift_comm, periodicLatticeShift_shiftBack]
    refine ⟨hcb _ _ n1 (by rw [e1]; exact n0), hcb _ _ (by rw [e1]; exact n0) (by rw [e1]; exact n3),
      hcb _ _ n4 (by rw [e2]; exact n3), hcb _ _ n1 n4, hcb _ _ (by rw [e1]; exact n0) (by rw [e1]; exact n2),
      hcb _ _ (by rw [e1]; exact n2) (by rw [e1]; exact n5), hcb _ _ (by rw [e1]; exact n3) (by rw [e1]; exact n6)⟩
  -- clause 3 at `x`
  have hdd : frobNorm (ddA η A x μ) ≤ β := by
    have hcr : ∀ ν : Fin 3, ν ≠ μ → CurlReads sites (periodicLatticeShiftBack x ν) ν μ ∧ CurlReads sites x ν μ := by
      intro ν hν
      obtain ⟨n0, n1, n2, n3, n4, n5, n6⟩ := near_list x ν μ hν
      have e1 : periodicLatticeShift (periodicLatticeShiftBack x ν) ν = x := periodicLatticeShift_shiftBack x ν
      have e2 : periodicLatticeShift (periodicLatticeShift (periodicLatticeShiftBack x ν) μ) ν
          = periodicLatticeShift x μ := by rw [shift_comm, periodicLatticeShift_shiftBack]
      refine ⟨⟨hcb _ _ (by rw [e1]; exact n0) (by rw [e1]; exact n3), hcb _ _ n1 n4, hcb _ _ n4 (by rw [e2]; exact n3),
        hcb _ _ n1 (by rw [e1]; exact n0)⟩, ⟨hcb _ _ n2 n5, hcb _ _ n0 n3, hcb _ _ n3 n6, hcb _ _ n0 n2⟩⟩
    have := hLap μ x hcr
    rw [hone, one_pow, mul_one] at this
    exact this.le
  have hJ := hloc.J_local_bound x μ β hneed hdd
  -- gauge covariance
  have hgauge : Jfield (periodicGaugeTransform g U) x μ = AdalyFormal.GaugeCov.cjM (g x) (Jfield U x μ) := by
    have h := AdalyFormal.GaugeCov.JfieldLoc_gauge g Set.univ U x μ
    rw [AdalyFormal.IngredientFamily.JfieldLoc_univ, AdalyFormal.IngredientFamily.JfieldLoc_univ] at h
    exact h
  rw [hgauge, frobNorm_cjM] at hJ
  refine hJ.trans ?_
  have hβ0 : 0 ≤ β := by
    have := hloc.small; nlinarith [hloc.a1_nonneg (x, μ) (by
      exact ⟨hnear x (near_self x), hnear _ (fun c => by simp only [shiftF_apply]; split_ifs <;> simp_all)⟩)]
  have : 8192 * η * β ^ 4 ≤ 8192 * β ^ 4 := by
    have := pow_nonneg hβ0 4; nlinarith
  have hη3 : 0 ≤ η ^ 3 := by positivity
  nlinarith

#print axioms shiftF_apply
#print axioms shiftBack_apply
#print axioms near_mem_box
#print axioms classCube_full
#print axioms near_list
#print axioms frobNorm_cjM
#print axioms J_class_frob

end AdalyFormal.DLayer
