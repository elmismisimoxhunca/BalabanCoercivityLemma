import R7Fork.DM7a

/-!
# DM7b -- tower combinatorics: block closure helpers and `x in Om_i  =>  OmGe i x` (the print's `Omega_i \ Omega_{i+1} = B^i(Lambda_i)`).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000
namespace AdalyFormal.DirichletMono

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice mem_CoarseLattice)

theorem blk_div (n M x : ℕ) : x / (M * n) = x / n / M := by
  rw [mul_comm, Nat.div_div_eq_div_mul]

theorem blk_mul (n M q : ℕ) (hn : 0 < n) : (n * q) / (M * n) = q / M := by
  rw [blk_div, Nat.mul_div_cancel_left _ hn]

theorem om_anti {L : PeriodicLatticeExtent} (S : Tower L) (hS : ∀ j, S.Om (j + 1) ⊆ S.Om j) {i j : ℕ}
    (h : i ≤ j) : S.Om j ⊆ S.Om i := by
  induction j, h using Nat.le_induction with
  | base => exact fun _ hx => hx
  | succ j hij ih => exact fun x hx => ih (hS j hx)

/-- `Om_j` is closed under `ell^j`-blocks of coarse centres: a point of the block of a centre in `Om_j` is in `Om_j` -/
theorem block_sub_Om {ell M R k : ℕ} (hell : 0 < ell) {L : PeriodicLatticeExtent} {S : Tower L}
    (hS : Admissible ell M R k S) {j : ℕ} (hj : j ≤ k) {y x : PeriodicLatticeSite L}
    (hy : ∀ ρ, ell ^ j ∣ (y ρ).val) (hyO : y ∈ S.Om j) (hx : x ∈ blockOf y (ell ^ j)) : x ∈ S.Om j := by
  have hn : 0 < ell ^ j := pow_pos hell j
  refine hS.2.2.2.1 j hj y hyO x (fun ρ => ?_)
  have h := (mem_blockOf.mp hx) ρ
  obtain ⟨q, hq⟩ := hy ρ
  unfold bigSide
  rw [blk_div, blk_div]
  congr 1
  have h1 : (x ρ).val / ell ^ j = q := by
    apply Nat.div_eq_of_lt_le
    · rw [mul_comm]; omega
    · rw [add_mul, one_mul, mul_comm]; omega
  have h2 : (y ρ).val / ell ^ j = q := by rw [hq]; exact Nat.mul_div_cancel_left _ hn
  rw [h1, h2]

/-- the centre of a block meeting `Om_{j+1}` is in `Om_{j+1}` -/
theorem anchor_sub_Om {ell M R k : ℕ} (hell : 0 < ell) {L : PeriodicLatticeExtent} {S : Tower L}
    (hS : Admissible ell M R k S) {j : ℕ} (hj : j + 1 ≤ k) {Y s : PeriodicLatticeSite L}
    (hY : ∀ ρ, ell ^ j ∣ (Y ρ).val) (hs : s ∈ blockOf Y (ell ^ j)) (hsO : s ∈ S.Om (j + 1)) :
    Y ∈ S.Om (j + 1) := by
  have hn : 0 < ell ^ j := pow_pos hell j
  refine hS.2.2.2.1 (j + 1) hj s hsO Y (fun ρ => ?_)
  have h := (mem_blockOf.mp hs) ρ
  obtain ⟨q, hq⟩ := hY ρ
  unfold bigSide
  rw [blk_div, blk_div]
  congr 1
  have h1 : (s ρ).val / ell ^ j = q := by
    apply Nat.div_eq_of_lt_le
    · rw [mul_comm]; omega
    · rw [add_mul, one_mul, mul_comm]; omega
  have h2 : (Y ρ).val / ell ^ j = q := by rw [hq]; exact Nat.mul_div_cancel_left _ hn
  rw [pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, h1, h2]

/-- **`Omega_i \ Omega_{i+1} = B^i(Lambda_i)`**: under `Admissible`, a point of `Om_i` (`i <= k`) satisfies `OmGe i` -/
theorem omGe_of_mem {ell M R k : ℕ} (hell : 0 < ell) {L : PeriodicLatticeExtent} {S : Tower L}
    (hS : Admissible ell M R k S) {i : ℕ} (hi : i ≤ k) {x : PeriodicLatticeSite L} (hx : x ∈ S.Om i) :
    OmGe (geomOf ell k S) i x := by
  classical
  have hex : ∃ m, x ∉ S.Om (i + m) :=
    ⟨k + 1, by rw [hS.2.1 (i + (k + 1)) (by omega)]; exact Set.notMem_empty x⟩
  set m0 := Nat.find hex with hm0def
  have hm0 : x ∉ S.Om (i + m0) := Nat.find_spec hex
  have hm0pos : 0 < m0 := by
    by_contra h
    have : m0 = 0 := by omega
    rw [this, Nat.add_zero] at hm0
    exact hm0 hx
  set i' := i + (m0 - 1) with hi'
  have hxi' : x ∈ S.Om i' := by
    by_contra h
    have := Nat.find_min' hex (m := m0 - 1) h
    omega
  have hnot : x ∉ S.Om (i' + 1) := by
    have : i' + 1 = i + m0 := by omega
    rw [this]; exact hm0
  have hik : i' ≤ k := by
    by_contra h
    have := hS.2.1 i' (by omega)
    rw [this] at hxi'
    exact hxi'
  have hn : 0 < ell ^ i' := pow_pos hell i'
  set y : PeriodicLatticeSite L := fun ρ => ⟨ell ^ i' * ((x ρ).val / ell ^ i'),
    lt_of_le_of_lt (Nat.mul_div_le _ _) (x ρ).isLt⟩ with hy
  have hydiv : ∀ ρ, ell ^ i' ∣ (y ρ).val := fun ρ => dvd_mul_right _ _
  have hyx : ∀ ρ, (y ρ).val / ell ^ i' = (x ρ).val / ell ^ i' := fun ρ => by
    show (ell ^ i' * ((x ρ).val / ell ^ i')) / ell ^ i' = _
    exact Nat.mul_div_cancel_left _ hn
  have hyO : y ∈ S.Om i' := by
    refine hS.2.2.2.1 i' hik x hxi' y (fun ρ => ?_)
    unfold bigSide
    rw [blk_div, blk_div, hyx ρ]
  have hyN : y ∉ S.Om (i' + 1) := by
    by_cases hk1 : i' + 1 ≤ k
    · intro h
      apply hnot
      refine hS.2.2.2.1 (i' + 1) hk1 y h x (fun ρ => ?_)
      unfold bigSide
      rw [blk_div, blk_div, pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hyx ρ]
    · have : S.Om (i' + 1) = ∅ := hS.2.1 (i' + 1) (by omega)
      rw [this]; exact Set.notMem_empty y
  refine ⟨i', by omega, hik, y, ⟨hydiv, hyO, hyN⟩, fun ρ => ⟨?_, ?_⟩⟩
  · exact Nat.mul_div_le _ _
  · show (x ρ).val < ell ^ i' * ((x ρ).val / ell ^ i') + ell ^ i'
    have := Nat.div_add_mod (x ρ).val (ell ^ i')
    have := Nat.mod_lt (x ρ).val hn
    omega

#print axioms block_sub_Om
#print axioms anchor_sub_Om
#print axioms omGe_of_mem

end AdalyFormal.DirichletMono
