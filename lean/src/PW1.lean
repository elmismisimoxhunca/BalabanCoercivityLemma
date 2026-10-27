import M1B
import MS7

/-!
# PW1 -- the two-stratum PATCH TOWER of node W3 (M1 lane D) and its geometry

`patchTower j Rg` on any fine torus: `Ω_i = torus` for `i ≤ j`, `Ω_{j+1} = Rg`, `Ω_i = ∅` for `i ≥ j+2`; used at height `k = j+1`.
`PatchOK ell j Rg`: `Rg` is a union of `ell^{j+1}`-blocks (`BlockClosed`) and `ell^{j+1}` divides every torus side.
One-stratum cases: `Rg = univ` is the full tower of height `j+1` (`patchTower_univ`); `Rg = ∅` has no level-`j+1` rows.
* `lam_lt`, `mem_lam_j`, `mem_lam_succ` : the constraint sites of the tower geometry.
* `patch_proper` : `ProperTower (geomOf ell (j+1) (patchTower j Rg)) ell (j+1)` (lane C's S1-S4 apply).
* `om0_univ` : `Ω₀ = univ`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M1Patch

open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity (ProperTower)
open AdalyFormal.StatementLane (Tower BlockClosed scaleUp)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice inBlock)

variable {L : PeriodicLatticeExtent}

/-- the two-stratum patch tower (bottom level `j`, top region `Rg`). -/
def patchTower (j : ℕ) (Rg : Set (PeriodicLatticeSite L)) : Tower L where
  Om := fun i => if i ≤ j then Set.univ else if i = j + 1 then Rg else ∅

/-- admissible patch data: `Rg` a union of `ell^{j+1}` blocks, `ell^{j+1}` divides the torus sides. -/
def PatchOK (ell j : ℕ) (Rg : Set (PeriodicLatticeSite L)) : Prop :=
  BlockClosed (ell ^ (j + 1)) Rg ∧ ∀ μ : Fin 3, ell ^ (j + 1) ∣ L μ + 1

theorem om_le (j : ℕ) (Rg : Set (PeriodicLatticeSite L)) {i : ℕ} (hi : i ≤ j) :
    (patchTower j Rg).Om i = Set.univ := by simp [patchTower, hi]

theorem om_succ (j : ℕ) (Rg : Set (PeriodicLatticeSite L)) : (patchTower j Rg).Om (j + 1) = Rg := by
  simp [patchTower]

theorem om_gt (j : ℕ) (Rg : Set (PeriodicLatticeSite L)) {i : ℕ} (hi : j + 1 < i) :
    (patchTower j Rg).Om i = ∅ := by
  simp only [patchTower]
  rw [if_neg (by omega), if_neg (by omega)]

theorem om0_univ (j : ℕ) (Rg : Set (PeriodicLatticeSite L)) (ell : ℕ) :
    (geomOf ell (j + 1) (patchTower j Rg)).Om0 = Set.univ := om_le j Rg (Nat.zero_le j)

theorem patchTower_univ (ell j : ℕ) (Lu : PeriodicLatticeExtent) :
    patchTower (L := scaleUp ell (j + 1) Lu) j Set.univ = fullTower ell (j + 1) Lu := by
  unfold patchTower fullTower
  congr 1
  funext i
  by_cases h1 : i ≤ j
  · rw [if_pos h1, if_pos (by omega)]
  · by_cases h2 : i = j + 1
    · rw [if_neg h1, if_pos h2, if_pos (by omega)]
    · rw [if_neg h1, if_neg h2, if_neg (by omega)]

theorem lam_lt (ell j : ℕ) (Rg : Set (PeriodicLatticeSite L)) {i : ℕ} (hi : i < j) :
    (geomOf ell (j + 1) (patchTower j Rg)).Lam i = ∅ := by
  ext x
  simp only [geomOf, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]
  intro _ _
  rw [om_le j Rg (by omega : i + 1 ≤ j)]; trivial

theorem mem_lam_j (ell j : ℕ) (Rg : Set (PeriodicLatticeSite L)) (x : PeriodicLatticeSite L) :
    x ∈ (geomOf ell (j + 1) (patchTower j Rg)).Lam j ↔ (∀ μ : Fin 3, ell ^ j ∣ (x μ).val) ∧ x ∉ Rg := by
  simp only [geomOf, Set.mem_setOf_eq, om_le j Rg le_rfl, om_succ, Set.mem_univ, true_and]

theorem mem_lam_succ (ell j : ℕ) (Rg : Set (PeriodicLatticeSite L)) (x : PeriodicLatticeSite L) :
    x ∈ (geomOf ell (j + 1) (patchTower j Rg)).Lam (j + 1) ↔ (∀ μ : Fin 3, ell ^ (j + 1) ∣ (x μ).val) ∧ x ∈ Rg := by
  simp only [geomOf, Set.mem_setOf_eq, om_succ, om_gt j Rg (by omega : j + 1 < j + 1 + 1), Set.mem_empty_iff_false,
    not_false_eq_true, and_true]

theorem lam_gt (ell j : ℕ) (Rg : Set (PeriodicLatticeSite L)) {i : ℕ} (hi : j + 1 < i) :
    (geomOf ell (j + 1) (patchTower j Rg)).Lam i = ∅ := by
  ext x
  simp only [geomOf, Set.mem_setOf_eq, om_gt j Rg hi, Set.mem_empty_iff_false, false_and, and_false]

/-- arithmetic: inside an `n`-aligned interval of length `n`, the `n*ell`-quotient is constant. -/
theorem div_eq_of_aligned {n ell a x : ℕ} (hn : 0 < n) (ha : n ∣ a) (h1 : a ≤ x) (h2 : x < a + n) :
    a / (n * ell) = x / (n * ell) := by
  obtain ⟨t, rfl⟩ := ha
  rw [← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  congr 1
  rw [Nat.mul_div_cancel_left t hn]
  exact (Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith)).symm

/-- the `m`-aligned corner of a site. -/
def corner (m : ℕ) (x : PeriodicLatticeSite L) : PeriodicLatticeSite L :=
  fun μ => ⟨(x μ).val / m * m, lt_of_le_of_lt (Nat.div_mul_le_self _ _) (x μ).isLt⟩

theorem corner_dvd (m : ℕ) (x : PeriodicLatticeSite L) (μ : Fin 3) : m ∣ (corner m x μ).val :=
  Dvd.intro_left _ rfl

theorem mem_block_corner {m : ℕ} (hm : 0 < m) (x : PeriodicLatticeSite L) : x ∈ blockOf (corner m x) m := by
  rw [mem_blockOf]
  intro μ
  show (x μ).val / m * m ≤ (x μ).val ∧ (x μ).val < (x μ).val / m * m + m
  refine ⟨Nat.div_mul_le_self _ _, ?_⟩
  have := Nat.lt_div_mul_add (a := (x μ).val) hm
  linarith

/-- a site and every point of its `ell^j`-aligned block lie in the same `ell^{j+1}`-block. -/
theorem same_big_block {ell j : ℕ} (hell : 0 < ell) {y x : PeriodicLatticeSite L} (hy : ∀ μ : Fin 3, ell ^ j ∣ (y μ).val)
    (hx : x ∈ blockOf y (ell ^ j)) (μ : Fin 3) : (y μ).val / ell ^ (j + 1) = (x μ).val / ell ^ (j + 1) := by
  have h := (mem_blockOf.mp hx) μ
  rw [pow_succ]
  exact div_eq_of_aligned (pow_pos hell j) (hy μ) h.1 h.2

theorem same_block_div {m : ℕ} {y x : PeriodicLatticeSite L} (hm : 0 < m) (hy : ∀ μ : Fin 3, m ∣ (y μ).val)
    (hx : x ∈ blockOf y m) (μ : Fin 3) : (y μ).val / m = (x μ).val / m := by
  have h := (mem_blockOf.mp hx) μ
  have := div_eq_of_aligned (ell := 1) hm (hy μ) h.1 h.2
  simpa using this

/-- **the patch geometry is a `ProperTower`** (so lane C's S1–S4 apply to it). -/
theorem patch_proper {ell j : ℕ} (hell : 0 < ell) {Rg : Set (PeriodicLatticeSite L)} (hRg : BlockClosed (ell ^ (j + 1)) Rg) :
    ProperTower (geomOf ell (j + 1) (patchTower j Rg)) ell (j + 1) where
  ell_eq := rfl
  k_eq := rfl
  coarse := by
    intro i _ y hy
    rw [mem_CoarseLattice]
    intro μ
    exact Nat.mod_eq_zero_of_dvd (hy.1 μ)
  disj := by
    -- levels other than `j`, `j+1` are empty
    have key : ∀ {y y' : PeriodicLatticeSite L}, y ∈ (geomOf ell (j + 1) (patchTower j Rg)).Lam j →
        y' ∈ (geomOf ell (j + 1) (patchTower j Rg)).Lam (j + 1) →
        Disjoint (blockOf y (ell ^ j)) (blockOf y' (ell ^ (j + 1))) := by
      intro y y' hy hy'
      rw [mem_lam_j] at hy; rw [mem_lam_succ] at hy'
      rw [Finset.disjoint_left]
      intro x hx hx'
      have hxR : x ∈ Rg := hRg y' hy'.2 x (fun μ => (same_block_div (pow_pos hell _) hy'.1 hx' μ).symm)
      exact hy.2 (hRg x hxR y (fun μ => same_big_block hell hy.1 hx μ))
    intro i i' hi hi' y hy y' hy' hne
    have hlev : ∀ {m : ℕ}, m ≤ j + 1 → ∀ {z : PeriodicLatticeSite L},
        z ∈ (geomOf ell (j + 1) (patchTower j Rg)).Lam m → m = j ∨ m = j + 1 := by
      intro m hm z hz
      by_contra h
      push Not at h
      rw [lam_lt ell j Rg (by omega : m < j)] at hz
      exact hz
    rcases hlev hi hy with rfl | rfl <;> rcases hlev hi' hy' with rfl | rfl
    · have hne' : y ≠ y' := hne.resolve_left (fun h => h rfl)
      rw [Finset.disjoint_left]
      intro x hx hx'
      apply hne'; funext μ; apply Fin.ext
      have a1 := same_block_div (pow_pos hell _) hy.1 hx μ
      have a2 := same_block_div (pow_pos hell _) hy'.1 hx' μ
      have e1 := (Nat.div_mul_cancel (hy.1 μ)).symm
      have e2 := (Nat.div_mul_cancel (hy'.1 μ)).symm
      rw [e1, e2, a1, a2]
    · exact key hy hy'
    · exact (key hy' hy).symm
    · have hne' : y ≠ y' := hne.resolve_left (fun h => h rfl)
      rw [Finset.disjoint_left]
      intro x hx hx'
      apply hne'; funext μ; apply Fin.ext
      have a1 := same_block_div (pow_pos hell _) hy.1 hx μ
      have a2 := same_block_div (pow_pos hell _) hy'.1 hx' μ
      have e1 := (Nat.div_mul_cancel (hy.1 μ)).symm
      have e2 := (Nat.div_mul_cancel (hy'.1 μ)).symm
      rw [e1, e2, a1, a2]
  cover := by
    intro x
    rw [om0_univ]
    simp only [Set.mem_univ, true_iff]
    by_cases hx : x ∈ Rg
    · refine ⟨j + 1, le_rfl, corner (ell ^ (j + 1)) x, ?_, mem_block_corner (pow_pos hell _) x⟩
      rw [mem_lam_succ]
      refine ⟨corner_dvd _ x, hRg x hx _ (fun μ => ?_)⟩
      exact (same_block_div (pow_pos hell _) (corner_dvd _ x) (mem_block_corner (pow_pos hell _) x) μ)
    · refine ⟨j, by omega, corner (ell ^ j) x, ?_, mem_block_corner (pow_pos hell _) x⟩
      rw [mem_lam_j]
      refine ⟨corner_dvd _ x, fun hc => hx (hRg _ hc x (fun μ => ?_))⟩
      exact (same_big_block hell (corner_dvd _ x) (mem_block_corner (pow_pos hell _) x) μ).symm

#print axioms patch_proper
#print axioms patchTower_univ

end AdalyFormal.M1Patch
