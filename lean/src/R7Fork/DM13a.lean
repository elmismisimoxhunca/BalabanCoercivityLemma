import R7Fork.DM12

/-!
# DM13a -- level structure of an admissible tower: the level `lev x` of a site, its stratum block `stBlock x` (the `ell^lev`-block of the
`Lambda_lev` centre containing `x`), and the facts the "adjacency induction" of DM13 needs.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000
namespace AdalyFormal.DirichletMono

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp Tower Admissible bigSide BlockClosed)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice mem_CoarseLattice)

section levels
variable {L : PeriodicLatticeExtent}

/-- `i` is the level of `x` -/
def IsLev (S : Tower L) (k : ℕ) (x : PeriodicLatticeSite L) (i : ℕ) : Prop :=
  i ≤ k ∧ (i = 0 ∨ x ∈ S.Om i) ∧ x ∉ S.Om (i + 1)

theorem isLev_unique {S : Tower L} (hS : ∀ j, S.Om (j + 1) ⊆ S.Om j) {k : ℕ} {x : PeriodicLatticeSite L} {i j : ℕ}
    (hi : IsLev S k x i) (hj : IsLev S k x j) : i = j := by
  have key : ∀ i j, IsLev S k x i → IsLev S k x j → i ≤ j := by
    intro i j hi hj
    by_contra h
    push_neg at h
    -- j < i
    have hi0 : i ≠ 0 := by omega
    have hxi : x ∈ S.Om i := hi.2.1.resolve_left hi0
    exact hj.2.2 (om_anti S hS (by omega : j + 1 ≤ i) hxi)
  exact le_antisymm (key i j hi hj) (key j i hj hi)

theorem exists_isLev {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (x : PeriodicLatticeSite L) :
    ∃ i, IsLev S k x i := by
  classical
  have hex : ∃ m, x ∉ S.Om (m + 1) :=
    ⟨k, by rw [hS.2.1 (k + 1) (Nat.lt_succ_self k)]; exact Set.notMem_empty x⟩
  refine ⟨Nat.find hex, Nat.find_min' hex (by rw [hS.2.1 (k + 1) (Nat.lt_succ_self k)]; exact Set.notMem_empty x),
    ?_, Nat.find_spec hex⟩
  rcases h : Nat.find hex with _ | m'
  · exact Or.inl rfl
  · right
    by_contra hx
    have := Nat.find_min hex (m := m') (by omega)
    exact this hx

/-- the level function -/
noncomputable def lev (S : Tower L) (x : PeriodicLatticeSite L) : ℕ := by
  classical exact if h : ∃ m, x ∉ S.Om (m + 1) then Nat.find h else 0

theorem lev_spec {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (x : PeriodicLatticeSite L) :
    IsLev S k x (lev S x) := by
  classical
  have hex : ∃ m, x ∉ S.Om (m + 1) :=
    ⟨k, by rw [hS.2.1 (k + 1) (Nat.lt_succ_self k)]; exact Set.notMem_empty x⟩
  have h := Classical.choose_spec (exists_isLev hS x)
  have hl : lev S x = Nat.find hex := by
    unfold lev; rw [dif_pos hex]
  rw [hl]
  refine ⟨Nat.find_min' hex (by rw [hS.2.1 (k + 1) (Nat.lt_succ_self k)]; exact Set.notMem_empty x), ?_,
    Nat.find_spec hex⟩
  rcases h2 : Nat.find hex with _ | m'
  · exact Or.inl rfl
  · right
    by_contra hx
    have := Nat.find_min hex (m := m') (by omega)
    exact this hx

/-- the `n`-aligned anchor of `x` -/
def anc (n : ℕ) (x : PeriodicLatticeSite L) : PeriodicLatticeSite L :=
  fun ρ => ⟨n * ((x ρ).val / n), lt_of_le_of_lt (Nat.mul_div_le _ _) (x ρ).isLt⟩

theorem anc_val (n : ℕ) (x : PeriodicLatticeSite L) (ρ : Fin 3) : ((anc n x) ρ).val = n * ((x ρ).val / n) := rfl

theorem anc_coarse {n : ℕ} (x : PeriodicLatticeSite L) : anc n x ∈ CoarseLattice L n := by
  rw [mem_CoarseLattice]
  intro ρ
  rw [anc_val]
  exact Nat.mul_mod_right _ _

theorem mem_block_anc {n : ℕ} (hn : 0 < n) (x : PeriodicLatticeSite L) : x ∈ blockOf (anc n x) n := by
  rw [mem_blockOf]
  intro ρ
  rw [anc_val]
  have h1 := Nat.div_add_mod (x ρ).val n
  have h2 := Nat.mod_lt (x ρ).val hn
  constructor <;> omega

theorem anc_eq_of_mem {n : ℕ} (hn : 0 < n) {y x : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L n)
    (hx : x ∈ blockOf y n) : anc n x = y := by
  funext ρ
  apply Fin.ext
  rw [anc_val]
  have h := (mem_blockOf.mp hx) ρ
  obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero ((mem_CoarseLattice.mp hy) ρ)
  have : (x ρ).val / n = q := by
    apply Nat.div_eq_of_lt_le
    · rw [mul_comm]; omega
    · rw [add_mul, one_mul, mul_comm]; omega
  rw [this, hq]

/-- the stratum block of `x` -/
noncomputable def stBlock (ell : ℕ) (S : Tower L) (x : PeriodicLatticeSite L) : Finset (PeriodicLatticeSite L) :=
  blockOf (anc (ell ^ lev S x) x) (ell ^ lev S x)

end levels

end AdalyFormal.DirichletMono
