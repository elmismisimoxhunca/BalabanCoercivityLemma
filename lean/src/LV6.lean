import LV5

/-!
# LV6 -- the two-stratum patch: regrouping, layers, the face relation, and the exact identity
`S + ℓ² Bg = Dev + Loc`

`n = ℓ^j`, `N = ℓ^j ℓ`; `Rg` a union of `N`-blocks; `N ∣ L+1`.
* `regroup` : `Σ_{z ∈ nℤ³} h z = Σ_{Z ∈ Nℤ³} Σ_{i ∈ cube ℓ} h (Z + off (n i))`.
* `tz Z k μ = Z + off (n k) + (n(ℓ-1)) e_μ` (top layer of the block `Z`), `bz Z k = Z + off (n k)` (bottom layer).
* `face_rel` : `Fl n N c Z μ = ℓ⁻² Σ_{k ∈ face ℓ μ} Fl n n c (tz Z k μ) μ` (exact).
* `small_regroup` : the summation-by-parts boundary terms of the small rows, regrouped by big blocks.
* `key_identity` : `S + ℓ² Bg = Dev + Loc` (exact, for divergence-free `c`).
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace AdalyFormal.LemIFlat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf)
open AdalyFormal.FlatCoercivity (eU)
open AdalyFormal.StatementLane (BlockClosed)
open AdalyFormal.M1Patch (corner corner_dvd)

variable {L : PeriodicLatticeExtent}

/-- top-layer cell of the block `Z` in direction `μ` -/
def tz (n ℓ : ℕ) (Z : PeriodicLatticeSite L) (k : Fin 3 → ℕ) (μ : Fin 3) : PeriodicLatticeSite L :=
  Z + off L (n • k) + (n * (ℓ - 1)) • eU L μ

/-- bottom-layer cell -/
def bz (n : ℕ) (Z : PeriodicLatticeSite L) (k : Fin 3 → ℕ) : PeriodicLatticeSite L := Z + off L (n • k)

theorem off_smul_update (n : ℕ) (i : Fin 3 → ℕ) (μ : Fin 3) (s : ℕ) :
    off L (n • i) = off L (n • Function.update i μ s) + (n * i μ) • eU L μ - (n * s) • eU L μ := by
  have h1 : i = Function.update i μ 0 + Pi.single μ (i μ) := by
    funext ν; by_cases h : ν = μ
    · subst h; simp
    · simp [Function.update_of_ne h, h]
  have h2 : Function.update i μ s = Function.update i μ 0 + Pi.single μ s := by
    funext ν; by_cases h : ν = μ
    · subst h; simp
    · simp [Function.update_of_ne h, h]
  rw [h2]
  conv_lhs => rw [h1]
  rw [smul_add, smul_add, off_add, off_add, ← Pi.single_smul, ← Pi.single_smul, off_single, off_single]
  simp only [smul_eq_mul]
  abel

theorem nat_layer (n ℓ : ℕ) (hn : 0 < n) (hℓ : 0 < ℓ) : n * (ℓ - 1) + (n - 1) = n * ℓ - 1 := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring_nf
  omega

/-- **the face relation**: the big face flux is the mean of the small face fluxes of the top layer. -/
theorem face_rel (c : Bond L → SuTwo) (n ℓ : ℕ) (hn : 0 < n) (hℓ : 0 < ℓ) (Z : PeriodicLatticeSite L) (μ : Fin 3) :
    Fl n (n * ℓ) c Z μ = (((ℓ : ℝ) ^ 2)⁻¹) • ∑ k ∈ face ℓ μ, Fl n n c (tz n ℓ Z k μ) μ := by
  unfold Fl flx tz
  simp only [face_decomp n ℓ hn μ]
  simp only [← Finset.smul_sum, smul_smul]
  congr 1
  · push_cast; field_simp
  · refine (Finset.sum_comm).trans ?_
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun v _ => Finset.sum_congr rfl (fun x _ => ?_)))
    have e : (n * ℓ - 1) • eU L μ = (n * (ℓ - 1)) • eU L μ + (n - 1) • eU L μ := by
      rw [← add_nsmul, nat_layer n ℓ hn hℓ]
    rw [off_add, e]
    congr 2
    abel

section patch
variable {ell j : ℕ} (hell : 0 < ell) {Rg : Set (PeriodicLatticeSite L)} (hRg : BlockClosed (ell ^ (j + 1)) Rg)
  (hdvd : ∀ μ : Fin 3, ell ^ (j + 1) ∣ L μ + 1)

include hell hdvd in
theorem regroup {M : Type*} [AddCommMonoid M] (h : PeriodicLatticeSite L → M) :
    ∑ z ∈ latF L (ell ^ j), h z = ∑ Z ∈ latF L (ell ^ j * ell), ∑ i ∈ cube ell, h (Z + off L (ell ^ j • i)) := by
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_nbij' (fun p => p.1 + off L (ell ^ j • p.2))
    (fun z => (corner (ell ^ (j + 1)) z, idx (ell ^ j) (ell ^ (j + 1)) z)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨Z, i⟩ hp
    simp only [Finset.mem_product, mem_latF] at hp
    rw [mem_latF]
    intro μ
    rw [← iota_eq_off]
    exact iota_onLat ell j hell hdvd Z hp.1 i hp.2 μ
  · intro z hz
    rw [mem_latF] at hz
    simp only [Finset.mem_product, mem_latF]
    exact ⟨corner_dvd _ z, idx_mem_cube ell j hell hdvd z hz⟩
  · rintro ⟨Z, i⟩ hp
    simp only [Finset.mem_product, mem_latF] at hp
    simp only [← iota_eq_off]
    rw [corner_iota ell j hell hdvd Z hp.1 i hp.2, idx_iota ell j hell hdvd Z hp.1 i hp.2]
  · intro z hz
    rw [mem_latF] at hz
    simp only [← iota_eq_off]
    exact iota_idx ell j hell hdvd z hz
  · intro _ _; rfl

include hell hRg hdvd in
theorem cell_Rg (Z : PeriodicLatticeSite L) (hZ : OnLatN (ell ^ j * ell) Z) (i : Fin 3 → ℕ) (hi : i ∈ cube ell) :
    Z + off L (ell ^ j • i) ∈ Rg ↔ Z ∈ Rg := by
  rw [← iota_eq_off]
  exact mem_Rg_of_block hell hRg hZ (iota_mem_block ell j hell hdvd Z hZ i hi)

include hell hRg hdvd in
/-- the up-neighbour of a cell: inside the block, or (top layer) in the next block. -/
theorem up_Rg (Z : PeriodicLatticeSite L) (hZ : OnLatN (ell ^ j * ell) Z) (hZR : Z ∉ Rg) (i : Fin 3 → ℕ)
    (hi : i ∈ cube ell) (μ : Fin 3) :
    Z + off L (ell ^ j • i) + ell ^ j • eU L μ ∈ Rg ↔ (i μ = ell - 1 ∧ Z + (ell ^ j * ell) • eU L μ ∈ Rg) := by
  have hdN : ∀ ν : Fin 3, ell ^ j * ell ∣ L ν + 1 := hdvd
  have hiμ : i μ < ell := (mem_cube ell i).mp hi μ
  by_cases htop : i μ = ell - 1
  · have hZ' : OnLatN (ell ^ j * ell) (Z + (ell ^ j * ell) • eU L μ) :=
      (onLat_add_iff hdN Z _ (onLat_smul_eU hdN μ)).mpr hZ
    have hi' : Function.update i μ 0 ∈ cube ell := by
      rw [mem_cube]; intro ν
      by_cases h : ν = μ
      · subst h; simp; omega
      · rw [Function.update_of_ne h]; exact (mem_cube ell i).mp hi ν
    have e : Z + off L (ell ^ j • i) + ell ^ j • eU L μ
        = (Z + (ell ^ j * ell) • eU L μ) + off L (ell ^ j • Function.update i μ 0) := by
      rw [off_smul_update (ell ^ j) i μ 0, htop]
      have : ell ^ j * ell = ell ^ j * (ell - 1) + ell ^ j := by
        obtain ⟨e', he'⟩ : ∃ e', ell = e' + 1 := ⟨ell - 1, by omega⟩
        rw [he', Nat.add_sub_cancel]; ring
      rw [this, add_nsmul, mul_zero, zero_smul, sub_zero]
      abel
    rw [e, cell_Rg hell hRg hdvd _ hZ' _ hi']
    simp [htop]
  · have hlt : i μ + 1 < ell := by omega
    have hi' : Function.update i μ (i μ + 1) ∈ cube ell := by
      rw [mem_cube]; intro ν
      by_cases h : ν = μ
      · subst h; simp; omega
      · rw [Function.update_of_ne h]; exact (mem_cube ell i).mp hi ν
    have e : Z + off L (ell ^ j • i) + ell ^ j • eU L μ = Z + off L (ell ^ j • Function.update i μ (i μ + 1)) := by
      rw [off_smul_update (ell ^ j) i μ (i μ + 1)]
      rw [show ell ^ j * (i μ + 1) = ell ^ j * i μ + ell ^ j by ring, add_nsmul]
      abel
    rw [e, cell_Rg hell hRg hdvd _ hZ _ hi']
    simp [htop, hZR]

include hell hRg hdvd in
/-- the down-neighbour of a cell. -/
theorem down_Rg (Z : PeriodicLatticeSite L) (hZ : OnLatN (ell ^ j * ell) Z) (hZR : Z ∉ Rg) (i : Fin 3 → ℕ)
    (hi : i ∈ cube ell) (μ : Fin 3) :
    Z + off L (ell ^ j • i) - ell ^ j • eU L μ ∈ Rg ↔ (i μ = 0 ∧ Z - (ell ^ j * ell) • eU L μ ∈ Rg) := by
  have hdN : ∀ ν : Fin 3, ell ^ j * ell ∣ L ν + 1 := hdvd
  have hiμ : i μ < ell := (mem_cube ell i).mp hi μ
  by_cases hbot : i μ = 0
  · have hZ' : OnLatN (ell ^ j * ell) (Z - (ell ^ j * ell) • eU L μ) := by
      rw [sub_eq_add_neg]
      exact (onLat_add_iff hdN Z _ (onLat_neg hdN _ (onLat_smul_eU hdN μ))).mpr hZ
    have hi' : Function.update i μ (ell - 1) ∈ cube ell := by
      rw [mem_cube]; intro ν
      by_cases h : ν = μ
      · subst h; simp; omega
      · rw [Function.update_of_ne h]; exact (mem_cube ell i).mp hi ν
    have e : Z + off L (ell ^ j • i) - ell ^ j • eU L μ
        = (Z - (ell ^ j * ell) • eU L μ) + off L (ell ^ j • Function.update i μ (ell - 1)) := by
      rw [off_smul_update (ell ^ j) i μ (ell - 1), hbot]
      have : ell ^ j * ell = ell ^ j * (ell - 1) + ell ^ j := by
        obtain ⟨e', he'⟩ : ∃ e', ell = e' + 1 := ⟨ell - 1, by omega⟩
        rw [he', Nat.add_sub_cancel]; ring
      rw [this, add_nsmul, mul_zero, zero_smul, add_zero]
      abel
    rw [e, cell_Rg hell hRg hdvd _ hZ' _ hi']
    simp [hbot]
  · have hi' : Function.update i μ (i μ - 1) ∈ cube ell := by
      rw [mem_cube]; intro ν
      by_cases h : ν = μ
      · subst h; simp; omega
      · rw [Function.update_of_ne h]; exact (mem_cube ell i).mp hi ν
    have e : Z + off L (ell ^ j • i) - ell ^ j • eU L μ = Z + off L (ell ^ j • Function.update i μ (i μ - 1)) := by
      rw [off_smul_update (ell ^ j) i μ (i μ - 1)]
      have : ell ^ j * i μ = ell ^ j * (i μ - 1) + ell ^ j := by
        obtain ⟨e', he'⟩ : ∃ e', i μ = e' + 1 := ⟨i μ - 1, by omega⟩
        rw [he', Nat.add_sub_cancel]; ring
      rw [this, add_nsmul]
      abel
    rw [e, cell_Rg hell hRg hdvd _ hZ _ hi']
    simp [hbot, hZR]

end patch

#print axioms tz
#print axioms bz
#print axioms off_smul_update
#print axioms nat_layer
#print axioms face_rel
#print axioms regroup
#print axioms cell_Rg
#print axioms up_Rg
#print axioms down_Rg

end AdalyFormal.LemIFlat
