import C5B
import UNI_Base

/-!
# C5C -- HEADLINE.  The print's cube `tilde-square^5` (side `12 g`, `g = M ell^j`) intersected with `Omega_0` lies in ONE block-closed
union of level-`i` blocks which is simultaneously
 * a member of `UNI.AllC.IsClassUnion` (the union-headline class: union of level-`i` blocks, `subset B^i u B^{i+1}`, meets `B^i`, UNIQUE index),
 * a member of `IsClassSetW ell M (12*ell)` (additionally enclosed in a periodic box of side `12 ell * M ell^i`),
for EVERY admissible tower, EVERY `k`, EVERY `j <= k`, EVERY `D_j` cube (all 8 octants of the B^j block), provided `21*ell <= R`, `2 <= ell`, `0 < M`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.P409C5

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.P409W
open AdalyFormal.GeneralClass (IsClassSetW)
open UNI.AllC (IsClassUnion UnionAt)
open AdalyFormal.M1 (strat IsPatch patch gsp)

variable {L : PeriodicLatticeExtent}

/-- p.408: `c` is the centre of a `D_j` cube (a point of the level-`j` lattice `M ell^j Z^3`), which is a union of `2^3` level-`j` blocks
(`dCube`) with at least one of them inside `B^j(Lambda_j)`: some site `x0` of the cube lies in `B^j = Omega_j \ Omega_{j+1}`
(`B^j` is a union of level-`j` blocks, so the whole block of `x0` is in `B^j`). -/
def IsDCube (ell M k : ℕ) (S : Tower L) (j : ℕ) (c : PeriodicLatticeSite L) : Prop :=
  j ≤ k ∧ GridCorner (bigSide M ell j) c ∧ ∃ x₀ : PeriodicLatticeSite L, x₀ ∈ towerBj S j ∧ x₀ ∈ dCube (bigSide M ell j) c

theorem dCube_eq (g : ℕ) (c : PeriodicLatticeSite L) : dCube g c = cubeR c g := by
  unfold dCube tildeCube; congr 1; ring

theorem printedCube5_eq (g : ℕ) (c : PeriodicLatticeSite L) : printedCube5 g c = cubeR c (6 * g) := by
  unfold printedCube5 tildeCube; congr 1

theorem siteBox_mono {z : PeriodicLatticeSite L} {s s' : ℕ} (h : s ≤ s') : siteBox z s ⊆ siteBox z s' :=
  fun _ hx μ => lt_of_lt_of_le (hx μ) h

/-- the stratum index of a set inside `B^i u B^{i+1}` meeting `B^i` is unique on a monotone tower. -/
theorem union_index_unique {S : Tower L} (hmono : ∀ j : ℕ, S.Om (j + 1) ⊆ S.Om j)
    {sites : Set (PeriodicLatticeSite L)} {i i' : ℕ}
    (h1 : sites ⊆ towerBj S i ∪ towerBj S (i + 1)) (h2 : (sites ∩ towerBj S i).Nonempty)
    (h1' : sites ⊆ towerBj S i' ∪ towerBj S (i' + 1)) (h2' : (sites ∩ towerBj S i').Nonempty) : i = i' := by
  have key : ∀ {a b : ℕ}, a < b → sites ⊆ towerBj S b ∪ towerBj S (b + 1) → (sites ∩ towerBj S a).Nonempty → False := by
    intro a b hab hb ha
    obtain ⟨w, hw, hwB⟩ := ha
    have hw' := hb hw
    have hwb : w ∈ S.Om b := by
      rcases hw' with h | h
      · exact h.1
      · exact AdalyFormal.GeneralClass.om_anti hmono (Nat.le_succ b) h.1
    exact hwB.2 (AdalyFormal.GeneralClass.om_anti hmono (show a + 1 ≤ b by omega) hwb)
  rcases lt_trichotomy i i' with hlt | heq | hgt
  · exact (key hlt h1' h2).elim
  · exact heq
  · exact (key hgt h1 h2').elim

theorem cube5_in_union {ell M R k j : ℕ} {S : Tower L} {c : PeriodicLatticeSite L}
    (hell : 2 ≤ ell) (hM : 0 < M) (hR : 21 * ell ≤ R)
    (hA : Admissible ell M R k S) (hgt : ∀ μ : Fin 3, bigSide M ell k < L μ + 1)
    (hD : IsDCube ell M k S j c) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ),
      IsClassSetW ell M (12 * ell) k S sites i ∧ IsClassUnion ell M k S sites i ∧
      BlockClosed (bigSide M ell i) sites ∧
      (printedCube5 (bigSide M ell j) c ∩ S.Om 0) ⊆ sites := by
  obtain ⟨hjk, hgrid, x₀, hx0, hx0c⟩ := hD
  have hell0 : 0 < ell := by omega
  set g := bigSide M ell j with hg
  have hx0c' : x₀ ∈ cubeR c g := by rw [← dCube_eq]; exact hx0c
  have hP : ∀ y, y ∈ printedCube5 g c ↔ y ∈ cubeR c (6 * g) := by intro y; rw [printedCube5_eq]
  obtain ⟨i, hij, hdvd, hle, hsub, hmeet, htwo⟩ := region_core (K := 21) (P := printedCube5 g c) (x₀ := x₀)
    hell hM (by norm_num) hR hA hgt hjk hx0
    (fun y hy => by
      have := cube_dist hx0c' ((hP y).1 hy)
      omega)
    (by rw [printedCube5_eq]; exact cubeR_mono (by omega) hx0c')
    (fun μ s hs => by
      rw [printedCube5_eq]
      exact sh_mem_cube hx0c' (by omega) μ s hs)
  have hjk' : i ≤ k := le_trans hij hjk
  have hgipos : 0 < bigSide M ell i := bigSide_pos' hM hell0 i
  have hgN : ∀ μ : Fin 3, bigSide M ell i ∣ L μ + 1 := hA.2.2.1 i hjk'
  have hgc : ∀ μ : Fin 3, bigSide M ell i ∣ (c μ).val := fun μ =>
    dvd_trans hdvd (Nat.dvd_of_mod_eq_zero (hgrid μ))
  have hgr : bigSide M ell i ∣ 6 * g := Dvd.dvd.mul_left hdvd 6
  let sites : Set (PeriodicLatticeSite L) :=
    {x | ∃ y : PeriodicLatticeSite L, (y ∈ printedCube5 g c ∧ y ∈ S.Om 0) ∧
      ∀ μ : Fin 3, (y μ).val / bigSide M ell i = (x μ).val / bigSide M ell i}
  have hself : ∀ y, y ∈ printedCube5 g c → y ∈ S.Om 0 → y ∈ sites :=
    fun y h1 h2 => ⟨y, ⟨h1, h2⟩, fun _ => rfl⟩
  have hbc : BlockClosed (bigSide M ell i) sites := by
    intro x ⟨y, hy, hxy⟩ y' hy'
    exact ⟨y, hy, fun μ => (hxy μ).trans (hy' μ).symm⟩
  have hsubB : sites ⊆ towerBj S i ∪ towerBj S (i + 1) := by
    intro x ⟨y, ⟨hy1, hy0⟩, hxy⟩
    have hyb := hsub y hy1 hy0
    have hyi : y ∈ S.Om i ∧ y ∉ S.Om (i + 2) := by
      rcases hyb with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨h1, fun h3 => h2 (hA.1 (i + 1) h3)⟩
      · exact ⟨hA.1 i h1, h2⟩
    have hxy' : ∀ μ : Fin 3, (x μ).val / bigSide M ell i = (y μ).val / bigSide M ell i := fun μ => (hxy μ).symm
    have hxi : x ∈ S.Om i := om_cell hA (le_refl i) hyi.1 hxy'
    have hxn : x ∉ S.Om (i + 2) := fun h => hyi.2 (om_cell hA (show i ≤ i + 2 by omega) h hxy)
    by_cases hx1 : x ∈ S.Om (i + 1)
    · exact Or.inr ⟨hx1, hxn⟩
    · exact Or.inl ⟨hxi, hx1⟩
  have hmeetB : (sites ∩ towerBj S i).Nonempty := by
    obtain ⟨y, h1, h2, h3⟩ := hmeet
    exact ⟨y, hself y h1 h2, h3⟩
  have hbox : ∃ z : PeriodicLatticeSite L, sites ⊆ siteBox z (12 * ell * bigSide M ell i) := by
    refine ⟨zsite c (6 * g), fun x ⟨y, ⟨hy1, hy0⟩, hxy⟩ => ?_⟩
    have hyb : y ∈ siteBox (zsite c (6 * g)) (2 * (6 * g)) := by
      rw [printedCube5_eq] at hy1; exact cubeR_box c (6 * g) hy1
    have hxb : x ∈ siteBox (zsite c (6 * g)) (2 * (6 * g)) :=
      siteBox_closed hgipos hgN (zsite_dvd c (6 * g) _ hgN hgc hgr) (Dvd.dvd.mul_left hgr 2) hyb
        (fun μ => (hxy μ).symm)
    refine siteBox_mono ?_ hxb
    have : g ≤ ell * bigSide M ell i := hle
    nlinarith
  obtain ⟨a, ha, b, hb, ha0, hb0, μ, hμ⟩ := htwo
  refine ⟨sites, i, ⟨hjk', hsubB, hmeetB, hbox, a, hself a ha ha0, b, hself b hb hb0, μ, hμ⟩, ?_, hbc,
    fun y hy => hself y hy.1 hy.2⟩
  refine ⟨⟨hjk', hbc, hsubB, hmeetB⟩, fun i' hi' => ?_⟩
  exact (union_index_unique hA.1 hsubB hmeetB hi'.2.2.1 hi'.2.2.2).symm

/-- the `l^1`-patch/`IsPatch` presentation (as in `p409_setw_holds`) gives a `D_j` cube centred at the patch corner. -/
theorem IsPatch.toDCube {ell M R k j : ℕ} {S : Tower L} {w : PeriodicLatticeSite L}
    (hM : 0 < M) (hell : 0 < ell) (hA : Admissible ell M R k S) (hp : IsPatch ell M k 1 S j w) :
    IsDCube ell M k S j w := by
  obtain ⟨hjk, hgrid, x₀, hx0, hs, hq⟩ := hp
  have hg : gsp ell M 1 j = bigSide M ell j := by simp [gsp]
  rw [hg] at hgrid hq
  refine ⟨hjk, hgrid, x₀, ((AdalyFormal.M1.strat_eq_iff hA hjk x₀).2 ⟨hx0, hs⟩), ?_⟩
  rw [dCube_eq]
  intro μ
  have h1 := hgrid μ
  have h2 := hq μ
  have h3 := Nat.div_add_mod (x₀ μ).val (bigSide M ell j)
  have h4 := Nat.div_add_mod (w μ).val (bigSide M ell j)
  have h5 := Nat.mod_lt (x₀ μ).val (bigSide_pos' hM hell j)
  refine ⟨((x₀ μ).val : ℤ) - ((w μ).val : ℤ), ?_, ?_, ?_⟩
  · have : (w μ).val ≤ (x₀ μ).val := by
      rw [h2] at h3; omega
    omega
  · rw [h2] at h3; omega
  · exact (Int.ModEq.refl _).trans (by ring_nf; exact Int.ModEq.refl _)

end AdalyFormal.P409C5
