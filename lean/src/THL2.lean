import THL1

/-!
# TL2 -- a non-radial thin layer is not an instance of `Admissible` at ANY radius (lane thin_layer_20261019)

CMP99b p.394 allows `Omega_0` to be any union of big blocks of `T_1` with `Omega_1 ⊂ Omega_0` ("we may add to `Omega_1` a thinner layer of the big
blocks surrounding `Omega_1`").  The frozen `Admissible` pins `Omega_0` to ONE shape: the union of `M`-blocks within `R M` of `Omega_1` (T6).
Here: on the 120-site torus, `ell = 2`, `M = 2`, `k = 1`, `Omega_1 = [20,100)` (direction 0) and `Omega_0 = [8,108)` (layer 12 on the left, 8 on the right):
* `asym_adm5` : the clauses T1-T5 of `Admissible` hold at radius `R = 4`;
* `asym_not_admissible` : for EVERY `R`, `Admissible 2 2 R 1 asymTower` is false (the layer is not a radial `R M`-neighbourhood).
So the radial reduction of `TL1` does not reach it: a non-radial layer needs the base-law clause (T6) of the pipeline to be generalised, not merely re-parametrised.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000

namespace AdalyFormal.ThinLayer

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane

/-- the clauses T1-T5 of `Admissible` (the first five conjuncts), at one radius `R`. -/
def AdmNoBase {L : PeriodicLatticeExtent} (ell M R k : ℕ) (S : Tower L) : Prop :=
  (∀ j : ℕ, S.Om (j + 1) ⊆ S.Om j) ∧
  (∀ j : ℕ, k < j → S.Om j = ∅) ∧
  (∀ j : ℕ, j ≤ k → ∀ μ : Fin 3, bigSide M ell j ∣ (L μ + 1)) ∧
  (∀ j : ℕ, j ≤ k → BlockClosed (bigSide M ell j) (S.Om j)) ∧
  (∀ j : ℕ, j ≤ k → ∀ x : PeriodicLatticeSite L, x ∉ S.Om j →
      ∀ y ∈ S.Om (j + 1), R * bigSide M ell j < pdist x y)

/-- the 120-site torus (`L + 1 = 120` in every direction). -/
def Lasym : PeriodicLatticeExtent := fun _ => 119

/-- `Omega_0 = [8,108)`, `Omega_1 = [20,100)` in direction 0, `Omega_j = ∅` for `j ≥ 2`. -/
def asymTower : Tower Lasym :=
  ⟨fun j => if j = 0 then {x | 8 ≤ (x 0).val ∧ (x 0).val < 108}
    else if j = 1 then {x | 20 ≤ (x 0).val ∧ (x 0).val < 100} else ∅⟩

theorem asym_om0 (x : PeriodicLatticeSite Lasym) :
    x ∈ asymTower.Om 0 ↔ 8 ≤ (x 0).val ∧ (x 0).val < 108 := by simp [asymTower]
theorem asym_om1 (x : PeriodicLatticeSite Lasym) :
    x ∈ asymTower.Om 1 ↔ 20 ≤ (x 0).val ∧ (x 0).val < 100 := by simp [asymTower]
theorem asym_om2 (j : ℕ) (hj : 2 ≤ j) (x : PeriodicLatticeSite Lasym) : x ∉ asymTower.Om j := by
  have h0 : j ≠ 0 := by omega
  have h1 : j ≠ 1 := by omega
  simp [asymTower, h0, h1]

theorem pdist_ge0 {L : PeriodicLatticeExtent} (x y : PeriodicLatticeSite L) :
    pcd (L 0 + 1) (x 0).val (y 0).val ≤ pdist x y :=
  Finset.single_le_sum (f := fun μ : Fin 3 => pcd (L μ + 1) (x μ).val (y μ).val) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ 0)

theorem xlt (x : PeriodicLatticeSite Lasym) : (x 0).val < 120 := by
  have := (x 0).isLt
  simpa [Lasym] using this

theorem asym_adm5 : AdmNoBase 2 2 4 1 asymTower := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j x hx
    rcases Nat.lt_or_ge j 1 with hj | hj
    · have : j = 0 := by omega
      subst this
      rw [asym_om1] at hx
      rw [asym_om0]; omega
    · exact absurd hx (asym_om2 (j + 1) (by omega) x)
  · intro j hj
    ext x
    exact ⟨fun hx => absurd hx (asym_om2 j (by omega) x), fun h => h.elim⟩
  · intro j hj μ
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · simp only [bigSide, Lasym]; norm_num
    · simp only [bigSide, Lasym]; norm_num
  · intro j hj
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · intro x hx y hy
      have hs : bigSide 2 2 0 = 2 := by simp [bigSide]
      rw [hs] at hy
      rw [asym_om0] at hx ⊢
      have h0 := hy 0
      omega
    · intro x hx y hy
      have hs : bigSide 2 2 1 = 4 := by simp [bigSide]
      rw [hs] at hy
      rw [asym_om1] at hx ⊢
      have h0 := hy 0
      omega
  · intro j hj x hx y hy
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · rw [asym_om0] at hx
      rw [asym_om1] at hy
      have hs : bigSide 2 2 0 = 2 := by simp [bigSide]
      rw [hs]
      have hx0 := xlt x
      have hy0 := xlt y
      refine lt_of_lt_of_le ?_ (pdist_ge0 x y)
      simp only [Lasym]
      unfold pcd
      split_ifs <;> omega
    · exact absurd hy (asym_om2 (1 + 1) (by omega) y)

/-- the base-law clause (T6) at radius `R` for the block size `M = 2`: the shape shared by `Admissible` (T6) and `AdmSplit` (T6). -/
def BaseLaw2 (R : ℕ) : Prop :=
  ∀ x : PeriodicLatticeSite Lasym, x ∈ asymTower.Om 0 ↔
    ∃ y ∈ asymTower.Om 1, ∃ z : PeriodicLatticeSite Lasym,
      (∀ μ : Fin 3, (z μ).val / 2 = (x μ).val / 2) ∧ pdist z y ≤ R * 2

/-- **the layer is not radial**: for every radius `R`, `asymTower` fails the base law (T6). -/
theorem asym_not_baseLaw (R : ℕ) : ¬ BaseLaw2 R := by
  intro h6
  -- the left edge `x₀ = 8` is in `Omega_0`: some site of its block is within `2R` of `Omega_1`, forcing `2R ≥ 12`
  let x8 : PeriodicLatticeSite Lasym := fun _ => ⟨8, by simp [Lasym]⟩
  have hx8 : x8 ∈ asymTower.Om 0 := by rw [asym_om0]; show 8 ≤ 8 ∧ 8 < 108; omega
  obtain ⟨y, hy, z, hz, hd⟩ := (h6 x8).1 hx8
  rw [asym_om1] at hy
  have hz0 : (z 0).val / 2 = (x8 0).val / 2 := hz 0
  have hx80 : (x8 0).val = 8 := rfl
  have hzl := xlt z
  have hyl := xlt y
  have hc := le_trans (pdist_ge0 z y) hd
  simp only [Lasym] at hc
  unfold pcd at hc
  have hR : 6 ≤ R := by
    rw [hx80] at hz0
    split_ifs at hc <;> omega
  -- the site `x₀ = 108` is outside `Omega_0` but within `2R` (>= 12) of the site `x₀ = 99 ∈ Omega_1`
  let x108 : PeriodicLatticeSite Lasym := fun _ => ⟨108, by simp [Lasym]⟩
  let y99 : PeriodicLatticeSite Lasym := fun μ => ⟨if μ = 0 then 99 else 108, by simp [Lasym]; split_ifs <;> omega⟩
  have hy99 : y99 ∈ asymTower.Om 1 := by rw [asym_om1]; show 20 ≤ 99 ∧ 99 < 100; omega
  have hn : x108 ∉ asymTower.Om 0 := by rw [asym_om0]; show ¬ (8 ≤ 108 ∧ 108 < 108); omega
  apply hn
  refine (h6 x108).2 ⟨y99, hy99, x108, fun μ => rfl, ?_⟩
  unfold pdist
  rw [Fin.sum_univ_three]
  have e1 : pcd (Lasym 0 + 1) (x108 0).val (y99 0).val = 9 := by
    show pcd (119 + 1) 108 99 = 9
    norm_num [pcd]
  have e2 : pcd (Lasym 1 + 1) (x108 1).val (y99 1).val = 0 := by
    show pcd (119 + 1) 108 108 = 0
    norm_num [pcd]
  have e3 : pcd (Lasym 2 + 1) (x108 2).val (y99 2).val = 0 := by
    show pcd (119 + 1) 108 108 = 0
    norm_num [pcd]
  rw [e1, e2, e3]
  omega

theorem asym_not_admissible (R : ℕ) : ¬ Admissible 2 2 R 1 asymTower := by
  intro hA
  obtain ⟨-, -, -, -, -, h6⟩ := hA
  exact asym_not_baseLaw R h6

/-- the same for the tower class with a separate level-0 radius: no `R0`, no `Rs`. -/
theorem asym_not_admSplit (R0 : ℕ) (Rs : ℕ → ℕ) : ¬ AdmSplit 2 2 R0 Rs 1 asymTower := by
  intro hA
  obtain ⟨-, -, -, -, -, -, h6⟩ := hA
  exact asym_not_baseLaw R0 h6

/-- the statement of the failure, quantified: no radius makes `asymTower` an `Admissible` tower, while T1-T5 hold at radius `4`. -/
theorem asym_thin_not_radial :
    AdmNoBase 2 2 4 1 asymTower ∧ ∀ R : ℕ, ¬ Admissible 2 2 R 1 asymTower :=
  ⟨asym_adm5, asym_not_admissible⟩

end AdalyFormal.ThinLayer

#print axioms AdalyFormal.ThinLayer.asym_adm5
#print axioms AdalyFormal.ThinLayer.asym_not_baseLaw
#print axioms AdalyFormal.ThinLayer.asym_not_admissible
#print axioms AdalyFormal.ThinLayer.asym_not_admSplit
#print axioms AdalyFormal.ThinLayer.asym_thin_not_radial
