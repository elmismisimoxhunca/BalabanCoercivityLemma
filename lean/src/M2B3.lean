import M2B2
import ZT5D2

/-!
# M2B3 -- B0 counterexample at a tower satisfying EVERY tower hypothesis of `M1Core` (m2_bridge_20261014, Layer B)

`TT` (ZR2B9/ZT5D): `ell = 2`, `M = 2`, `R = 6`, `k = 1`, torus `120` per direction, `Ω₁ = {20 ≤ x₀ < 100}`, `Ω₀ = {8 ≤ x₀ < 112}`,
`Ω₂ = ∅`.  By `proper_tower_hyps_p` this tower has `TorusOK`, `Admissible 2 2 6 1`, `CoversOm0p 2 2 12 1`, `LambdaOK2` (the non-vacuity
package of `M1Core`'s tower hypotheses).  The G3 patch `(j,w) = (1, (24,0,0))` with `κ = 1`, `c = 5` is an `IsPatch` (anchor `w` itself, stratum 1),
its `ℓ¹` ball (radius `5·4 = 20`) contains `v = (10,0,0)` of stratum 0, and `12·bigSide 2 2 0 = 24 ≤ 2·(5·4) = 40`: by `patch_inter_not_in_class_cube` (far pair `w ± 20 e₁`, both in `Ω₀`)
NO class cube (factor 12, any index) contains `patch ∩ Ω₀`.

* `b0_counterexample` : the statement (conclusion: no class cube contains `patch ∩ Ω₀`).
* `TTR` family : `ell = 2`, `M = 2`, `k = 1`, ARBITRARY `R ≥ 2`, torus `8R + 120`, `Ω₁ = [4R+8, 4R+88)`, `Ω₀ = [2R+8, 6R+88)` (= `Ω₁` widened by
  `R·M = 2R`): `TTR_admissible` and the same obstruction (`b0_counterexample_R`) at every `R ≥ 2`: the proof of the obstruction uses only the sizes
  `f·M·ell^(j-1)` vs `c·κ·M·ell^j`, a stratum-`(j-1)` site and a far pair inside the patch -- none depends on `R`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.M2Bridge

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG
open AdalyFormal.M1 (strat strat_eq_iff IsPatch patch gsp)

/-! ## the R = 6 witness -/

theorem b0_counterexample {Lu Lf : PeriodicLatticeExtent} (hLu : ∀ μ, Lu μ + 1 = 60) (hLf : ∀ μ, Lf μ + 1 = 120)
    {α₀ : ℝ} (hα : 0 < α₀) (hα1 : α₀ ≤ 1 / 2) :
    TorusOK 2 2 Lu ∧ Admissible 2 2 6 1 (TT Lf) ∧ CoversOm0p 2 2 12 1 (TT Lf) ∧ LambdaOK2 (Lu := Lu) (Lf := Lf) 2 2 6 1 (TT Lf) (LamT Lu) ∧
    ∃ w : PeriodicLatticeSite Lf, IsPatch 2 2 1 1 (TT Lf) 1 w ∧
      ¬ ∃ (sites : Set (PeriodicLatticeSite Lf)) (i : ℕ), IsClassCube 2 2 12 1 (TT Lf) sites i ∧
          {y | y ∈ patch 2 2 1 5 1 w ∧ y ∈ (TT Lf).Om 0} ⊆ sites := by
  obtain ⟨h1, h2, h3, -, -, -, h7, -, -, -⟩ := proper_tower_hyps_p hLu hLf hα hα1
  refine ⟨h1, h2, h3, h7, ?_⟩
  have hN0 := hLf 0
  let w : PeriodicLatticeSite Lf := fun μ => ⟨if μ = 0 then 24 else 0, by have := hLf μ; split_ifs <;> omega⟩
  have hw0 : (w 0).val = 24 := by simp [w]
  have hw1 : (w 1).val = 0 := by simp [w]
  have hw2 : (w 2).val = 0 := by simp [w]
  have hwOm1 : w ∈ (TT Lf).Om 1 := by
    simp only [TT, if_neg (by decide : (1 : ℕ) ≠ 0), if_true, OmB, Set.mem_setOf_eq]; omega
  have hwOm0 : w ∈ (TT Lf).Om 0 := by
    simp only [TT, if_true, OmA, Set.mem_setOf_eq]; omega
  have hwB : w ∈ towerBj (TT Lf) 1 := by
    refine ⟨hwOm1, ?_⟩
    simp [TT]
  have hs1 : strat (TT Lf) 1 w = 1 := ((strat_eq_iff h2 (le_refl 1) w).mp hwB).2
  let v : PeriodicLatticeSite Lf := Function.update w 0 ⟨10, by omega⟩
  have hv0 : (v 0).val = 10 := by simp [v]
  have hvB : v ∈ towerBj (TT Lf) 0 := by
    refine ⟨?_, ?_⟩
    · simp only [TT, if_true, OmA, Set.mem_setOf_eq]; omega
    · simp only [TT, if_neg (by decide : (0 + 1 : ℕ) ≠ 0), if_true, OmB, Set.mem_setOf_eq]; omega
  have hs0 : strat (TT Lf) 1 v = 0 := ((strat_eq_iff h2 (Nat.zero_le 1) v).mp hvB).2
  have hpatch : IsPatch 2 2 1 1 (TT Lf) 1 w := by
    refine ⟨le_refl 1, ?_, w, hwOm0, hs1, fun μ => rfl⟩
    intro μ
    show (w μ).val % (1 * bigSide 2 2 1) = 0
    simp only [bigSide]
    fin_cases μ
    · simp [hw0]
    · simp [hw1]
    · simp [hw2]
  refine ⟨w, hpatch, ?_⟩
  have hvp : v ∈ patch 2 2 1 5 1 w := by
    show pdist w v ≤ 5 * gsp 2 2 1 1
    unfold pdist gsp
    simp only [bigSide]
    rw [Fin.sum_univ_three]
    have e1 : pcd (Lf 1 + 1) (w 1).val (v 1).val = 0 := by
      have : v 1 = w 1 := by simp [v]
      rw [this]; unfold pcd; simp
    have e2 : pcd (Lf 2 + 1) (w 2).val (v 2).val = 0 := by
      have : v 2 = w 2 := by simp [v]
      rw [this]; unfold pcd; simp
    have e0 : pcd (Lf 0 + 1) (w 0).val (v 0).val = 14 := by
      rw [hw0, hv0, hN0]; unfold pcd; simp
    rw [e0, e1, e2]; norm_num
  have hv0 : v ∈ (TT Lf).Om 0 := hvB.1
  let p1 : PeriodicLatticeSite Lf := Function.update w 1 ⟨20, by have := hLf 1; omega⟩
  let p2 : PeriodicLatticeSite Lf := Function.update w 1 ⟨100, by have := hLf 1; omega⟩
  have hp1 : p1 ∈ patch 2 2 1 5 1 w := by
    show pdist w p1 ≤ 5 * gsp 2 2 1 1
    rw [pdist_update, hw1, hLf 1]; unfold pcd gsp; simp [bigSide]
  have hp2 : p2 ∈ patch 2 2 1 5 1 w := by
    show pdist w p2 ≤ 5 * gsp 2 2 1 1
    rw [pdist_update, hw1, hLf 1]; unfold pcd gsp; simp [bigSide]
  have h0p : ∀ q : PeriodicLatticeSite Lf, (q 0).val = 24 → q ∈ (TT Lf).Om 0 := fun q hq => by
    simp only [TT, if_true, OmA, Set.mem_setOf_eq]; omega
  have hp10 : p1 ∈ (TT Lf).Om 0 := h0p _ (by simp only [p1, Function.update_of_ne (by decide : (0 : Fin 3) ≠ 1)]; exact hw0)
  have hp20 : p2 ∈ (TT Lf).Om 0 := h0p _ (by simp only [p2, Function.update_of_ne (by decide : (0 : Fin 3) ≠ 1)]; exact hw0)
  exact patch_inter_not_in_class_cube (c := 5) (κ := 1) (f := 12) h2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hpatch hvp hv0 (by rw [hs0]) hp1 hp10 hp2 hp20 1
    (by simp only [p1, p2, Function.update_self]; rw [hLf 1]; unfold pcd bigSide; norm_num)

/-! ## the family, arbitrary `R` -/

def OmAR (R : ℕ) (L : PeriodicLatticeExtent) : Set (PeriodicLatticeSite L) :=
  {x | 2 * R + 8 ≤ (x 0).val ∧ (x 0).val < 6 * R + 88}
def OmBR (R : ℕ) (L : PeriodicLatticeExtent) : Set (PeriodicLatticeSite L) :=
  {x | 4 * R + 8 ≤ (x 0).val ∧ (x 0).val < 4 * R + 88}
def TTR (R : ℕ) (L : PeriodicLatticeExtent) : Tower L :=
  ⟨fun j => if j = 0 then OmAR R L else if j = 1 then OmBR R L else ∅⟩

theorem pcd_far_R (R N a b : ℕ) (hN : N = 8 * R + 120) (ha : a < 2 * R + 8 ∨ 6 * R + 88 ≤ a) (ha2 : a < N)
    (hb : 4 * R + 8 ≤ b ∧ b < 4 * R + 88) : 2 * R < pcd N a b := by
  subst hN; unfold pcd; split_ifs <;> omega

theorem pcd_near_R (R N a b : ℕ) (hN : N = 8 * R + 120) (ha : a < N) (hb : 4 * R + 8 ≤ b ∧ b < 4 * R + 88)
    (h : pcd N a b ≤ 2 * R) : 2 * R + 8 ≤ a ∧ a < 6 * R + 88 := by
  subst hN; unfold pcd at h; split_ifs at h <;> omega

theorem pcd_clamp_R (R N a : ℕ) (hN : N = 8 * R + 120) (ha : 2 * R + 8 ≤ a ∧ a < 6 * R + 88) :
    pcd N a (if a < 4 * R + 8 then 4 * R + 8 else if a < 4 * R + 88 then a else 4 * R + 87) ≤ 2 * R := by
  subst hN; unfold pcd; split_ifs <;> omega

theorem TTR_admissible {L : PeriodicLatticeExtent} (R : ℕ) (hN : ∀ μ, L μ + 1 = 8 * R + 120) :
    Admissible 2 2 R 1 (TTR R L) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j x hx
    by_cases h0 : j = 0
    · subst h0; simp only [TTR, if_true, if_neg (by decide : (0 + 1 : ℕ) ≠ 0), if_true, OmAR, OmBR,
        Set.mem_setOf_eq] at hx ⊢
      omega
    · by_cases h1 : j = 1
      · subst h1; simp [TTR] at hx
      · have : j + 1 ≠ 0 := by omega
        have : j + 1 ≠ 1 := by omega
        simp [TTR, *] at hx
  · intro j hj
    have h0 : j ≠ 0 := by omega
    have h1 : j ≠ 1 := by omega
    simp [TTR, h0, h1]
  · intro j hj μ
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl <;> simp [bigSide, hN μ] <;> omega
  · intro j hj
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · intro x hx y hy
      simp only [TTR, if_true, OmAR, Set.mem_setOf_eq] at hx ⊢
      have := hy 0
      simp [bigSide] at this
      omega
    · intro x hx y hy
      simp only [TTR, if_neg (by decide : (1 : ℕ) ≠ 0), if_true, OmBR, Set.mem_setOf_eq] at hx ⊢
      have := hy 0
      simp [bigSide] at this
      omega
  · intro j hj x hx y hy
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · simp only [TTR, if_true, if_neg (by decide : (0 + 1 : ℕ) ≠ 0), OmAR, OmBR, Set.mem_setOf_eq,
        not_and_or, not_le, not_lt] at hx hy
      have hxl : (x 0).val < 8 * R + 120 := by have := (x 0).isLt; have := hN 0; omega
      have hlt : 2 * R < pcd (L 0 + 1) (x 0).val (y 0).val :=
        pcd_far_R R _ _ _ (hN 0) hx (x 0).isLt hy
      unfold pdist
      show R * bigSide 2 2 0 < _
      simp only [bigSide, pow_zero, mul_one]
      have h2 : R * 2 = 2 * R := by ring
      rw [h2]
      exact lt_of_lt_of_le hlt
        (Finset.single_le_sum (f := fun μ : Fin 3 => pcd (L μ + 1) (x μ).val (y μ).val)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0))
    · simp [TTR] at hy
  · intro x
    simp only [TTR, if_true, if_neg (by decide : (1 : ℕ) ≠ 0), OmAR, OmBR, Set.mem_setOf_eq]
    constructor
    · intro hx
      have hxN : (x 0).val < 8 * R + 120 := by have := (x 0).isLt; have := hN 0; omega
      let v : ℕ := if (x 0).val < 4 * R + 8 then 4 * R + 8 else if (x 0).val < 4 * R + 88 then (x 0).val else 4 * R + 87
      have hv : v < L 0 + 1 := by have := hN 0; simp only [v]; split_ifs <;> omega
      refine ⟨Function.update x 0 ⟨v, hv⟩, ?_, x, fun μ => rfl, ?_⟩
      · simp only [Function.update_self]; simp only [v]; split_ifs <;> omega
      · unfold pdist
        rw [Finset.sum_eq_single (0 : Fin 3)]
        · simp only [Function.update_self]
          have := pcd_clamp_R R (L 0 + 1) (x 0).val (hN 0) hx
          simpa [v, bigSide, mul_comm] using this
        · intro μ _ h
          rw [Function.update_of_ne h]; unfold pcd; simp
        · intro h; exact absurd (Finset.mem_univ _) h
    · rintro ⟨y, hy, z, hz, hd⟩
      have hz0 : (z 0).val / 2 = (x 0).val / 2 := by simpa using hz 0
      have hlt := Finset.single_le_sum (f := fun μ : Fin 3 => pcd (L μ + 1) (z μ).val (y μ).val)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
      have h12 : pcd (L 0 + 1) (z 0).val (y 0).val ≤ 2 * R := by
        have := le_trans hlt hd
        simpa [bigSide, mul_comm] using this
      have hzN : (z 0).val < 8 * R + 120 := by have := (z 0).isLt; have := hN 0; omega
      have hzr := pcd_near_R R _ _ _ (hN 0) (z 0).isLt hy h12
      omega

theorem b0_counterexample_R {L : PeriodicLatticeExtent} (R : ℕ) (hR : 2 ≤ R) (hN : ∀ μ, L μ + 1 = 8 * R + 120) :
    Admissible 2 2 R 1 (TTR R L) ∧ ∃ w : PeriodicLatticeSite L, IsPatch 2 2 1 1 (TTR R L) 1 w ∧
      ¬ ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), IsClassCube 2 2 12 1 (TTR R L) sites i ∧
          {y | y ∈ patch 2 2 1 5 1 w ∧ y ∈ (TTR R L).Om 0} ⊆ sites := by
  have h2 := TTR_admissible R hN
  refine ⟨h2, ?_⟩
  have hN0 := hN 0
  let w : PeriodicLatticeSite L := fun μ => ⟨if μ = 0 then 4 * R + 12 else 0, by have := hN μ; split_ifs <;> omega⟩
  have hw0 : (w 0).val = 4 * R + 12 := by simp [w]
  have hw1 : (w 1).val = 0 := by simp [w]
  have hw2 : (w 2).val = 0 := by simp [w]
  have hwOm1 : w ∈ (TTR R L).Om 1 := by
    simp only [TTR, if_neg (by decide : (1 : ℕ) ≠ 0), if_true, OmBR, Set.mem_setOf_eq]; omega
  have hwOm0 : w ∈ (TTR R L).Om 0 := by
    simp only [TTR, if_true, OmAR, Set.mem_setOf_eq]; omega
  have hwB : w ∈ towerBj (TTR R L) 1 := by
    refine ⟨hwOm1, ?_⟩
    simp [TTR]
  have hs1 : strat (TTR R L) 1 w = 1 := ((strat_eq_iff h2 (le_refl 1) w).mp hwB).2
  let v : PeriodicLatticeSite L := Function.update w 0 ⟨4 * R + 4, by omega⟩
  have hv0 : (v 0).val = 4 * R + 4 := by simp [v]
  have hvB : v ∈ towerBj (TTR R L) 0 := by
    refine ⟨?_, ?_⟩
    · simp only [TTR, if_true, OmAR, Set.mem_setOf_eq]; omega
    · simp only [TTR, if_neg (by decide : (0 + 1 : ℕ) ≠ 0), if_true, OmBR, Set.mem_setOf_eq]; omega
  have hs0 : strat (TTR R L) 1 v = 0 := ((strat_eq_iff h2 (Nat.zero_le 1) v).mp hvB).2
  have hpatch : IsPatch 2 2 1 1 (TTR R L) 1 w := by
    refine ⟨le_refl 1, ?_, w, hwOm0, hs1, fun μ => rfl⟩
    intro μ
    show (w μ).val % (1 * bigSide 2 2 1) = 0
    simp only [bigSide]
    fin_cases μ
    · simp [hw0]
    · simp [hw1]
    · simp [hw2]
  refine ⟨w, hpatch, ?_⟩
  have hvp : v ∈ patch 2 2 1 5 1 w := by
    show pdist w v ≤ 5 * gsp 2 2 1 1
    unfold pdist gsp
    simp only [bigSide]
    rw [Fin.sum_univ_three]
    have e1 : pcd (L 1 + 1) (w 1).val (v 1).val = 0 := by
      have : v 1 = w 1 := by simp [v]
      rw [this]; unfold pcd; simp
    have e2 : pcd (L 2 + 1) (w 2).val (v 2).val = 0 := by
      have : v 2 = w 2 := by simp [v]
      rw [this]; unfold pcd; simp
    have e0 : pcd (L 0 + 1) (w 0).val (v 0).val = 8 := by
      rw [hw0, hv0, hN0]; unfold pcd; split_ifs <;> omega
    rw [e0, e1, e2]; norm_num
  have hv0 : v ∈ (TTR R L).Om 0 := hvB.1
  let p1 : PeriodicLatticeSite L := Function.update w 1 ⟨20, by have := hN 1; omega⟩
  let p2 : PeriodicLatticeSite L := Function.update w 1 ⟨8 * R + 100, by have := hN 1; omega⟩
  have hp1 : p1 ∈ patch 2 2 1 5 1 w := by
    show pdist w p1 ≤ 5 * gsp 2 2 1 1
    rw [pdist_update, hw1, hN 1]; unfold pcd gsp; simp [bigSide]
  have hp2 : p2 ∈ patch 2 2 1 5 1 w := by
    show pdist w p2 ≤ 5 * gsp 2 2 1 1
    rw [pdist_update, hw1, hN 1]; unfold pcd gsp; simp [bigSide]
  have h0p : ∀ q : PeriodicLatticeSite L, (q 0).val = 4 * R + 12 → q ∈ (TTR R L).Om 0 := fun q hq => by
    simp only [TTR, if_true, OmAR, Set.mem_setOf_eq]; omega
  have hp10 : p1 ∈ (TTR R L).Om 0 := h0p _ (by simp only [p1, Function.update_of_ne (by decide : (0 : Fin 3) ≠ 1)]; exact hw0)
  have hp20 : p2 ∈ (TTR R L).Om 0 := h0p _ (by simp only [p2, Function.update_of_ne (by decide : (0 : Fin 3) ≠ 1)]; exact hw0)
  exact patch_inter_not_in_class_cube (c := 5) (κ := 1) (f := 12) h2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hpatch hvp hv0 (by rw [hs0]) hp1 hp10 hp2 hp20 1
    (by simp only [p1, p2, Function.update_self]; rw [hN 1]; unfold pcd bigSide; simp)

end AdalyFormal.M2Bridge

#print axioms AdalyFormal.M2Bridge.b0_counterexample
#print axioms AdalyFormal.M2Bridge.TTR_admissible
#print axioms AdalyFormal.M2Bridge.b0_counterexample_R
