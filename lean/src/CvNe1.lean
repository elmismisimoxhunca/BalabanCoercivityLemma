import CvF2
import NC5

/-!
# CvNe1 -- a NESTED slab tower of height `k = 2` and its `Admissible` proof (lane cover_nested_20261016)

`Ω₀ = [P0,Q0)`, `Ω₁ = [P1,Q1)` (ONE interval), `Ω₂ = [A',B') ∪ [A,B)` (a thin and a fat component, both inside `Ω₁`), intervals in
the coordinate `x₀`; `Ω_j = ∅` for `j ≥ 3`.  `Geo3` collects the arithmetic facts the six clauses of the frozen `Admissible` need;
`tw3_admissible` proves `Admissible ell M R 2 (tw3 ..)` from them.  Modelled on NC2 (`tw2`, height 1); reuses the `pcd`/interval
lemmas of NV1 (lane nonvac_20261015).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000

namespace AdalyFormal.CoverNested

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.NonVac (pcd_gt_left pcd_gt_right pcd_self' pcd_near pcd_clamp iv_iff iv_block)

/-- the nested slab tower. -/
def tw3 (L : PeriodicLatticeExtent) (P0 Q0 P1 Q1 A' B' A B : ℕ) : Tower L :=
  ⟨fun j => if j = 0 then {x | P0 ≤ (x 0).val ∧ (x 0).val < Q0}
    else if j = 1 then {x | P1 ≤ (x 0).val ∧ (x 0).val < Q1}
    else if j = 2 then {x | (A' ≤ (x 0).val ∧ (x 0).val < B') ∨ (A ≤ (x 0).val ∧ (x 0).val < B)} else ∅⟩

section
variable {L : PeriodicLatticeExtent} {P0 Q0 P1 Q1 A' B' A B : ℕ}

theorem tw3_om0 (x : PeriodicLatticeSite L) :
    x ∈ (tw3 L P0 Q0 P1 Q1 A' B' A B).Om 0 ↔ P0 ≤ (x 0).val ∧ (x 0).val < Q0 := by simp [tw3]
theorem tw3_om1 (x : PeriodicLatticeSite L) :
    x ∈ (tw3 L P0 Q0 P1 Q1 A' B' A B).Om 1 ↔ P1 ≤ (x 0).val ∧ (x 0).val < Q1 := by simp [tw3]
theorem tw3_om2 (x : PeriodicLatticeSite L) :
    x ∈ (tw3 L P0 Q0 P1 Q1 A' B' A B).Om 2 ↔
      (A' ≤ (x 0).val ∧ (x 0).val < B') ∨ (A ≤ (x 0).val ∧ (x 0).val < B) := by simp [tw3]
theorem tw3_omHi (j : ℕ) (hj : 3 ≤ j) (x : PeriodicLatticeSite L) :
    x ∉ (tw3 L P0 Q0 P1 Q1 A' B' A B).Om j := by
  have h0 : j ≠ 0 := by omega
  have h1 : j ≠ 1 := by omega
  have h2 : j ≠ 2 := by omega
  simp [tw3, h0, h1, h2]
end

/-- the arithmetic content of `Admissible` for `tw3`. -/
structure Geo3 (M ell R N P0 Q0 P1 Q1 A' B' A B : ℕ) : Prop where
  hM : 0 < M
  hell : 0 < ell
  w2 : A' < B'
  gap : B' ≤ A
  w2' : A < B
  QN : Q0 ≤ N
  d0 : M ∣ N
  d1 : M * ell ∣ N
  d2 : M * ell ^ 2 ∣ N
  b0P : M ∣ P0
  b0Q : M ∣ Q0
  b1P : M * ell ∣ P1
  b1Q : M * ell ∣ Q1
  b2A' : M * ell ^ 2 ∣ A'
  b2B' : M * ell ^ 2 ∣ B'
  b2A : M * ell ^ 2 ∣ A
  b2B : M * ell ^ 2 ∣ B
  cP : P1 = P0 + R * M
  cQ : Q0 = Q1 + R * M
  cP2 : A' = P1 + R * (M * ell)
  cQ2 : Q1 = B + R * (M * ell)

theorem tw3_admissible {M ell R N P0 Q0 P1 Q1 A' B' A B : ℕ} (G : Geo3 M ell R N P0 Q0 P1 Q1 A' B' A B)
    {L : PeriodicLatticeExtent} (hN : ∀ μ, L μ + 1 = N) :
    Admissible ell M R 2 (tw3 L P0 Q0 P1 Q1 A' B' A B) := by
  obtain ⟨hM, hell, w2, gap, w2', QN, d0, d1, d2, b0P, b0Q, b1P, b1Q, b2A', b2B', b2A, b2B, cP, cQ, cP2, cQ2⟩ := G
  have hs1 : 0 < M * ell := Nat.mul_pos hM hell
  have hs2 : 0 < M * ell ^ 2 := Nat.mul_pos hM (pow_pos hell 2)
  have pd : ∀ x y : PeriodicLatticeSite L, ∀ D, D < pcd N (x 0).val (y 0).val → D < pdist x y := by
    intro x y D h
    unfold pdist
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun μ : Fin 3 => pcd (L μ + 1) (x μ).val (y μ).val)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0))
    simpa [hN 0] using h
  have xlt : ∀ x : PeriodicLatticeSite L, (x 0).val < N := fun x => by have := (x 0).isLt; have := hN 0; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j x hx
    by_cases h0 : j = 0
    · subst h0
      rw [tw3_om1] at hx; rw [tw3_om0]; omega
    · by_cases h1 : j = 1
      · subst h1
        rw [tw3_om2] at hx; rw [tw3_om1]; omega
      · exact absurd hx (tw3_omHi (j + 1) (by omega) x)
  · intro j hj
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    exact tw3_omHi j (by omega) x
  · intro j hj μ
    rw [hN μ]
    have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases this with rfl | rfl | rfl
    · simpa [bigSide] using d0
    · simpa [bigSide] using d1
    · simpa [bigSide] using d2
  · intro j hj
    have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases this with rfl | rfl | rfl
    · intro x hx y hy
      rw [tw3_om0] at hx; rw [tw3_om0]
      have h := hy 0
      simp only [bigSide, pow_zero, mul_one] at h
      exact iv_block hM b0P b0Q h hx
    · intro x hx y hy
      rw [tw3_om1] at hx; rw [tw3_om1]
      have h := hy 0
      simp only [bigSide, pow_one] at h
      exact iv_block hs1 b1P b1Q h hx
    · intro x hx y hy
      rw [tw3_om2] at hx; rw [tw3_om2]
      have h := hy 0
      simp only [bigSide] at h
      rcases hx with hx | hx
      · exact Or.inl (iv_block hs2 b2A' b2B' h hx)
      · exact Or.inr (iv_block hs2 b2A b2B h hx)
  · intro j hj x hx y hy
    have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases this with rfl | rfl | rfl
    · rw [tw3_om0] at hx; rw [tw3_om1] at hy
      simp only [bigSide, pow_zero, mul_one]
      apply pd
      have hxl := xlt x
      by_cases hl : (x 0).val < P0
      · exact pcd_gt_left (by omega) (by omega)
      · exact pcd_gt_right hxl (by omega) (by omega)
    · rw [tw3_om1] at hx; rw [tw3_om2] at hy
      simp only [bigSide, pow_one]
      apply pd
      have hxl := xlt x
      have hy' : A' ≤ (y 0).val ∧ (y 0).val < B := by omega
      by_cases hl : (x 0).val < P1
      · exact pcd_gt_left (by omega) (by omega)
      · exact pcd_gt_right hxl (by omega) (by omega)
    · exact absurd hy (tw3_omHi 3 le_rfl y)
  · intro x
    rw [tw3_om0]
    constructor
    · intro hx
      have hxl := xlt x
      let v : ℕ := if (x 0).val < P1 then P1 else if (x 0).val < Q1 then (x 0).val else Q1 - 1
      have hv : v < L 0 + 1 := by rw [hN 0]; simp only [v]; split_ifs <;> omega
      refine ⟨Function.update x 0 ⟨v, hv⟩, ?_, x, fun μ => rfl, ?_⟩
      · rw [tw3_om1]; simp only [Function.update_self]
        simp only [v]; split_ifs <;> omega
      · unfold pdist
        rw [Finset.sum_eq_single (0 : Fin 3)]
        · simp only [Function.update_self]
          have hcl := pcd_clamp (N := N) (a := (x 0).val) (lo := P1) (hi := Q1) (D := R * M) (by omega)
            (by omega) hxl (by omega)
          simpa [hN 0, v] using hcl
        · intro μ _ h
          rw [Function.update_of_ne h, pcd_self']
        · intro h; exact absurd (Finset.mem_univ _) h
    · rintro ⟨y, hy, z, hz, hd⟩
      rw [tw3_om1] at hy
      have hz0 : (z 0).val / M = (x 0).val / M := hz 0
      have hle := Finset.single_le_sum (f := fun μ : Fin 3 => pcd (L μ + 1) (z μ).val (y μ).val)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
      have hw' : pcd N (z 0).val (y 0).val ≤ R * M := by
        have := le_trans hle hd
        simpa [hN 0] using this
      have h3 := pcd_near (N := N) (xlt z) hy (by omega) (by omega) hw'
      exact iv_block hM b0P b0Q hz0.symm (by omega)

#print axioms tw3_admissible

end AdalyFormal.CoverNested
