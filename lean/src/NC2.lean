import NV1

/-!
# NC2 -- a two-component slab tower of height `k = 1` (a thick component and a thin one) and its `Admissible` proof
(lane nocover_20261015)

`Ω₀ = [P0,Q0) ∪ [P0',Q0')`, `Ω₁ = [P1,Q1) ∪ [P1',Q1')` (intervals in the coordinate `x₀`), `Ω_j = ∅` for `j ≥ 2`.
`Geo2` collects the arithmetic facts the six clauses of the frozen `Admissible` need; `tw2_admissible` proves
`Admissible ell M R 1 (tw2 ..)` from them.  Reuses the `pcd`/interval lemmas of `NV1` (lane nonvac_20261015).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000

namespace AdalyFormal.NoCover

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.NonVac (pcd_gt_left pcd_gt_right pcd_self' pcd_near pcd_clamp iv_iff iv_block)

/-- the two-component slab tower. -/
def tw2 (L : PeriodicLatticeExtent) (P0 Q0 P1 Q1 P0' Q0' P1' Q1' : ℕ) : Tower L :=
  ⟨fun j => if j = 0 then {x | (P0 ≤ (x 0).val ∧ (x 0).val < Q0) ∨ (P0' ≤ (x 0).val ∧ (x 0).val < Q0')}
    else if j = 1 then {x | (P1 ≤ (x 0).val ∧ (x 0).val < Q1) ∨ (P1' ≤ (x 0).val ∧ (x 0).val < Q1')} else ∅⟩

section
variable {L : PeriodicLatticeExtent} {P0 Q0 P1 Q1 P0' Q0' P1' Q1' : ℕ}

theorem tw2_om0 (x : PeriodicLatticeSite L) :
    x ∈ (tw2 L P0 Q0 P1 Q1 P0' Q0' P1' Q1').Om 0 ↔
      (P0 ≤ (x 0).val ∧ (x 0).val < Q0) ∨ (P0' ≤ (x 0).val ∧ (x 0).val < Q0') := by simp [tw2]
theorem tw2_om1 (x : PeriodicLatticeSite L) :
    x ∈ (tw2 L P0 Q0 P1 Q1 P0' Q0' P1' Q1').Om 1 ↔
      (P1 ≤ (x 0).val ∧ (x 0).val < Q1) ∨ (P1' ≤ (x 0).val ∧ (x 0).val < Q1') := by simp [tw2]
theorem tw2_omHi (j : ℕ) (hj : 2 ≤ j) (x : PeriodicLatticeSite L) :
    x ∉ (tw2 L P0 Q0 P1 Q1 P0' Q0' P1' Q1').Om j := by
  have h0 : j ≠ 0 := by omega
  have h1 : j ≠ 1 := by omega
  simp [tw2, h0, h1]
end

/-- the arithmetic content of `Admissible` for `tw2`. -/
structure Geo2 (M ell R N P0 Q0 P1 Q1 P0' Q0' P1' Q1' : ℕ) : Prop where
  hM : 0 < M
  hell : 0 < ell
  w1 : P1 < Q1
  w1' : P1' < Q1'
  gap : Q0 ≤ P0'
  QN : Q0' ≤ N
  d0 : M ∣ N
  d1 : M * ell ∣ N
  b0P : M ∣ P0
  b0Q : M ∣ Q0
  b0P' : M ∣ P0'
  b0Q' : M ∣ Q0'
  b1P : M * ell ∣ P1
  b1Q : M * ell ∣ Q1
  b1P' : M * ell ∣ P1'
  b1Q' : M * ell ∣ Q1'
  cP : P1 = P0 + R * M
  cQ : Q0 = Q1 + R * M
  cP' : P1' = P0' + R * M
  cQ' : Q0' = Q1' + R * M

theorem tw2_admissible {M ell R N P0 Q0 P1 Q1 P0' Q0' P1' Q1' : ℕ} (G : Geo2 M ell R N P0 Q0 P1 Q1 P0' Q0' P1' Q1')
    {L : PeriodicLatticeExtent} (hN : ∀ μ, L μ + 1 = N) :
    Admissible ell M R 1 (tw2 L P0 Q0 P1 Q1 P0' Q0' P1' Q1') := by
  obtain ⟨hM, hell, w1, w1', gap, QN, d0, d1, b0P, b0Q, b0P', b0Q', b1P, b1Q, b1P', b1Q', cP, cQ, cP', cQ'⟩ := G
  have hs1 : 0 < M * ell := Nat.mul_pos hM hell
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
      rw [tw2_om1] at hx; rw [tw2_om0]; omega
    · exact absurd hx (tw2_omHi (j + 1) (by omega) x)
  · intro j hj
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    exact tw2_omHi j (by omega) x
  · intro j hj μ
    rw [hN μ]
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · simpa [bigSide] using d0
    · simpa [bigSide] using d1
  · intro j hj
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · intro x hx y hy
      rw [tw2_om0] at hx; rw [tw2_om0]
      have h := hy 0
      simp only [bigSide, pow_zero, mul_one] at h
      rcases hx with hx | hx
      · exact Or.inl (iv_block hM b0P b0Q h hx)
      · exact Or.inr (iv_block hM b0P' b0Q' h hx)
    · intro x hx y hy
      rw [tw2_om1] at hx; rw [tw2_om1]
      have h := hy 0
      simp only [bigSide, pow_one] at h
      rcases hx with hx | hx
      · exact Or.inl (iv_block hs1 b1P b1Q h hx)
      · exact Or.inr (iv_block hs1 b1P' b1Q' h hx)
  · intro j hj x hx y hy
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · rw [tw2_om0] at hx; rw [tw2_om1] at hy
      simp only [bigSide, pow_zero, mul_one]
      apply pd
      have hxl := xlt x
      rcases hy with hy | hy
      · by_cases hl : (x 0).val < P0
        · exact pcd_gt_left (by omega) (by omega)
        · exact pcd_gt_right hxl (by omega) (by omega)
      · by_cases hl : (x 0).val < P0'
        · exact pcd_gt_left (by omega) (by omega)
        · exact pcd_gt_right hxl (by omega) (by omega)
    · exact absurd hy (tw2_omHi 2 le_rfl y)
  · intro x
    rw [tw2_om0]
    constructor
    · intro hx
      have hxl := xlt x
      -- clamp into the matching level-1 interval
      have mk : ∀ lo hi : ℕ, lo < hi → hi + R * M ≤ N → R * M ≤ lo →
          (lo - R * M ≤ (x 0).val ∧ (x 0).val < hi + R * M) →
          ((lo = P1 ∧ hi = Q1) ∨ (lo = P1' ∧ hi = Q1')) →
          ∃ y ∈ (tw2 L P0 Q0 P1 Q1 P0' Q0' P1' Q1').Om 1, ∃ z : PeriodicLatticeSite L,
            (∀ μ : Fin 3, (z μ).val / M = (x μ).val / M) ∧ pdist z y ≤ R * M := by
        intro lo hi hlh hhiN hlo hx' hsel
        let v : ℕ := if (x 0).val < lo then lo else if (x 0).val < hi then (x 0).val else hi - 1
        have hv : v < L 0 + 1 := by rw [hN 0]; simp only [v]; split_ifs <;> omega
        refine ⟨Function.update x 0 ⟨v, hv⟩, ?_, x, fun μ => rfl, ?_⟩
        · rw [tw2_om1]; simp only [Function.update_self]
          rcases hsel with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · left; simp only [v]; split_ifs <;> omega
          · right; simp only [v]; split_ifs <;> omega
        · unfold pdist
          rw [Finset.sum_eq_single (0 : Fin 3)]
          · simp only [Function.update_self]
            have hcl := pcd_clamp (N := N) (a := (x 0).val) (lo := lo) (hi := hi) (D := R * M) hlh hx' hxl hhiN
            simpa [hN 0, v] using hcl
          · intro μ _ h
            rw [Function.update_of_ne h, pcd_self']
          · intro h; exact absurd (Finset.mem_univ _) h
      rcases hx with hx | hx
      · exact mk P1 Q1 w1 (by omega) (by omega) (by omega) (Or.inl ⟨rfl, rfl⟩)
      · exact mk P1' Q1' w1' (by omega) (by omega) (by omega) (Or.inr ⟨rfl, rfl⟩)
    · rintro ⟨y, hy, z, hz, hd⟩
      rw [tw2_om1] at hy
      have hz0 : (z 0).val / M = (x 0).val / M := hz 0
      have hle := Finset.single_le_sum (f := fun μ : Fin 3 => pcd (L μ + 1) (z μ).val (y μ).val)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
      have hw' : pcd N (z 0).val (y 0).val ≤ R * M := by
        have := le_trans hle hd
        simpa [hN 0] using this
      rcases hy with hy | hy
      · have h3 := pcd_near (N := N) (xlt z) hy (by omega) (by omega) hw'
        exact Or.inl (iv_block hM b0P b0Q hz0.symm (by omega))
      · have h3 := pcd_near (N := N) (xlt z) hy (by omega) (by omega) hw'
        exact Or.inr (iv_block hM b0P' b0Q' hz0.symm (by omega))

#print axioms tw2_admissible

end AdalyFormal.NoCover
