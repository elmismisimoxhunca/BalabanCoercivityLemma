import ZStatementP428
import ZR2B5

/-!
# NV1 -- a three-level slab tower (k = 2) with symbolic ell, M, R and its `Admissible` proof (lane nonvac_20261015)

`Ω_j = {P_j ≤ x₀ < Q_j}` for `j = 0,1,2` (`Ω_j = ∅` for `j ≥ 3`).  `SlabGeo` collects exactly the arithmetic facts that the six
clauses of the frozen `Admissible` need; `slab3_admissible` proves `Admissible ell M R 2 (slab3 ..)` from them.
Generalises `M1W4Num.slab_admissible` (k = 1, ell = 2) to k = 2 and symbolic ell.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000

namespace AdalyFormal.NonVac

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane

def slab3 (L : PeriodicLatticeExtent) (P0 Q0 P1 Q1 P2 Q2 : ℕ) : Tower L :=
  ⟨fun j => if j = 0 then {x | P0 ≤ (x 0).val ∧ (x 0).val < Q0}
    else if j = 1 then {x | P1 ≤ (x 0).val ∧ (x 0).val < Q1}
    else if j = 2 then {x | P2 ≤ (x 0).val ∧ (x 0).val < Q2} else ∅⟩

section
variable {L : PeriodicLatticeExtent} {P0 Q0 P1 Q1 P2 Q2 : ℕ}

theorem om0_mem (x : PeriodicLatticeSite L) :
    x ∈ (slab3 L P0 Q0 P1 Q1 P2 Q2).Om 0 ↔ P0 ≤ (x 0).val ∧ (x 0).val < Q0 := by simp [slab3]
theorem om1_mem (x : PeriodicLatticeSite L) :
    x ∈ (slab3 L P0 Q0 P1 Q1 P2 Q2).Om 1 ↔ P1 ≤ (x 0).val ∧ (x 0).val < Q1 := by simp [slab3]
theorem om2_mem (x : PeriodicLatticeSite L) :
    x ∈ (slab3 L P0 Q0 P1 Q1 P2 Q2).Om 2 ↔ P2 ≤ (x 0).val ∧ (x 0).val < Q2 := by simp [slab3]
theorem om3_mem (j : ℕ) (hj : 3 ≤ j) (x : PeriodicLatticeSite L) :
    x ∉ (slab3 L P0 Q0 P1 Q1 P2 Q2).Om j := by
  have h0 : j ≠ 0 := by omega
  have h1 : j ≠ 1 := by omega
  have h2 : j ≠ 2 := by omega
  simp [slab3, h0, h1, h2]
end

/-- the arithmetic content of `Admissible` for the slab tower. -/
structure SlabGeo (M ell R N P0 Q0 P1 Q1 P2 Q2 : ℕ) : Prop where
  hM : 0 < M
  hell : 0 < ell
  nest01 : P0 ≤ P1
  nest12 : P1 ≤ P2
  nestw : P2 < Q2
  nest21 : Q2 ≤ Q1
  nest10 : Q1 ≤ Q0
  QN : Q0 ≤ N
  d0 : M ∣ N
  d1 : M * ell ∣ N
  d2 : M * ell ^ 2 ∣ N
  b0P : M ∣ P0
  b0Q : M ∣ Q0
  b1P : M * ell ∣ P1
  b1Q : M * ell ∣ Q1
  b2P : M * ell ^ 2 ∣ P2
  b2Q : M * ell ^ 2 ∣ Q2
  c0P : P1 = P0 + R * M
  c0Q : Q0 = Q1 + R * M
  c0D : R * M ≤ P1
  c1P : P1 + R * (M * ell) ≤ P2
  c1Q : Q2 + R * (M * ell) ≤ Q1
  c1D : R * (M * ell) ≤ P2

theorem pcd_gt_left {N a b D : ℕ} (hab : a + D < b) (hb : b + D < N) : D < pcd N a b := by
  unfold pcd; split_ifs <;> omega

theorem pcd_gt_right {N a b D : ℕ} (ha : a < N) (hba : b + D < a) (hD : D ≤ b) : D < pcd N a b := by
  unfold pcd; split_ifs <;> omega

theorem pcd_self' (N a : ℕ) : pcd N a a = 0 := by unfold pcd; simp

theorem pcd_near {N a b D lo hi : ℕ} (ha : a < N) (hb : lo ≤ b ∧ b < hi) (hD : D ≤ lo) (hN : hi + D ≤ N)
    (h : pcd N a b ≤ D) : lo - D ≤ a ∧ a < hi + D := by
  unfold pcd at h; split_ifs at h <;> omega

theorem pcd_clamp {N a lo hi D : ℕ} (hlh : lo < hi) (ha : lo - D ≤ a ∧ a < hi + D) (_haN : a < N) (_hhiN : hi + D ≤ N) :
    pcd N a (if a < lo then lo else if a < hi then a else hi - 1) ≤ D := by
  unfold pcd; split_ifs <;> omega

/-- membership of a half-open interval with endpoints multiples of `s` is a block property. -/
theorem iv_iff {s t u x : ℕ} (hs : 0 < s) : (s * t ≤ x ∧ x < s * u) ↔ (t ≤ x / s ∧ x / s < u) := by
  rw [Nat.le_div_iff_mul_le hs, Nat.div_lt_iff_lt_mul hs, mul_comm t s, mul_comm u s]

theorem iv_block {s a b x y : ℕ} (hs : 0 < s) (ha : s ∣ a) (hb : s ∣ b) (hxy : y / s = x / s)
    (hx : a ≤ x ∧ x < b) : a ≤ y ∧ y < b := by
  obtain ⟨t, rfl⟩ := ha
  obtain ⟨u, rfl⟩ := hb
  rw [iv_iff hs] at hx ⊢
  rw [hxy]; exact hx

theorem slab3_admissible {M ell R N P0 Q0 P1 Q1 P2 Q2 : ℕ} (G : SlabGeo M ell R N P0 Q0 P1 Q1 P2 Q2)
    {L : PeriodicLatticeExtent} (hN : ∀ μ, L μ + 1 = N) :
    Admissible ell M R 2 (slab3 L P0 Q0 P1 Q1 P2 Q2) := by
  obtain ⟨hM, hell, n01, n12, nw, n21, n10, QN, d0, d1, d2, b0P, b0Q, b1P, b1Q, b2P, b2Q, c0P, c0Q, c0D, c1P, c1Q, c1D⟩ := G
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
  · -- nesting
    intro j x hx
    by_cases h0 : j = 0
    · subst h0
      rw [om1_mem] at hx; rw [om0_mem]; omega
    · by_cases h1 : j = 1
      · subst h1
        rw [om2_mem] at hx; rw [om1_mem]; omega
      · by_cases h2 : j = 2
        · subst h2; exact absurd hx (om3_mem 3 le_rfl x)
        · exact absurd hx (om3_mem (j + 1) (by omega) x)
  · intro j hj
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    exact om3_mem j (by omega) x
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
      rw [om0_mem] at hx; rw [om0_mem]
      have h := hy 0
      simp only [bigSide, pow_zero, mul_one] at h
      exact iv_block hM b0P b0Q h hx
    · intro x hx y hy
      rw [om1_mem] at hx; rw [om1_mem]
      have h := hy 0
      simp only [bigSide, pow_one] at h
      exact iv_block hs1 b1P b1Q h hx
    · intro x hx y hy
      rw [om2_mem] at hx; rw [om2_mem]
      have h := hy 0
      simp only [bigSide] at h
      exact iv_block hs2 b2P b2Q h hx
  · intro j hj x hx y hy
    have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases this with rfl | rfl | rfl
    · rw [om0_mem] at hx; rw [om1_mem] at hy
      simp only [bigSide, pow_zero, mul_one]
      apply pd
      have hxl := xlt x
      by_cases hl : (x 0).val < P0
      · exact pcd_gt_left (by omega) (by omega)
      · exact pcd_gt_right hxl (by omega) (by omega)
    · rw [om1_mem] at hx; rw [om2_mem] at hy
      simp only [bigSide, pow_one]
      apply pd
      have hxl := xlt x
      by_cases hl : (x 0).val < P1
      · exact pcd_gt_left (by omega) (by omega)
      · exact pcd_gt_right hxl (by omega) (by omega)
    · exact absurd hy (om3_mem 3 le_rfl y)
  · intro x
    rw [om0_mem]
    constructor
    · intro hx
      let v : ℕ := if (x 0).val < P1 then P1 else if (x 0).val < Q1 then (x 0).val else Q1 - 1
      have hv : v < L 0 + 1 := by rw [hN 0]; simp only [v]; split_ifs <;> omega
      refine ⟨Function.update x 0 ⟨v, hv⟩, ?_, x, fun μ => rfl, ?_⟩
      · rw [om1_mem]; simp only [Function.update_self]; simp only [v]; split_ifs <;> omega
      · unfold pdist
        rw [Finset.sum_eq_single (0 : Fin 3)]
        · simp only [Function.update_self]
          have hcl := pcd_clamp (N := N) (a := (x 0).val) (lo := P1) (hi := Q1) (D := R * M) (by omega)
            (by omega) (xlt x) (by omega)
          simpa [hN 0, v] using hcl
        · intro μ _ h
          rw [Function.update_of_ne h, pcd_self']
        · intro h; exact absurd (Finset.mem_univ _) h
    · rintro ⟨y, hy, z, hz, hd⟩
      rw [om1_mem] at hy
      have hz0 : (z 0).val / M = (x 0).val / M := hz 0
      have hle := Finset.single_le_sum (f := fun μ : Fin 3 => pcd (L μ + 1) (z μ).val (y μ).val)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
      have hw' : pcd N (z 0).val (y 0).val ≤ R * M := by
        have := le_trans hle hd
        simpa [hN 0] using this
      have h3 := pcd_near (N := N) (xlt z) hy c0D (by omega) hw'
      exact iv_block hM b0P b0Q hz0.symm (by omega)

end AdalyFormal.NonVac
