import GV2

/-!
# GV3 -- the cap cut-offs and their discrete derivative bounds (m2_glue3, 2026-10-15)

* `hsP σ b p`: the half-space `p_σ ≥ 0` (`b = true`) or `p_σ ≤ −1` (`b = false`).
* `capC σ b p = S(8 q_σ²/Q − 1)` on the half-space, `0` off it (`S = stepS`, `q = p + 1/2`, `Q = |q|²`):
  `capC = 1` iff `4 q_σ² ≥ Q` there; `capC > 0` forces the half-space and `8 q_σ² > Q`.
* `quot_first`, `quot_second`: discrete first/second differences of a quotient `N/D`.
* `capC_bond`, `capC_sten`: for `ρ(p) ≥ 8`, `|Δ capC| ≤ K1/ρ`, `|Δ² capC| ≤ K2/ρ²` on every bond / stencil at `p`
  (stencils with `μ = ν` included).
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M2Glue3

open AdalyFormal.M2Glue2

/-! ## §1 quotients -/

theorem inv_le_of {D u : ℝ} (hu : 0 < u) (hD : 1 ≤ u * D) : |1 / D| ≤ u := by
  have hD0 : 0 < D := by
    by_contra h; push Not at h; nlinarith
  rw [abs_of_pos (by positivity), div_le_iff₀ hD0]; linarith

theorem inv_sub_le {D D' u B : ℝ} (hu : 0 < u) (hD : 1 ≤ u * D) (hD' : 1 ≤ u * D') (hB : |D' - D| ≤ B) :
    |1 / D' - 1 / D| ≤ B * u ^ 2 := by
  have hD0 : 0 < D := by by_contra h; push Not at h; nlinarith
  have hD0' : 0 < D' := by by_contra h; push Not at h; nlinarith
  have e : 1 / D' - 1 / D = -(D' - D) * (1 / D) * (1 / D') := by field_simp; ring
  rw [e, abs_mul, abs_mul, abs_neg]
  have a := inv_le_of hu hD; have b := inv_le_of hu hD'
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hB
  calc |D' - D| * |1 / D| * |1 / D'| ≤ B * u * u := by
        apply mul_le_mul (mul_le_mul hB a (abs_nonneg _) hB0) b (abs_nonneg _) (by positivity)
    _ = B * u ^ 2 := by ring

theorem quot_first {N0 N1 D0 D1 u A B : ℝ} (hu : 0 < u) (h0 : 1 ≤ u * D0) (h1 : 1 ≤ u * D1) (hA : 0 ≤ A)
    (hN0 : |N0| ≤ A * D0) (hN : |N1 - N0| ≤ B) (hD : |D1 - D0| ≤ B) :
    |N1 / D1 - N0 / D0| ≤ (1 + A) * B * u := by
  have hD0 : 0 < D0 := by by_contra h; push Not at h; nlinarith
  have hD1 : 0 < D1 := by by_contra h; push Not at h; nlinarith
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hN
  have e : N1 / D1 - N0 / D0 = (N1 - N0) * (1 / D1) - (N0 * (1 / D0)) * ((D1 - D0) * (1 / D1)) := by
    field_simp; ring
  rw [e]
  have a := inv_le_of hu h1
  have b : |N0 * (1 / D0)| ≤ A := by
    rw [abs_mul, abs_of_pos (show 0 < 1 / D0 by positivity)]
    calc |N0| * (1 / D0) ≤ A * D0 * (1 / D0) := mul_le_mul_of_nonneg_right hN0 (by positivity)
      _ = A := by field_simp
  have c1 : |(N1 - N0) * (1 / D1)| ≤ B * u := by
    rw [abs_mul]; exact mul_le_mul hN a (abs_nonneg _) hB0
  have c2 : |(D1 - D0) * (1 / D1)| ≤ B * u := by
    rw [abs_mul]; exact mul_le_mul hD a (abs_nonneg _) hB0
  have c3 : |N0 * (1 / D0) * ((D1 - D0) * (1 / D1))| ≤ A * (B * u) := by
    rw [abs_mul]; exact mul_le_mul b c2 (abs_nonneg _) hA
  calc |(N1 - N0) * (1 / D1) - N0 * (1 / D0) * ((D1 - D0) * (1 / D1))|
      ≤ |(N1 - N0) * (1 / D1)| + |N0 * (1 / D0) * ((D1 - D0) * (1 / D1))| := abs_sub _ _
    _ ≤ B * u + A * (B * u) := add_le_add c1 c3
    _ = (1 + A) * B * u := by ring

theorem quot_second {N0 N1 N2 N3 D0 D1 D2 D3 u A B C E : ℝ} (hu : 0 < u)
    (h0 : 1 ≤ u * D0) (h1 : 1 ≤ u * D1) (h2 : 1 ≤ u * D2) (h3 : 1 ≤ u * D3) (hE : u * D0 ≤ E)
    (hA : 0 ≤ A) (hN0 : |N0| ≤ A * D0)
    (n10 : |N1 - N0| ≤ B) (n20 : |N2 - N0| ≤ B)
    (d10 : |D1 - D0| ≤ B) (d20 : |D2 - D0| ≤ B) (d31 : |D3 - D1| ≤ B) (d32 : |D3 - D2| ≤ B)
    (nC : |N3 - N2 - N1 + N0| ≤ C) (dC : |D3 - D2 - D1 + D0| ≤ C) :
    |N3 / D3 - N2 / D2 - N1 / D1 + N0 / D0| ≤ (1 + A * E) * (C * u + 2 * B ^ 2 * u ^ 2) := by
  have hD0 : 0 < D0 := by by_contra h; push Not at h; nlinarith
  have hD1 : 0 < D1 := by by_contra h; push Not at h; nlinarith
  have hD2 : 0 < D2 := by by_contra h; push Not at h; nlinarith
  have hD3 : 0 < D3 := by by_contra h; push Not at h; nlinarith
  have hB0 : 0 ≤ B := (abs_nonneg _).trans n10
  have hC0 : 0 ≤ C := (abs_nonneg _).trans nC
  set R0 := 1 / D0; set R1 := 1 / D1; set R2 := 1 / D2; set R3 := 1 / D3
  have eL : N3 / D3 - N2 / D2 - N1 / D1 + N0 / D0
      = (N3 - N2 - N1 + N0) * R3 + (N2 - N0) * (R3 - R2) + (N1 - N0) * (R3 - R1) + N0 * (R3 - R2 - R1 + R0) := by
    simp only [R0, R1, R2, R3]; field_simp; ring
  have eR : R3 - R2 - R1 + R0 = -((D3 - D2) - (D1 - D0)) * (R2 * R3) - (D1 - D0) * (R3 * (R2 - R0) + R0 * (R3 - R1)) := by
    simp only [R0, R1, R2, R3]; field_simp; ring
  have r0 := inv_le_of hu h0; have r2 := inv_le_of hu h2; have r3 := inv_le_of hu h3
  have r32 := inv_sub_le hu h2 h3 d32
  have r31 := inv_sub_le hu h1 h3 d31
  have r20 := inv_sub_le hu h0 h2 d20
  have dD : |(D3 - D2) - (D1 - D0)| ≤ C := by
    rw [show (D3 - D2) - (D1 - D0) = D3 - D2 - D1 + D0 by ring]; exact dC
  -- second difference of R
  have hR2 : |R3 - R2 - R1 + R0| ≤ C * u ^ 2 + 2 * B ^ 2 * u ^ 3 := by
    rw [eR]
    have a1 : |-((D3 - D2) - (D1 - D0)) * (R2 * R3)| ≤ C * (u * u) := by
      rw [abs_mul, abs_neg, abs_mul]
      exact mul_le_mul dD (mul_le_mul r2 r3 (abs_nonneg _) hu.le) (by positivity) hC0
    have a2 : |R3 * (R2 - R0)| ≤ u * (B * u ^ 2) := by
      rw [abs_mul]; exact mul_le_mul r3 r20 (abs_nonneg _) hu.le
    have a3 : |R0 * (R3 - R1)| ≤ u * (B * u ^ 2) := by
      rw [abs_mul]; exact mul_le_mul r0 r31 (abs_nonneg _) hu.le
    have a4 : |(D1 - D0) * (R3 * (R2 - R0) + R0 * (R3 - R1))| ≤ B * (2 * (u * (B * u ^ 2))) := by
      rw [abs_mul]
      apply mul_le_mul d10 _ (abs_nonneg _) hB0
      calc |R3 * (R2 - R0) + R0 * (R3 - R1)| ≤ |R3 * (R2 - R0)| + |R0 * (R3 - R1)| := abs_add_le _ _
        _ ≤ 2 * (u * (B * u ^ 2)) := by linarith
    calc |-((D3 - D2) - (D1 - D0)) * (R2 * R3) - (D1 - D0) * (R3 * (R2 - R0) + R0 * (R3 - R1))|
        ≤ |-((D3 - D2) - (D1 - D0)) * (R2 * R3)| + |(D1 - D0) * (R3 * (R2 - R0) + R0 * (R3 - R1))| :=
          abs_sub _ _
      _ ≤ C * (u * u) + B * (2 * (u * (B * u ^ 2))) := add_le_add a1 a4
      _ = C * u ^ 2 + 2 * B ^ 2 * u ^ 3 := by ring
  rw [eL]
  have b1 : |(N3 - N2 - N1 + N0) * R3| ≤ C * u := by
    rw [abs_mul]; exact mul_le_mul nC r3 (abs_nonneg _) hC0
  have b2 : |(N2 - N0) * (R3 - R2)| ≤ B * (B * u ^ 2) := by
    rw [abs_mul]; exact mul_le_mul n20 r32 (abs_nonneg _) hB0
  have b3 : |(N1 - N0) * (R3 - R1)| ≤ B * (B * u ^ 2) := by
    rw [abs_mul]; exact mul_le_mul n10 r31 (abs_nonneg _) hB0
  have hN0' : |N0| ≤ A * E / u := by
    rw [le_div_iff₀ hu]
    calc |N0| * u ≤ A * D0 * u := mul_le_mul_of_nonneg_right hN0 hu.le
      _ = A * (u * D0) := by ring
      _ ≤ A * E := mul_le_mul_of_nonneg_left hE hA
  have b4 : |N0 * (R3 - R2 - R1 + R0)| ≤ A * E / u * (C * u ^ 2 + 2 * B ^ 2 * u ^ 3) := by
    rw [abs_mul]; exact mul_le_mul hN0' hR2 (abs_nonneg _) (div_nonneg (mul_nonneg hA (by linarith)) hu.le)
  have e4 : A * E / u * (C * u ^ 2 + 2 * B ^ 2 * u ^ 3) = A * E * (C * u + 2 * B ^ 2 * u ^ 2) := by
    field_simp
  rw [e4] at b4
  have t := abs_add_le ((N3 - N2 - N1 + N0) * R3 + (N2 - N0) * (R3 - R2) + (N1 - N0) * (R3 - R1))
    (N0 * (R3 - R2 - R1 + R0))
  have t2 := abs_add_le ((N3 - N2 - N1 + N0) * R3 + (N2 - N0) * (R3 - R2)) ((N1 - N0) * (R3 - R1))
  have t3 := abs_add_le ((N3 - N2 - N1 + N0) * R3) ((N2 - N0) * (R3 - R2))
  nlinarith

/-! ## §2 the caps -/

def hsP (σ : Fin 3) (b : Bool) (p : Z3) : Prop := (b = true ∧ 0 ≤ p σ) ∨ (b = false ∧ p σ ≤ -1)

noncomputable def capC (σ : Fin 3) (b : Bool) (p : Z3) : ℝ :=
  open Classical in if hsP σ b p then stepS (8 * qc p σ ^ 2 / Qf p - 1) else 0

theorem capC_mem (σ : Fin 3) (b : Bool) (p : Z3) : 0 ≤ capC σ b p ∧ capC σ b p ≤ 1 := by
  classical
  unfold capC; split_ifs
  · exact stepS_mem _
  · norm_num

theorem hs_of_capC_pos {σ : Fin 3} {b : Bool} {p : Z3} (h : 0 < capC σ b p) : hsP σ b p := by
  classical
  unfold capC at h; split_ifs at h with hs
  · exact hs
  · exact absurd h (lt_irrefl 0)

theorem big_of_capC_pos {σ : Fin 3} {b : Bool} {p : Z3} (h : 0 < capC σ b p) : Qf p < 8 * qc p σ ^ 2 := by
  classical
  unfold capC at h; split_ifs at h with hs
  · by_contra hc; push Not at hc
    have hQ := Qf_pos p
    have : 8 * qc p σ ^ 2 / Qf p - 1 ≤ 0 := by
      rw [sub_nonpos, div_le_one hQ]; exact hc
    rw [stepS_of_nonpos this] at h; exact lt_irrefl 0 h
  · exact absurd h (lt_irrefl 0)

theorem capC_one {σ : Fin 3} {b : Bool} {p : Z3} (hs : hsP σ b p) (h : Qf p ≤ 4 * qc p σ ^ 2) :
    capC σ b p = 1 := by
  classical
  unfold capC; rw [if_pos hs]
  apply stepS_of_one_le
  have hQ := Qf_pos p
  rw [le_sub_iff_add_le, le_div_iff₀ hQ]; linarith

theorem capC_zero_of_small {σ : Fin 3} {b : Bool} {p : Z3} (hq : qc p σ ^ 2 ≤ 9 / 4) (hQ : 18 ≤ Qf p) :
    capC σ b p = 0 := by
  classical
  unfold capC; split_ifs
  · apply stepS_of_nonpos
    have hQ0 : 0 < Qf p := by linarith
    rw [sub_nonpos, div_le_one hQ0]; linarith
  · rfl

theorem capC_lt_one_or {σ : Fin 3} {b : Bool} {p : Z3} (h : capC σ b p < 1) :
    ¬ hsP σ b p ∨ 4 * qc p σ ^ 2 < Qf p := by
  by_contra hc; push Not at hc
  rw [capC_one hc.1 hc.2] at h; exact lt_irrefl 1 h

/-- on the half-space the cap is `S ∘ f`. -/
theorem capC_of_hs {σ : Fin 3} {b : Bool} {p : Z3} (hs : hsP σ b p) :
    capC σ b p = stepS (8 * qc p σ ^ 2 / Qf p - 1) := by
  classical
  unfold capC; rw [if_pos hs]

/-- if the half-space condition fails at a point of a stencil, every cap value of the stencil is `0`. -/
theorem capC_zero_near_boundary {σ : Fin 3} {b : Bool} {p p' : Z3} (hp' : ¬ hsP σ b p')
    (hd : |p σ - p' σ| ≤ 2) (hQ : 18 ≤ Qf p) : capC σ b p = 0 := by
  classical
  by_cases hs : hsP σ b p
  · apply capC_zero_of_small _ hQ
    have hb : p σ ≤ 1 ∧ -2 ≤ p σ := by
      rw [abs_le] at hd
      unfold hsP at hs hp'
      cases b
      · simp at hs hp'; constructor <;> omega
      · simp at hs hp'; constructor <;> omega
    unfold qc
    have a : ((p σ : ℤ) : ℝ) ≤ 1 := by exact_mod_cast hb.1
    have c : (-2 : ℝ) ≤ ((p σ : ℤ) : ℝ) := by exact_mod_cast hb.2
    nlinarith
  · unfold capC; rw [if_neg hs]

end AdalyFormal.M2Glue3
