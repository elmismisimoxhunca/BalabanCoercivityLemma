import P4L4

/-!
# SH1 -- one-dimensional "corner" lemmas and the site-level pairing lemma.

For two cubes `cubeR c r1`, `cubeR c r2` (same centre `c`, on the level-`g` grid) and block sizes `h1 | r1`, `h2 | r2` dividing the torus sides and `c`:
every pair of sites `y in cubeR c r1`, `x in cubeR c r2` has blocks (`h1`-block of `y`, `h2`-block of `x`) containing points `y'`, `x'` with
`pdist y' x' <= 3 * ((r1 - h1) + (r2 - h2) + 1)`.  (Take in every coordinate the corner of the block nearest to the centre.)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.P409S

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.P409
open AdalyFormal.P409W
open AdalyFormal.P409C5

/-- translation invariance of the circular distance. -/
theorem pcd_translate (N a b c : ℕ) (ha : a < N) (hb : b < N) (hc : c < N) :
    pcd N ((a + c) % N) ((b + c) % N) = pcd N a b := by
  rcases mod_add_cases a c N ha hc.le with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  rcases mod_add_cases b c N hb hc.le with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
  rw [h2, h4] <;> unfold pcd <;> split_ifs <;> omega

/-- offsets and back. -/
theorem off_back (N a c : ℕ) (ha : a < N) (hc : c < N) : (((a + N - c) % N) + c) % N = a := by
  rw [off_eq N a c ha hc]
  split_ifs with h
  · have : a - c + c = a := by omega
    rw [this, Nat.mod_eq_of_lt ha]
  · have : a + N - c + c = a + N := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt ha]

/-- the corner of the `h`-block of `v` nearest to the origin of the window `[0, r) u [N - r, N)` (offset coordinates). -/
theorem corner_off (N h r A v : ℕ) (hh : 0 < h) (hhN : h ∣ N) (hhr : h ∣ r) (hA : A + h = r) (hv : v < N)
    (hw : v < r ∨ N ≤ v + r) :
    ∃ v' : ℕ, v' < N ∧ v' / h = v / h ∧ (v' ≤ A ∨ N ≤ v' + A + 1) := by
  obtain ⟨a, ha⟩ := hhN
  obtain ⟨b, hb⟩ := hhr
  have hq := Nat.div_add_mod v h
  have hml := Nat.mod_lt v hh
  set q := v / h with hqd
  set s := v % h with hsd
  by_cases hlt : v < r
  · refine ⟨h * q, ?_, ?_, Or.inl ?_⟩
    · have : h * q ≤ v := by omega
      omega
    · exact Nat.mul_div_cancel_left q hh
    · -- h*q + h <= r
      have hqb : q < b := by
        by_contra hc
        push Not at hc
        have : h * b ≤ h * q := Nat.mul_le_mul_left h hc
        omega
      have : h * (q + 1) ≤ h * b := Nat.mul_le_mul_left h hqb
      have e : h * (q + 1) = h * q + h := by ring
      omega
  · have hNr : N ≤ v + r := by
      rcases hw with h1 | h1
      · exact absurd h1 hlt
      · exact h1
    have hrv : r ≤ v := by omega
    have hqa : q < a := by
      by_contra hc
      push Not at hc
      have : h * a ≤ h * q := Nat.mul_le_mul_left h hc
      omega
    refine ⟨h * q + (h - 1), ?_, ?_, Or.inr ?_⟩
    · have : h * (q + 1) ≤ h * a := Nat.mul_le_mul_left h hqa
      have e : h * (q + 1) = h * q + h := by ring
      omega
    · rw [Nat.mul_add_div hh]
      have : (h - 1) / h = 0 := Nat.div_eq_of_lt (by omega)
      omega
    · -- N <= h q + (h-1) + A + 1 = h q + r
      have hbq : a - b ≤ q := by
        by_contra hc
        push Not at hc
        have h1 : h * q + h ≤ h * (a - b) := by
          have : h * (q + 1) ≤ h * (a - b) := Nat.mul_le_mul_left h (by omega)
          have e : h * (q + 1) = h * q + h := by ring
          omega
        have h2 : h * (a - b) = h * a - h * b := Nat.mul_sub h a b
        have h3 : h * b ≤ h * a := Nat.mul_le_mul_left h (by
          by_contra hc2; push Not at hc2
          have : h * a < h * b := Nat.mul_lt_mul_of_pos_left hc2 hh
          omega)
        omega
      have h4 : h * (a - b) ≤ h * q := Nat.mul_le_mul_left h hbq
      have h2 : h * (a - b) = h * a - h * b := Nat.mul_sub h a b
      have h3 : h * b ≤ h * a := by omega
      omega

/-- circular distance between two points near the origin of their windows. -/
theorem pcd_near (N u w A B : ℕ) (hu : u < N) (hw : w < N)
    (h1 : u ≤ A ∨ N ≤ u + A + 1) (h2 : w ≤ B ∨ N ≤ w + B + 1) : pcd N u w ≤ A + B + 1 := by
  unfold pcd
  split_ifs <;> omega

/-- membership in `cubeR c r` in offset coordinates. -/
theorem cube_off (N c r y : ℕ) (hy : y < N) (hc : c < N) (t : ℤ) (ht1 : -(r : ℤ) ≤ t) (ht2 : t < (r : ℤ))
    (h : (y : ℤ) ≡ (c : ℤ) + t [ZMOD (N : ℤ)]) :
    (y + N - c) % N < r ∨ N ≤ (y + N - c) % N + r := by
  have hN : 0 < N := by omega
  by_cases hrN : N ≤ r
  · left
    have := Nat.mod_lt (y + N - c) hN
    omega
  · push Not at hrN
    have hv : ((y + N - c) % N : ℕ) < N := Nat.mod_lt _ hN
    have hm : (((y + N - c) % N : ℕ) : ℤ) ≡ (y : ℤ) + (N : ℤ) - (c : ℤ) [ZMOD (N : ℤ)] := by
      have := Int.natCast_modEq_iff.2 (Nat.mod_modEq (y + N - c) N)
      rw [Nat.cast_sub (by omega)] at this
      push_cast at this
      exact this
    have h2 : (y : ℤ) + (N : ℤ) - (c : ℤ) ≡ t [ZMOD (N : ℤ)] := by
      have h3 : (y : ℤ) + (N : ℤ) - (c : ℤ) ≡ ((c : ℤ) + t) + (N : ℤ) - (c : ℤ) [ZMOD (N : ℤ)] :=
        (h.add_right (N : ℤ)).sub_right (c : ℤ)
      refine h3.trans ?_
      have e : ((c : ℤ) + t) + (N : ℤ) - (c : ℤ) = t + (N : ℤ) * 1 := by ring
      rw [e]
      exact Int.modEq_iff_dvd.2 ⟨-1, by ring⟩
    have h4 := hm.trans h2
    obtain ⟨q, hq⟩ := Int.modEq_iff_dvd.1 h4.symm
    -- hq : (v : ℤ) - t = N * q
    have hq1 : q < 2 := by
      by_contra hc
      push Not at hc
      have : (N : ℤ) * 2 ≤ (N : ℤ) * q := by nlinarith
      omega
    have hq2 : -1 < q := by
      by_contra hc
      push Not at hc
      have : (N : ℤ) * q ≤ (N : ℤ) * (-1) := by nlinarith
      omega
    interval_cases q
    · left; omega
    · right; omega

theorem pcd_le_natAbs_aux (N a b : ℕ) : pcd N a b ≤ (if a ≤ b then b - a else a - b) := by
  unfold pcd; exact Nat.min_le_left _ _

/-- the coordinate lemma. -/
theorem coord_pair (N c h1 r1 A1 h2 r2 A2 a b : ℕ) (hc : c < N)
    (hh1 : 0 < h1) (hh1N : h1 ∣ N) (hh1c : h1 ∣ c) (hh1r : h1 ∣ r1) (hA1 : A1 + h1 = r1)
    (hh2 : 0 < h2) (hh2N : h2 ∣ N) (hh2c : h2 ∣ c) (hh2r : h2 ∣ r2) (hA2 : A2 + h2 = r2)
    (ha : a < N) (hb : b < N)
    (hra : (a + N - c) % N < r1 ∨ N ≤ (a + N - c) % N + r1)
    (hrb : (b + N - c) % N < r2 ∨ N ≤ (b + N - c) % N + r2) :
    ∃ a' b' : ℕ, a' < N ∧ b' < N ∧ a' / h1 = a / h1 ∧ b' / h2 = b / h2 ∧ pcd N a' b' ≤ A1 + A2 + 1 := by
  have hN : 0 < N := by omega
  have hva : (a + N - c) % N < N := Nat.mod_lt _ hN
  have hvb : (b + N - c) % N < N := Nat.mod_lt _ hN
  obtain ⟨v', hv'1, hv'2, hv'3⟩ := corner_off N h1 r1 A1 ((a + N - c) % N) hh1 hh1N hh1r hA1 hva hra
  obtain ⟨w', hw'1, hw'2, hw'3⟩ := corner_off N h2 r2 A2 ((b + N - c) % N) hh2 hh2N hh2r hA2 hvb hrb
  refine ⟨(v' + c) % N, (w' + c) % N, Nat.mod_lt _ hN, Nat.mod_lt _ hN, ?_, ?_, ?_⟩
  · have key := div_shift h1 N v' ((a + N - c) % N) c hh1 hh1N hh1c hv'2
    rw [key, off_back N a c ha hc]
  · have key := div_shift h2 N w' ((b + N - c) % N) c hh2 hh2N hh2c hw'2
    rw [key, off_back N b c hb hc]
  · rw [pcd_translate N v' w' c hv'1 hw'1 hc]
    exact pcd_near N v' w' A1 A2 hv'1 hw'1 hv'3 hw'3

variable {L : PeriodicLatticeExtent}

/-- the site-level pairing lemma. -/
theorem site_pair (c y x : PeriodicLatticeSite L) (h1 r1 A1 h2 r2 A2 : ℕ)
    (hh1 : 0 < h1) (hh1N : ∀ μ : Fin 3, h1 ∣ L μ + 1) (hh1c : ∀ μ : Fin 3, h1 ∣ (c μ).val) (hh1r : h1 ∣ r1) (hA1 : A1 + h1 = r1)
    (hh2 : 0 < h2) (hh2N : ∀ μ : Fin 3, h2 ∣ L μ + 1) (hh2c : ∀ μ : Fin 3, h2 ∣ (c μ).val) (hh2r : h2 ∣ r2) (hA2 : A2 + h2 = r2)
    (hy : y ∈ cubeR c r1) (hx : x ∈ cubeR c r2) :
    ∃ y' x' : PeriodicLatticeSite L, (∀ μ : Fin 3, (y' μ).val / h1 = (y μ).val / h1) ∧
      (∀ μ : Fin 3, (x' μ).val / h2 = (x μ).val / h2) ∧ pdist y' x' ≤ 3 * (A1 + A2 + 1) := by
  have h : ∀ μ : Fin 3, ∃ a' b' : ℕ, a' < L μ + 1 ∧ b' < L μ + 1 ∧ a' / h1 = (y μ).val / h1 ∧ b' / h2 = (x μ).val / h2 ∧
      pcd (L μ + 1) a' b' ≤ A1 + A2 + 1 := by
    intro μ
    obtain ⟨t1, e1, e2, e3⟩ := hy μ
    obtain ⟨t2, f1, f2, f3⟩ := hx μ
    exact coord_pair (L μ + 1) (c μ).val h1 r1 A1 h2 r2 A2 (y μ).val (x μ).val (c μ).isLt hh1 (hh1N μ) (hh1c μ) hh1r hA1
      hh2 (hh2N μ) (hh2c μ) hh2r hA2 (y μ).isLt (x μ).isLt
      (cube_off (L μ + 1) (c μ).val r1 (y μ).val (y μ).isLt (c μ).isLt t1 e1 e2 e3)
      (cube_off (L μ + 1) (c μ).val r2 (x μ).val (x μ).isLt (c μ).isLt t2 f1 f2 f3)
  choose ya xa hya hxa hyd hxd hp using h
  refine ⟨fun μ => ⟨ya μ, hya μ⟩, fun μ => ⟨xa μ, hxa μ⟩, hyd, hxd, ?_⟩
  unfold pdist
  rw [Fin.sum_univ_three]
  have := hp 0; have := hp 1; have := hp 2
  show pcd (L 0 + 1) (ya 0) (xa 0) + pcd (L 1 + 1) (ya 1) (xa 1) + pcd (L 2 + 1) (ya 2) (xa 2) ≤ _
  omega

end AdalyFormal.P409S
