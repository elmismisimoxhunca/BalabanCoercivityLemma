import NVC1

/-!
# NVC2 -- the instance of `SlabGeo` with layout scale `T ≥ R` at `N = M ell² (6T+2)` (lane nonvac_c_20261017)

`s2 = M ell²`.  `Ω₂ = [s2·2T, s2·(4T+1))`, `Ω₁ = [s2·T, s2·(5T+1))`, `Ω₀ = [M (ell² T - R), s2 (5T+1) + R M)`, torus `s2 (6T+2)`.
`R` is the `Admissible` collar parameter; `T` is the layout scale, any `T ≥ R`, `T ≥ 1` (NV2 is the case `T = R`).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000

namespace AdalyFormal.NonVacC

def nvcN (ell M T : ℕ) : ℕ := M * ell ^ 2 * (6 * T + 2)
def nvcP2 (ell M T : ℕ) : ℕ := M * ell ^ 2 * (2 * T)
def nvcQ2 (ell M T : ℕ) : ℕ := M * ell ^ 2 * (4 * T + 1)
def nvcP1 (ell M T : ℕ) : ℕ := M * ell ^ 2 * T
def nvcQ1 (ell M T : ℕ) : ℕ := M * ell ^ 2 * (5 * T + 1)
def nvcP0 (ell M R T : ℕ) : ℕ := M * (ell ^ 2 * T - R)
def nvcQ0 (ell M R T : ℕ) : ℕ := M * ell ^ 2 * (5 * T + 1) + R * M

theorem slabGeo_inst {ell M R T : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hdvd : ell ∣ M) (hRT : R ≤ T) (hT : 1 ≤ T) :
    SlabGeo M ell R (nvcN ell M T) (nvcP0 ell M R T) (nvcQ0 ell M R T) (nvcP1 ell M T) (nvcQ1 ell M T)
      (nvcP2 ell M T) (nvcQ2 ell M T) := by
  have hell0 : 0 < ell := by omega
  obtain ⟨e, he⟩ : ∃ e, e = ell ^ 2 := ⟨_, rfl⟩
  have he1 : ell ≤ e := by rw [he]; nlinarith
  have he2 : 1 ≤ e := by omega
  have hs : ell ^ 2 = e := he.symm
  have hTe : T ≤ e * T := Nat.le_mul_of_pos_left T (by omega)
  obtain ⟨g, hg⟩ : ∃ g, e * T = R + g := ⟨e * T - R, by omega⟩
  have hP0 : nvcP0 ell M R T = M * g := by simp only [nvcP0, hs]; congr 1; omega
  have hRl : R * ell ≤ e * T := by
    have h1 : R * ell ≤ T * ell := Nat.mul_le_mul_right ell hRT
    have h2 : T * ell ≤ T * e := Nat.mul_le_mul_left T he1
    nlinarith
  have hMRl : M * (R * ell) ≤ M * (e * T) := Nat.mul_le_mul_left M hRl
  have hMg : M * (e * T) = M * R + M * g := by rw [hg]; ring
  have hMe : M * 1 ≤ M * e := Nat.mul_le_mul_left M he2
  have hMf : M * ell ≤ M * e := Nat.mul_le_mul_left M he1
  have hMT : M * (e * T) = M * e * T := by ring
  have hX : 0 < M * e := Nat.mul_pos hM (by omega)
  refine ⟨hM, hell0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- nest01
    rw [hP0]; simp only [nvcP1, hs]; nlinarith [Nat.zero_le (M * R)]
  · simp only [nvcP1, nvcP2, hs]; nlinarith [Nat.zero_le (M * e * T)]
  · simp only [nvcP2, nvcQ2, hs]; nlinarith [Nat.zero_le (M * e * T)]
  · simp only [nvcQ2, nvcQ1, hs]; nlinarith [Nat.zero_le (M * e * T)]
  · simp only [nvcQ1, nvcQ0, hs]; try omega
  · simp only [nvcQ0, nvcN, hs]
    nlinarith [Nat.mul_le_mul_right T hMe, Nat.zero_le (M * e * T), Nat.zero_le (M * g), Nat.mul_le_mul_left M hTe]
  · exact ⟨ell ^ 2 * (6 * T + 2), by simp only [nvcN] <;> ring⟩
  · exact ⟨ell * (6 * T + 2), by simp only [nvcN] <;> ring⟩
  · exact ⟨6 * T + 2, by simp only [nvcN] <;> ring⟩
  · rw [hP0]; exact Dvd.intro _ rfl
  · exact ⟨ell ^ 2 * (5 * T + 1) + R, by simp only [nvcQ0] <;> ring⟩
  · exact ⟨ell * T, by simp only [nvcP1] <;> ring⟩
  · exact ⟨ell * (5 * T + 1), by simp only [nvcQ1] <;> ring⟩
  · exact ⟨2 * T, by simp only [nvcP2] <;> ring⟩
  · exact ⟨4 * T + 1, by simp only [nvcQ2] <;> ring⟩
  · rw [hP0]; simp only [nvcP1, hs]; nlinarith
  · simp only [nvcQ0, nvcQ1]
  · simp only [nvcP1, hs]; nlinarith [Nat.mul_le_mul_right T hMe]
  · simp only [nvcP1, nvcP2, hs]; nlinarith [Nat.zero_le (M * e * T)]
  · simp only [nvcQ2, nvcQ1, hs]; nlinarith [Nat.zero_le (M * e * T)]
  · simp only [nvcP2, hs]; nlinarith [Nat.zero_le (M * e * T)]

end AdalyFormal.NonVacC
