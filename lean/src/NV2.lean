import NV1

/-!
# NV2 -- the instance of `SlabGeo` at `N = M ell² (6R+2)` (lane nonvac_20261015)

`s2 = M ell²`.  `Ω₂ = [s2·2R, s2·(4R+1))`, `Ω₁ = [s2·R, s2·(5R+1))`, `Ω₀ = [M R (ell²-1), s2 (5R+1) + R M)`, torus `s2 (6R+2)`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000

namespace AdalyFormal.NonVac

def nvN (ell M R : ℕ) : ℕ := M * ell ^ 2 * (6 * R + 2)
def nvP2 (ell M R : ℕ) : ℕ := M * ell ^ 2 * (2 * R)
def nvQ2 (ell M R : ℕ) : ℕ := M * ell ^ 2 * (4 * R + 1)
def nvP1 (ell M R : ℕ) : ℕ := M * ell ^ 2 * R
def nvQ1 (ell M R : ℕ) : ℕ := M * ell ^ 2 * (5 * R + 1)
def nvP0 (ell M R : ℕ) : ℕ := M * R * (ell ^ 2 - 1)
def nvQ0 (ell M R : ℕ) : ℕ := M * ell ^ 2 * (5 * R + 1) + R * M

theorem slabGeo_inst {ell M R : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hdvd : ell ∣ M) (hR : 1 ≤ R) :
    SlabGeo M ell R (nvN ell M R) (nvP0 ell M R) (nvQ0 ell M R) (nvP1 ell M R) (nvQ1 ell M R)
      (nvP2 ell M R) (nvQ2 ell M R) := by
  have hell0 : 0 < ell := by omega
  obtain ⟨e, he⟩ : ∃ e, e = ell ^ 2 := ⟨_, rfl⟩
  have he1 : ell ≤ e := by rw [he]; nlinarith
  have he2 : 1 ≤ e := by omega
  have hee : e - 1 + 1 = e := by omega
  have hP0 : nvP0 ell M R = M * R * (e - 1) := by simp [nvP0, he]
  have hs : ell ^ 2 = e := he.symm
  have hMe : M * 1 ≤ M * e := Nat.mul_le_mul_left M he2
  have hMf : M * ell ≤ M * e := Nat.mul_le_mul_left M he1
  refine ⟨hM, hell0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- nest01
    simp only [hP0, nvP1, hs]
    obtain ⟨d, hd⟩ : ∃ d, e = d + 1 := ⟨e - 1, by omega⟩
    subst hd
    simp only [Nat.add_sub_cancel]
    nlinarith [Nat.zero_le (M * R * d)]
  · simp only [nvP1, nvP2, hs]; nlinarith [Nat.zero_le (M * e * R)]
  · simp only [nvP2, nvQ2, hs]; nlinarith [Nat.mul_pos hM (show 0 < e by omega), Nat.zero_le (M * e * R)]
  · simp only [nvQ2, nvQ1, hs]; nlinarith [Nat.zero_le (M * e * R)]
  · simp only [nvQ1, nvQ0, hs]; try omega
  · simp only [nvQ0, nvN, hs]
    nlinarith [Nat.mul_le_mul_right R hMe, Nat.zero_le (M * e * R), Nat.zero_le (M * R)]
  · exact ⟨ell ^ 2 * (6 * R + 2), by simp only [nvN] <;> ring⟩
  · exact ⟨ell * (6 * R + 2), by simp only [nvN] <;> ring⟩
  · exact ⟨6 * R + 2, by simp only [nvN] <;> ring⟩
  · exact ⟨R * (ell ^ 2 - 1), by simp only [nvP0] <;> ring⟩
  · exact ⟨ell ^ 2 * (5 * R + 1) + R, by simp only [nvQ0] <;> ring⟩
  · exact ⟨ell * R, by simp only [nvP1] <;> ring⟩
  · exact ⟨ell * (5 * R + 1), by simp only [nvQ1] <;> ring⟩
  · exact ⟨2 * R, by simp only [nvP2] <;> ring⟩
  · exact ⟨4 * R + 1, by simp only [nvQ2] <;> ring⟩
  · obtain ⟨d, hd⟩ : ∃ d, ell ^ 2 = d + 1 := ⟨ell ^ 2 - 1, by omega⟩
    have h1 : ell ^ 2 - 1 = d := by omega
    simp only [nvP1, nvP0]; rw [h1, hd]; ring
  · simp only [nvQ0, nvQ1]
  · simp only [nvP1, hs]; nlinarith [Nat.mul_le_mul_right R hMe]
  · simp only [nvP1, nvP2, hs]; nlinarith [Nat.mul_le_mul_left R hMf, Nat.zero_le (M * e * R)]
  · simp only [nvQ2, nvQ1, hs]; nlinarith [Nat.mul_le_mul_left R hMf, Nat.zero_le (M * e * R)]
  · simp only [nvP2, hs]; nlinarith [Nat.mul_le_mul_left R hMf, Nat.zero_le (M * e * R)]

end AdalyFormal.NonVac
