import NuD1a

/-!
# NuD1b -- the first blocked level of the direction-0 staggered family at EVERY base (lane ncwdh_ell2_20261018)

`stag0Cfg xs t ∈ 𝒞(D0 xs, a ↦ sgn(a) t)`.  For `ell` even and an even transverse side:
`bg1 (z, 0) = cartan (Sw0 (z₀) · Ubg0 z)`, `bg1 (z, 1) = bg1 (z, 2) = 1`, where
`Ubg0 z = sgn(z₁) t · (1 - 2 cnt₀ cnt₂ ⌊cnt₁/2⌋ / ell³)` (`cnt_μ = min ell (N_μ - z_μ)`): zero on every full block (in particular at every aligned base).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.NcwdhTwo

open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverOmega
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge loopVar coarseBondVar gammaVarStrided cPlusS cPlusS_eq)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)

section
variable [CfData]
variable {L : PeriodicLatticeExtent}

/-- the transverse profile of the staggered family. -/
def uSt (t : ℝ) : ℕ → ℕ → ℝ := fun a1 _ => sgnNat a1 * t

theorem stag0_isUTemp (xs : ℕ) (t : ℝ) :
    IsUTemp (D0 xs) (uSt t) (stag0Cfg (L := L) xs t : PeriodicLinkConfiguration SU2 L) := by
  intro z
  refine ⟨?_, ?_, ?_⟩
  · unfold stag0Cfg
    by_cases h : (z 0).val = xs
    · simp only [h, true_and, if_true, D0, uSt, stagSign, sgnNat]
      congr 1
      split_ifs <;> ring
    · have h' : ¬ ((z 0).val = xs ∧ (0 : Fin 3) = 0) := fun hh => h hh.1
      rw [if_neg h']
      simp only [D0, h, if_false, zero_mul]
      exact cartan_zero.symm
  · unfold stag0Cfg
    rw [if_neg (by simp)]
  · unfold stag0Cfg
    rw [if_neg (by simp)]

/-- the exact loop angle expression of the class (restated as a function). -/
noncomputable def uPhi (s ell : ℕ) (D : ℕ → ℝ) (u : ℕ → ℕ → ℝ) (y : PeriodicLatticeSite L) (μ : Fin 3)
    (x : PeriodicLatticeSite L) : ℝ :=
  if μ = 0 then (∑ j ∈ Finset.range ell, D (((y 0).val + s * j) % (L 0 + 1))) * (u (x 1).val (x 2).val - u (y 1).val (y 2).val)
       else if μ = 1 then (∑ j ∈ Finset.range ((x 0 - y 0).val / s), D (((y 0).val + s * j) % (L 0 + 1))) *
          (u (x 1).val (x 2).val - u (((x 1).val + s * ell) % (L 1 + 1)) (x 2).val)
       else (∑ j ∈ Finset.range ((x 0 - y 0).val / s), D (((y 0).val + s * j) % (L 0 + 1))) *
          (u (x 1).val (x 2).val - u (x 1).val (((x 2).val + s * ell) % (L 2 + 1)))

theorem loopVar_uPhi {s ell : ℕ} {D : ℕ → ℝ} {u : ℕ → ℕ → ℝ} {V : PeriodicLinkConfiguration SU2 L} (hV : IsUTemp D u V)
    (y : PeriodicLatticeSite L) (μ : Fin 3) {x : PeriodicLatticeSite L} (hx : x ∈ stepBlockOf y s ell) :
    loopVar s ell V (y, μ) x = cartan (uPhi s ell D u y μ x) := loopVar_uTemp hV y μ hx

theorem uPhi_abs_lt {s ell : ℕ} (hs : 0 < s) {D : ℕ → ℝ} {u : ℕ → ℕ → ℝ} {B : ℝ} (hu : ∀ a b, |u a b| ≤ B)
    (hB : 2 * B < Real.pi)
    (hD : ∀ (a m : ℕ), m ≤ ell → |∑ j ∈ Finset.range m, D ((a + s * j) % (L 0 + 1))| ≤ 1)
    (y : PeriodicLatticeSite L) (μ : Fin 3) {x : PeriodicLatticeSite L} (hx : x ∈ stepBlockOf y s ell) :
    |uPhi s ell D u y μ x| < Real.pi := by
  have hb : ∀ (S p q : ℝ), |S| ≤ 1 → |p| ≤ B → |q| ≤ B → |S * (p - q)| < Real.pi := by
    intro S p q hS hp hq
    rw [abs_mul]
    have : |p - q| ≤ 2 * B := by
      calc |p - q| ≤ |p| + |q| := abs_sub _ _
        _ ≤ 2 * B := by linarith
    calc |S| * |p - q| ≤ 1 * (2 * B) := by gcongr
      _ < Real.pi := by linarith
  have hq : (((x 0 - y 0).val) / s) ≤ ell := by
    have h0 := (mem_stepBlockOf.mp hx 0)
    have e0 := n_eq hx 0
    have hlt : (x 0).val < (y 0).val + s * ell := by simpa using h0.2.1
    rw [e0] at hlt
    have : s * (((x 0 - y 0).val) / s) < s * ell := Nat.lt_of_add_lt_add_left hlt
    exact (Nat.lt_of_mul_lt_mul_left this).le
  unfold uPhi
  split_ifs
  · exact hb _ _ _ (hD (y 0).val ell le_rfl) (hu _ _) (hu _ _)
  · exact hb _ _ _ (hD (y 0).val _ hq) (hu _ _) (hu _ _)
  · exact hb _ _ _ (hD (y 0).val _ hq) (hu _ _) (hu _ _)

theorem sgnNat_mod_even {a N ell : ℕ} (hN : 2 ∣ N) (hE : 2 ∣ ell) : sgnNat ((a + ell) % N) = sgnNat a := by
  unfold sgnNat
  have h1 : (a + ell) % N % 2 = (a + ell) % 2 := Nat.mod_mod_of_dvd _ hN
  have h2 : (a + ell) % 2 = a % 2 := by omega
  rw [h1, h2]

/-- the `x₁`-profile of the first blocked level. -/
noncomputable def Ubg0 (ell : ℕ) (t : ℝ) (z : PeriodicLatticeSite L) : ℝ :=
  (sgnNat (z 1).val * t) *
    (1 - 2 * (((min ell (L 0 + 1 - (z 0).val) : ℕ) : ℝ) * ((min ell (L 2 + 1 - (z 2).val) : ℕ) : ℝ) *
      (((min ell (L 1 + 1 - (z 1).val)) / 2 : ℕ) : ℝ)) / (ell : ℝ) ^ 3)

end

end AdalyFormal.NcwdhTwo
