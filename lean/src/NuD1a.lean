import NuD0b
import NsCvO13

/-!
# NuD1a -- window sums of the point profile `D0 xs`, and `RegBg2` of a class-`𝒞(D,u)` configuration (lane ncwdh_ell2_20261018)

* `D0 xs v = [v = xs]`; `sum_D0_le_one`: any `n ≤ N` consecutive residues mod `N` contain `xs` at most once.
* `Sw0 xs ell N0 v = Σ_{i<ell} D0 xs ((v+i) mod N0)`; `sum_Sw0_le_one`: `Σ_{j<m} Sw0 ((a+ell j) mod N0) ∈ [0,1]` for `m ≤ ell ≤ ...`, `ell*ell ≤ N0`.
* `regBg2_of_uTemp`: if `V ∈ 𝒞(D,u)`, `|u| ≤ B`, `2B < π` and the `D`-window sums along stride `s` lie in `[-1,1]`, then `RegBg2 s ell V`.
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

/-- the point profile. -/
def D0 (xs v : ℕ) : ℝ := if v = xs then 1 else 0

/-- the window profile: `[xs ∈ {v, …, v+ell-1} mod N0]`. -/
def Sw0 (xs ell N0 v : ℕ) : ℝ := ∑ i ∈ Finset.range ell, D0 xs ((v + i) % N0)

theorem sum_D0_le_one (xs a N n : ℕ) (hn : n ≤ N) :
    0 ≤ ∑ r ∈ Finset.range n, D0 xs ((a + r) % N) ∧ ∑ r ∈ Finset.range n, D0 xs ((a + r) % N) ≤ 1 := by
  unfold D0
  rw [Finset.sum_boole]
  refine ⟨Nat.cast_nonneg _, ?_⟩
  have hc : ((Finset.range n).filter (fun r => (a + r) % N = xs)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro r1 h1 r2 h2
    simp only [Finset.mem_filter, Finset.mem_range] at h1 h2
    have hm : (a + r1) ≡ (a + r2) [MOD N] := by
      unfold Nat.ModEq; rw [h1.2, h2.2]
    have hm' : r1 ≡ r2 [MOD N] := Nat.ModEq.add_left_cancel' a hm
    exact Nat.ModEq.eq_of_lt_of_lt hm' (by omega) (by omega)
  exact_mod_cast hc

theorem sum_range_mul_add (f : ℕ → ℝ) (m e : ℕ) :
    ∑ j ∈ Finset.range m, ∑ i ∈ Finset.range e, f (e * j + i) = ∑ r ∈ Finset.range (m * e), f r := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, show (m + 1) * e = m * e + e by ring, Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1; ring

theorem sum_Sw0_le_one (xs ell N0 a m : ℕ) (hm : m * ell ≤ N0) :
    0 ≤ ∑ j ∈ Finset.range m, Sw0 xs ell N0 ((a + ell * j) % N0) ∧
      ∑ j ∈ Finset.range m, Sw0 xs ell N0 ((a + ell * j) % N0) ≤ 1 := by
  have h : ∑ j ∈ Finset.range m, Sw0 xs ell N0 ((a + ell * j) % N0) = ∑ r ∈ Finset.range (m * ell), D0 xs ((a + r) % N0) := by
    rw [← sum_range_mul_add (fun r => D0 xs ((a + r) % N0)) m ell]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    unfold Sw0
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Nat.mod_add_mod]
    congr 2; ring
  rw [h]
  exact sum_D0_le_one xs a N0 (m * ell) hm

/-- **`RegBg2` for a class-`𝒞(D,u)` configuration** (every base bond, every loop of the stride-`s` block). -/
theorem regBg2_of_uTemp {s ell : ℕ} (hs : 0 < s) {D : ℕ → ℝ} {u : ℕ → ℕ → ℝ} {V : PeriodicLinkConfiguration SU2 L}
    (hV : IsUTemp D u V) {B : ℝ} (hu : ∀ a b, |u a b| ≤ B) (hB : 2 * B < Real.pi)
    (hD : ∀ (a m : ℕ), m ≤ ell → |∑ j ∈ Finset.range m, D ((a + s * j) % (L 0 + 1))| ≤ 1) :
    RegBg2 s ell V := by
  apply regBg2_of_ne_negOne
  intro cc x hx
  obtain ⟨y, μ⟩ := cc
  rw [loopVar_uTemp hV y μ hx]
  apply cartan_ne_negOne
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
  split_ifs
  · exact hb _ _ _ (hD (y 0).val ell le_rfl) (hu _ _) (hu _ _)
  · exact hb _ _ _ (hD (y 0).val _ hq) (hu _ _) (hu _ _)
  · exact hb _ _ _ (hD (y 0).val _ hq) (hu _ _) (hu _ _)

end

end AdalyFormal.NcwdhTwo
