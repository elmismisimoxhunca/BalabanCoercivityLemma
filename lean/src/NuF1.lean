import NuC1

/-!
# NuF1 -- the trial vector `f0 + τ es` has arbitrarily negative `qF1` near the crossing (lane ncwdh_ell2_20261018)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.NcwdhTwo

open Finset Filter Topology
open AdalyFormal.CoverJacobi

section
variable {n : ℕ}

theorem qF1_cont_c (C : ℕ) (e : Fin n → ℝ) : Continuous (fun c : ℝ => qF1 C c e) := by
  unfold qF1; fun_prop

theorem trial_neg (C : ℕ) (cs : ℝ) (es f0 : Fin n → ℝ) (hqes : qF1 C cs es = 0) (hΩ : BF1 C cs es f0 ≠ 0) (M0 : ℝ) :
    ∃ τ ε : ℝ, 0 < ε ∧ ∀ c : ℝ, cs < c → c < cs + ε → qF1 C c (f0 + τ • es) < M0 := by
  set Ω := BF1 C cs es f0 with hΩdef
  set T0 := qF1 C cs f0 with hT0
  set τ : ℝ := (M0 - T0 - 1) / (2 * Ω) with hτ
  have hτΩ : 2 * τ * Ω = M0 - T0 - 1 := by
    rw [hτ]; field_simp
  have hP : ∀ c : ℝ, qF1 C c (f0 + τ • es) = qF1 C c f0 + 2 * τ * BF1 C c f0 es + τ ^ 2 * qF1 C c es := by
    intro c
    rw [qF1_add, BF1_smul_right, qF1_smul]; ring
  have hcs : qF1 C cs (f0 + τ • es) = M0 - 1 := by
    rw [hP cs, hqes, BF1_comm C cs f0 es]
    linarith
  have hcont : Continuous (fun c : ℝ => qF1 C c (f0 + τ • es)) := qF1_cont_c C _
  have hlt : ∀ᶠ c in 𝓝 cs, qF1 C c (f0 + τ • es) < M0 := by
    have : qF1 C cs (f0 + τ • es) < M0 := by rw [hcs]; linarith
    exact hcont.continuousAt.eventually (gt_mem_nhds this)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hlt
  refine ⟨τ, ε, hε, fun c h1 h2 => hball ?_⟩
  rw [Real.dist_eq, abs_lt]; constructor <;> linarith

end

end AdalyFormal.NcwdhTwo
