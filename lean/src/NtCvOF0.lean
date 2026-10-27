import NtCvO48

/-!
# CvOF0 -- sums over sites of a function of `x₀` (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open Finset
open AdalyFormal.Target.ClayStatement

theorem sum_site_x0 (L : PeriodicLatticeExtent) (h : ℕ → ℝ) :
    ∑ x : PeriodicLatticeSite L, h (x 0).val = ((L 1 + 1) * (L 2 + 1) : ℕ) * ∑ v ∈ range (L 0 + 1), h v := by
  have e := Fin.consEquiv (fun μ : Fin 3 => Fin (L μ + 1))
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun μ : Fin 3 => Fin (L μ + 1))) (fun p => h p.1.val) _ ?_]
  · rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fin.prod_univ_two, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    have : ∑ a : Fin (L 0 + 1), h a.val = ∑ v ∈ range (L 0 + 1), h v := Fin.sum_univ_eq_sum_range h _
    rw [this]
    simp [Fin.succ]
  · intro p
    simp [Fin.consEquiv]

#print axioms sum_site_x0

end AdalyFormal.CoverOmega
