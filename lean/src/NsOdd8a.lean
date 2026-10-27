import NsOdd7

/-!
# NsOdd8a -- sums over full strided blocks as triple sums (lane ncwdh_strong_20261017)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)

variable {L : PeriodicLatticeExtent}

theorem sum_fun3 (ell : ℕ) (F : ℕ → ℕ → ℕ → ℝ) :
    ∑ f : Fin 3 → Fin ell, F (f 0).val (f 1).val (f 2).val =
      ∑ a ∈ Finset.range ell, ∑ b ∈ Finset.range ell, ∑ c ∈ Finset.range ell, F a b c := by
  have h : ∑ a ∈ Finset.range ell, ∑ b ∈ Finset.range ell, ∑ c ∈ Finset.range ell, F a b c =
      ∑ p ∈ (Finset.range ell ×ˢ Finset.range ell ×ˢ Finset.range ell), F p.1 p.2.1 p.2.2 := by
    simp [Finset.sum_product]
  rw [h]
  refine Finset.sum_bij' (fun f _ => ((f 0).val, (f 1).val, (f 2).val))
    (fun p hp => fun i => ⟨if i = 0 then p.1 else if i = 1 then p.2.1 else p.2.2, by
      simp only [Finset.mem_product, Finset.mem_range] at hp
      split_ifs <;> omega⟩) ?_ ?_ ?_ ?_ ?_
  · intro f _; simp [(f 0).isLt, (f 1).isLt, (f 2).isLt]
  · intro p hp; simp
  · intro f _; funext i; fin_cases i <;> simp
  · intro p hp; simp
  · intro f _; simp

theorem sum_block_stride (y : PeriodicLatticeSite L) (s ell : ℕ) (hs : 0 < s) (hfit : ∀ μ, (y μ).val + s * ell ≤ L μ + 1)
    (F : ℕ → ℕ → ℕ → ℝ) :
    ∑ x ∈ stepBlockOf y s ell, F (((x 0).val - (y 0).val) / s) (((x 1).val - (y 1).val) / s) (((x 2).val - (y 2).val) / s) =
      ∑ a ∈ Finset.range ell, ∑ b ∈ Finset.range ell, ∑ c ∈ Finset.range ell, F a b c := by
  rw [stepBlockOf_eq_image y s ell hs hfit, Finset.sum_image (fun f _ g' _ h => siteOfF_injective y s ell hs hfit h)]
  have : ∀ f : Fin 3 → Fin ell, ∀ μ : Fin 3, ((((siteOfF y s ell hfit hs f) μ).val - (y μ).val) / s) = (f μ).val := by
    intro f μ
    simp only [siteOfF, Nat.add_sub_cancel_left]
    rw [Nat.mul_div_cancel_left _ hs]
  simp only [this]
  exact sum_fun3 ell F

#print axioms sum_block_stride

end AdalyFormal.CoverOmega
