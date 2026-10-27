import NtCvO25

/-!
# CvO26 -- `Δ_loc` maps Z-fields to Z-fields (lane omega)

For `U` Cartan and a plaquette set `P` whose (0,1)-weight `[p∈P]·holCos` depends only on `x₀` (`hω`):
`deltaKLocCLM U P (zfield f) = zfield g`, `g v = Wa(prv v) - Wa v`, `Wa v = ω v · (f(nxt v) - f v)`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShiftEquiv periodicLatticeShiftBack_shift
  periodicLatticeShift_shiftBack periodicLatticeShiftEquiv_apply periodicLatticeShiftEquiv_symm_apply hsInner_sub_left)
open AdalyFormal.Balaban.DeltaKU (hsInner_zero_right)

variable {L : PeriodicLatticeExtent}

/-- the (0,1) plane. -/
def q01 : PeriodicPlaquetteDirections := ⟨((0 : Fin 3), (1 : Fin 3)), by decide⟩

open Classical in
theorem plaq_sum_reduce {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L} (hU : CartanCfg U)
    (P : Set (PeriodicLatticePlaquette L)) (w : Bond L → SuTwo) (f : ℕ → ℝ) :
    (∑ p : PeriodicLatticePlaquette L, if p ∈ P then holCos U p * hsInner (curlValueCovariant U w p) (curlValueCovariant U (zfun f) p) else 0) =
    ∑ x : PeriodicLatticeSite L, (if (x, q01) ∈ P then holCos U (x, q01) else 0) *
      hsInner (curlValueCovariant U w (x, q01)) (dgS (f ((periodicLatticeShift x 0) 0).val - f (x 0).val)) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_eq_single q01]
  · have := curl_zfun_01 hU f x (q01.2)
    simp only [q01] at this ⊢
    rw [this]
    split_ifs <;> simp
  · intro q _ hq
    obtain ⟨⟨μ, ν⟩, h⟩ := q
    have key : ∀ (μ ν : Fin 3), μ < ν → (μ = 0 ∧ ν = 1) ∨ (μ = 0 ∧ ν = 2) ∨ (μ = 1 ∧ ν = 2) := by decide
    rcases key μ ν h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hq
    · rw [curl_zfun_02 f x h]; simp [hsInner_zero_right]
    · rw [curl_zfun_12 hU f x h]; simp [hsInner_zero_right]
  · intro h; exact absurd (Finset.mem_univ _) h

#print axioms plaq_sum_reduce

end AdalyFormal.CoverOmega
