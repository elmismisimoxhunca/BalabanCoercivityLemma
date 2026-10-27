import NsCvOF12

/-!
# CvOF13 -- the chain assembly: crossing `cs`, window index `p`, saddles `e_c` with prescribed row sums and `qF_c(e_c) < M0` (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open Finset
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.StatementLane (scaleUp)

variable {ell M R : ℕ}

theorem BF_f0N (hg : NGeo ell M R) (C : ℕ) (c : ℝ) (es : Fin (nN ell M R) → ℝ) {i1 p : ℕ} (hp : i1 + p + 1 < RN hg) :
    BF C c (f0N ell M R i1 p) es =
      (ell : ℝ) ^ 2 * (rowMu C c es (stN ell M R) (i1 + p) - rowMu C c es (stN ell M R) (i1 + p + 1)) := by
  have hn := stN_RN hg
  have hs1 : stN ell M R (i1 + p) < nN ell M R := by
    have := stN_strictMono hg (show i1 + p < RN hg by omega); omega
  have hs2 : stN ell M R (i1 + p + 1) < nN ell M R := by
    have := stN_strictMono hg (show i1 + p + 1 < RN hg by omega); omega
  have hf : f0N ell M R i1 p = ((ell : ℝ) ^ 2) • (Pi.single (⟨stN ell M R (i1 + p), hs1⟩ : Fin (nN ell M R)) (1 : ℝ) : Fin (nN ell M R) → ℝ)
      + (-((ell : ℝ) ^ 2)) • (Pi.single (⟨stN ell M R (i1 + p + 1), hs2⟩ : Fin (nN ell M R)) (1 : ℝ) : Fin (nN ell M R) → ℝ) := by
    funext x
    simp only [f0N, Pi.add_apply, Pi.smul_apply, Pi.single_apply, Fin.ext_iff, smul_eq_mul]
    ring
  rw [BF_comm, hf, BF_add_right, BF_smul_right, BF_smul_right]
  unfold rowMu
  rw [dif_pos hs1, dif_pos hs2]
  ring

#print axioms BF_f0N

end AdalyFormal.CoverOmega
