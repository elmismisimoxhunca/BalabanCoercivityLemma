import GenP1
import Q409L2
import Q409W4
import ProsX0

set_option autoImplicit false
namespace SolP409Review
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.GeneralClass
open AdalyFormal.P409

-- A missing explicit uniqueness clause does not mean the index can be non-unique.
theorem setw_index_unique {L : PeriodicLatticeExtent} {ell M R k F G i j : ℕ}
    {S : Tower L} {sites : Set (PeriodicLatticeSite L)}
    (hA : Admissible ell M R k S)
    (hi : IsClassSetW ell M F k S sites i)
    (hj : IsClassSetW ell M G k S sites j) : i = j := by
  have key : ∀ {a b F G : ℕ}, a < b → IsClassSetW ell M F k S sites a →
      IsClassSetW ell M G k S sites b → False := by
    intro a b F G hab ha hb
    obtain ⟨x, hx, hxa⟩ := ha.2.2.1
    have hxb : x ∈ S.Om b := by
      rcases hb.2.1 hx with h | h
      · exact h.1
      · exact hA.1 b h.1
    exact hxa.2 (AdalyFormal.GeneralClass.om_anti hA.1 (by omega : a + 1 ≤ b) hxb)
  rcases lt_trichotomy i j with h | h | h
  · exact (key h hi hj).elim
  · exact h
  · exact (key h hj hi).elim

-- The prosecution's actual numerical premise really does exclude the advertised patch factor.
theorem cube5_rejects_patch_factor {L : PeriodicLatticeExtent} {N ell M A0 A B B0 : ℕ}
    (hN : ∀ μ, L μ + 1 = N) (hM : 2 ≤ M) (hell : 2 ≤ ell)
    (hA0 : A0 + 1 ≤ A) (hAB : A < B) (hBB0 : B ≤ B0) (hAN : A < N)
    (hN24 : 24 * (M * ell) ≤ N)
    (w : PeriodicLatticeSite L) (hw0 : (w 0).val = A)
    (hw1 : (w 1).val = 0) (hw2 : (w 2).val = 0) :
    ¬ ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ),
      IsClassSetW ell M (10 * ell + 1) 1 (TG A0 A B B0 L) sites i ∧
      {y | (∀ μ : Fin 3, pcd (L μ + 1) (w μ).val (y μ).val ≤ 6 * (M * ell) - 1) ∧
        y ∈ (TG A0 A B B0 L).Om 0} ⊆ sites := by
  exact cube5_needs_12ell hN hM hell hA0 hAB hBB0 hAN hN24
    (10 * ell + 1) (by omega) w hw0 hw1 hw2

#print axioms setw_index_unique
#print axioms cube5_rejects_patch_factor
#print axioms AdalyFormal.P409.cube5_needs_12ell
#print AdalyFormal.StatementLane.pdist
#print AdalyFormal.M1.IsPatch
#print AdalyFormal.M1.patch
#print AdalyFormal.GeneralClass.IsClassSetW
end SolP409Review
