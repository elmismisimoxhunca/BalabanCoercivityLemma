import NtCvOF1
import NtCvOI4

/-!
# CvOF2 -- the `Dpi` energy of a chain vector: `<zfield (fe e), zfield (zprof ..)> = c0 T1 qF(e)` (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)

variable {ell M R : ℕ}

theorem Dpi_energy (hell3 : 3 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (t : ℝ) (e : Fin (nN ell M R) → ℝ) :
    (inner ℝ (zfield (fe (neP0 ell M R) e) : BondFnL2 (scaleUp ell 2 (neLu M R)))
        (zfield (zprof (scaleUp ell 2 (neLu M R) 0)
          (omegaW (fun v => neP0 ell M R ≤ v ∧ v < neQ0 ell M R) (scaleUp ell 2 (neLu M R) 0) (neC ell M R) t) (fe (neP0 ell M R) e))) : ℝ) =
      c0 * ((((scaleUp ell 2 (neLu M R)) 1 + 1) * ((scaleUp ell 2 (neLu M R)) 2 + 1) : ℕ) : ℝ) *
        qF (neC ell M R - neP0 ell M R) (Real.cos t) e := by
  have hg := nGeo hell3 hdvd hM hR
  have hell : 0 < ell := by omega
  rw [inner_zfield_zfield]
  congr 1
  set N := scaleUp ell 2 (neLu M R) 0 with hN
  have hN1 : N + 1 = neN ell M R := ne_scaleUp hell hM 0
  have hQ := ne_Q0_lt_N hell3 hM hR
  have hP0 := ne_P0_pos hell3 hM hR
  -- restrict the sum to [P0, Q0)
  have hsub : ∀ v ∈ range (N + 1), v ∉ (Finset.univ : Finset (Fin (nN ell M R))).image (fun x => neP0 ell M R + x.val) →
      fe (neP0 ell M R) e v * zprof N (omegaW (fun v => neP0 ell M R ≤ v ∧ v < neQ0 ell M R) N (neC ell M R) t) (fe (neP0 ell M R) e) v = 0 := by
    intro v hv hvn
    have hfv : fe (neP0 ell M R) e v = 0 := by
      by_cases h1 : v < neP0 ell M R
      · exact fe_lt _ e h1
      · apply fe_ge
        by_contra h2
        apply hvn
        have h2' : v < neP0 ell M R + nN ell M R := by omega
        exact Finset.mem_image.mpr ⟨⟨v - neP0 ell M R, by omega⟩, Finset.mem_univ _, by simp; omega⟩
    rw [hfv, zero_mul]
  have himg : (Finset.univ : Finset (Fin (nN ell M R))).image (fun x => neP0 ell M R + x.val) ⊆ range (N + 1) := by
    intro v hv
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hv
    have := x.2; unfold nN at this
    simp only [Finset.mem_range]; omega
  rw [← Finset.sum_subset himg (fun v hv hvn => hsub v hv hvn)]
  rw [Finset.sum_image (fun x _ y _ h => Fin.ext (by simpa using h))]
  rw [show qF (neC ell M R - neP0 ell M R) (Real.cos t) e = BF (neC ell M R - neP0 ell M R) (Real.cos t) e e from (BF_self _ _ _).symm]
  rw [BF_eq_sum_single]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [fe_at, zprof_eq_BF hell3 hdvd hM hR t e x]

#print axioms Dpi_energy

end AdalyFormal.CoverOmega
