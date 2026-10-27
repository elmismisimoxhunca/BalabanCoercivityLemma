import ScalarHodge
set_option autoImplicit false
namespace HConstruction.DRepair
open HConstruction.Carrier HConstruction.Covariance
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.DeltaKUnified (bfl2Equiv)
open AdalyFormal.Balaban.LatticeOperators (curlValue)

/-- Hodge on the actual su(2) Hilbert carrier, retaining all three harmonic
classes of the periodic torus. The scalar theorem is freshly reproduced. -/
theorem flatCurl_hodge (A : H) (hA : flatCurl A = 0) :
    ∃ (f : S) (c : Fin 3 → SuTwo), A = flatGrad f + constBond c := by
  classical
  let β := Module.finBasis ℝ SuTwo
  have hc (p : PeriodicLatticePlaquette witnessL) :
      curlValueCovariant (trivialU witnessL) (bfl2Equiv A) p = 0 := by
    have h := congrArg (fun X => fiberEquiv _ X p) hA
    have h' : (2 : ℝ) • curlValueCovariant (trivialU witnessL) (bfl2Equiv A) p = 0 := by
      simpa [flatCurl, curlCovariantLM] using h
    exact (smul_eq_zero.mp h').resolve_left (by norm_num)
  have hs (i : Fin (Module.finrank ℝ SuTwo)) : Hodge.CurlFree
      (fun b => β.repr (bfl2Equiv A b) i) := by
    intro p
    have h := congrArg (fun X : SuTwo => β.repr X i) (hc p)
    simpa [curlValueCovariant, trivialU, RMap_one, curlValue, map_add, map_sub] using h
  choose f c he using fun i => Hodge.curlFree_eq_grad_add_const (hs i)
  let ff : S := (fiberEquiv _).symm (fun x => (1/2 : ℝ) • ∑ i, f i x • β i)
  let cc : Fin 3 → SuTwo := fun μ => ∑ i, c i μ • β i
  refine ⟨ff,cc,?_⟩
  apply bfl2Equiv.injective
  funext b
  have hh : bfl2Equiv A b =
      (∑ i, f i (periodicLatticeShift b.1 b.2) • β i) -
      (∑ i, f i b.1 • β i) + ∑ i, c i b.2 • β i := by
    calc
      bfl2Equiv A b = ∑ i, β.repr (bfl2Equiv A b) i • β i := (β.sum_repr _).symm
      _ = ∑ i, (f i (periodicLatticeShift b.1 b.2) - f i b.1 + c i b.2) • β i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [he i b]
      _ = _ := by simp only [add_smul, sub_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hh]
  simp [flatGrad, ff, cc, constBond, gradCovariantLM, gradValueCovariant,
    trivialU, RMap_one]
  module
end HConstruction.DRepair
