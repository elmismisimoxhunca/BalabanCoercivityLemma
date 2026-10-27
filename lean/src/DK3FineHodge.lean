import DK3FineTests
set_option autoImplicit false
namespace HConstruction.DK3.FineScale.Physical
open HConstruction.Carrier HConstruction.Covariance
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.DeltaKUnified (bfl2Equiv)
open AdalyFormal.Balaban.LatticeOperators (curlValue)

variable {L : PeriodicLatticeExtent}

noncomputable def constBond (c : Fin 3 → SuTwo) : H L := bfl2Equiv.symm (fun b => c b.2)

/-- Hodge on the actual su(2) Hilbert carrier, retaining all three harmonic
classes of the periodic torus. The scalar theorem is freshly reproduced. -/
theorem flatCurl_hodge (A : H L) (hA : covCurl (trivialU L) A = 0) :
    ∃ (f : S L) (c : Fin 3 → SuTwo), A = covGrad (trivialU L) f + constBond c := by
  classical
  let β := Module.finBasis ℝ SuTwo
  have hc (p : PeriodicLatticePlaquette L) :
      curlValueCovariant (trivialU L) (bfl2Equiv A) p = 0 := by
    have h := congrArg (fun X => fiberEquiv _ X p) hA
    have h' : (8 : ℝ) • curlValueCovariant (trivialU L) (bfl2Equiv A) p = 0 := by
      simpa [covCurl, curlCovariantLM] using h
    exact (smul_eq_zero.mp h').resolve_left (by norm_num)
  have hs (i : Fin (Module.finrank ℝ SuTwo)) : HConstruction.DRepair.Hodge.CurlFree
      (fun b => β.repr (bfl2Equiv A b) i) := by
    intro p
    have h := congrArg (fun X : SuTwo => β.repr X i) (hc p)
    simpa [curlValueCovariant, trivialU, RMap_one, curlValue, map_add, map_sub] using h
  choose f c he using fun i => HConstruction.DRepair.Hodge.curlFree_eq_grad_add_const (hs i)
  let ff : S L := (fiberEquiv _).symm (fun x => (1/8 : ℝ) • ∑ i, f i x • β i)
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
  simp [covGrad, ff, cc, constBond, gradCovariantLM, gradValueCovariant,
    trivialU, RMap_one]
  module
end HConstruction.DK3.FineScale.Physical

namespace HConstruction.DK3.FineScale
open Physical (covGrad siteDeltaU)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)

/-- The genuine composite-Qprime gauge term excludes all of its null pure gauges. -/
theorem gauge_excludes_Qprime_gradients (f : SF) (hf : siteQU 0 f = 0)
    (hg : gaugeConstraintU 0 (covGrad (U 0) f) = 0) : covGrad (U 0) f = 0 := by
  have hm : siteDeltaU (U 0) f ∈ gaugeImageU 0 := ⟨f,hf,rfl⟩
  have he : siteRU 0 (siteDeltaU (U 0) f) = siteDeltaU (U 0) f :=
    Submodule.starProjection_eq_self_iff.mpr hm
  have hd : siteDeltaU (U 0) f = 0 := he.symm.trans hg
  have h : (inner ℝ f (siteDeltaU (U 0) f) : ℝ) = 0 := by rw [hd,inner_zero_right]
  have hn : ‖covGrad (U 0) f‖^2 = 0 := by
    simpa only [siteDeltaU,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right,real_inner_self_eq_norm_sq] using h
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (covGrad (U 0) f)])

#print axioms Physical.flatCurl_hodge
#print axioms gauge_excludes_Qprime_gradients
end HConstruction.DK3.FineScale
