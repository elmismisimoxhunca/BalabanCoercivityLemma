import DK3FineSource
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000
noncomputable section
namespace HConstruction.DK3.FineScale
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)
open AdalyFormal.Balaban.DeltaPrime (holonomyElem holonomyElemInv imHolonomy)
open AdalyFormal.Balaban.SuTwoLogExp (M2 coe_inv)
open HConstruction.NfRepair.Reproduced
open HConstruction.Reproduced.Source
open HConstruction.Predicate

def front (ν : Fin 3) (hν : 0 < ν) : PeriodicLatticePlaquette fineL := (origin, ⟨(0,ν),hν⟩)
def back (ν : Fin 3) (hν : 0 < ν) : PeriodicLatticePlaquette fineL :=
  (periodicLatticeShiftBack origin ν, ⟨(0,ν),hν⟩)

theorem shift_origin_ne (ν : Fin 3) : periodicLatticeShift origin ν ≠ origin := by
  intro h
  have hv := congrFun h ν
  change (Function.update origin ν (origin ν + 1)) ν = origin ν at hv
  simp only [Function.update_self, origin] at hv
  norm_num at hv

theorem back_origin_ne (ν : Fin 3) : periodicLatticeShiftBack origin ν ≠ origin := by
  intro h
  have hv := congrArg (fun x => periodicLatticeShift x ν) h
  rw [AdalyFormal.Balaban.CovariantHjMinimizer.periodicLatticeShift_shiftBack] at hv
  exact shift_origin_ne ν hv.symm

theorem front_hol (t : ℝ) (ν : Fin 3) (hν : 0 < ν) :
    holonomyElem (U t) (front ν hν) = rotElem t := by
  fin_cases ν <;> norm_num at hν
  all_goals
    unfold holonomyElem periodicPlaquetteHolonomy front
    simp only [U]
    norm_num [shift_origin_ne]

theorem back_hol (t : ℝ) (ν : Fin 3) (hν : 0 < ν) :
    holonomyElem (U t) (back ν hν) = (rotElem t)⁻¹ := by
  fin_cases ν <;> norm_num at hν
  all_goals
    unfold holonomyElem periodicPlaquetteHolonomy back
    simp only [U]
    norm_num [back_origin_ne,
      AdalyFormal.Balaban.CovariantHjMinimizer.periodicLatticeShift_shiftBack]

private theorem im_rot (t : ℝ) (p : PeriodicLatticePlaquette fineL)
    (hp : holonomyElem (U t) p = rotElem t) :
    imHolonomy (U t) p = !![0, -(rotB t : ℂ)*Complex.I; (rotB t : ℂ)*Complex.I, 0] := by
  rw [imHolonomy,holonomyElemInv,hp,coe_inv,rotElem_coe,rotM_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotM] <;> ring

private theorem im_rot_inv (t : ℝ) (p : PeriodicLatticePlaquette fineL)
    (hp : holonomyElem (U t) p = (rotElem t)⁻¹) :
    imHolonomy (U t) p = !![0, (rotB t : ℂ)*Complex.I; -(rotB t : ℂ)*Complex.I, 0] := by
  rw [imHolonomy,holonomyElemInv,hp,inv_inv,coe_inv,rotElem_coe,rotM_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotM] <;> ring

theorem source_entry (t : ℝ) :
    (Jsource (U t) (origin,0) 0 1).im = -4 * rotB t := by
  have h1 := im_rot t (front 1 (by decide)) (front_hol t 1 (by decide))
  have h2 := im_rot t (front 2 (by decide)) (front_hol t 2 (by decide))
  have h3 := im_rot_inv t (back 1 (by decide)) (back_hol t 1 (by decide))
  have h4 := im_rot_inv t (back 2 (by decide)) (back_hol t 2 (by decide))
  have u1 : U t (periodicLatticeShiftBack origin 1,1) = 1 := by simp [U]
  have u2 : U t (periodicLatticeShiftBack origin 2,2) = 1 := by simp [U]
  simp only [Jsource,Jfield,Fin.sum_univ_three]
  norm_num only [show (1 : Fin 3) ≠ 0 by decide,show (2 : Fin 3) ≠ 0 by decide,
    ↓reduceIte,zero_add]
  simp only [DstarDir,u1,u2,inv_one,AdalyFormal.Balaban.SourceJ.conjByAmbient_one_apply]
  simp only [front] at h1 h2
  simp only [back] at h3 h4
  norm_num [FnuMu,h1,h2,h3,h4,piProj,Matrix.trace,Matrix.diag,Fin.sum_univ_two,Fin.lt_def]
  ring

theorem sourceFunctional_nonzero (t : ℝ) (ht : t ≠ 0) : sourceFunctional t ≠ 0 := by
  intro h
  have hc := (sourceCoordinates_eq_zero_iff (sourceFunctional t)).mpr h
  change sourceCoordinates (genuineSource (U t)) = 0 at hc
  rw [genuineSource_exact] at hc
  have he := congrArg (fun f : Bond fineL → M2 => (f (origin,0) 0 1).im) hc
  rw [source_entry] at he
  have hb : rotB t = 0 := by simpa using he
  unfold rotB at hb
  have hz := (div_eq_zero_iff).mp hb
  rcases hz with hz | hz
  · exact ht (by linarith)
  · nlinarith [sq_nonneg t]

theorem JF_nonzero (t : ℝ) (ht : t ≠ 0) : JF t ≠ 0 :=
  smul_ne_zero (by norm_num) (sourceFunctional_nonzero t ht)

#print axioms JF_nonzero

end HConstruction.DK3.FineScale
