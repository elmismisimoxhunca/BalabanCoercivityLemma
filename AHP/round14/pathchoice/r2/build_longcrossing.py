#!/usr/bin/env python3
"""Build the conditional whole-kernel-line package for the tail path."""
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
base=(ROOT/'AHP/round13/shared/assembly/R2_P2Goal.lean').read_text()
base=base.replace('push_neg','push Not')
base=base.replace('import DrPath3\n',
    'import DrPath3\n\nset_option linter.unusedVariables false\nset_option linter.unusedSimpArgs false\nset_option linter.deprecated false\n',1)
long=(ROOT/'AHP/round14/pathchoice/r2/LongArm.lean').read_text()
start=long.index('\nnamespace AdalyFormal.Round14.PathChoice\n')
end=long.index('\nend AdalyFormal.Round14.PathChoice\n',start)
path=long[start:end]
for line in [
 'open AdalyFormal.Round10.Nonvanishing.DilatedFlux (blockCount)\n',
 'open AdalyFormal.Round13.Detection.PhysicalArea\n',
 'open AdalyFormal.Round12.Kernel.ResponseActual\n']:
    assert line in path
    path=path.replace(line,'')
path=path.replace('open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)\n',
    'open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)\nopen AdalyFormal.GaugeCov\nopen AdalyFormal.Balaban.SuTwoInner (hsInner)\nopen AdalyFormal.Balaban.DeltaPrime\n')
assert 'theorem vacA_tailRightStar' in path
append=r'''
open AdalyFormal.Round12.Kernel.Crossing
open AdalyFormal.Round12.Kernel.Actual
open AdalyFormal.Round9.Guarded.QualitativeR2Joint (flat_loc_unit)
set_option linter.unusedVariables false

/-- Negative-direction input at the original pi endpoint. -/
def TailEndpointNegative : Prop :=
  ∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
    ∃ w : TwistSpace q R, ⟪w, vacA q R (tailRightStar hq R) 1 Real.pi w⟫ < 0

/-- Zero-coordinate positivity only at the canonical crossing, not on a whole
prefix.  This is the weaker input used by the crossing package below. -/
def TailCrossingPositive : Prop :=
  ∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (x : TwistSpace q R), x ≠ 0 →
    AdalyFormal.Round12.Kernel.Actual.chargedCoordinate q R
      (rightSite hq R, (0 : Fin 3)) x = 0 →
    0 < ⟪x, vacA q R (tailRightStar hq R) 1 (vacEdge q R (tailRightStar hq R)) x⟫

/-- Continuity of the actual tail-path carrier, using its proved analytic path. -/
theorem tailRightStar_vacA_cont {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    Continuous (vacA q R (tailRightStar hq R) 1) := by
  exact pathA_continuous hq hR (by nlinarith) (tailRightStar_cont hq R) (fun _ => 0) 0 1

/-- Positive-definite start for the same actual carrier. -/
theorem tailRightStar_vacA_pd_zero {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R)
    (x : TwistSpace q R) (hx : x ≠ 0) :
    0 < ⟪x, vacA q R (tailRightStar hq R) 1 0 x⟫ := by
  exact vacA_pd_zero (tailRightStar_zero hq R) (flat_loc_unit hq hR) x hx

/-- A negative pi direction and positivity at the crossing suffice for the
complete charged line and real nullity two; no full-interval P2 is assumed. -/
theorem tailKernelLine_of_inputs {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (hneg : ∃ w : TwistSpace q R, ⟪w, vacA q R (tailRightStar hq R) 1 Real.pi w⟫ < 0)
    (hpos : ∀ x : TwistSpace q R, x ≠ 0 →
      AdalyFormal.Round12.Kernel.Actual.chargedCoordinate q R
        (rightSite hq R, (0 : Fin 3)) x = 0 →
      0 < ⟪x, vacA q R (tailRightStar hq R) 1 (vacEdge q R (tailRightStar hq R)) x⟫) :
    0 < vacEdge q R (tailRightStar hq R) ∧ vacEdge q R (tailRightStar hq R) < Real.pi ∧
      ∃ u : TwistSpace q R, KernelLine q R (tailRightStar hq R) u ∧
        Module.finrank ℝ (vacA q R (tailRightStar hq R) 1
          (vacEdge q R (tailRightStar hq R))).ker = 2 := by
  obtain ⟨w,hw⟩ := hneg
  have hc := tailRightStar_vacA_cont hq hR hR18
  have hpd : ∀ x : TwistSpace q R, x ≠ 0 →
      0 < ⟪x, vacA q R (tailRightStar hq R) 1 0 x⟫ :=
    tailRightStar_vacA_pd_zero (q := q) (R := R) hq (by omega)
  have hs : ∀ t x y, ⟪vacA q R (tailRightStar hq R) 1 t x,y⟫ =
      ⟪x, vacA q R (tailRightStar hq R) 1 t y⟫ := by
    intro t x y
    exact (AdalyFormal.D1Literal.dataS AdalyFormal.D1Literal.selAll
      AdalyFormal.D1Literal.selAll (pathP q R (tailRightStar hq R) (fun _ => 0) 0 1 t)).Ginv_symm
      (AdalyFormal.D1Literal.dataS_laws _ _ _) x y
  have heq : vacEdge q R (tailRightStar hq R) =
      psdEdge (vacA q R (tailRightStar hq R) 1) 0 Real.pi :=
    psdEdge_same_after_negative _ (by positivity) (le_refl _) w hw
  obtain ⟨h0,ht,_,hn,_,_⟩ := psdEdge_singular_without_isolation
    (vacA q R (tailRightStar hq R) 1) hc hs Real.pi_pos hpd w hw
  rw [← heq] at h0 ht hn
  obtain ⟨u,hu,hAu⟩ := exists_kernel_of_nonunit _ hn
  have hl := kernelLine_of_boundary_positive q R (tailRightStar hq R)
    (rightSite hq R, (0 : Fin 3)) (tailRightStar_fixed hq R _ _) hpos u hu hAu
  exact ⟨h0,ht,u,hl,kernelLine_finrank q R (tailRightStar hq R)
    (tailRightStar_fixed hq R _ _) u hl⟩

/-- Exact all-instance crossing package remaining for the modified path. -/
def TailKernelLinePackage : Prop :=
  ∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
    0 < vacEdge q R (tailRightStar hq R) ∧ vacEdge q R (tailRightStar hq R) < Real.pi ∧
      ∃ u : TwistSpace q R, KernelLine q R (tailRightStar hq R) u ∧
        Module.finrank ℝ (vacA q R (tailRightStar hq R) 1
          (vacEdge q R (tailRightStar hq R))).ker = 2

theorem tailKernelLinePackage_of_inputs (hneg : TailEndpointNegative)
    (hpos : TailCrossingPositive) : TailKernelLinePackage := by
  intro q R hq hR hR18
  exact tailKernelLine_of_inputs hq hR hR18 (hneg hq hR hR18) (hpos hq hR hR18)

/-- Original four arms are contained in every longer finite-arm support. -/
theorem starLinks_subset_longStarLinks (x : PeriodicLatticeSite L) :
    starLinks x ⊆ longStarLinks x 1 := by
  rintro ⟨z,ν⟩ ⟨hν,hz | hz⟩
  · change ν ≠ 0 at hν
    change z = x at hz
    subst z
    exact ⟨ν,hν,0,by omega,Or.inl rfl⟩
  · change periodicLatticeShift z ν = x at hz
    have hz' : z = periodicLatticeShiftBack x ν := by
      rw [← hz, AdalyFormal.Balaban.CovariantHjMinimizer.periodicLatticeShiftBack_shift]
    subst z
    exact ⟨ν,hν,0,by omega,Or.inr rfl⟩

theorem longStarLinks_mono (x : PeriodicLatticeSite L) {N M : ℕ} (hNM : N ≤ M) :
    longStarLinks x N ⊆ longStarLinks x M := by
  rintro e ⟨μ,hμ,n,hn,he⟩
  exact ⟨μ,hμ,n,lt_of_lt_of_le hn hNM,he⟩

theorem tailPath_original (x : PeriodicLatticeSite L) (e : Bond L)
    (he : e ∈ starLinks x) (t : ℝ) : tailPath x t e = uθ t := by
  have hs := starLinks_subset_longStarLinks x he
  have hs3 := longStarLinks_mono x (by omega : 1 ≤ 3) hs
  simp [tailPath, longStarPath, hs3, tailCoeff_zero_level x e hs]

theorem tailPath_interior (Om : Set (PeriodicLatticeSite L))
    (x : PeriodicLatticeSite L) (hx : x ∉ Om)
    (htrans : ∀ z (ν : Fin 3), ν ≠ 0 → (periodicLatticeShift z ν ∈ Om ↔ z ∈ Om))
    (t : ℝ) (e : Bond L) (he : e.1 ∈ Om) : tailPath x t e = 1 := by
  have hh : e ∉ longStarLinks x 3 := fun h => (longStarLinks_exterior Om x hx htrans 3 h).1 he
  simp [tailPath, longStarPath, hh]

theorem tailPath_normal (x z : PeriodicLatticeSite L) (t : ℝ) :
    tailPath x t (z,0) = 1 := by
  have hh : (z,0) ∉ longStarLinks x 3 := by
    rintro ⟨μ,hμ,n,hn,he⟩
    change (z,0) = forwardBond x μ n ∨ (z,0) = backwardBond x μ (n+1) at he
    rcases he with h | h
    · exact hμ (congrArg (fun e : Bond L => e.2) h).symm
    · exact hμ (congrArg (fun e : Bond L => e.2) h).symm
  simp [tailPath, longStarPath, hh]

theorem tailPath_holonomy1 {Om : Set (PeriodicLatticeSite L)} {x : PeriodicLatticeSite L}
    (hbd : BdPt Om x) (t : ℝ) (ν : {ν : Fin 3 // 0 < ν}) :
    holonomyElem (tailPath (periodicLatticeShift x 0) t) (P1 x ν) = uθ t := by
  have hν : ν.1 ≠ 0 := ne_of_gt ν.2
  have h1 := tailPath_normal (periodicLatticeShift x 0) x t
  have h2 : tailPath (periodicLatticeShift x 0) t (periodicLatticeShift x 0,ν.1) = uθ t :=
    tailPath_original _ _ (by simp [starLinks, hν]) t
  have h3 := tailPath_normal (periodicLatticeShift x 0) (periodicLatticeShift x ν.1) t
  have h4 := tailPath_interior Om (periodicLatticeShift x 0) hbd.hx' hbd.trans t (x,ν.1) hbd.hx
  change periodicPlaquetteHolonomy _ _ = _
  unfold periodicPlaquetteHolonomy P1
  simp only
  rw [h1,h2,h3,h4]
  simp

theorem tailPath_holonomy2 {Om : Set (PeriodicLatticeSite L)} {x : PeriodicLatticeSite L}
    (hbd : BdPt Om x) (t : ℝ) (ν : {ν : Fin 3 // 0 < ν}) :
    holonomyElem (tailPath (periodicLatticeShift x 0) t) (P2 x ν) = uθ t := by
  have hν : ν.1 ≠ 0 := ne_of_gt ν.2
  have h1 := tailPath_normal (periodicLatticeShift x 0) (periodicLatticeShiftBack x ν.1) t
  have h2 : tailPath (periodicLatticeShift x 0) t
      (periodicLatticeShift (periodicLatticeShiftBack x ν.1) 0,ν.1) = uθ t := by
    apply tailPath_original
    have hs : periodicLatticeShift (periodicLatticeShift (periodicLatticeShiftBack x ν.1) 0) ν.1 =
        periodicLatticeShift x 0 := by
      rw [AdalyFormal.StatementLaneR8.shift_comm _ (Ne.symm hν), periodicLatticeShift_shiftBack]
    simp [starLinks, hν, hs]
  have h3 := tailPath_normal (periodicLatticeShift x 0) x t
  have h4 := tailPath_interior Om (periodicLatticeShift x 0) hbd.hx' hbd.trans t
    (periodicLatticeShiftBack x ν.1,ν.1) (hbd.shiftBack_mem ν)
  change periodicPlaquetteHolonomy _ _ = _
  unfold periodicPlaquetteHolonomy P2
  simp only
  rw [h1,h2,periodicLatticeShift_shiftBack,h3,h4]
  simp

/-- The original central-bond negative-energy trial is unchanged by the added arms. -/
theorem tailPath_negative_endpoint {ell M R k : ℕ} {Lu : PeriodicLatticeExtent}
    (hell0 : 0 < ell) (S : Tower (scaleUp ell k Lu))
    (Lam : Set (PeriodicLatticeSite Lu)) (a : ℝ)
    (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17*ell ≤ R*M)
    {x : PeriodicLatticeSite (scaleUp ell k Lu)} (hbd : BdPt (S.Om 0) x)
    (ha : 0 ≤ a) (ha4 : a < 4) (X : SuTwo) (hX : X ≠ 0) :
    ∃ v : ↥(bondSupp (geomOf ell k S)),
      ⟪v, (dataS selAll selAll (gparams ell k Lu hell0 S
        (tailPath (periodicLatticeShift x 0) Real.pi) a Lam)).Ginv v⟫ < 0 := by
  let U := tailPath (periodicLatticeShift x 0) Real.pi
  let P := gparams ell k Lu hell0 S U a Lam
  have hm := sing_mem_bondSupp (geomOf ell k S) hbd.hx X
  let v : ↥(bondSupp (geomOf ell k S)) := ⟨sing (x,0) X,hm⟩
  have hn : 0 < hsInner X X := by
    exact lt_of_le_of_ne (real_inner_self_nonneg (x := X))
      (fun h => hX (AdalyFormal.Balaban.SuTwoInner.hsInner_self_eq_zero h.symm))
  have hd : ⟪v, (dataS selAll selAll P).Dpi v⟫ = -4*hsInner X X := by
    have e := E0_Dpi_inner selAll (geomOf ell k S) U a v
    refine e.trans ?_
    have hw : Wop (geomOf ell k S) U a (iE (geomOf ell k S) v) = sing (x,0) X :=
      Wop_sing hS (by omega) hbd U a X
    rw [hw]
    apply delta_value U x X hbd.side
    · intro ν
      change ((holonomyElem (tailPath _ Real.pi) (P1 x ν) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = -1
      rw [tailPath_holonomy1 hbd, uθ_pi_coe]
    · intro ν
      change ((holonomyElem (tailPath _ Real.pi) (P2 x ν) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = -1
      rw [tailPath_holonomy2 hbd, uθ_pi_coe]
    · intro ν
      exact tailPath_interior (S.Om 0) _ hbd.hx' hbd.trans _ _ (hbd.shiftBack_mem ν)
  have ht : (dataS selAll selAll P).T v = 0 :=
    Tfull_sing_zero hS (by omega) hbd U X
  have hmass : ⟪v, (dataS selAll selAll P).Mass v⟫ ≤ a*hsInner X X := by
    change ⟪v, ((pE (geomOf ell k S)).comp ((MassFull (geomOf ell k S) a
      (bondSectorOf (geomOf ell k S) U)).comp (iE (geomOf ell k S)))) v⟫ ≤ _
    simp only [ContinuousLinearMap.comp_apply]
    rw [pE_inner_right]
    exact Mass_sing_le hS hell (by omega) hbd U a ha X
  refine ⟨v,?_⟩
  change ⟪v, (dataS selAll selAll P).Ginv v⟫ < 0
  rw [BaseDataS.inner_Ginv,hd,ht]
  simp only [norm_zero]
  nlinarith

theorem tailRightStar_negative_pi {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    ∃ w : TwistSpace q R, ⟪w, vacA q R (tailRightStar hq R) 1 Real.pi w⟫ < 0 := by
  rw [vacA_tailRightStar]
  unfold tailRightStar
  exact tailPath_negative_endpoint (by norm_num) (dilTower q R) (dilLam q R) 1
    (dil_admissible hq hR) (by norm_num) (by nlinarith)
    (rightSite_bd hq R) (by norm_num) (by norm_num) suTwoWitness suTwoWitness_ne_zero

theorem tailEndpointNegative : TailEndpointNegative := by
  intro q R hq hR hR18
  exact tailRightStar_negative_pi hq hR hR18

/-- After the proved endpoint input, only crossing positivity remains for the
complete charged-line package. -/
theorem tailKernelLinePackage_of_crossingPositive (hpos : TailCrossingPositive) :
    TailKernelLinePackage :=
  tailKernelLinePackage_of_inputs tailEndpointNegative hpos

#print axioms longStarLinks_mono
#print axioms starLinks_subset_longStarLinks
#print axioms tailPath_original
#print axioms tailPath_interior
#print axioms tailPath_normal
#print axioms tailPath_holonomy1
#print axioms tailPath_holonomy2
#print axioms tailPath_negative_endpoint
#print axioms tailRightStar_negative_pi
#print axioms tailEndpointNegative
#print axioms tailKernelLinePackage_of_crossingPositive
#print axioms TailEndpointNegative
#print axioms TailCrossingPositive
#print axioms tailRightStar_vacA_cont
#print axioms tailRightStar_vacA_pd_zero
#print axioms tailKernelLine_of_inputs
#print axioms TailKernelLinePackage
#print axioms tailKernelLinePackage_of_inputs
#check @tailKernelLinePackage_of_inputs
end AdalyFormal.Round14.PathChoice
'''
append=append.replace('(P1 x ν)','(AdalyFormal.D1Literal.P1 x ν)')
append=append.replace('(P2 x ν)','(AdalyFormal.D1Literal.P2 x ν)')
append=append.replace('periodicPlaquetteHolonomy P1','periodicPlaquetteHolonomy AdalyFormal.D1Literal.P1')
append=append.replace('periodicPlaquetteHolonomy P2','periodicPlaquetteHolonomy AdalyFormal.D1Literal.P2')
local=ROOT/'AHP/round14/pathchoice/r2/LongCrossing.lean'
shared=ROOT/'AHP/round14/shared/pathchoice/R2_LongCrossing.lean'
local.parent.mkdir(parents=True,exist_ok=True); shared.parent.mkdir(parents=True,exist_ok=True)
local.write_text(base+path+append); shared.write_text(base+path+append)
print(local); print(shared); print('lines',len((base+path+append).splitlines()))
