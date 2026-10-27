import DrEquiv
/-! Actual arbitrary-field locality of the dressing on a level-zero collar. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.Round12.Kernel.Boundary
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLaneR8
open AdalyFormal.D1Literal
open AdalyFormal.SliceCoerc
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 gradValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer
  (periodicLatticeShiftBack periodicLatticeShift_shiftBack periodicLatticeShiftBack_shift)
variable {L : PeriodicLatticeExtent}

-- Copied verbatim from frozen CvN2.NQp_vanish, in this namespace.
theorem NQp_vanish {ell : ℕ} {S : Tower L} {U : Cfg L} {f : SiteL2 L} (hf : f ∈ NQp (geomOf ell 1 S) U)
    (x : PeriodicLatticeSite L) (hx : x ∉ S.Om 1) : f x = 0 := by
  by_cases h0 : x ∈ S.Om 0
  · have := hf.2 0 (Nat.zero_le _) x ⟨fun μ => by simp, h0, hx⟩
    rw [Qlev_apply] at this
    exact this
  · exact hf.1 x h0

/-- The actual gauge potential used by W vanishes at every collar site. -/
theorem gaugePotential_off {ell : ℕ} {S : Tower L} (U : Cfg L) (a : ℝ)
    (hu : IsUnit (DelpA (geomOf ell 1 S) U a + (1 - siteMask (S.Om 0))))
    (u : BondFnL2 L) (x : PeriodicLatticeSite L) (hx : x ∉ S.Om 1) :
    Gp (geomOf ell 1 S) U a (Tfull (geomOf ell 1 S) U u) x = 0 := by
  exact NQp_vanish (Gp_Rproj_mem (geomOf ell 1 S) U a hu (gradAdj U u)).1 x hx

/-- W fixes the value of EVERY field on EVERY bond with both endpoints off Omega1.
This is not the weaker assertion that W fixes a specially supported trial. -/
theorem Wop_apply_off {ell : ℕ} {S : Tower L} (U : Cfg L) (a : ℝ)
    (hu : IsUnit (DelpA (geomOf ell 1 S) U a + (1 - siteMask (S.Om 0))))
    (u : BondFnL2 L) (b : Bond L)
    (h0 : b.1 ∉ S.Om 1) (h1 : periodicLatticeShift b.1 b.2 ∉ S.Om 1) :
    Wop (geomOf ell 1 S) U a u b = u b := by
  change (u - gradL2 U (Gp (geomOf ell 1 S) U a
    (Tfull (geomOf ell 1 S) U u))) b = u b
  rw [PiLp.sub_apply, gradL2_apply]
  unfold gradValueCovariant
  rw [gaugePotential_off U a hu u _ h0, gaugePotential_off U a hu u _ h1]
  simp

/-- Admissibility makes every site within RM of an exterior point a collar site. -/
theorem off_one_of_close {ell M R : ℕ} {S : Tower L}
    (hS : Admissible ell M R 1 S) {x z : PeriodicLatticeSite L}
    (hx : x ∉ S.Om 0) (hz : pdist x z ≤ R * M) : z ∉ S.Om 1 := by
  intro hm
  have h := hS.2.2.2.2.1 0 (Nat.zero_le _) x hx z hm
  have hb : bigSide M ell 0 = M := by simp [bigSide]
  rw [hb] at h
  omega

/-- Exact arbitrary-field boundary-patch dictionary, with only geometric distance bounds. -/
theorem Wop_apply_close {ell M R : ℕ} {S : Tower L}
    (hS : Admissible ell M R 1 S) (U : Cfg L) (a : ℝ)
    (hu : IsUnit (DelpA (geomOf ell 1 S) U a + (1 - siteMask (S.Om 0))))
    {x : PeriodicLatticeSite L} (hx : x ∉ S.Om 0)
    (u : BondFnL2 L) (b : Bond L)
    (h0 : pdist x b.1 ≤ R * M)
    (h1 : pdist x (periodicLatticeShift b.1 b.2) ≤ R * M) :
    Wop (geomOf ell 1 S) U a u b = u b :=
  Wop_apply_off U a hu u b (off_one_of_close hS hx h0) (off_one_of_close hS hx h1)

/-- In particular the normal charged trace used by KernelLine is untouched by W. -/
theorem Wop_apply_boundary {ell M R : ℕ} {S : Tower L}
    (hS : Admissible ell M R 1 S) (hRM : 1 ≤ R * M)
    {x : PeriodicLatticeSite L} (hbd : BdPt (S.Om 0) x)
    (U : Cfg L) (a : ℝ)
    (hu : IsUnit (DelpA (geomOf ell 1 S) U a + (1 - siteMask (S.Om 0))))
    (u : BondFnL2 L) : Wop (geomOf ell 1 S) U a u (x,0) = u (x,0) := by
  apply Wop_apply_close hS U a hu hbd.hx' u (x,0)
  · have h : pdist (periodicLatticeShift x 0) x ≤ 1 := by
      rw [pdist_comm]; exact pdist_shift_le x 0
    exact h.trans hRM
  · rw [AdalyFormal.StatementLaneR8.pdist_self]; omega

#print axioms NQp_vanish
#print axioms gaugePotential_off
#print axioms Wop_apply_off
#print axioms off_one_of_close
#print axioms Wop_apply_close
#print axioms Wop_apply_boundary
end AdalyFormal.Round12.Kernel.Boundary
