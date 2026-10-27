import DrEquiv
/-! Actual boundary dressing and gauge-fixing identities, for all carrier fields.
The results do not assert a crossing or response noncancellation. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.Round12.Noncancel.Boundary
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneR8
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Guarded
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 gradValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer
  (periodicLatticeShiftBack periodicLatticeShift_shiftBack gradCovariantAdjointValue)
variable {L : PeriodicLatticeExtent}

/-- The exact dressing potential is zero outside the first coarse region.
This includes the whole collar and does not require an inverse-unit premise. -/
theorem potential_zero_off_om1 {ell k : ℕ} (S : Tower L) (U : Cfg L)
    (a : ℝ) (f : SiteL2 L) {x : PeriodicLatticeSite L} (hx : x ∉ S.Om 1) :
    (Gp (geomOf ell k S) U a (Rproj (geomOf ell k S) U f)) x = 0 := by
  by_cases hx0 : x ∈ S.Om 0
  · apply Gp_Rproj_lam0
    exact ⟨fun μ => by simp, hx0, by simpa using hx⟩
  · exact Gp_Rproj_out _ _ _ _ hx0

/-- W agrees pointwise with the original field on every bond with both endpoints
outside Omega_1. This is not restricted to a single-bond test field. -/
theorem Wop_eq_on_collar {ell k : ℕ} (S : Tower L) (U : Cfg L) (a : ℝ)
    (A : BondFnL2 L) (e : Bond L)
    (h0 : e.1 ∉ S.Om 1) (h1 : periodicLatticeShift e.1 e.2 ∉ S.Om 1) :
    (Wop (geomOf ell k S) U a A) e = A e := by
  have hz : (gradL2 U (Gp (geomOf ell k S) U a
      (Rproj (geomOf ell k S) U (gradAdj U A)))) e = 0 := by
    rw [gradL2_apply]
    unfold gradValueCovariant
    rw [potential_zero_off_om1 S U a _ h0, potential_zero_off_om1 S U a _ h1]
    simp
  change A e - (gradL2 U (Gp (geomOf ell k S) U a
    (Rproj (geomOf ell k S) U (gradAdj U A)))) e = A e
  rw [hz, sub_zero]

/-- Every omitted plaquette is in the collar. Therefore its four dressed atoms
are exactly the four raw atoms, for an arbitrary fine field. -/
theorem Wop_eq_on_omitted {ell M R k : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) (h4 : 4 ≤ R*M) (U : Cfg L) (a : ℝ)
    (A : BondFnL2 L) {p : PeriodicLatticePlaquette L}
    (hp : p ∉ plaqIn (S.Om 0)) {e : Bond L} (he : e ∈ periodicPlaquetteBoundaryEdges p) :
    (Wop (geomOf ell k S) U a A) e = A e := by
  obtain ⟨h0,h1⟩ := edge_ends_not_om1_of_notIn hS h4 hp he
  exact Wop_eq_on_collar S U a A e h0 h1

/-- A single bond of arbitrary orientation has divergence supported at its endpoints. -/
theorem gradAdj_sing_support (U : Cfg L) (e : Bond L) (X : SuTwo)
    (z : PeriodicLatticeSite L) (hz0 : z ≠ e.1)
    (hz1 : z ≠ periodicLatticeShift e.1 e.2) :
    gradAdj U (sing e X) z = 0 := by
  rw [show gradAdj U (sing e X) z = (WithLp.ofLp (gradAdj U (sing e X))) z from rfl,
    gradAdj_apply]
  unfold gradCovariantAdjointValue
  refine Finset.sum_eq_zero (fun μ _ => ?_)
  have h0 : (WithLp.ofLp (sing e X)) (z,μ) = 0 :=
    sing_apply_ne _ _ (fun h => hz0 (congrArg Prod.fst h))
  have h1 : (WithLp.ofLp (sing e X)) (periodicLatticeShiftBack z μ,μ) = 0 := by
    apply sing_apply_ne
    intro h
    have hμ : μ = e.2 := congrArg Prod.snd h
    have hx : periodicLatticeShiftBack z μ = e.1 := congrArg Prod.fst h
    apply hz1
    rw [← hx, ← hμ, periodicLatticeShift_shiftBack]
  rw [h0,h1]
  simp

/-- On a finite-radius boundary patch, a raw single-bond field has zero gauge term.
The same exterior witness can be used for any orientation, including tangential leaves. -/
theorem Tfull_sing_zero_near {ell M R k d : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) (hd : d+1 ≤ R*M)
    (U : Cfg L) (e : Bond L) (X : SuTwo)
    (x : PeriodicLatticeSite L) (hx : x ∉ S.Om 0)
    (h0 : pdist x e.1 ≤ d) (h1 : pdist x (periodicLatticeShift e.1 e.2) ≤ d) :
    Tfull (geomOf ell k S) U (sing e X) = 0 := by
  unfold Tfull
  simp only [ContinuousLinearMap.comp_apply]
  unfold Rproj
  rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.mem_orthogonal]
  intro u hu
  rw [PiLp.inner_apply]
  refine Finset.sum_eq_zero (fun z _ => ?_)
  by_cases hz : z = e.1 ∨ z = periodicLatticeShift e.1 e.2
  · have huz : u z = 0 := by
      apply RImage_support S U hu z
      intro y hy hy1
      have hcl := hS.2.2.2.2.1 0 (Nat.zero_le _) x hx y hy1
      have hxz : pdist x z ≤ d := by
        rcases hz with rfl | rfl
        · exact h0
        · exact h1
      have hyz : pdist z y ≤ 1 := hy
      have ht := pdist_triangle x z y
      have hb : bigSide M ell 0 = M := by simp [bigSide]
      rw [hb] at hcl
      omega
    rw [huz]
    simp
  · push Not at hz
    rw [gradAdj_sing_support U e X z hz.1 hz.2]
    simp

theorem Wop_sing_near {ell M R k d : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) (hd : d+1 ≤ R*M)
    (U : Cfg L) (a : ℝ) (e : Bond L) (X : SuTwo)
    (x : PeriodicLatticeSite L) (hx : x ∉ S.Om 0)
    (h0 : pdist x e.1 ≤ d) (h1 : pdist x (periodicLatticeShift e.1 e.2) ≤ d) :
    Wop (geomOf ell k S) U a (sing e X) = sing e X := by
  have ht := Tfull_sing_zero_near hS hd U e X x hx h0 h1
  unfold Tfull at ht
  simp only [ContinuousLinearMap.comp_apply] at ht
  unfold Wop
  simp only [sub_apply, one_apply_eq_self,
    ContinuousLinearMap.comp_apply]
  rw [ht]
  simp

#print axioms potential_zero_off_om1
#print axioms Wop_eq_on_collar
#print axioms Wop_eq_on_omitted
#print axioms gradAdj_sing_support
#print axioms Tfull_sing_zero_near
#print axioms Wop_sing_near
end AdalyFormal.Round12.Noncancel.Boundary
