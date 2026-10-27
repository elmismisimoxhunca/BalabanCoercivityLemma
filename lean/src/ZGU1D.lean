import ZGU1C

/-!
# GU1D -- the algebraic reduction of the genuine first term of (3.156) at ANY level `k`,
flat `U`, full support:  `genForm B = η ( ‖curl A*‖² + ‖R D* A*‖² )` where `A* = G₁ Q* (QG₁Q*)⁻¹ τ*B`
is the explicit minimiser-candidate with `Q A* = τ*B`.  The `η`-power and the mass weight `ell^k` cancel
(this is exactly where a wrong `η`-power or a wrong mass weight would break).
Standard axioms only (see the #print axioms lines).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000
namespace AdalyFormal.GenuineU1

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)

namespace Gen
variable (P : IngrBParams)

/-- generic: for unit `G₁⁻¹` and unit `N`, the explicit candidate `A* = G₁ Q* N⁻¹ y` solves `Q A* = y`
and `⟨y, N⁻¹ y⟩ = ⟨A*, G₁⁻¹ A*⟩`. -/
theorem firstTerm_core (hG : IsUnit P.G1inv) (hN : IsUnit (GenP.Nmat P)) (y : FSp P.G) :
    ∃ A : ↥(bondSupp P.G), P.data.Q A = y ∧
      ⟪y, Ring.inverse (GenP.Nmat P) y⟫ = ⟪A, P.G1inv A⟫ := by
  set z := Ring.inverse (GenP.Nmat P) y with hz
  have hNz : GenP.Nmat P z = y := by
    have := Ring.mul_inverse_cancel _ hN
    exact ContinuousLinearMap.ext_iff.mp this y
  set A : ↥(bondSupp P.G) := P.data.G1 P.G1inv (P.data.Qs z) with hA
  have hG1 : P.G1inv A = P.data.Qs z := by
    have := Ring.mul_inverse_cancel _ hG
    exact ContinuousLinearMap.ext_iff.mp this (P.data.Qs z)
  have hQA : P.data.Q A = y := by
    rw [← hNz]; rfl
  refine ⟨A, hQA, ?_⟩
  rw [hG1, ← P.data.Q_adj, hQA]



/-- full support: every index of `𝔅` has level `k` -/
theorem level_eq (hFS : P.FullSupp) (p : BIdx P.G) : (p.1 : ℕ) = P.k := by
  obtain ⟨⟨j, hj⟩, ⟨b, hb⟩⟩ := p
  have hjk : j ≤ P.k := Nat.lt_succ_iff.mp hj
  by_cases hlt : j < P.k
  · exact absurd hb (by rw [hFS.1 j hlt]; exact Set.notMem_empty b)
  · exact le_antisymm hjk (not_lt.mp hlt)

theorem tau_adj_apply (hFS : P.FullSupp) (B : BondFnL2 P.Lu) (e : Bond P.Lu) :
    (WithLp.ofLp (ContinuousLinearMap.adjoint P.tau B)) (P.eqv hFS e) = B e := by
  have hb := P.tau_bijective hFS
  obtain ⟨g, rfl⟩ := hb.2 B
  have h1 : ContinuousLinearMap.adjoint P.tau (P.tau g) = g := by
    refine ext_inner_left ℝ (fun h => ?_)
    rw [ContinuousLinearMap.adjoint_inner_right]
    simp only [PiLp.inner_apply]
    refine (Fintype.sum_equiv (P.eqv hFS) _ _ (fun e => ?_))
    rw [IngrBParams.tau_apply P hFS, IngrBParams.tau_apply P hFS]
  rw [h1, IngrBParams.tau_apply P hFS]

theorem tau_adj_norm (hFS : P.FullSupp) (B : BondFnL2 P.Lu) :
    ‖ContinuousLinearMap.adjoint P.tau B‖ = ‖B‖ := by
  have hb := P.tau_bijective hFS
  obtain ⟨g, rfl⟩ := hb.2 B
  have h1 : ContinuousLinearMap.adjoint P.tau (P.tau g) = g := by
    refine ext_inner_left ℝ (fun h => ?_)
    rw [ContinuousLinearMap.adjoint_inner_right]
    simp only [PiLp.inner_apply]
    refine (Fintype.sum_equiv (P.eqv hFS) _ _ (fun e => ?_))
    rw [IngrBParams.tau_apply P hFS, IngrBParams.tau_apply P hFS]
  rw [h1]
  have h2 : ‖P.tau g‖ ^ 2 = ‖g‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    exact Fintype.sum_equiv (P.eqv hFS) (fun e => ‖(WithLp.ofLp (P.tau g)) e‖ ^ 2)
      (fun p => ‖(WithLp.ofLp g) p‖ ^ 2) (fun e => by rw [IngrBParams.tau_apply P hFS])
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2.symm

/-- the mass term at full support: `⟨A, Mass A⟩ = a · ell^k · ‖Q A‖²` -/
theorem mass_inner (hFS : P.FullSupp) (A : ↥(bondSupp P.G)) :
    ⟪A, P.data.Mass A⟫ = P.a * (P.ell : ℝ) ^ P.k * ‖P.data.Q A‖ ^ 2 := by
  have h1 : ⟪A, P.data.Mass A⟫ = ⟪iE P.G A, MassFull P.G P.a P.sector (iE P.G A)⟫ := by
    show ⟪A, (pE P.G) ((MassFull P.G P.a P.sector) ((iE P.G) A))⟫ = _
    rw [pE_inner_right]
  rw [h1, inner_MassFull, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have hp : (p.1 : ℕ) = P.k := level_eq P hFS p
  show P.a * (P.G.ell : ℝ) ^ (p.1 : ℕ) * ‖P.sector.Qfull (iE P.G A) p‖ ^ 2 = _
  rw [hp]
  rfl

end Gen

#print axioms Gen.firstTerm_core
#print axioms Gen.level_eq
#print axioms Gen.tau_adj_apply
#print axioms Gen.tau_adj_norm
#print axioms Gen.mass_inner

end AdalyFormal.GenuineU1
