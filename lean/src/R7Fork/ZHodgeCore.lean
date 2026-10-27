import R7Fork.ZXR3E
import R7Fork.R2Flat1
import R7Fork.AdalyFormal.Balaban.Weitzenbock
import AdalyFormal.Balaban.U1AnchorPoincare

/-!
# HodgeCore -- flat-background discrete Hodge facts on the periodic torus (genuine-U=1 sub-lane)

Reuses (LAW-19): `Weitzenbock.weitzenbock_flat`, `U1AnchorPoincare.eq_of_shiftInvariant`,
`R3E.curl_gradL2_flat`, `R2Ops1.gradAdj_apply`, `DeltaKFull.curlCovariantCLM_L2_toLp`.
-/
set_option autoImplicit false
namespace AdalyFormal.GenuineU1H

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.IngredientFamilyR2 (SiteL2 gradL2 gradAdj flatCfg gradL2_apply gradAdj_apply)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2 curlCovariantCLM_L2_toLp)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU gradCovariantAdjointValue)

variable {L : PeriodicLatticeExtent}

/-- the flat background, with the matrix-group type spelled out -/
abbrev flatU (L : PeriodicLatticeExtent) :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L := flatCfg

theorem flatU_eq_trivialU : flatU L = trivialU L := rfl

/-- the constant-per-direction bond field `b ↦ c b.2` -/
def constBond (L : PeriodicLatticeExtent) (c : Fin 3 → SuTwo) : BondFnL2 L :=
  WithLp.toLp 2 (fun b : Bond L => c b.2)

theorem constBond_apply (c : Fin 3 → SuTwo) (b : Bond L) : constBond L c b = c b.2 := rfl

/-- the constant site field -/
def constSite (L : PeriodicLatticeExtent) (X : SuTwo) : SiteL2 L :=
  WithLp.toLp 2 (fun _ => X)

theorem gradL2_flat_apply (φ : SiteL2 L) (b : Bond L) :
    gradL2 (flatU L) φ b = φ (periodicLatticeShift b.1 b.2) - φ b.1 := by
  have h := congrArg (fun f => f b) (gradL2_apply (flatU L) φ)
  simp only at h
  rw [show (gradL2 (flatU L) φ) b = ((gradL2 (flatU L)) φ).ofLp b from rfl, h]
  simp [gradValueCovariant, flatU, flatCfg, RMap_one]

/-- K3: a site field with vanishing flat gradient is constant. -/
theorem K3 (φ : SiteL2 L) (h : gradL2 (flatU L) φ = 0) : ∃ X : SuTwo, ∀ x, φ x = X := by
  have hs : ∀ (x : PeriodicLatticeSite L) (μ : Fin 3), φ (periodicLatticeShift x μ) = φ x := by
    intro x μ
    have h1 := congrArg (fun A : BondFnL2 L => A (x, μ)) h
    simp only [gradL2_flat_apply] at h1
    exact sub_eq_zero.mp (by simpa using h1)
  exact ⟨φ (fun _ => 0), fun x =>
    AdalyFormal.Balaban.U1AnchorPoincare.eq_of_shiftInvariant (fun x => φ x) hs x _⟩

theorem gradL2_flat_constSite (X : SuTwo) : gradL2 (flatU L) (constSite L X) = 0 := by
  ext b
  rw [gradL2_flat_apply]
  simp [constSite]

theorem curl_flat_constBond (c : Fin 3 → SuTwo) :
    curlCovariantCLM_L2 (flatU L) (constBond L c) = 0 := by
  unfold constBond
  rw [curlCovariantCLM_L2_toLp]
  have : curlValueCovariant (flatU L) (fun b : Bond L => c b.2) = 0 := by
    funext p
    simp [curlValueCovariant, flatU, flatCfg, RMap_one]
  rw [this]; rfl

theorem gradAdj_flat_constBond (c : Fin 3 → SuTwo) :
    gradAdj (flatU L) (constBond L c) = 0 := by
  ext x
  have h := congrArg (fun f => f x) (gradAdj_apply (flatU L) (constBond L c))
  simp only at h
  rw [show (gradAdj (flatU L) (constBond L c)) x = ((gradAdj (flatU L)) (constBond L c)).ofLp x from rfl, h]
  simp [gradCovariantAdjointValue, constBond, flatU, flatCfg, RMap_one]

/-- K1: flat-harmonic bond fields (curl-free and divergence-free) are constant per direction. -/
theorem K1 (y : BondFnL2 L) (hc : curlCovariantCLM_L2 (flatU L) y = 0)
    (hd : gradAdj (flatU L) y = 0) : ∃ c : Fin 3 → SuTwo, ∀ b : Bond L, y b = c b.2 := by
  set A : Bond L → SuTwo := y.ofLp with hAdef
  have hcurl : ∀ p, curlValueCovariant (trivialU L) A p = 0 := by
    intro p
    have hy : y = WithLp.toLp 2 A := rfl
    rw [hy, curlCovariantCLM_L2_toLp] at hc
    have := congrArg (fun F => F.ofLp p) hc
    exact this
  have hdiv : ∀ x, gradCovariantAdjointValue (trivialU L) A x = 0 := by
    intro x
    have := congrArg (fun F => F.ofLp x) hd
    simp only [gradAdj_apply] at this
    exact this
  have hW := AdalyFormal.Balaban.Weitzenbock.weitzenbock_flat A
  have hP : AdalyFormal.Balaban.RegularUPerturbation.plaqEnergy
      (curlCovariantLM (trivialU L) A) = 0 := by
    unfold AdalyFormal.Balaban.RegularUPerturbation.plaqEnergy
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [show curlCovariantLM (trivialU L) A p = curlValueCovariant (trivialU L) A p from rfl,
      hcurl p, norm_zero]
    simp
  rw [hP, AdalyFormal.Balaban.Weitzenbock.divEnergy_eq_zero_of_div_free _ A hdiv, add_zero] at hW
  have hG := hW.symm
  unfold AdalyFormal.Balaban.Weitzenbock.gradEnergy at hG
  have hz : ∀ (x : PeriodicLatticeSite L) (μ ν : Fin 3),
      A (periodicLatticeShift x μ, ν) = A (x, ν) := by
    intro x μ ν
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => by positivity)).mp hG x
      (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun μ _ => by positivity)).mp h1 μ
      (Finset.mem_univ _)
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun ν _ => by positivity)).mp h2 ν
      (Finset.mem_univ _)
    have h4 : AdalyFormal.Balaban.Weitzenbock.dfwd A μ ν x = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3
      exact norm_eq_zero.mp this
    unfold AdalyFormal.Balaban.Weitzenbock.dfwd at h4
    exact sub_eq_zero.mp h4
  refine ⟨fun ν => A ((fun _ => 0), ν), fun b => ?_⟩
  exact AdalyFormal.Balaban.U1AnchorPoincare.eq_of_shiftInvariant (fun x => A (x, b.2))
    (fun x μ => hz x μ b.2) b.1 _

/-- K2: discrete Hodge decomposition of flat-curl-free bond fields. -/
theorem K2 (A : BondFnL2 L) (h : curlCovariantCLM_L2 (flatU L) A = 0) :
    ∃ (φ : SiteL2 L) (c : Fin 3 → SuTwo), A = gradL2 (flatU L) φ + constBond L c := by
  set K : Submodule ℝ (BondFnL2 L) := LinearMap.range (gradL2 (flatU L)).toLinearMap with hK
  have hmem : A ∈ K ⊔ Kᗮ := by
    rw [Submodule.sup_orthogonal_of_hasOrthogonalProjection]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨φ, rfl⟩ := LinearMap.mem_range.mp ha
  have horth : ∀ lam : SiteL2 L, ⟪gradL2 (flatU L) lam, b⟫ = 0 := fun lam =>
    (Submodule.mem_orthogonal K b).mp hb _ (LinearMap.mem_range_self _ lam)
  have hd : gradAdj (flatU L) b = 0 := by
    have h1 : ⟪gradAdj (flatU L) b, gradAdj (flatU L) b⟫ =
        ⟪b, gradL2 (flatU L) (gradAdj (flatU L) b)⟫ :=
      ContinuousLinearMap.adjoint_inner_left _ _ _
    have h2 := horth (gradAdj (flatU L) b)
    rw [real_inner_comm] at h2
    rw [h2] at h1
    exact inner_self_eq_zero.mp h1
  have hbeq : b = A - gradL2 (flatU L) φ := by rw [← hab]; simp
  have hc : curlCovariantCLM_L2 (flatU L) b = 0 := by
    rw [hbeq, map_sub, h, AdalyFormal.StatementLane3.curl_gradL2_flat, sub_zero]
  obtain ⟨c, hcb⟩ := K1 b hc hd
  refine ⟨φ, c, ?_⟩
  rw [← hab]
  congr 1
  have hbb : b = WithLp.toLp 2 b.ofLp := rfl
  rw [hbb]
  unfold constBond
  congr 1
  funext e
  exact hcb e

#print axioms K3
#print axioms K1
#print axioms K2
#print axioms gradL2_flat_constSite
#print axioms curl_flat_constBond
#print axioms gradAdj_flat_constBond

end AdalyFormal.GenuineU1H
