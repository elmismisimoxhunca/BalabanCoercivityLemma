import ZR2Ops2
import GN2
import SectBNonflat

/-!
# SC1 -- bridge: the genuine R2 site operator `DelpA` at a ONE-LEVEL tower (block side `n`, `k = 1`, `Ω₀ = univ`)
equals `n⁻²` times the Family-1 operator `covDeltaPrime` (weight `a` in place of `topWeight k`).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
namespace AdalyFormal.SiteCoercivity

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)
open HConstruction.GenK (fineExtent)

variable (M : PeriodicLatticeExtent) {n : ℕ}

/-- one-level tower geometry: block side `n`, depth `k = 1`, full Dirichlet region, `Λ₁` = the coarse lattice. -/
noncomputable def oneLevelGeom (M : PeriodicLatticeExtent) (n : ℕ) : TowerGeom (fineExtent M n) where
  ell := n
  k := 1
  Om0 := Set.univ
  Lam := fun j => if j = 1 then ((CoarseLattice (fineExtent M n) n : Finset _) : Set _) else ∅

theorem DelpA_univ {L : PeriodicLatticeExtent} (G : TowerGeom L) (hOm : G.Om0 = Set.univ) (U : Cfg L) (a : ℝ)
    (f : SiteL2 L) : DelpA G U a f = lapFull U f + Qpa G U a f := by
  unfold DelpA
  simp only [ContinuousLinearMap.comp_apply, hOm, AdalyFormal.SliceCoerc.siteMask_univ,
    ContinuousLinearMap.add_apply]

theorem Qlev_oneLevel (U : Cfg (fineExtent M n)) (y : PeriodicLatticeSite (fineExtent M n)) (f : SiteL2 (fineExtent M n)) :
    Qlev (oneLevelGeom M n) U 1 y f
      = AdalyFormal.Balaban.CoarseRestrictTransported.coarseRestrictSiteCovariantU U n (fun x => f x) y := by
  rw [Qlev_apply]
  have h := AdalyFormal.Balaban.QjComposite.Qcomposite_one (bgTower (oneLevelGeom M n) U) n (WithLp.ofLp f)
  have e0 : bgTower (oneLevelGeom M n) U 0 = U := rfl
  rw [e0] at h
  have := congrFun h y
  exact this


open HConstruction.GenK (norm_sq_coordinates bondEnergy bondEnergy_norm)
open HConstruction.SectBP1 (Links covGrad covQPrime covDeltaPrime covDeltaPrime_form covDeltaPrime_floor)
open AdalyFormal.Balaban.DeltaKUnified (bfl2Equiv)

theorem norm_sq_gradL2 (U : Cfg (fineExtent M n)) (f : SiteL2 (fineExtent M n)) :
    ‖gradL2 U f‖ ^ 2 = ∑ b, ‖AdalyFormal.Balaban.CovariantOperators.gradValueCovariant U (WithLp.ofLp f) b‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

theorem norm_sq_covGrad (U : Links M (n := n)) (f : HConstruction.GenK.Site M (n := n)) :
    ‖covGrad M U f‖ ^ 2 = (n : ℝ) ^ 2 * ‖gradL2 U f‖ ^ 2 := by
  rw [← bondEnergy_norm, norm_sq_gradL2, Finset.mul_sum]
  unfold bondEnergy
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [HConstruction.SectBP1.covGrad_apply]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rfl


theorem norm_sq_covQPrime (U : Links M (n := n)) (f : HConstruction.GenK.Site M (n := n)) :
    ‖covQPrime M U f‖ ^ 2 = ∑ y ∈ CoarseLattice (fineExtent M n) n,
      ‖AdalyFormal.Balaban.CoarseRestrictTransported.coarseRestrictSiteCovariantU U n (fun x => f x) y‖ ^ 2 := by
  rw [norm_sq_coordinates]
  simp only [HConstruction.SectBP1.covQPrime_apply]
  exact (Finset.sum_subtype (CoarseLattice (fineExtent M n) n) (fun _ => Iff.rfl)
    (fun y => ‖AdalyFormal.Balaban.CoarseRestrictTransported.coarseRestrictSiteCovariantU U n (fun x => f x) y‖ ^ 2)).symm

theorem ajSeq_one (a : ℝ) (m : ℕ) : ajSeq a m 1 = a := by
  unfold ajSeq
  simp [AdalyFormal.Balaban.ConstantA.aSeq, AdalyFormal.Balaban.ConstantA.aSeqAux]

theorem oneLevelGeom_Lam0 : (oneLevelGeom M n).Lam 0 = ∅ := by
  simp [oneLevelGeom]

theorem oneLevelGeom_Lam1 : (oneLevelGeom M n).Lam 1 = ((CoarseLattice (fineExtent M n) n : Finset _) : Set _) := by
  simp [oneLevelGeom]

/-- THE BRIDGE: `n² ⟨f, Δ'_a(U) f⟩` of the genuine R2 operator equals the Family-1 form with weight `a`. -/
theorem n2_inner_DelpA (U : Cfg (fineExtent M n)) (a : ℝ) (f : SiteL2 (fineExtent M n)) :
    (n : ℝ) ^ 2 * ⟪f, DelpA (oneLevelGeom M n) U a f⟫
      = ‖covGrad M U f‖ ^ 2 + (a * (n : ℝ) ^ 3) * ‖covQPrime M U f‖ ^ 2 := by
  rw [DelpA_univ _ rfl, inner_add_right, inner_lapFull, inner_Qpa, norm_sq_covGrad, norm_sq_covQPrime]
  have hk : (oneLevelGeom M n).k = 1 := rfl
  have he : (oneLevelGeom M n).ell = n := rfl
  rw [hk, he]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, oneLevelGeom_Lam0, oneLevelGeom_Lam1,
    Set.mem_empty_iff_false, if_false, Finset.sum_const_zero, Finset.mem_coe, ajSeq_one]
  have hq : ∀ x : PeriodicLatticeSite (fineExtent M n),
      ‖Qlev (oneLevelGeom M n) U 1 x f‖ = ‖AdalyFormal.Balaban.CoarseRestrictTransported.coarseRestrictSiteCovariantU U n (fun x => f x) x‖ := by
    intro x; rw [Qlev_oneLevel]
  simp only [hq]
  rw [Finset.sum_ite_mem Finset.univ (CoarseLattice (fineExtent M n) n), Finset.univ_inter]
  simp only [← Finset.mul_sum]
  ring


open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond)

/-- THE EXPLICIT SITE COERCIVITY, genuine R2 object, one-level tower (block side `n`, any `n ≥ 1`, any torus `M`),
every background with `frobSupBond U ≤ α/n`, every `a > 0`:
`min(a,1)·(1/6 − 48α²)·‖f‖² ≤ n² ⟨f, Δ'_a(U) f⟩`. -/
theorem site_coercive_oneLevel (hn : 0 < n) (U : Cfg (fineExtent M n)) (α : ℝ)
    (hsmall : frobSupBond U ≤ α / (n : ℝ)) (a : ℝ) (ha : 0 < a) (f : SiteL2 (fineExtent M n)) :
    min a 1 * ((1 / 6 - 48 * α ^ 2) * ‖f‖ ^ 2) ≤ (n : ℝ) ^ 2 * ⟪f, DelpA (oneLevelGeom M n) U a f⟫ := by
  have h1 := covDeltaPrime_floor M hn U 1 α hsmall f
  rw [covDeltaPrime_form] at h1
  have htw : HConstruction.SectBBase.topWeight 1 = 1 := rfl
  rw [htw] at h1
  rw [n2_inner_DelpA]
  have hK : 0 ≤ ‖covGrad M U f‖ ^ 2 := sq_nonneg _
  have hQ : 0 ≤ (n : ℝ) ^ 3 * ‖covQPrime M U f‖ ^ 2 := by positivity
  have hm0 : 0 ≤ min a 1 := le_min ha.le zero_le_one
  have hma : min a 1 ≤ a := min_le_left _ _
  have hm1 : min a 1 ≤ 1 := min_le_right _ _
  have e1 : (1 * (n : ℝ) ^ 3) * ‖covQPrime M U f‖ ^ 2 = (n : ℝ) ^ 3 * ‖covQPrime M U f‖ ^ 2 := by ring
  rw [e1] at h1
  have h2 := mul_le_mul_of_nonneg_left h1 hm0
  nlinarith [mul_le_mul_of_nonneg_right hma hQ, mul_le_mul_of_nonneg_right hm1 hK]

end AdalyFormal.SiteCoercivity
