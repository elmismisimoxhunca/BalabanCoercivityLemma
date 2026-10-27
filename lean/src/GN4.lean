import GN3
import SL3

/-!
# GN4 -- conditional `Ginv` coercivity for the genuine base data at `Ω₀ = univ` (the B1 route)

`ginv_coercive_cond`: for the genuine `baseData G U a S Jf` (any `U`, any bond sector `S`, any `Jf`), with
`Ω₀ = univ`, if
* `hu`     : the Dirichlet site operator is invertible (site coercivity; SiteC `unit_of_site_coercive`),
* `hB0`    : `Q(U) D_U ν = 0` for `ν ∈ N(Q'_U)` (B0, print (3.115); NOT proved here),
* `hPoinc` : Poincare on `N(Q'_U)`: `‖ν‖ ≤ P ‖D_U ν‖` (SiteC `poincare_NQp_proper`, R2 carrier),
* `hslice` : slice coercivity `cs‖x‖² ≤ ⟪x,Δ x⟫ + ⟪x,Q*aQ x⟫` on `ker(R_U D_U*)`,
then `‖x‖² ≤ max(2/cs, 2P²) ⟪x, Ginv x⟫` for every `x ∈ E₀`.
In the scaled use `cs = c_s n⁻²`, `P = C_P n`: `‖x‖² ≤ n² max(2/c_s, 2C_P²) ⟪x,Ginv x⟫`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.SliceCoerc

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)

variable {L : PeriodicLatticeExtent}

theorem ginv_form_eq (G : TowerGeom L) (U : Cfg L) (a : ℝ) (S : BondSector G) (Jf : BondFnL2 L)
    (x : ↥(bondSupp G)) :
    ⟪x, (baseData G U a S Jf).Ginv x⟫
      = ⟪iE G x, DpiFull G U a (iE G x)⟫ + ‖Tfull G U (iE G x)‖ ^ 2
        + ⟪iE G x, MassFull G a S (iE G x)⟫ := by
  rw [BaseDataS.inner_Ginv]
  simp only [baseData, ContinuousLinearMap.comp_apply, pE_inner_right]

theorem ginv_coercive_cond (G : TowerGeom L) (hOm : G.Om0 = Set.univ) (U : Cfg L) (a : ℝ)
    (S : BondSector G) (Jf : BondFnL2 L)
    (hu : IsUnit (DelpA G U a + (1 - siteMask G.Om0)))
    (hB0 : ∀ ν ∈ NQp G U, S.Qfull (gradL2 U ν) = 0)
    (P : ℝ) (hP : 0 ≤ P) (hPoinc : ∀ ν ∈ NQp G U, ‖ν‖ ≤ P * ‖gradL2 U ν‖)
    (cs : ℝ) (hcs : 0 < cs)
    (hslice : ∀ x : BondFnL2 L, Rproj G U (gradAdj U x) = 0 →
      cs * ‖x‖ ^ 2 ≤ ⟪x, Delta G U x⟫ + ⟪x, MassFull G a S x⟫)
    (x : ↥(bondSupp G)) :
    ‖x‖ ^ 2 ≤ max (2 / cs) (2 * P ^ 2) * ⟪x, (baseData G U a S Jf).Ginv x⟫ := by
  set A : BondFnL2 L := iE G x with hA
  set A' := Wop G U a A with hA'
  have hnx : ‖x‖ = ‖A‖ := rfl
  have hB1 := B1_form G U a S hu hB0 A
  have hsl := hslice A' (slice_of_Wop G hOm U a hu A)
  have hgp := gauge_part_le G hOm U a hu P hP hPoinc A
  have htri : ‖A‖ ^ 2 ≤ 2 * ‖A'‖ ^ 2 + 2 * ‖A - A'‖ ^ 2 := by
    have hdec : A = A' + (A - A') := by abel
    have h1 : ‖A‖ ≤ ‖A'‖ + ‖A - A'‖ := by
      calc ‖A‖ = ‖A' + (A - A')‖ := by rw [← hdec]
        _ ≤ ‖A'‖ + ‖A - A'‖ := norm_add_le _ _
    nlinarith [norm_nonneg A, norm_nonneg A', norm_nonneg (A - A'), sq_nonneg (‖A'‖ - ‖A - A'‖)]
  have hpo : ‖A - A'‖ ^ 2 ≤ P ^ 2 * ‖Tfull G U A‖ ^ 2 := by
    have h0 := norm_nonneg (A - A')
    have := mul_le_mul hgp hgp h0 (mul_nonneg hP (norm_nonneg _))
    nlinarith
  rw [hnx, ginv_form_eq, ← hA, hB1]
  exact ginv_of_slice cs (P ^ 2) (‖A‖ ^ 2) (‖A'‖ ^ 2) (‖A - A'‖ ^ 2)
    (⟪A', Delta G U A'⟫ + ⟪A', MassFull G a S A'⟫) (‖Tfull G U A‖ ^ 2) _ hcs
    (sq_nonneg _) (sq_nonneg _) htri (by ring) hsl hpo

#print axioms ginv_form_eq
#print axioms ginv_coercive_cond

end AdalyFormal.SliceCoerc
