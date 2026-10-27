import WC7d

/-!
# WC7e -- **`qs_injective_charts`**: `Q_U*` injective from per-row charts (M2 W6 lane)
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace AdalyFormal.M2W6

open Finset
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.NonflatJet
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible scaleUp pdist)
open AdalyFormal.StatementLaneR8
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.BondComposite
open SmallnessBridge.Assemble (loopFactorBound)
open AdalyFormal.W6
open AdalyFormal.TowerLoc
open AdalyFormal.GaugeCov (adBL adFL adGen_symm_apply)

section fin
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

/-- `S = T - I - N` -/
def Slin (hell : 0 < ell) (U : LinkCfg (scaleUp ell k Lu)) (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu)) :
    FSp (geomOf ell k S) →ₗ[ℝ] FSp (geomOf ell k S) :=
  Tlin hell U γ - LinearMap.id - Nlin hell γ

theorem Slin_apply (hell : 0 < ell) (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 1 ≤ M) (hR : 8 * ell ≤ R)
    (U : LinkCfg (scaleUp ell k Lu)) (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu))
    (y : FSp (geomOf ell k S)) : Slin hell U γ y = Sfun hell U γ y := by
  show Tlin hell U γ y - y - Nlin hell γ y = _
  rw [Tlin_row hell hell2 hS hM hR U γ y]
  abel

theorem T_split (hell : 0 < ell) (U : LinkCfg (scaleUp ell k Lu))
    (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu)) (y : FSp (geomOf ell k S)) :
    Tlin hell U γ y = y + Nlin hell γ y + Slin hell U γ y := by
  show Tlin hell U γ y = y + Nlin hell γ y + (Tlin hell U γ y - y - Nlin hell γ y)
  abel

theorem symm_mem (γ : GaugeFn (scaleUp ell k Lu)) (f : BondFnL2 (scaleUp ell k Lu))
    (hf : f ∈ bondSupp (geomOf ell k S)) : (adBL γ).symm f ∈ bondSupp (geomOf ell k S) := by
  intro b hb
  have h := hf b hb
  show ((adBL γ).symm f).ofLp b = 0
  rw [show ((adBL γ).symm f).ofLp b = RMap (((γ b.1))⁻¹) (f.ofLp b) from
    adGen_symm_apply (fun b : Bond (scaleUp ell k Lu) => γ b.1) f b, h, map_zero]

theorem EU_mem (hell : 0 < ell) (hS : Admissible ell M R k S)
    (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu)) (y : FSp (geomOf ell k S)) :
    EU hell γ y ∈ bondSupp (geomOf ell k S) := by
  rw [EU_apply]
  refine Submodule.sum_mem _ (fun p _ => ?_)
  exact symm_mem (γ p) _ (EflatL_mem hell hS _)

variable (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 0 < M) (hR : 8 * ell ≤ R) (hroom : 17 * ell ≤ R * M)
  (U : LinkCfg (scaleUp ell k Lu)) (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu)) (ε : ℕ → ℕ → ℝ)
  (hch : ChartHyp ell k Lu S U γ ε)
  (hε0 : ∀ j' l, l < k → 0 ≤ ε j' l) (hsm : ∀ j' l, l < k → rhoOf ell (ε j' l) < Real.pi / 2)
  (hr : ∀ j' l, l < k → Real.pi / 2 * ((loopFactorBound ell : ℝ) * ε j' l) < r0)
  (Sstar : ℝ) (hSstar : ∀ j' : ℕ, j' ≤ k → ∑ l ∈ range j', thetaOf ell (ε j' l) ≤ Sstar)

include hell2 hS hM hR hroom hch hε0 hsm hr hSstar in
/-- **`Q_U*` is injective from per-row charts** (no global gauge, no global regularity). -/
theorem qs_injective_charts (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (hsmall : 2 * CsrcS ell Sstar * (1 + CsrcA ell Sstar) < 1) :
    Function.Injective (gparams ell k Lu (by omega : 0 < ell) S U a Lam).data.Qs := by
  have hell : 0 < ell := by omega
  have hM1 : 1 ≤ M := hM
  have hSnn : 0 ≤ CsrcS ell Sstar := by unfold CsrcS mult0 CE; positivity
  have hTnn : 0 ≤ CsrcT ell Sstar := by unfold CsrcT mult0 CE; positivity
  have hAnn : 0 ≤ CsrcA ell Sstar := by unfold CsrcA; linarith
  have hSb : ∀ y, nF (Slin hell U γ y) ≤ CsrcS ell Sstar * nF y := fun y => by
    rw [Slin_apply hell hell2 hS hM1 hR U γ y]
    exact nF_Sfun hell2 hS hM hroom U γ ε hch hε0 hsm hr Sstar hSstar y
  have hNb : ∀ y, nF (Nlin hell γ y) ≤ CsrcA ell Sstar * nF y := fun y => by
    have e : Nlin hell γ y = Tlin hell U γ y + -y + -(Sfun hell U γ y) := by
      have := Tlin_row hell hell2 hS hM1 hR U γ y
      rw [this]; abel
    rw [e]
    have h1 := nF_add_le hell (Tlin hell U γ y + -y) (-(Sfun hell U γ y))
    have h2 := nF_add_le hell (Tlin hell U γ y) (-y)
    rw [nF_neg] at h1 h2
    have h3 := nF_Tlin hell2 hS hM hroom U γ ε hch hε0 hsm hr Sstar hSstar y
    have h4 := nF_Sfun hell2 hS hM hroom U γ ε hch hε0 hsm hr Sstar hSstar y
    unfold CsrcA
    linarith [nF_nonneg hell y]
  have hTinj : Function.Injective (Tlin hell U γ) :=
    inj_of_perturbed (fun y : FSp (geomOf ell k S) => nF y) (fun y => nF_nonneg hell y) (nF_add_le hell) nF_neg
      (fun y hy => eq_zero_of_nF hell y hy) (Nlin hell γ) (Slin hell U γ) (Tlin hell U γ)
      (fun y => T_split hell U γ y)
      (fun y => Nlin_Nlin hell hell2 hS hM1 hR γ y)
      (CsrcA ell Sstar) (CsrcS ell Sstar) hNb hSb hSnn hAnn hsmall
  have hTsurj : Function.Surjective (Tlin hell U γ) := LinearMap.injective_iff_surjective.mp hTinj
  set A : ↥(bondSupp (geomOf ell k S)) →L[ℝ] FSp (geomOf ell k S) :=
    ((bondSectorOf (geomOf ell k S) U).Qfull).comp (iE (geomOf ell k S)) with hA
  set E2 : FSp (geomOf ell k S) →ₗ[ℝ] ↥(bondSupp (geomOf ell k S)) :=
    LinearMap.codRestrict (bondSupp (geomOf ell k S)) (EU hell γ) (fun y => EU_mem hell hS γ y) with hE2
  have hAE : ∀ y, A (E2 y) = Tlin hell U γ y := fun y => rfl
  show Function.Injective (ContinuousLinearMap.adjoint A)
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨y, hy⟩ := hTsurj z
  have h1 : ⟪z, z⟫ = 0 := by
    calc ⟪z, z⟫ = ⟪A (E2 y), z⟫ := by rw [hAE y, hy]
      _ = ⟪E2 y, ContinuousLinearMap.adjoint A z⟫ := by rw [ContinuousLinearMap.adjoint_inner_right]
      _ = 0 := by rw [hz, inner_zero_right]
  exact inner_self_eq_zero.mp h1

end fin

end AdalyFormal.M2W6

#print axioms AdalyFormal.M2W6.qs_injective_charts
