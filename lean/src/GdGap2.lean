import GdV
import GdAlg

/-!
# GdGap2 -- the guard gap `GapAt` on the whole boundary-twist family, in the regime where `Q*` is injective.

For `A ∈ ker Q` the field vanishes on the level-0 bonds (identity rows of `Q`), so `Ginv(θ) A = Ginv(0) A` (`GdV`).  `Ginv(0)` is positive semidefinite (D1Main),
hence `⟨A, Ginv(θ) A⟩ = 0` forces `Ginv(0) A = 0` and `Ginv(θ) A = 0`, so `A = 0` when `Ginv(θ)` is a unit.  Hence `Ginv(θ)` is positive definite on `ker Q`
whenever it is a unit, and the Schur step of `GdSchur` gives `Q G Q*` a unit.

* `Ginv_psd_flat`            : `Ginv(0)` is positive semidefinite, for any plaquette selectors.
* `Ginv_form_mono_flat`      : at the flat point, `⟨x, Ginv_loc x⟩ ≤ ⟨x, Ginv_lit x⟩`.
* `Q_level0_coord`, `adjoint_tau_level0` : level-0 rows of `Q` and of `τ*`.
* (`GapAt_twist`, the consequence for `GapAt` at every `θ` given `Q*` injective, is in GdGapAll.)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.D1Guarded

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.StatementLaneR8
open AdalyFormal.StatementLaneR6
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (PlaqFnL2)

section psd
variable {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) {S : Tower (scaleUp ell k Lu)} (a : ℝ)
  (Lam : Set (PeriodicLatticeSite Lu))

/-- `Ginv(0)` is positive semidefinite for ANY plaquette selectors. -/
theorem Ginv_psd_flat (sD sJ : PlaqSel) (ha : 0 ≤ a) :
    PSD (dataS sD sJ (Pth ell k Lu hell0 S a Lam 0)).Ginv := by
  intro (w : ↥(bondSupp (Pth ell k Lu hell0 S a Lam 0).G))
  show 0 ≤ ⟪w, (dataS sD sJ (Pth ell k Lu hell0 S a Lam 0)).Ginv w⟫
  rw [BaseDataS.inner_Ginv]
  have h1 : 0 ≤ ⟪w, (dataS sD sJ (Pth ell k Lu hell0 S a Lam 0)).Dpi w⟫ := by
    have e := E0_Dpi_inner sD (geomOf ell k S) (Uth (S.Om 0) 0) a w
    have : Uth (S.Om 0) 0 = AdalyFormal.Balaban.DeltaPrime.trivialU := by rw [Uth_zero]; rfl
    refine le_of_le_of_eq ?_ e.symm
    unfold DeltaS
    rw [this]
    exact deltaKLocCLM_flat_nonneg _ _
  have h2 : 0 ≤ ‖(dataS sD sJ (Pth ell k Lu hell0 S a Lam 0)).T w‖ ^ 2 := by positivity
  have h3 : 0 ≤ ⟪w, (dataS sD sJ (Pth ell k Lu hell0 S a Lam 0)).Mass w⟫ := by
    have e := E0_Mass_inner (geomOf ell k S) a (bondSectorOf (geomOf ell k S) (Uth (S.Om 0) 0)) w
    refine le_of_le_of_eq ?_ e.symm
    refine Finset.sum_nonneg (fun p _ => ?_)
    have : (0 : ℝ) ≤ ((geomOf ell k S).ell : ℝ) ^ (p.1 : ℕ) := by positivity
    positivity
  linarith

end psd

theorem plaqMask_inner_mono {L : PeriodicLatticeExtent} {P Q : Set (PeriodicLatticePlaquette L)} (h : P ⊆ Q)
    (f : PlaqFnL2 L) : (inner ℝ (plaqMask P f) (plaqMask P f) : ℝ) ≤ inner ℝ (plaqMask Q f) (plaqMask Q f) := by
  classical
  simp only [PiLp.inner_apply, plaqMask_apply]
  refine Finset.sum_le_sum (fun p _ => ?_)
  by_cases hp : p ∈ P
  · simp [hp, h hp]
  · by_cases hq : p ∈ Q
    · simp only [hp, hq, if_false, if_true, inner_zero_left]
      exact real_inner_self_nonneg
    · simp [hp, hq]

/-- on the flat background the plaquette-restricted `Δ` is monotone in the plaquette set. -/
theorem deltaK_flat_mono {L : PeriodicLatticeExtent} {P Q : Set (PeriodicLatticePlaquette L)} (h : P ⊆ Q)
    (X : BondFnL2 L) :
    ⟪X, deltaKLocCLM (AdalyFormal.Balaban.DeltaPrime.trivialU (L := L)) P X⟫ ≤
      ⟪X, deltaKLocCLM (AdalyFormal.Balaban.DeltaPrime.trivialU (L := L)) Q X⟫ := by
  rw [inner_deltaKLocCLM, inner_deltaKLocCLM]
  have e1 : deltaPrimeBilL2NormLoc (AdalyFormal.Balaban.DeltaPrime.trivialU (L := L)) P X X = 0 :=
    deltaPrimeBilNormLoc_trivialU P _ _
  have e2 : deltaPrimeBilL2NormLoc (AdalyFormal.Balaban.DeltaPrime.trivialU (L := L)) Q X X = 0 :=
    deltaPrimeBilNormLoc_trivialU Q _ _
  rw [e1, e2, add_zero, add_zero]
  exact plaqMask_inner_mono h _

theorem dataS_T_eq (sD sJ : PlaqSel) (P : IngrBParams) : (dataS sD sJ P).T = (Tfull P.G P.U).comp (iE P.G) := rfl
theorem dataS_Mass_eq (sD sJ : PlaqSel) (P : IngrBParams) :
    (dataS sD sJ P).Mass = (pE P.G).comp ((MassFull P.G P.a P.sector).comp (iE P.G)) := rfl
theorem dataS_Dpi_eq (sD sJ : PlaqSel) (P : IngrBParams) :
    (dataS sD sJ P).Dpi = (pE P.G).comp ((DpiFullS sD P.G P.U P.a).comp (iE P.G)) := rfl

section generic
variable {E S F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- if two base data share `T` and `Mass`, the `Ginv`-form is ordered by the `Dpi`-form. -/
theorem ginv_form_le (D1 D2 : BaseDataS E S F) (hT : D1.T = D2.T) (hM : D1.Mass = D2.Mass) (w : E)
    (hD : ⟪w, D1.Dpi w⟫ ≤ ⟪w, D2.Dpi w⟫) : ⟪w, D1.Ginv w⟫ ≤ ⟪w, D2.Ginv w⟫ := by
  rw [BaseDataS.inner_Ginv, BaseDataS.inner_Ginv, hT, hM]
  linarith

end generic

section mono
variable {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) {S : Tower (scaleUp ell k Lu)} (a : ℝ)
  (Lam : Set (PeriodicLatticeSite Lu))

/-- the `Dpi`-forms at the flat point: restricting the plaquette set decreases the form. -/
theorem Dpi_form_mono_flat (sD sD' : PlaqSel) (h : ∀ (L : PeriodicLatticeExtent) (G : TowerGeom L), sD L G ⊆ sD' L G)
    (w : ↥(bondSupp (geomOf ell k S))) :
    ⟪w, ((pE (geomOf ell k S)).comp ((DpiFullS sD (geomOf ell k S) (Uth (S.Om 0) 0) a).comp (iE (geomOf ell k S)))) w⟫ ≤
      ⟪w, ((pE (geomOf ell k S)).comp ((DpiFullS sD' (geomOf ell k S) (Uth (S.Om 0) 0) a).comp (iE (geomOf ell k S)))) w⟫ := by
  rw [E0_Dpi_inner sD, E0_Dpi_inner sD']
  have : Uth (S.Om 0) 0 = AdalyFormal.Balaban.DeltaPrime.trivialU := by rw [Uth_zero]; rfl
  unfold DeltaS
  rw [this]
  exact deltaK_flat_mono (h _ _) _

/-- **at the flat point the localised `Ginv` is below the literal one** (as quadratic forms on `E₀`). -/
theorem Ginv_form_mono_flat (sJ sJ' : PlaqSel) (w : ↥(bondSupp (Pth ell k Lu hell0 S a Lam 0).G)) :
    ⟪w, (dataS selIn sJ' (Pth ell k Lu hell0 S a Lam 0)).Ginv w⟫ ≤
      ⟪w, (dataS selAll sJ (Pth ell k Lu hell0 S a Lam 0)).Ginv w⟫ := by
  refine ginv_form_le (dataS selIn sJ' (Pth ell k Lu hell0 S a Lam 0)) (dataS selAll sJ (Pth ell k Lu hell0 S a Lam 0))
    (by rw [dataS_T_eq, dataS_T_eq]) (by rw [dataS_Mass_eq, dataS_Mass_eq]) w ?_
  rw [dataS_Dpi_eq, dataS_Dpi_eq]
  exact Dpi_form_mono_flat (ell := ell) (k := k) (Lu := Lu) (S := S) a selIn selAll (fun _ _ => Set.subset_univ _) w

end mono

section level0
/-- the level-0 rows of `Q` are the identity on the level-0 bonds. -/
theorem Q_level0_coord (sD sJ : PlaqSel) (P : IngrBParams) (x : ↥(bondSupp P.G)) (β : Bond P.Lf)
    (hβ : β ∈ bondsLam P.G (((0 : Fin (P.G.k + 1)) : Fin (P.G.k + 1)) : ℕ)) :
    (WithLp.ofLp ((dataS sD sJ P).Q x)) ⟨(0 : Fin (P.G.k + 1)), ⟨β, hβ⟩⟩ = (WithLp.ofLp (iE P.G x)) β := by
  rw [dataS_Q_eq]
  simp [QfullOf, QlinB_zero]

/-- `τ*` has no level-0 component (needs `1 ≤ k`). -/
theorem adjoint_tau_level0 (P : IngrBParams) (hk : 1 ≤ P.k) (B : BondFnL2 P.Lu) (β : Bond P.Lf)
    (hβ : β ∈ bondsLam P.G (((0 : Fin (P.G.k + 1)) : Fin (P.G.k + 1)) : ℕ)) :
    (WithLp.ofLp (ContinuousLinearMap.adjoint P.tau B)) ⟨(0 : Fin (P.G.k + 1)), ⟨β, hβ⟩⟩ = 0 := by
  classical
  refine ext_inner_right ℝ (fun v => ?_)
  rw [inner_zero_left]
  have h1 : ⟪(WithLp.ofLp (ContinuousLinearMap.adjoint P.tau B)) ⟨(0 : Fin (P.G.k + 1)), ⟨β, hβ⟩⟩, v⟫ =
      ⟪ContinuousLinearMap.adjoint P.tau B, (WithLp.toLp 2 (Pi.single (⟨(0 : Fin (P.G.k + 1)), ⟨β, hβ⟩⟩ : BIdx P.G) v) : FSp P.G)⟫ := by
    rw [PiLp.inner_apply, Finset.sum_eq_single (⟨(0 : Fin (P.G.k + 1)), ⟨β, hβ⟩⟩ : BIdx P.G)]
    · simp
    · intro p _ hp
      have h0 : (WithLp.ofLp (WithLp.toLp 2 (Pi.single (⟨(0 : Fin (P.G.k + 1)), ⟨β, hβ⟩⟩ : BIdx P.G) v) : FSp P.G)) p = 0 :=
        by simp only [WithLp.ofLp_toLp, Pi.single_apply]; rw [if_neg hp]
      rw [h0]
      simp
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h1, ContinuousLinearMap.adjoint_inner_left]
  have h2 : P.tau (WithLp.toLp 2 (Pi.single (⟨(0 : Fin (P.G.k + 1)), ⟨β, hβ⟩⟩ : BIdx P.G) v) : FSp P.G) = 0 := by
    refine PiLp.ext (fun e => ?_)
    unfold IngrBParams.tau tauExt
    simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]
    split_ifs with hb
    · rw [Pi.single_apply]
      rw [if_neg]
      · rfl
      · intro h
        have := congrArg (fun z : BIdx P.G => (z.1 : ℕ)) h
        simp [Fin.last] at this
        omega
    · rfl
  rw [h2]
  simp

end level0

#print axioms Ginv_psd_flat
#print axioms plaqMask_inner_mono
#print axioms deltaK_flat_mono
#print axioms ginv_form_le
#print axioms Dpi_form_mono_flat
#print axioms Ginv_form_mono_flat
#print axioms Q_level0_coord
#print axioms adjoint_tau_level0

end AdalyFormal.D1Guarded
