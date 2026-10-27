
namespace AdalyFormal.Round4.Guarded.DecayR2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Guarded
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round2.Guarded.R2Prove
open AdalyFormal.Round3.Guarded.R2Prove
open AdalyFormal.Round4.Guarded.DecayR1

section Algebra
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The relative return can be evaluated without taking an inverse on W.
The all-carrier inverse is used on the full carrier, not on a compression. -/
theorem relativeReturn_apply (Θ B D : E →L[ℝ] E)
    (hB : IsUnit B) (hC : IsUnit (B - D)) (hA : IsUnit (B + Θ))
    (y : Θ.range) :
    (relativeReturn Θ B (B - D) y : E) =
      Θ (Ring.inverse (B + Θ) (D (Ring.inverse (B - D) y))) := by
  let v := Ring.inverse (B - D) (y : E)
  let u := Ring.inverse (B + Θ) (D v)
  let q : Θ.range := ⟨Θ u, ⟨u, rfl⟩⟩
  have hv : (B - D) v = (y : E) :=
    congrArg (fun T : E →L[ℝ] E => T y) (Ring.mul_inverse_cancel (B - D) hC)
  have hu : (B + Θ) u = D v :=
    congrArg (fun T : E →L[ℝ] E => T (D v)) (Ring.mul_inverse_cancel (B + Θ) hA)
  have hi : ∀ x, Ring.inverse B (B x) = x := fun x =>
    congrArg (fun T : E →L[ℝ] E => T x) (Ring.inverse_mul_cancel B hB)
  have htheta : Θ u = D v - B u := by
    change B u + Θ u = D v at hu
    exact eq_sub_of_add_eq' hu
  have hd : D v = B v - (y : E) := by
    change B v - D v = (y : E) at hv
    calc
      D v = B v - (B v - D v) := by abel
      _ = _ := by rw [hv]
  have hBi : Ring.inverse B (Θ u) = v - Ring.inverse B (y : E) - u := by
    rw [htheta, map_sub, hi, hd, map_sub, hi]
  have hq : response Θ B q = (response Θ (B - D) - response Θ B) y := by
    apply Subtype.ext
    change Θ u + Θ (Ring.inverse B (Θ u)) =
      ((y : E) + Θ v) - ((y : E) + Θ (Ring.inverse B y))
    rw [hBi, map_sub, map_sub]
    abel
  have hK := (unit_add_iff_response Θ B hB).mp hA
  have hr : Ring.inverse (response Θ B) (response Θ B q) = q :=
    congrArg (fun T : Θ.range →L[ℝ] Θ.range => T q)
      (Ring.inverse_mul_cancel (response Θ B) hK)
  have heq : relativeReturn Θ B (B - D) y = q := by
    change Ring.inverse (response Θ B) ((response Θ (B - D) - response Θ B) y) = q
    rw [← hq, hr]
  exact congrArg (fun z : Θ.range => (z : E)) heq

/-- A source-specific bound avoids the crude product of the full inverse
response norm with the absolute return. Only the jet-observed all-carrier
Green response to Theta is required on the first pass. -/
theorem relativeReturn_norm_le_observed (Θ B D : E →L[ℝ] E)
    (N : Submodule ℝ E) (hB : IsUnit B) (hC : IsUnit (B - D))
    (hA : IsUnit (B + Θ))
    (hΘ : ∀ x y, ⟪Θ x, y⟫ = ⟪x, Θ y⟫)
    (hAs : ∀ x y, ⟪(B + Θ) x, y⟫ = ⟪x, (B + Θ) y⟫)
    (hDs : ∀ x y, ⟪D x, y⟫ = ⟪x, D y⟫)
    (hN : ∀ x ∈ N, D x = 0)
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hat : ∀ x : E, ‖Nᗮ.starProjection (Ring.inverse (B + Θ) (Θ x))‖ ≤ a * ‖x‖)
    (hct : ∀ y : Θ.range, ‖Nᗮ.starProjection (Ring.inverse (B - D) y)‖ ≤ c * ‖y‖) :
    ‖relativeReturn Θ B (B - D)‖ ≤ a * ‖D‖ * c := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro y
  change ‖(relativeReturn Θ B (B - D) y : E)‖ ≤ _
  rw [relativeReturn_apply Θ B D hB hC hA y]
  let u := Ring.inverse (B - D) (y : E)
  let r := Θ (Ring.inverse (B + Θ) (D u))
  have hpair : ‖r‖ ^ 2 =
      ⟪Nᗮ.starProjection (Ring.inverse (B + Θ) (Θ r)), D (Nᗮ.starProjection u)⟫ := by
    calc
      ‖r‖ ^ 2 = ⟪r, r⟫ := (real_inner_self_eq_norm_sq r).symm
      _ = ⟪Θ r, Ring.inverse (B + Θ) (D u)⟫ := (hΘ _ _).symm
      _ = ⟪Ring.inverse (B + Θ) (Θ r), D u⟫ := inverse_pairing _ hA hAs _ _
      _ = _ := pair_eq_observed D N hN hDs _ _
  have he : ‖r‖ ^ 2 ≤ (a * ‖D‖ * c) * ‖y‖ * ‖r‖ := by
    calc
      ‖r‖ ^ 2 ≤ ‖Nᗮ.starProjection (Ring.inverse (B + Θ) (Θ r))‖ *
          ‖D (Nᗮ.starProjection u)‖ := by
        rw [hpair]; exact real_inner_le_norm _ _
      _ ≤ (a * ‖r‖) * (‖D‖ * (c * ‖y‖)) := by
        gcongr
        · exact hat r
        · exact (D.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hct y) (norm_nonneg D))
      _ = (a * ‖D‖ * c) * ‖y‖ * ‖r‖ := by ring
  change ‖r‖ ≤ _
  by_cases hr : r = 0
  · rw [hr, norm_zero]; positivity
  · have hp : ‖r‖ * ‖r‖ ≤ (a * ‖D‖ * c) * ‖y‖ * ‖r‖ := by nlinarith
    exact le_of_mul_le_mul_right hp (norm_pos_iff.mpr hr)

end Algebra
section Concrete
variable (P : IngrBParams)

/-- Genuine correction-sensitive transfer. This need not grow with inverse
norms of modes invisible to the dressed jet. No bound is assumed by its definition. -/
noncomputable def observedGuardTransfer : ↥(bondSupp P.G) →L[ℝ] ↥(bondSupp P.G) :=
  (jetObservation P).comp ((Ring.inverse (dataS selAll selAll P).Ginv).comp (boundaryShift P))

/-- Exact inverse-relative return for the unchanged lattice assembly. -/
theorem actual_relative_return_apply (hW : WellDefAt selIn selIn P)
    (hu : IsUnit (dataS selAll selAll P).Ginv) (y : (boundaryShift P).range) :
    (relativeReturn (boundaryShift P) (dataS selIn selIn P).Ginv (localCorrected P) y :
      ↥(bondSupp P.G)) =
      boundaryShift P (Ring.inverse (dataS selAll selAll P).Ginv
        ((dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)
          (Ring.inverse (localCorrected P) y))) := by
  have hC : IsUnit (localCorrected P) := by
    rw [localCorrected_eq P]; exact hW.2.1
  simpa only [← carrier_eq_local_add_shift P] using
    relativeReturn_apply (boundaryShift P) (dataS selIn selIn P).Ginv
      ((dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)) hW.1 hC
      (by rwa [← carrier_eq_local_add_shift P]) y

/-- Main partial bound: the missing all-carrier control is now restricted to
what the actual nonlinear correction can observe, rather than the entire guard. -/
theorem actual_relative_return_norm_le_observed (hW : WellDefAt selIn selIn P)
    (hu : IsUnit (dataS selAll selAll P).Ginv) {c : ℝ} (hc : 0 ≤ c)
    (hct : ∀ y : (boundaryShift P).range,
      ‖jetObservation P (Ring.inverse (localCorrected P) y)‖ ≤ c * ‖y‖) :
    ‖relativeReturn (boundaryShift P) (dataS selIn selIn P).Ginv (localCorrected P)‖ ≤
      ‖observedGuardTransfer P‖ *
        ‖(dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)‖ * c := by
  have hC : IsUnit (localCorrected P) := by
    rw [localCorrected_eq P]; exact hW.2.1
  apply relativeReturn_norm_le_observed _ _ _ (jetInputZero P) hW.1 hC
    (by rwa [← carrier_eq_local_add_shift P]) (boundaryShift_symmetric P)
    (fun x y => by rw [← carrier_eq_local_add_shift P];
      exact (dataS selAll selAll P).Ginv_symm (dataS_laws selAll selAll P) x y)
    ((dataS selIn selIn P).Delta2_spec (dataS_laws selIn selIn P)).1
    (correction_kills_jetInputZero P) (norm_nonneg _) hc _ hct
  intro x
  rw [← carrier_eq_local_add_shift P]
  exact (observedGuardTransfer P).le_opNorm x

/-- A conditional criterion, not a new guard or a change to either pinned goal. -/
theorem pencil_isUnit_of_observed_guard_decay (hW : WellDefAt selIn selIn P)
    (hu : IsUnit (dataS selAll selAll P).Ginv) {c : ℝ} (hc : 0 ≤ c)
    (hct : ∀ y : (boundaryShift P).range,
      ‖jetObservation P (Ring.inverse (localCorrected P) y)‖ ≤ c * ‖y‖)
    (hsmall : ‖observedGuardTransfer P‖ *
      ‖(dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)‖ * c < 1) :
    IsUnit ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)) := by
  apply (pencil_isUnit_iff_response P hW.2.1).mpr
  apply unit_of_relative_norm_lt_one _ _ ((carrier_isUnit_iff_response P hW.1).mp hu)
  exact (actual_relative_return_norm_le_observed P hW hu hc hct).trans_lt hsmall

/-- Failure forces amplification in the jet-visible guard transfer, not just
some unrelated small spectral mode of the full response. -/
theorem failure_requires_observed_amplification (hW : WellDefAt selIn selIn P)
    (hu : IsUnit (dataS selAll selAll P).Ginv)
    (hbad : ¬ IsUnit ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)))
    {c : ℝ} (hc : 0 ≤ c)
    (hct : ∀ y : (boundaryShift P).range,
      ‖jetObservation P (Ring.inverse (localCorrected P) y)‖ ≤ c * ‖y‖) :
    1 ≤ ‖observedGuardTransfer P‖ *
      ‖(dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)‖ * c := by
  by_contra hn
  exact hbad (pencil_isUnit_of_observed_guard_decay P hW hu hc hct (lt_of_not_ge hn))

end Concrete

/-- A new analytic obligation, kept separate from the unchanged headline. -/
def CObservedGuardSmall : ∀ (ell k : ℕ) (Lu : PeriodicLatticeExtent) (_ : 0 < ell)
    (_ : Tower (scaleUp ell k Lu))
    (_ : AdalyFormal.Balaban.CoercUMainDesigned.LinkCfg (scaleUp ell k Lu))
    (_ : ℝ) (_ : Set (PeriodicLatticeSite Lu)), Prop :=
  fun ell k Lu h S U a Lam =>
    let P := gparams ell k Lu h S U a Lam
    ∃ c : ℝ, 0 ≤ c ∧
      (∀ y : (boundaryShift P).range,
        ‖jetObservation P (Ring.inverse (localCorrected P) y)‖ ≤ c * ‖y‖) ∧
      ‖observedGuardTransfer P‖ *
        ‖(dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)‖ * c < 1

/-- Conditional only: class-wide correction-sensitive decay would close the
original GoalPos2, with its radius/cap order and all other binders intact. -/
theorem goalPos2_of_observed_guard_decay (h : GShape CObservedGuardSmall) : GoalPos2 := by
  apply goalPos2_iff_goalPos1.mpr
  apply AdalyFormal.D1Residual.GShape_imp CObservedGuardSmall AdalyFormal.D1Residual.CPen _ h
  intro ell k h0 M R Lu S U a Lam _ _ hW hu ht
  obtain ⟨c, hc, hct, hsmall⟩ := ht
  exact pencil_isUnit_of_observed_guard_decay (gparams ell k Lu h0 S U a Lam)
    hW hu hc hct hsmall

#print axioms CObservedGuardSmall
#print axioms goalPos2_of_observed_guard_decay
#print axioms relativeReturn_apply
#print axioms relativeReturn_norm_le_observed
#print axioms observedGuardTransfer
#print axioms actual_relative_return_apply
#print axioms actual_relative_return_norm_le_observed
#print axioms pencil_isUnit_of_observed_guard_decay
#print axioms failure_requires_observed_amplification
end AdalyFormal.Round4.Guarded.DecayR2
