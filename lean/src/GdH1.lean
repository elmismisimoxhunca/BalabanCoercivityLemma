import GdSchur

/-!
# GdH1 -- (H1) `Q*` is injective on the boundary-twist family `U = Uth (Ω₀) θ`.

* `Qfull_theta_flat`: the bond sector `Q(U_θ)` equals `Q(flat)` (locality of `QfullOf`: `StatementLaneR8.QfullOf_congr`, which needs the two
  configurations to agree on the bonds with BOTH endpoints in `Ω₀`; `Uth` is `1` on every bond with its base point in `Ω₀`).
* `Qs_injective_twist`: from the proved `classRightInv` (compute/m2_rightinv_20261015/src/RI5.lean:283) at the flat configuration and `qs_inj_of_hext`, `Q*` is injective at
  every `Uth (Ω₀) θ`, in the regime of `ClassRightInv` (thick torus, `Λ ≠ ∅`, `m`, `R` large, `α₀` small).
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
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

/-- locality of the bond sector on the twist family: `Q(U_θ) = Q(flat)`. -/
theorem Qfull_theta_flat {L : PeriodicLatticeExtent} {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S)
    (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M) (θ : ℝ) :
    QfullOf (geomOf ell k S) (Uth (S.Om 0) θ) = QfullOf (geomOf ell k S) (flatCfg : Cfg L) :=
  QfullOf_congr hS hell hroom (fun e he => by
    show Uth (S.Om 0) θ e = (1 : SU2m)
    exact Uth_one_of_base _ θ e he.1)

#print axioms Qfull_theta_flat

/-- `Qs` of the assembled data only reads the bond sector. -/
theorem dataS_Qs_eq (sD sJ : PlaqSel) (P : IngrBParams) :
    (dataS sD sJ P).Qs = ContinuousLinearMap.adjoint ((QfullOf P.G P.U).comp (iE P.G)) := rfl

theorem dataS_Q_eq (sD sJ : PlaqSel) (P : IngrBParams) :
    (dataS sD sJ P).Q = (QfullOf P.G P.U).comp (iE P.G) := rfl

/-- **(H1)** `Q*` is injective on the twist family, in the regime of the proved `ClassRightInv`. -/
theorem Qs_injective_twist (ell : ℕ) (hell2 : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∀ m : ℕ, m₁ ≤ m → ∃ R₁ : ℕ, 18 ≤ R₁ ∧ ∀ R : ℕ, R₁ ≤ R → ∃ s : ℝ, 0 < s ∧
      ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ s →
        TorusOK ell (ell ^ m) Lu → ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
        (∀ σ : Fin 3, 13 * ell ^ m ≤ Lu σ + 1) →
        ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam → Lam.Nonempty →
        ∀ θ : ℝ, ClassCoupled ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ (Uth (S.Om 0) θ) →
        ∀ sD sJ : PlaqSel,
          Function.Injective (dataS sD sJ (gparams ell k Lu (by omega) S (Uth (S.Om 0) θ) a Lam)).Qs := by
  obtain ⟨m₁, h1⟩ := AdalyFormal.M2RightInv.classRightInv ell hell2 a ha
  refine ⟨max m₁ 1, le_max_right _ _, fun m hm => ?_⟩
  obtain ⟨bN, hbN, R₁, h2⟩ := h1 m (le_trans (le_max_left _ _) hm)
  refine ⟨max R₁ 18, le_max_right _ _, fun R hR => ?_⟩
  obtain ⟨s, hs, h3⟩ := h2 R (le_trans (le_max_left _ _) hR)
  refine ⟨s, hs, fun k hk Lu α₀ hα hαs hT S hS hthick Lam hL hLne θ hU sD sJ => ?_⟩
  have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
  have hR18 : 18 ≤ R := le_trans (le_max_right _ _) hR
  have hell0 : 0 < ell := by omega
  have hroom : 17 * ell ≤ R * ell ^ m := by
    have h1 : ell ≤ ell ^ m := by
      calc ell = ell ^ 1 := (pow_one ell).symm
        _ ≤ ell ^ m := Nat.pow_le_pow_right hell0 hm1
    calc 17 * ell ≤ 18 * ell ^ m := by omega
      _ ≤ R * ell ^ m := Nat.mul_le_mul_right _ hR18
  have hflat : ClassCoupled ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ (flatCfg : LinkCfg (scaleUp ell k Lu)) :=
    ⟨hU.1, AdalyFormal.StatementLaneG.flat_perCubeRegular2cG ell (ell ^ m) 12 k hell0 (Nat.one_le_pow _ _ hell0) (by norm_num) hα S⟩
  have hext := h3 k hk Lu α₀ hα hαs hT S hS hthick Lam hL hLne flatCfg hflat (fun e _ => rfl)
  have hinj := AdalyFormal.M2OpLayer.qs_inj_of_hext hell0 S (flatCfg : LinkCfg (scaleUp ell k Lu)) a Lam bN hext
  have hQ := Qfull_theta_flat (L := scaleUp ell k Lu) hS hell2 hroom θ
  rw [dataS_Qs_eq]
  show Function.Injective (ContinuousLinearMap.adjoint ((QfullOf (geomOf ell k S) (Uth (S.Om 0) θ)).comp (iE (geomOf ell k S))))
  rw [hQ]
  exact hinj

#print axioms dataS_Qs_eq
#print axioms Qs_injective_twist

end AdalyFormal.D1Guarded
