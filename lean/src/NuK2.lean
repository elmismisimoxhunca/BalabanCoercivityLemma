import NuK1
import NuG4
import NtCvOU3
import NtCvOF6

/-!
# NuK2 -- `τ` on Z-rows and the orthogonality of the transverse-sum-zero part (lane ncwdh_ell2_20261018)

`tau_zrow`: `τ (zrow ρ) = zfield (gRho ρ)` with `gRho ρ u₀ = [isRowN 2 (ell² u₀)] ρ 2 (ell² u₀)`.
`Bperp uE = Bpat uE - zfield (gbar uE)` has zero pairing with every `zfield`, hence `τ* Bperp ⊥ zrow ρ`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.NcwdhTwo

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverOmega
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

section
variable [CfData]
variable {ell M R : ℕ}
variable {L : PeriodicLatticeExtent}

/-- the unit profile read off a Z-row. -/
noncomputable def gRho (ell M R : ℕ) (ρ : ℕ → ℕ → ℝ) : ℕ → ℝ := fun u =>
  open Classical in if isRowN ell M R 2 (ell ^ 2 * u) then ρ 2 (ell ^ 2 * u) else 0

open Classical in
theorem tau_zrow (hg : NGeo ell M R) (hM : 0 < M) (ρ : ℕ → ℕ → ℝ) :
    tauExt ell 2 (neLu M R) (by have := hg.hell; omega) (neS ell M R) (zrow (geomOf ell 2 (neS ell M R)) ρ) =
      (zfield (gRho ell M R ρ) : BondFnL2 (neLu M R)) := by
  have hell : 0 < ell := by have := hg.hell; omega
  refine PiLp.ext (fun e => ?_)
  show (if hb : unitBondEmb ell 2 (neLu M R) hell e ∈ bondsLam (geomOf ell 2 (neS ell M R)) 2
      then WithLp.ofLp (zrow (geomOf ell 2 (neS ell M R)) ρ) ⟨Fin.last 2, ⟨unitBondEmb ell 2 (neLu M R) hell e, hb⟩⟩ else 0) =
    (if e.2 = 1 then dgS (gRho ell M R ρ (e.1 0).val) else 0)
  by_cases h1 : e.2 = 1
  · rw [if_pos h1]
    have hemb0 : ((unitBondEmb ell 2 (neLu M R) hell e).1 0).val = ell ^ 2 * (e.1 0).val := rfl
    have hemb2 : (unitBondEmb ell 2 (neLu M R) hell e).2 = 1 := h1
    have hcrs : Crs (ell ^ 2) (unitBondEmb ell 2 (neLu M R) hell e).1 := by
      intro μ
      exact ⟨(e.1 μ).val, rfl⟩
    have hmemiff : unitBondEmb ell 2 (neLu M R) hell e ∈ bondsLam (geomOf ell 2 (neS ell M R)) 2 ↔ isRowN ell M R 2 (ell ^ 2 * (e.1 0).val) := by
      have := bondsLam_one_iff hg hM (j := 2) le_rfl (unitBondEmb ell 2 (neLu M R) hell e).1
      have hb : unitBondEmb ell 2 (neLu M R) hell e = ((unitBondEmb ell 2 (neLu M R) hell e).1, (1 : Fin 3)) := Prod.ext rfl hemb2
      rw [hb, this, hemb0]
      exact ⟨fun h => h.2, fun h => ⟨hcrs, h⟩⟩
    by_cases hr : isRowN ell M R 2 (ell ^ 2 * (e.1 0).val)
    · have hb := hmemiff.mpr hr
      rw [dif_pos hb]
      show (if (unitBondEmb ell 2 (neLu M R) hell e).2 = 1 then dgS (ρ 2 ((unitBondEmb ell 2 (neLu M R) hell e).1 0).val) else 0) = _
      rw [if_pos hemb2, hemb0]
      unfold gRho
      rw [if_pos hr]
    · have hb : unitBondEmb ell 2 (neLu M R) hell e ∉ bondsLam (geomOf ell 2 (neS ell M R)) 2 := fun h => hr (hmemiff.mp h)
      rw [dif_neg hb]
      unfold gRho
      rw [if_neg hr, dgS_zero]
  · rw [if_neg h1]
    by_cases hb : unitBondEmb ell 2 (neLu M R) hell e ∈ bondsLam (geomOf ell 2 (neS ell M R)) 2
    · rw [dif_pos hb]
      show (if (unitBondEmb ell 2 (neLu M R) hell e).2 = 1 then dgS (ρ 2 ((unitBondEmb ell 2 (neLu M R) hell e).1 0).val) else 0) = 0
      have : ¬ ((unitBondEmb ell 2 (neLu M R) hell e).2 = 1) := h1
      rw [if_neg this]
    · rw [dif_neg hb]


/-- the transverse-sum-zero part of the pattern. -/
noncomputable def Bperp (uE : ℕ) : BondFnL2 L := Bpat uE - zfield (gbar uE)

theorem inner_Bperp_zfield (uE : ℕ) (huE : uE + 1 < L 0 + 1) (h1 : 2 ∣ L 1 + 1) (h2 : 2 ∣ L 2 + 1) (g : ℕ → ℝ) :
    (inner ℝ (Bperp uE : BondFnL2 L) (zfield g) : ℝ) = 0 := by
  unfold Bperp
  rw [inner_sub_left, inner_sig_zfield _ (Bpat_sig uE) g, inner_zfield_zfield]
  simp only [thetaOf_Bpat]
  rw [sum_betaPat uE huE h1 h2 g]
  ring

theorem perp_orth (hg : NGeo ell M R) (hM : 0 < M) (uE : ℕ) (huE : uE + 1 < neLu M R 0 + 1)
    (h1 : 2 ∣ neLu M R 1 + 1) (h2 : 2 ∣ neLu M R 2 + 1) (ρ : ℕ → ℕ → ℝ) :
    (inner ℝ (ContinuousLinearMap.adjoint (tauExt ell 2 (neLu M R) (by have := hg.hell; omega) (neS ell M R)) (Bperp uE))
      (zrow (geomOf ell 2 (neS ell M R)) ρ) : ℝ) = 0 := by
  rw [ContinuousLinearMap.adjoint_inner_left, tau_zrow hg hM]
  exact inner_Bperp_zfield uE huE h1 h2 _

end

end AdalyFormal.NcwdhTwo
