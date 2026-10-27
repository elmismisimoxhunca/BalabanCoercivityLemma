import SoGeo
import NuZ1

/-!
# SoZ1 -- positions `C` of the staggered layer: the structure `CPos`, `soC` satisfies it, and `nested_z0Setup` at a general `C` (lane sites_only_20261019)

Every analytic statement of the ell=2 lane (`NuE2`..`NuM3`) is stated at `C = neC0 ell M R`; they only use that `C` is a legal position (`CPos`) and, in the chain
modules, row-alignment facts.  Here `CPos` collects the first kind, `nested_z0Setup_S` is `NuZ1.nested_z0Setup` for any `C` with `CPos`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.SitesOnly

open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverOmega
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLaneG
open AdalyFormal.NcwdhTwo

/-- `C` is a legal position of the layer of `neS ell M R`: inside the chain, away from the ends. -/
structure CPos [CfData] (ell M R C : ℕ) : Prop where
  hge : neP0 ell M R ≤ C
  hlt : C + 1 < neQ0 ell M R
  hell : ell ≤ C
  hhi : C + ell * ell < neN ell M R

section
variable [CfData]
variable {ell M R : ℕ}

/-- `soC` is a legal position (any `c` with `10 <= c`, `SoRel ell c`). -/
theorem cpos_soC {c : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) (hrel : SoRel ell c) (hc : 10 ≤ c) :
    CPos ell M R (soC ell M R c) := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin_two hell hM hR
  have hthin := so_thin_atoms (M := M) hrel (by omega : 1 ≤ c)
  have hsucc := soC_succ (ell := ell) (M := M) (R := R) hell hM (by omega : 1 ≤ c)
  have hY1 : 0 < ell * M := Nat.mul_pos (by omega) hM
  have hY12 : ell * M ≤ ell * (ell * M) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
  have hell_le : ell ≤ ell * M := Nat.le_mul_of_pos_right _ hM
  have hee : ell * ell ≤ ell * (ell * M) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hM)
  have hcm1 : 1 * (ell * M) ≤ (c - 1) * (ell * M) := Nat.mul_le_mul_right _ (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [neP0, neP1, neA']; omega
  · simp only [neQ0, neQ1, neB]; omega
  · omega
  · simp only [neN]; omega

/-- `NuZ1.nested_z0Setup` at a general legal position `C`. -/
theorem nested_z0Setup_S {C : ℕ} (hC : CPos ell M R C) (hell2 : 2 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (t : ℝ)
    (ht : |t| < Real.pi / 2) :
    Z0Setup (scaleUp ell 2 (neLu M R)) ell C t (geomOf ell 2 (neS ell M R)) (isRowN ell M R) := by
  have hg := nGeo_two hell2 hdvd hM hR
  have hell : 0 < ell := by omega
  have hdiv : ∀ μ, ell * ell ∣ scaleUp ell 2 (neLu M R) μ + 1 := by
    intro μ
    rw [ne_scaleUp hell hM]
    exact ⟨M * (4 * R + (2 * CfData.cf + 6)), by unfold neN; ring⟩
  have hN2 : 2 ∣ scaleUp ell 2 (neLu M R) 1 + 1 := by
    rw [ne_scaleUp hell hM]
    exact ⟨ell * (ell * (M * (2 * R + CfData.cf + 3))), by unfold neN; ring⟩
  have hlo : ell ≤ C := hC.hell
  have hhi : C + ell * ell < scaleUp ell 2 (neLu M R) 0 + 1 := by
    rw [ne_scaleUp hell hM]; exact hC.hhi
  refine ⟨⟨hN2, hE, hell, hdiv, hlo, hhi, ht⟩, rfl, rfl, ?_, ?_⟩
  · intro p
    have hj : (p.1 : ℕ) ≤ 2 := by have := p.1.2; simp [geomOf] at this ⊢; omega
    exact crs_of_bondsLam hg hM hj p.2.1 p.2.2
  · intro j hj y
    exact bondsLam_one_iff hg hM hj y

end

#print axioms cpos_soC
#print axioms nested_z0Setup_S

end AdalyFormal.SitesOnly
