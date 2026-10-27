import CvOG9
import CvO40

/-!
# CvOH1 -- the genuine bond sets `bondsLam` of the nested instance in terms of `x₀` (lane omega)

`Omv j v`: the slab `Ω_j` of the nested tower as a predicate of `x₀`; `omGe0`: the `OmGe` condition as a predicate of `x₀`.
`bondsLam_one_iff`: `(y,1) ∈ bondsLam G j ↔ Crs (ell^j) y ∧ isRowN j (y 0)`;  `crs_of_bondsLam`: base sites of `bondsLam` bonds are aligned.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega

open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)

variable {ell M R : ℕ}

/-- `Ω_j` as a predicate of `x₀`. -/
def Omv (ell M R : ℕ) : ℕ → ℕ → Prop
  | 0, v => neP0 ell M R ≤ v ∧ v < neQ0 ell M R
  | 1, v => neP1 ell M R ≤ v ∧ v < neQ1 ell M R
  | 2, v => reg2 ell M R v
  | _, _ => False

theorem Omv_ge3 {j : ℕ} (hj : 3 ≤ j) (v : ℕ) : ¬ Omv ell M R j v := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 3 := ⟨j - 3, by omega⟩
  simp [Omv]

theorem Omv_site (j : ℕ) (x : PeriodicLatticeSite (scaleUp ell 2 (neLu M R))) :
    x ∈ (neS ell M R).Om j ↔ Omv ell M R j (x 0).val := by
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ 3 ≤ j by omega) with rfl | rfl | rfl | hj
  · exact neS_om0 x
  · exact neS_om1 x
  · simp only [Omv, reg2]; exact neS_om2 x
  · constructor
    · intro h; exact absurd h (tw3_omHi j hj x)
    · intro h; exact absurd h (Omv_ge3 hj _)

/-- `OmGe` as a predicate of `x₀`. -/
def omGe0 (ell M R : ℕ) (j v : ℕ) : Prop :=
  ∃ i, j ≤ i ∧ i ≤ 2 ∧ ∃ w, ell ^ i ∣ w ∧ Omv ell M R i w ∧ ¬ Omv ell M R (i + 1) w ∧ w ≤ v ∧ v < w + ell ^ i

end AdalyFormal.CoverOmega
