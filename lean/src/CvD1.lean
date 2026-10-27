import CvR2
import AdalyFormal.Balaban.NormalizationAudit

/-!
# CvD1 -- the `cos t` plaquette weight of `Delta_k` on the sigma_3 block of a Cartan configuration (lane cover_jacobi_20261016)

For a Cartan-valued configuration `U` and a sigma_3-valued bond field `A` (every `A b` diagonal), the genuine quadratic form
`deltaKQuadFormNormalizedCorrected U A = <A, Delta_k A>` (`D*D` + the source-normalised, transported `Delta'`) equals
`sum_p cos(theta_p) * ||curl_U A (p)||^2`, `cos(theta_p) = Re U(dp)_{00}`:
the second (commutator) term of `Delta'` vanishes because all four `A'(b)` are diagonal, and the first term turns `||curl||^2` into
`cos(theta_p) ||curl||^2` because `Re U(dp) = cos(theta_p) * 1`.  On the Cartan layer path `cos(theta_p) = cos t` on the plaquettes that
contain a layer link and `1` elsewhere.  The proof is for ALL Cartan `U` and ALL `L`; the identification of `theta_p` with `0, +-t` along `neU` is NOT done here.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverJacobi

open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHj
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.NormalizationAudit

variable {L : PeriodicLatticeExtent}

theorem isCartan_one : IsCartan (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  unfold IsCartan; simp

theorem isCartan_mul {V W : Matrix.specialUnitaryGroup (Fin 2) ℂ} (hV : IsCartan V) (hW : IsCartan W) : IsCartan (V * W) := by
  obtain ⟨a1, a2⟩ := hV
  obtain ⟨b1, b2⟩ := hW
  unfold IsCartan
  simp [Matrix.mul_apply, Fin.sum_univ_two, a1, a2, b1, b2]

theorem inv_coe (V : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ((V⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = (V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := rfl

theorem isCartan_inv {V : Matrix.specialUnitaryGroup (Fin 2) ℂ} (hV : IsCartan V) : IsCartan V⁻¹ := by
  obtain ⟨a1, a2⟩ := hV
  unfold IsCartan
  rw [inv_coe]
  simp [Matrix.conjTranspose_apply, a1, a2]

theorem holonomy_cartan {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L} (hU : CartanCfg U)
    (p : PeriodicLatticePlaquette L) : IsCartan (holonomyElem U p) := by
  unfold holonomyElem periodicPlaquetteHolonomy
  exact isCartan_mul (isCartan_mul (isCartan_mul (hU _) (hU _)) (isCartan_inv (hU _))) (isCartan_inv (hU _))

/-- `cos(theta_p)`: the real part of the diagonal entry of the plaquette holonomy. -/
noncomputable def holCos (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (p : PeriodicLatticePlaquette L) : ℝ :=
  (((holonomyElem U p : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re

theorem cartan_entries {H : Matrix.specialUnitaryGroup (Fin 2) ℂ} (hH : IsCartan H) :
    (H : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = star ((H : Matrix (Fin 2) (Fin 2) ℂ) 0 0) := by
  have hu := H.2
  rw [Matrix.mem_specialUnitaryGroup_iff] at hu
  obtain ⟨hu1, hdet⟩ := hu
  have hU : (H : Matrix (Fin 2) (Fin 2) ℂ) * (H : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = 1 := by
    rw [Matrix.mem_unitaryGroup_iff] at hu1
    simpa [Matrix.star_eq_conjTranspose] using hu1
  obtain ⟨h01, h10⟩ := hH
  have e0 := congrFun (congrFun hU 0) 0
  have e1 := congrFun (congrFun hU 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, h01, h10] at e0 e1
  rw [Matrix.det_fin_two] at hdet
  simp [h01, h10] at hdet
  -- H00 * conj H00 = 1 and H00 * H11 = 1  =>  H11 = conj H00
  have h00 : (H : Matrix (Fin 2) (Fin 2) ℂ) 0 0 ≠ 0 := by
    intro h; rw [h] at e0; simp at e0
  have : (H : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * ((H : Matrix (Fin 2) (Fin 2) ℂ) 1 1 - star ((H : Matrix (Fin 2) (Fin 2) ℂ) 0 0)) = 0 := by
    rw [mul_sub]
    simp only [Complex.star_def] at *
    linear_combination hdet - e0
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h h00
  · exact sub_eq_zero.mp h

theorem reHolonomy_eq {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L} (hU : CartanCfg U)
    (p : PeriodicLatticePlaquette L) : reHolonomy U p = ((holCos U p : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hH := holonomy_cartan hU p
  have h11 := cartan_entries hH
  obtain ⟨h01, h10⟩ := hH
  unfold reHolonomy holonomyElemInv holCos
  simp only [inv_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, h01, h10, h11, Complex.ext_iff] <;> ring

#print axioms isCartan_one
#print axioms isCartan_mul
#print axioms inv_coe
#print axioms isCartan_inv
#print axioms holonomy_cartan
#print axioms holCos
#print axioms cartan_entries
#print axioms reHolonomy_eq

end AdalyFormal.CoverJacobi
