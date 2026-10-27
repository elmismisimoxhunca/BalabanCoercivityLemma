import CvD2
import NsCvNe3
import NsCvR4

/-!
# CvD3 -- the plaquette weights along the Cartan layer path (lane cover_jacobi_20261016)

On `layerCfg c (cartan t)` (CvNe2/CvNe3) the plaquette weight `holCos` of CvD1 is
`cos(t (ind(x_0 + 1 = c) - ind(x_0 = c)))` for the plaquettes in the (0,1)-plane and `1` for the (0,2)- and (1,2)-planes.
Combined with CvD2 (`delta_sigma3_form`): on the sigma_3 block the printed `Delta_k` is the flat plaquette form with weight `cos t` on the
(0,1)-plaquettes at `x_0 = c - 1` and `x_0 = c` (the two layers adjacent to the layer of links), and `1` elsewhere.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverJacobi


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.DeltaPrime

theorem cartan_zero : cartan 0 = 1 := by
  apply Subtype.ext
  rw [cartan_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply]

theorem cartan_mul (s s' : ℝ) : cartan s * cartan s' = cartan (s + s') := by
  apply Subtype.ext
  show ((cartan s : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * (cartan s' : Matrix (Fin 2) (Fin 2) ℂ) = _
  rw [cartan_coe, cartan_coe, cartan_coe, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i
  · simp [← Complex.exp_add]; ring_nf
  · simp [← Complex.exp_add]; ring_nf

theorem cartan_inv (s : ℝ) : (cartan s)⁻¹ = cartan (-s) := by
  apply Subtype.ext
  rw [inv_coe, cartan_coe, cartan_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, Matrix.diagonal_apply, ← Complex.exp_conj] <;>
    ring_nf

theorem holCos_of_eq_cartan {L : PeriodicLatticeExtent}
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L} {p : PeriodicLatticePlaquette L} {s : ℝ}
    (h : holonomyElem U p = cartan s) : holCos U p = Real.cos s := by
  unfold holCos
  rw [h, cartan_coe]
  simp [← Complex.ofReal_cos, Complex.exp_ofReal_mul_I_re]

/-- the (0,1)-plane plaquette holonomy of the layer configuration. -/
theorem holonomy_layer_01 {L : PeriodicLatticeExtent} (c : ℕ) (t : ℝ) (x : PeriodicLatticeSite L)
    (h : ((0 : Fin 3), (1 : Fin 3)).1 < ((0 : Fin 3), (1 : Fin 3)).2) :
    holonomyElem (layerCfg (L := L) c (cartan t)) (x, ⟨((0 : Fin 3), (1 : Fin 3)), h⟩) =
      cartan (t * ((if ((periodicLatticeShift x 0) 0).val = c then 1 else 0) - (if (x 0).val = c then 1 else 0))) := by
  unfold holonomyElem periodicPlaquetteHolonomy layerCfg
  by_cases h1 : ((periodicLatticeShift x 0) 0).val = c <;> by_cases h2 : (x 0).val = c <;>
    simp [h1, h2, cartan_inv, cartan_mul, cartan_zero]

/-- the (0,2)-plane plaquette holonomy is trivial. -/
theorem holonomy_layer_02 {L : PeriodicLatticeExtent} (c : ℕ) (t : ℝ) (x : PeriodicLatticeSite L)
    (h : ((0 : Fin 3), (2 : Fin 3)).1 < ((0 : Fin 3), (2 : Fin 3)).2) :
    holonomyElem (layerCfg (L := L) c (cartan t)) (x, ⟨((0 : Fin 3), (2 : Fin 3)), h⟩) = cartan 0 := by
  unfold holonomyElem periodicPlaquetteHolonomy layerCfg
  simp [cartan_zero]

/-- the (1,2)-plane plaquette holonomy is trivial: the two layer links of the plaquette cancel. -/
theorem holonomy_layer_12 {L : PeriodicLatticeExtent} (c : ℕ) (t : ℝ) (x : PeriodicLatticeSite L)
    (h : ((1 : Fin 3), (2 : Fin 3)).1 < ((1 : Fin 3), (2 : Fin 3)).2) :
    holonomyElem (layerCfg (L := L) c (cartan t)) (x, ⟨((1 : Fin 3), (2 : Fin 3)), h⟩) = cartan 0 := by
  unfold holonomyElem periodicPlaquetteHolonomy layerCfg
  have e : (periodicLatticeShift x 2) 0 = x 0 := by
    simp [periodicLatticeShift]
  by_cases h2 : (x 0).val = c <;> simp [e, h2, cartan_zero]

/-- the exponent: nonzero only in the (0,1)-plane. -/
noncomputable def layerEps {L : PeriodicLatticeExtent} (c : ℕ) (p : PeriodicLatticePlaquette L) : ℝ :=
  if p.2.1 = ((0 : Fin 3), (1 : Fin 3)) then
    ((if ((periodicLatticeShift p.1 0) 0).val = c then 1 else 0) - (if (p.1 0).val = c then 1 else 0))
  else 0

/-- **every plaquette weight along the layer path is `cos (t * layerEps)`.** -/
theorem holCos_layer {L : PeriodicLatticeExtent} (c : ℕ) (t : ℝ) (p : PeriodicLatticePlaquette L) :
    holCos (layerCfg (L := L) c (cartan t)) p = Real.cos (t * layerEps c p) := by
  obtain ⟨x, ⟨⟨μ, ν⟩, h⟩⟩ := p
  have key : ∀ (μ ν : Fin 3), μ < ν → (μ = 0 ∧ ν = 1) ∨ (μ = 0 ∧ ν = 2) ∨ (μ = 1 ∧ ν = 2) := by decide
  rcases key μ ν h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [holCos_of_eq_cartan (holonomy_layer_01 c t x h)]
    simp [layerEps]
  · rw [holCos_of_eq_cartan (holonomy_layer_02 c t x h)]
    simp [layerEps]
  · rw [holCos_of_eq_cartan (holonomy_layer_12 c t x h)]
    simp [layerEps]

theorem holCos_neU (ell M R : ℕ) (t : ℝ) (p : PeriodicLatticePlaquette (scaleUp ell 2 (neLu M R))) :
    holCos (neU ell M R t) p = Real.cos (t * layerEps (neC ell M R) p) := holCos_layer _ t p

open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.Balaban.NormalizationAudit

/-- on sigma_3-valued bond fields the covariant curl of a Cartan configuration is the flat curl. -/
theorem curl_sigma3_flat {L : PeriodicLatticeExtent}
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L} (hU : CartanCfg U)
    (A : Bond L → SuTwo) (hA : ∀ b, diagP (A b) = A b) (p : PeriodicLatticePlaquette L) :
    curlValueCovariant U A p = curlValueCovariant (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) A p := by
  have hR : ∀ (V : Matrix.specialUnitaryGroup (Fin 2) ℂ), IsCartan V → ∀ b, RMap V (A b) = A b := by
    intro V hV b
    have := RMap_diagP hV (A b)
    rwa [hA b] at this
  simp only [curlValueCovariant, hR _ (hU _), RMap_one, LinearMap.id_apply]

/-- **the genuine `<A, Delta_k A>` on the sigma_3 block along the Cartan layer path**: the flat plaquette form with weight
`cos (t * layerEps)`, i.e. `cos t` on the (0,1)-plaquettes at `x_0 = c - 1` and `x_0 = c`, and `1` elsewhere. -/
theorem delta_sigma3_neU (ell M R : ℕ) (t : ℝ) (A : Bond (scaleUp ell 2 (neLu M R)) → SuTwo)
    (hA : ∀ b, diagP (A b) = A b) :
    deltaKQuadFormNormalizedCorrected (neU ell M R t) A =
      ∑ p : PeriodicLatticePlaquette (scaleUp ell 2 (neLu M R)),
        Real.cos (t * layerEps (neC ell M R) p) *
          hsInner (curlValueCovariant (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) A p)
            (curlValueCovariant (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) A p) := by
  rw [delta_sigma3_form (neU_cartan ell M R t) A hA]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [holCos_neU, curl_sigma3_flat (neU_cartan ell M R t) A hA]

#print axioms cartan_zero
#print axioms cartan_mul
#print axioms cartan_inv
#print axioms holCos_of_eq_cartan
#print axioms holonomy_layer_01
#print axioms holonomy_layer_02
#print axioms holonomy_layer_12
#print axioms layerEps
#print axioms holCos_layer
#print axioms holCos_neU
#print axioms curl_sigma3_flat
#print axioms delta_sigma3_neU

end AdalyFormal.CoverJacobi
