import CvD3
import CvR4

/-!
# CvO1 -- the STAGGERED layer: alternating-sign Cartan angle on the layer links (lane omega, route Omega)

`stagCfg c t`: the direction-1 bond based at `x₀ = c`, transverse position `x₁`, carries `cartan (s(x₁) t)` with `s(x₁) = +1` for
even `x₁`, `-1` for odd `x₁`; every other bond is `1`.  (Contrast `layerCfg c (cartan t)`: the same angle `t` for all `x₁`.)

* the (0,1)-plaquettes at `x₀ = c-1` and `x₀ = c` have holonomy `cartan (± t)`, hence `holCos = cos t` UNIFORMLY (cos is even):
  the `σ₃` block of `Δ_k` is the SAME flat plaquette form with weight `cos t` as for the uniform layer (CvD3);
* the (0,2)- and (1,2)-plaquettes are flat;
* class membership is proved exactly as for the uniform layer (`perCube_congr`: the class reads `U` only on class-cube bonds);
* it is a Cartan configuration.

NOT here: the loop-angle bound that makes the tower analytic in `t` (numerics: lane NOTES, `o2_stag`).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega

open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.NoCover (perCube_one)
open AdalyFormal.Balaban.DeltaPrime

/-- `+1` for even transverse coordinate `x₁`, `-1` for odd. -/
def stagSign {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) : ℝ :=
  if (x 1).val % 2 = 0 then 1 else -1

theorem stagSign_cases {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) : stagSign x = 1 ∨ stagSign x = -1 := by
  unfold stagSign; split_ifs <;> simp

theorem stagSign_shift {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) (μ : Fin 3) (hμ : μ ≠ 1) :
    stagSign (periodicLatticeShift x μ) = stagSign x := by
  unfold stagSign
  have : (periodicLatticeShift x μ) 1 = x 1 := by
    simp [periodicLatticeShift, Function.update_of_ne (Ne.symm hμ)]
  rw [this]

/-- the staggered layer configuration. -/
noncomputable def stagCfg {L : PeriodicLatticeExtent} (c : ℕ) (t : ℝ) : LinkCfg L :=
  fun e => if (e.1 0).val = c ∧ e.2 = 1 then cartan (stagSign e.1 * t) else 1

theorem stagCfg_cartan {L : PeriodicLatticeExtent} (c : ℕ) (t : ℝ) : CartanCfg (stagCfg (L := L) c t) := by
  intro e
  unfold stagCfg
  split_ifs
  · exact cartan_isCartan _
  · unfold IsCartan; simp

/-- the explicit staggered path on the nested instance. -/
noncomputable def stagU (ell M R : ℕ) (t : ℝ) : LinkCfg (scaleUp ell 2 (neLu M R)) := stagCfg (neC ell M R) t

theorem stagU_cartan (ell M R : ℕ) (t : ℝ) : CartanCfg (stagU ell M R t) := stagCfg_cartan _ t

theorem stagCfg_zero {L : PeriodicLatticeExtent} (c : ℕ) :
    stagCfg (L := L) c 0 = fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  funext e; unfold stagCfg; split_ifs
  · rw [mul_zero]; exact cartan_zero
  · rfl

/-- **the staggered layer is in the factor-12 class for every `t` and every `α₀ > 0`** (the class reads `U` only on class-cube bonds). -/
theorem ne_stag_class {ell M R : ℕ} (hell : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) (t : ℝ) {α₀ : ℝ} (hα : 0 < α₀) :
    PerCubeRegular2 ell M 12 2 (neS ell M R) α₀ ((ell : ℝ) ^ 2)⁻¹ (stagU ell M R t) := by
  have hη : (0 : ℝ) < ((ell : ℝ) ^ 2)⁻¹ := by
    have : (0 : ℝ) < ell := by exact_mod_cast (show 0 < ell by omega)
    positivity
  refine perCube_congr (perCube_one (by omega) hM (by norm_num) hα hη) (fun e he => ?_)
  obtain ⟨sites, j, hq, hes⟩ := he
  have hne : (e.1 0).val ≠ neC ell M R := fun h => ne_layer_uncovered hell hM hR e.1 h sites j hq hes
  simp [stagU, stagCfg, hne]

/-! ## plaquette holonomies -/

/-- (0,1)-plane: `cartan (± t · layerEps)`. -/
theorem holonomy_stag_01 {L : PeriodicLatticeExtent} (c : ℕ) (t : ℝ) (x : PeriodicLatticeSite L)
    (h : ((0 : Fin 3), (1 : Fin 3)).1 < ((0 : Fin 3), (1 : Fin 3)).2) :
    holonomyElem (stagCfg (L := L) c t) (x, ⟨((0 : Fin 3), (1 : Fin 3)), h⟩) =
      cartan (stagSign x * (t * ((if ((periodicLatticeShift x 0) 0).val = c then 1 else 0) - (if (x 0).val = c then 1 else 0)))) := by
  unfold holonomyElem periodicPlaquetteHolonomy stagCfg
  have e1 : stagSign (periodicLatticeShift x 0) = stagSign x := stagSign_shift x 0 (by decide)
  by_cases h1 : ((periodicLatticeShift x 0) 0).val = c <;> by_cases h2 : (x 0).val = c <;>
    simp [h1, h2, e1, cartan_inv, cartan_mul, cartan_zero, mul_sub, mul_add, sub_eq_add_neg]

theorem holonomy_stag_02 {L : PeriodicLatticeExtent} (c : ℕ) (t : ℝ) (x : PeriodicLatticeSite L)
    (h : ((0 : Fin 3), (2 : Fin 3)).1 < ((0 : Fin 3), (2 : Fin 3)).2) :
    holonomyElem (stagCfg (L := L) c t) (x, ⟨((0 : Fin 3), (2 : Fin 3)), h⟩) = cartan 0 := by
  unfold holonomyElem periodicPlaquetteHolonomy stagCfg
  simp [cartan_zero]

theorem holonomy_stag_12 {L : PeriodicLatticeExtent} (c : ℕ) (t : ℝ) (x : PeriodicLatticeSite L)
    (h : ((1 : Fin 3), (2 : Fin 3)).1 < ((1 : Fin 3), (2 : Fin 3)).2) :
    holonomyElem (stagCfg (L := L) c t) (x, ⟨((1 : Fin 3), (2 : Fin 3)), h⟩) = cartan 0 := by
  unfold holonomyElem periodicPlaquetteHolonomy stagCfg
  have e : (periodicLatticeShift x 2) 0 = x 0 := by
    simp [periodicLatticeShift]
  have e1 : stagSign (periodicLatticeShift x 2) = stagSign x := stagSign_shift x 2 (by decide)
  by_cases h2 : (x 0).val = c <;> simp [e, e1, h2, cartan_zero]

/-- **every plaquette weight along the staggered path is `cos (t * layerEps)`: the same weights as the uniform layer.** -/
theorem holCos_stag {L : PeriodicLatticeExtent} (c : ℕ) (t : ℝ) (p : PeriodicLatticePlaquette L) :
    holCos (stagCfg (L := L) c t) p = Real.cos (t * layerEps c p) := by
  obtain ⟨x, ⟨⟨μ, ν⟩, h⟩⟩ := p
  have key : ∀ (μ ν : Fin 3), μ < ν → (μ = 0 ∧ ν = 1) ∨ (μ = 0 ∧ ν = 2) ∨ (μ = 1 ∧ ν = 2) := by decide
  rcases key μ ν h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [holCos_of_eq_cartan (holonomy_stag_01 c t x h)]
    rcases stagSign_cases x with hs | hs <;> rw [hs] <;> simp [layerEps, Real.cos_neg]
  · rw [holCos_of_eq_cartan (holonomy_stag_02 c t x h)]
    simp [layerEps]
  · rw [holCos_of_eq_cartan (holonomy_stag_12 c t x h)]
    simp [layerEps]

theorem holCos_stagU (ell M R : ℕ) (t : ℝ) (p : PeriodicLatticePlaquette (scaleUp ell 2 (neLu M R))) :
    holCos (stagU ell M R t) p = Real.cos (t * layerEps (neC ell M R) p) := holCos_stag _ t p

open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.Balaban.NormalizationAudit

/-- **the genuine `<A, Δ_k A>` on the σ₃ block along the STAGGERED path**: identical to the uniform layer (CvD3 `delta_sigma3_neU`). -/
theorem delta_sigma3_stagU (ell M R : ℕ) (t : ℝ) (A : Bond (scaleUp ell 2 (neLu M R)) → SuTwo)
    (hA : ∀ b, diagP (A b) = A b) :
    deltaKQuadFormNormalizedCorrected (stagU ell M R t) A =
      deltaKQuadFormNormalizedCorrected (neU ell M R t) A := by
  rw [delta_sigma3_form (stagU_cartan ell M R t) A hA, delta_sigma3_neU ell M R t A hA]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [holCos_stagU, curl_sigma3_flat (stagU_cartan ell M R t) A hA]

#print axioms stagSign_cases
#print axioms stagSign_shift
#print axioms stagCfg_cartan
#print axioms stagCfg_zero
#print axioms ne_stag_class
#print axioms holonomy_stag_01
#print axioms holonomy_stag_02
#print axioms holonomy_stag_12
#print axioms holCos_stag
#print axioms holCos_stagU
#print axioms delta_sigma3_stagU

end AdalyFormal.CoverOmega
