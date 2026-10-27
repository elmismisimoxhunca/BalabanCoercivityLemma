import NsCvNe2

/-!
# CvNe3 -- the remaining condition, made explicit: a pole along ONE explicit path on ONE explicit family (lane cover_nested_20261016)

* `cartan t = diag(e^{it}, e^{-it}) = exp(i t σ₃) ∈ SU(2)`; `neU ell M R t = layerCfg c (cartan t)`: the Cartan angle `t` on every
  direction-1 bond of the uncovered layer of the nested instance (CvNe2), `1` elsewhere.
* `LayerPoleAt ell M R hell a`: along `t ↦ neU ell M R t` on the nested instance `(neLu, neS, neLam)`, some admissible `B̃` has
  `⟨C B̃, Δ_k C B̃⟩ = p t / d t + r t` near `t₀` (where `d t ≠ 0`), with `d t₀ = 0`, `d` changing sign at `t₀`, `p t₀ ≠ 0`, `d, p, r`
  continuous at `t₀`, and every printed object existing (`WellDefG`) at those `t`.  NO class-membership or geometry clause: both are
  PROVED for the family (CvNe2).
* `poleAt_of_layerPole : LayerPoleAt .. → PoleAt ..` (CvF2), hence
* **`not_WDH_of_layer_poles`**: layer poles for infinitely many `m` and, for each, infinitely many `R` (some `ell ≥ 3`, `a > 0`) refute
  `P428Target8NCWDH`; **`coverage_necessary_strong_of_layer_poles`** gives `P428Target8 ∧ ¬ P428Target8NCWDH`.
* `nested_instance`: the record of what the family satisfies, for every `ell ≥ 3`, `m ≥ 1`, `R ≥ 1`.
NOT proved: `LayerPoleAt` at any `(m, R)` (lane NOTES: numerics on a scaled-down analogue only).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000

namespace AdalyFormal.CoverNested

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2 (plaqIn)
open AdalyFormal.NoCover (pStar)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

/-! ## the Cartan element `exp(i t σ₃)` -/

noncomputable def cartanM (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![Complex.exp ((t : ℂ) * Complex.I), Complex.exp (-((t : ℂ) * Complex.I))]

theorem cartanM_mem (t : ℝ) : cartanM t ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  have hc : ∀ z : ℂ, star (Complex.exp z) = Complex.exp (star z) := fun z => (Complex.exp_conj z).symm
  have hI : star ((t : ℂ) * Complex.I) = -((t : ℂ) * Complex.I) := by
    rw [star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I]; ring
  have hI' : star (-((t : ℂ) * Complex.I)) = (t : ℂ) * Complex.I := by rw [star_neg, hI, neg_neg]
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · unfold cartanM
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i
    · show Complex.exp ((t : ℂ) * Complex.I) * star (Complex.exp ((t : ℂ) * Complex.I)) = 1
      rw [hc, hI, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    · show Complex.exp (-((t : ℂ) * Complex.I)) * star (Complex.exp (-((t : ℂ) * Complex.I))) = 1
      rw [hc, hI', ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  · unfold cartanM
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

/-- `exp(i t σ₃) ∈ SU(2)`. -/
noncomputable def cartan (t : ℝ) : Matrix.specialUnitaryGroup (Fin 2) ℂ := ⟨cartanM t, cartanM_mem t⟩

theorem cartan_coe (t : ℝ) :
    ((cartan t : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.diagonal ![Complex.exp ((t : ℂ) * Complex.I), Complex.exp (-((t : ℂ) * Complex.I))] := rfl

/-- the explicit path on the nested instance: Cartan angle `t` on the uncovered layer. -/
noncomputable def neU [CfData] (ell M R : ℕ) (t : ℝ) : LinkCfg (scaleUp ell 2 (neLu M R)) := layerCfg (neC ell M R) (cartan t)

/- [removed in the strong-NCWDH copy: LayerPoleAt / poleAt_of_layerPole / not_WDH_of_layer_poles / coverage_necessary_strong_of_layer_poles /
nested_instance (statements about the frozen factor-12 headline; not used by the staggered route)] -/

#print axioms cartanM_mem

end AdalyFormal.CoverNested
