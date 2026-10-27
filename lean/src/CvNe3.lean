import CvNe2

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
open AdalyFormal.CoverStrong (P428Target8NCWDH)
open AdalyFormal.CoverFinish (PoleAt not_WDH_of_poles)
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
noncomputable def neU (ell M R : ℕ) (t : ℝ) : LinkCfg (scaleUp ell 2 (neLu M R)) := layerCfg (neC ell M R) (cartan t)

/-! ## the remaining condition -/

/-- **a pole with nonzero residue of the printed form along the explicit layer path on the nested instance.** -/
def LayerPoleAt (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  ∃ (Bt : Bond (neLu M R) → SuTwo) (d p r : ℝ → ℝ) (t₀ δ : ℝ),
    OnLambdaTildeIn (neLam M R) ell Bt ∧ OnLambdaT (neLam M R) Bt ∧
    ContinuousAt d t₀ ∧ d t₀ = 0 ∧ ContinuousAt p t₀ ∧ p t₀ ≠ 0 ∧ ContinuousAt r t₀ ∧
    (∀ ε : ℝ, 0 < ε → (∃ t : ℝ, |t - t₀| < ε ∧ d t < 0) ∧ (∃ t : ℝ, |t - t₀| < ε ∧ 0 < d t)) ∧
    0 < δ ∧ ∀ t : ℝ, |t - t₀| < δ → d t ≠ 0 →
      GenP.WellDefG (gparams ell 2 (neLu M R) hell (neS ell M R) (neU ell M R t) a (neLam M R)) ∧
      GenP.genForm (gparams ell 2 (neLu M R) hell (neS ell M R) (neU ell M R t) a (neLam M R))
        (WithLp.toLp 2 (GenP.genC (gparams ell 2 (neLu M R) hell (neS ell M R) (neU ell M R t) a (neLam M R)) Bt))
          = p t / d t + r t

/-- the class and geometry clauses of `PoleAt` are discharged on the nested family. -/
theorem poleAt_of_layerPole {ell M R : ℕ} (hell3 : 3 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R)
    {hell : 0 < ell} {a : ℝ} (h : LayerPoleAt ell M R hell a) : PoleAt ell M R hell a := by
  obtain ⟨Bt, d, p, r, t₀, δ, h1, h2, hd, hd0, hp, hp0, hr, hboth, hδ, hpath⟩ := h
  refine ⟨2, by norm_num, neLu M R, torusOK_ne hell3 hdvd hM, neS ell M R, ne_admissible hell3 hM hR, neLam M R,
    lambdaOK2_ne hell3 hdvd hM hR, neU ell M R, Bt, d, p, r, t₀, δ, h1, h2, hd, hd0, hp, hp0, hr, hboth, hδ,
    fun t ht hdt => ⟨fun α hα => ne_layer_class hell3 hM hR _ hα, (hpath t ht hdt).1, (hpath t ht hdt).2⟩⟩

/-- **layer poles for infinitely many `m` and, for each, infinitely many `R` refute `P428Target8NCWDH`.** -/
theorem not_WDH_of_layer_poles (ell : ℕ) (hell : 3 ≤ ell) (a : ℝ) (ha : 0 < a)
    (h : ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ LayerPoleAt ell (ell ^ m) R (by omega) a) :
    ¬ P428Target8NCWDH := by
  refine not_WDH_of_poles ell (by omega) a ha (fun m₀ => ?_)
  obtain ⟨m, hm, hR⟩ := h (max m₀ 1)
  refine ⟨m, le_trans (le_max_left _ _) hm, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hP⟩ := hR (max R₀ 1)
  have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
  have hM : 0 < ell ^ m := pow_pos (by omega) m
  have hdvd : ell ∣ ell ^ m := dvd_pow_self ell (by omega)
  exact ⟨R, le_trans (le_max_left _ _) hRR,
    poleAt_of_layerPole hell hdvd hM (le_trans (le_max_right _ _) hRR) hP⟩

/-- `coverage_necessary_strong`, conditional on layer poles. -/
theorem coverage_necessary_strong_of_layer_poles (ell : ℕ) (hell : 3 ≤ ell) (a : ℝ) (ha : 0 < a)
    (h : ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ LayerPoleAt ell (ell ^ m) R (by omega) a) :
    AdalyFormal.StatementLaneG.P428Target8 ∧ ¬ P428Target8NCWDH :=
  ⟨AdalyFormal.M2RightInv.p428Target8, not_WDH_of_layer_poles ell hell a ha h⟩

/-! ## the record of the family -/

/-- **the nested instance in the headline regime** (`k = 2`, every `ell ≥ 3`, `m ≥ 1`, `R ≥ 1`, `M = ell^m`): torus, admissible tower,
`Λ ≠ ∅` with `LambdaOK2`, a nonzero `B̃ ∈ Λ̃`; a layer `x₀ = c` of sites of `Ω₂` (thin component) and `Ω₀`, in NO factor-12 class
cube, whose plaquettes `(x;0,1)` are read by the operators; the layer configuration is in the class for EVERY `v ∈ SU(2)` and every
`α₀ > 0`; and the sites between the thin and the fat `Ω₂` components (a nonempty `x₀`-range) are level-1 sites (`Ω₁ \ Ω₂`). -/
theorem nested_instance {ell m R : ℕ} (hell : 3 ≤ ell) (hm : 1 ≤ m) (hR : 1 ≤ R) :
    TorusOK ell (ell ^ m) (neLu (ell ^ m) R) ∧ Admissible ell (ell ^ m) R 2 (neS ell (ell ^ m) R) ∧
    LambdaOK2 ell (ell ^ m) R 2 (neS ell (ell ^ m) R) (neLam (ell ^ m) R) ∧ (neLam (ell ^ m) R).Nonempty ∧
    (∃ Bt : Bond (neLu (ell ^ m) R) → SuTwo, OnLambdaTildeIn (neLam (ell ^ m) R) ell Bt ∧
      OnLambdaT (neLam (ell ^ m) R) Bt ∧ 0 < bondEnergy Bt) ∧
    (∀ x : PeriodicLatticeSite (scaleUp ell 2 (neLu (ell ^ m) R)), (x 0).val = neC ell (ell ^ m) R →
      x ∈ (neS ell (ell ^ m) R).Om 2 ∧ x ∈ (neS ell (ell ^ m) R).Om 0 ∧
      (∀ (sites : Set (PeriodicLatticeSite (scaleUp ell 2 (neLu (ell ^ m) R)))) (j : ℕ),
        IsClassCube ell (ell ^ m) 12 2 (neS ell (ell ^ m) R) sites j → x ∉ sites) ∧
      pStar x ∈ plaqIn ((neS ell (ell ^ m) R).Om 0)) ∧
    (∀ (v : Matrix.specialUnitaryGroup (Fin 2) ℂ) (α₀ : ℝ), 0 < α₀ →
      PerCubeRegular2 ell (ell ^ m) 12 2 (neS ell (ell ^ m) R) α₀ ((ell : ℝ) ^ 2)⁻¹ (layerCfg (neC ell (ell ^ m) R) v)) ∧
    neB' ell (ell ^ m) R < neA ell (ell ^ m) R ∧
    (∀ x : PeriodicLatticeSite (scaleUp ell 2 (neLu (ell ^ m) R)),
      neB' ell (ell ^ m) R ≤ (x 0).val ∧ (x 0).val < neA ell (ell ^ m) R →
      x ∈ (neS ell (ell ^ m) R).Om 1 ∧ x ∉ (neS ell (ell ^ m) R).Om 2) := by
  have hM : 0 < ell ^ m := pow_pos (by omega) m
  have hdvd : ell ∣ ell ^ m := dvd_pow_self ell (by omega)
  obtain ⟨Bp1, Bp2, Bp3, -⟩ := BseedNe_props (R := R) hell hdvd hM
  refine ⟨torusOK_ne hell hdvd hM, ne_admissible hell hM hR, lambdaOK2_ne hell hdvd hM hR, neLam_nonempty hM,
    ⟨_, Bp1, Bp2, Bp3⟩, fun x hx => ⟨(ne_layer_mem hell hM hR x hx).1, (ne_layer_mem hell hM hR x hx).2,
      fun sites j hq => ne_layer_uncovered hell hM hR x hx sites j hq, ne_layer_plaqIn hell hM hR x hx⟩,
    fun v α₀ hα => ne_layer_class hell hM hR v hα, ne_gap_pos hell hM hR, fun x hx => ne_between_level1 hell hM hR x hx⟩

#print axioms cartanM_mem
#print axioms poleAt_of_layerPole
#print axioms not_WDH_of_layer_poles
#print axioms coverage_necessary_strong_of_layer_poles
#print axioms nested_instance

end AdalyFormal.CoverNested
