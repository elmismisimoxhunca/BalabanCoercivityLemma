import CvO1

/-!
# CvO2 -- `StagPoleAt`: a pole with nonzero residue along the STAGGERED layer path, and its consequence (lane omega)

`StagPoleAt ell M R hell a` is `CvNe3.LayerPoleAt` with `neU` replaced by `stagU` (CvO1).  The bridge `poleAt_of_stagPole` is the copy of
`poleAt_of_layerPole` (class membership: `ne_stag_class`), and `not_WDH_of_stag_poles` / `coverage_necessary_strong_of_stag_poles`
the copies of the CvNe3 consequences.  NOT proved: `StagPoleAt` at any `(ell, m, R)`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000

namespace AdalyFormal.CoverOmega

open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.CoverStrong (P428Target8NCWDH)
open AdalyFormal.CoverFinish (PoleAt not_WDH_of_poles)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

/-- **a pole with nonzero residue of the printed form along the explicit STAGGERED layer path on the nested instance.** -/
def StagPoleAt (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  ∃ (Bt : Bond (neLu M R) → SuTwo) (d p r : ℝ → ℝ) (t₀ δ : ℝ),
    OnLambdaTildeIn (neLam M R) ell Bt ∧ OnLambdaT (neLam M R) Bt ∧
    ContinuousAt d t₀ ∧ d t₀ = 0 ∧ ContinuousAt p t₀ ∧ p t₀ ≠ 0 ∧ ContinuousAt r t₀ ∧
    (∀ ε : ℝ, 0 < ε → (∃ t : ℝ, |t - t₀| < ε ∧ d t < 0) ∧ (∃ t : ℝ, |t - t₀| < ε ∧ 0 < d t)) ∧
    0 < δ ∧ ∀ t : ℝ, |t - t₀| < δ → d t ≠ 0 →
      GenP.WellDefG (gparams ell 2 (neLu M R) hell (neS ell M R) (stagU ell M R t) a (neLam M R)) ∧
      GenP.genForm (gparams ell 2 (neLu M R) hell (neS ell M R) (stagU ell M R t) a (neLam M R))
        (WithLp.toLp 2 (GenP.genC (gparams ell 2 (neLu M R) hell (neS ell M R) (stagU ell M R t) a (neLam M R)) Bt))
          = p t / d t + r t

theorem poleAt_of_stagPole {ell M R : ℕ} (hell3 : 3 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R)
    {hell : 0 < ell} {a : ℝ} (h : StagPoleAt ell M R hell a) : PoleAt ell M R hell a := by
  obtain ⟨Bt, d, p, r, t₀, δ, h1, h2, hd, hd0, hp, hp0, hr, hboth, hδ, hpath⟩ := h
  refine ⟨2, by norm_num, neLu M R, torusOK_ne hell3 hdvd hM, neS ell M R, ne_admissible hell3 hM hR, neLam M R,
    lambdaOK2_ne hell3 hdvd hM hR, stagU ell M R, Bt, d, p, r, t₀, δ, h1, h2, hd, hd0, hp, hp0, hr, hboth, hδ,
    fun t ht hdt => ⟨fun α hα => ne_stag_class hell3 hM hR t hα, (hpath t ht hdt).1, (hpath t ht hdt).2⟩⟩

/-- staggered poles for infinitely many `m` and, for each, infinitely many `R` refute `P428Target8NCWDH`. -/
theorem not_WDH_of_stag_poles (ell : ℕ) (hell : 3 ≤ ell) (a : ℝ) (ha : 0 < a)
    (h : ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ StagPoleAt ell (ell ^ m) R (by omega) a) :
    ¬ P428Target8NCWDH := by
  refine not_WDH_of_poles ell (by omega) a ha (fun m₀ => ?_)
  obtain ⟨m, hm, hR⟩ := h (max m₀ 1)
  refine ⟨m, le_trans (le_max_left _ _) hm, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hP⟩ := hR (max R₀ 1)
  have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
  have hM : 0 < ell ^ m := pow_pos (by omega) m
  have hdvd : ell ∣ ell ^ m := dvd_pow_self ell (by omega)
  exact ⟨R, le_trans (le_max_left _ _) hRR,
    poleAt_of_stagPole hell hdvd hM (le_trans (le_max_right _ _) hRR) hP⟩

theorem coverage_necessary_strong_of_stag_poles (ell : ℕ) (hell : 3 ≤ ell) (a : ℝ) (ha : 0 < a)
    (h : ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ StagPoleAt ell (ell ^ m) R (by omega) a) :
    AdalyFormal.StatementLaneG.P428Target8 ∧ ¬ P428Target8NCWDH :=
  ⟨AdalyFormal.M2RightInv.p428Target8, not_WDH_of_stag_poles ell hell a ha h⟩

#print axioms poleAt_of_stagPole
#print axioms not_WDH_of_stag_poles
#print axioms coverage_necessary_strong_of_stag_poles

end AdalyFormal.CoverOmega
