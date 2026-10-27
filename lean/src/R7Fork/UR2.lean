import R7Fork.UR1
import R7Fork.ZT5A
import R7Fork.ZT5C
import R7Fork.ZT5D2
import R7Fork.ZT6B
import R7Fork.DM14

/-!
# UR2 -- STATEMENT DEFECT: the frozen conclusion `genForm (C B̃)` reads `U` outside `Ω₀`, and the frozen headline
`P428Genuine6 2 2 6` is FALSE for every mass `a > 0`.

Tower `TT` (r7 witness: `k = 1`, `ell = 2`, `M = 2`, `R = 6`, fine torus `120³`, `Ω₀ = {8 ≤ x₀ < 112}`,
`Ω₁ = {20 ≤ x₀ < 100}`), `Λ = LamT`.  `Ubad = cfg1 (−1)`: `−1` on the ONE bond `b1 = (0, e₀)` (both endpoints at
`x₀ ∈ {0,1}`, outside `Ω₀`, so not class-constrained), `1` on every other bond.
* `Ubad` is in the class `ClassCoupled 2 2 12 1 TT α₀ (1/2)` for every `α₀ > 0` (`classCoupled_bad`: it agrees with
  `U = 1` on every bond with both endpoints in `Ω₀`; `perCubeRegular2_congr`).
* `QlinCompX` at level 1 is the junk `0` (`UR1.QlinStepX_bad_eq_zero`), so the level-1 rows of `Q` vanish, `N = QG₁Q*`
  is not a unit (`Nmat_bad_not_unit`), `Ring.inverse N = 0`, `firstTerm = 0`, `H₁ = 0`, and
  `genForm B = −a⟪B,B⟫` for EVERY `B` (`genForm_bad`).
* hence `InstIneq` fails at `Ubad` for every `γ₀ > 0` (`instIneq_bad_false`) and `¬ P428Genuine6 2 2 6 _ a`
  (`not_P428Genuine6_TT`).
* LOCALITY FAILS: `U = 1` and `Ubad` agree off the single bond `b1` (outside `Ω₀`), both are in the class, and at the
  same `B̃` the flat value is `≥ ‖B̃‖²/1728 > 0` (`DirichletMono.tt_instIneq`) while the bad value is `≤ 0`
  (`genForm_not_local`); `WellDef` holds at `U = 1` (`DirichletMono.proper_wellDef`) and fails at `Ubad`
  (`wellDef_not_local`).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace AdalyFormal.URLocality

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

/-- the unit torus of the witness: `60³` -/
abbrev Lu60 : PeriodicLatticeExtent := fun _ => 59

theorem hLu60 : ∀ μ, Lu60 μ + 1 = 60 := fun _ => rfl

theorem scale_eq : scaleUp 2 1 Lu60 = L0 := by
  funext μ; rfl

/-- the bad configuration: `−1` on `b1 = (0, e₀)`, `1` elsewhere -/
noncomputable def Ubad : LinkCfg (scaleUp 2 1 Lu60) := cfg1 su2NegOne

/-! ## 1. the level-1 jet is junk -/

theorem QlinCompX_one_bad (S : Tower (scaleUp 2 1 Lu60)) :
    QlinCompX (geomOf 2 1 S).ell (bgTower (geomOf 2 1 S) Ubad) 1 = 0 := by
  show fderiv ℝ (qStepX (2 ^ 0) 2 Ubad ∘ id) 0 = 0
  rw [Function.comp_id, pow_zero]
  exact QlinStepX_bad_eq_zero scale_eq

theorem QlinB_one_bad (S : Tower (scaleUp 2 1 Lu60)) : QlinB (geomOf 2 1 S) Ubad 1 = 0 := by
  ext1 A
  rw [QlinB_apply, QlinCompX_one_bad]
  simp

/-! ## 2. a level-1 bond of `𝔅` on `TT` -/

/-- the fine site `(20, 0, 0)` -/
def s20 : PeriodicLatticeSite (scaleUp 2 1 Lu60) := fun μ => if μ = 0 then 20 else 0

theorem s20_props : (∀ μ : Fin 3, 2 ^ 1 ∣ (s20 μ).val) ∧ 20 ≤ (s20 0).val ∧ (s20 0).val < 100 := by decide

theorem b20_mem : ((s20, 0) : Bond (scaleUp 2 1 Lu60)) ∈ bondsLam (geomOf 2 1 (TT (scaleUp 2 1 Lu60))) 1 := by
  refine ⟨Or.inl ⟨s20_props.1, ?_, ?_⟩, ?_⟩
  · show s20 ∈ (TT (scaleUp 2 1 Lu60)).Om 1
    simp only [TT, OmB]
    exact ⟨s20_props.2.1, s20_props.2.2⟩
  · show s20 ∉ (TT (scaleUp 2 1 Lu60)).Om 2
    simp [TT]
  · rintro (h | h) <;> exact not_OmGe_of_lt (G := geomOf 2 1 (TT (scaleUp 2 1 Lu60))) (by show 1 < 2; omega) _ h

/-- the level-1 index `(1, (s20, e₀))` of `𝔅` -/
def p1 : BIdx (geomOf 2 1 (TT (scaleUp 2 1 Lu60))) := ⟨⟨1, by show 1 < 1 + 1; omega⟩, ⟨(s20, 0), b20_mem⟩⟩

/-! ## 3. `N = QG₁Q*` is not a unit at `Ubad`, `genForm = −a‖B‖²` -/

/-- the parameters of the counterexample -/
noncomputable abbrev Pbad (a : ℝ) : IngrBParams :=
  gparams 2 1 Lu60 (by norm_num) (TT (scaleUp 2 1 Lu60)) Ubad a (LamT Lu60)

theorem Qs_kills_p1 (a : ℝ) :
    (Pbad a).data.Qs (WithLp.toLp 2 (Pi.single p1 suTwoWitness)) = 0 := by
  refine ext_inner_left ℝ (fun x => ?_)
  rw [inner_zero_right]
  show ⟪x, ContinuousLinearMap.adjoint ((QfullOf (Pbad a).G Ubad).comp (iE (Pbad a).G))
      (WithLp.toLp 2 (Pi.single p1 suTwoWitness))⟫ = 0
  rw [ContinuousLinearMap.adjoint_inner_right, PiLp.inner_apply]
  rw [Finset.sum_eq_single p1]
  · show ⟪(((2 : ℕ) : ℝ) ^ (1 : ℕ))⁻¹ • (WithLp.ofLp (QlinB (Pbad a).G Ubad 1 (iE (Pbad a).G x))) (s20, 0),
        (Pi.single p1 suTwoWitness : BIdx _ → SuTwo) p1⟫ = 0
    rw [QlinB_one_bad]
    simp
  · intro p _ hp
    simp [Pi.single_apply, hp]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem Nmat_bad_not_unit (a : ℝ) : ¬ IsUnit (GenP.Nmat (Pbad a)) := by
  intro hu
  have hinj := (ContinuousLinearMap.isUnit_iff_bijective.mp hu).1
  have h0 : GenP.Nmat (Pbad a) (WithLp.toLp 2 (Pi.single p1 suTwoWitness)) = GenP.Nmat (Pbad a) 0 := by
    rw [map_zero]
    show ((Pbad a).data.Q.comp ((Pbad a).data.G1 (Pbad a).G1inv)) ((Pbad a).data.Qs _) = 0
    rw [Qs_kills_p1, map_zero]
  have := congrArg (fun f : FSp (Pbad a).G => (WithLp.ofLp f) p1) (hinj h0)
  simp at this
  exact suTwoWitness_ne_zero this

theorem genForm_bad (a : ℝ) (B : BondFnL2 Lu60) : GenP.genForm (Pbad a) B = -a * ⟪B, B⟫ := by
  have hinv : Ring.inverse (GenP.Nmat (Pbad a)) = 0 := Ring.inverse_non_unit _ (Nmat_bad_not_unit a)
  have hH : (Pbad a).H1in = 0 := by
    show (iE (Pbad a).G).comp (((Pbad a).data.H1 (Pbad a).G1inv).comp (ContinuousLinearMap.adjoint (Pbad a).tau)) = 0
    have : (Pbad a).data.H1 (Pbad a).G1inv
        = (((Pbad a).data.G1 (Pbad a).G1inv).comp (Pbad a).data.Qs).comp (Ring.inverse (GenP.Nmat (Pbad a))) := rfl
    rw [this, hinv]
    simp
  unfold GenP.genForm GenP.firstTerm
  rw [hinv, hH]
  simp

/-! ## 4. the class, the failure of `InstIneq`, and the refutation of the headline at `(2,2,6)` -/

theorem Ubad_off_b1 (e : Bond (scaleUp 2 1 Lu60)) (he : e ≠ b1) : Ubad e = flatCfg e := by
  show (if e = b1 then su2NegOne else 1) = 1
  rw [if_neg he]

theorem b1_not_cube : ¬ CubeBond ((TT (scaleUp 2 1 Lu60)).Om 0) (b1 : Bond (scaleUp 2 1 Lu60)) := by
  rintro ⟨h1, -⟩
  simp only [TT, OmA, if_pos] at h1
  exact absurd h1.1 (by decide)

theorem classCoupled_bad {α₀ : ℝ} (hα : 0 < α₀) :
    ClassCoupled 2 2 12 1 (TT (scaleUp 2 1 Lu60)) α₀ (((2 : ℕ) : ℝ) ^ 1)⁻¹ Ubad := by
  obtain ⟨-, -, -, hadm, -, -, -⟩ := AdalyFormal.DirichletMono.tt_hypotheses hLu60
  refine ⟨TT2_coversp (AdalyFormal.DirichletMono.tt_fine_extent hLu60), ?_⟩
  refine perCubeRegular2_congr hadm.1 (U := flatCfg) (fun e he => ?_)
    (flat_perCubeRegular2cG 2 2 12 1 (by norm_num) (by norm_num) (by norm_num) hα _)
  have hne : e ≠ b1 := by rintro rfl; exact b1_not_cube he
  exact (Ubad_off_b1 e hne).symm

theorem classCoupled_flat {α₀ : ℝ} (hα : 0 < α₀) :
    ClassCoupled 2 2 12 1 (TT (scaleUp 2 1 Lu60)) α₀ (((2 : ℕ) : ℝ) ^ 1)⁻¹ flatCfg :=
  ⟨TT2_coversp (AdalyFormal.DirichletMono.tt_fine_extent hLu60),
    flat_perCubeRegular2cG 2 2 12 1 (by norm_num) (by norm_num) (by norm_num) hα _⟩

theorem instIneq_bad_false {a γ₀ : ℝ} (ha : 0 < a) (hγ : 0 < γ₀) :
    ¬ InstIneq 2 1 (by norm_num) a Lu60 γ₀ (TT (scaleUp 2 1 Lu60)) (LamT Lu60) Ubad := by
  intro h
  obtain ⟨-, -, -, -, -, -, ⟨Bt, h1, h2, hE⟩⟩ := AdalyFormal.DirichletMono.tt_hypotheses hLu60
  have hI := h Bt h1 h2
  have hg := genForm_bad a (WithLp.toLp 2 (GenP.genC (Pbad a) Bt))
  have hpos : 0 ≤ ⟪(WithLp.toLp 2 (GenP.genC (Pbad a) Bt) : BondFnL2 Lu60), WithLp.toLp 2 (GenP.genC (Pbad a) Bt)⟫ :=
    real_inner_self_nonneg
  have : GenP.genForm (gparams 2 1 Lu60 (by norm_num) (TT (scaleUp 2 1 Lu60)) Ubad a (LamT Lu60))
      (WithLp.toLp 2 (GenP.genC (gparams 2 1 Lu60 (by norm_num) (TT (scaleUp 2 1 Lu60)) Ubad a (LamT Lu60)) Bt)) ≤ 0 := by
    show GenP.genForm (Pbad a) _ ≤ 0
    rw [hg]; nlinarith
  nlinarith [mul_pos hγ hE]

/-- **THE FROZEN HEADLINE IS FALSE AT `(ell, M, R) = (2, 2, 6)` FOR EVERY MASS `a > 0`.** -/
theorem not_P428Genuine6_TT (a : ℝ) (ha : 0 < a) : ¬ P428Genuine6 2 2 6 (by norm_num) a := by
  rintro ⟨-, a₀, ha₀, γ₀, hγ₀, h⟩
  have hα : 0 < a₀ / 24 := by positivity
  have hc := h 1 le_rfl Lu60 (a₀ / 24) hα (by push_cast; linarith)
  obtain ⟨-, -, -, hadm, hLam, -, -⟩ := AdalyFormal.DirichletMono.tt_hypotheses hLu60
  exact instIneq_bad_false ha hγ₀ (hc (torusOK_60_M2 hLu60) _ hadm _ hLam Ubad (classCoupled_bad hα))

/-- **LOCALITY FAILS.** Two class configurations that agree on every bond except ONE bond with no endpoint in `Ω₀`
give different values of the frozen conclusion at the same `B̃ ∈ Λ̃`. -/
theorem genForm_not_local {a : ℝ} (ha : 0 < a) :
    (∀ e : Bond (scaleUp 2 1 Lu60), e ≠ b1 → Ubad e = flatCfg e) ∧
    (b1 : Bond (scaleUp 2 1 Lu60)).1 ∉ (TT (scaleUp 2 1 Lu60)).Om 0 ∧
    periodicLatticeShift (b1 : Bond (scaleUp 2 1 Lu60)).1 (b1 : Bond (scaleUp 2 1 Lu60)).2 ∉ (TT (scaleUp 2 1 Lu60)).Om 0 ∧
    (∀ α₀ : ℝ, 0 < α₀ → ClassCoupled 2 2 12 1 (TT (scaleUp 2 1 Lu60)) α₀ (((2 : ℕ) : ℝ) ^ 1)⁻¹ Ubad ∧
       ClassCoupled 2 2 12 1 (TT (scaleUp 2 1 Lu60)) α₀ (((2 : ℕ) : ℝ) ^ 1)⁻¹ flatCfg) ∧
    ∃ Bt : Bond Lu60 → SuTwo, OnLambdaTildeIn (LamT Lu60) 2 Bt ∧ OnLambdaT (LamT Lu60) Bt ∧
      GenP.genForm (gparams 2 1 Lu60 (by norm_num) (TT (scaleUp 2 1 Lu60)) Ubad a (LamT Lu60))
          (WithLp.toLp 2 (GenP.genC (gparams 2 1 Lu60 (by norm_num) (TT (scaleUp 2 1 Lu60)) Ubad a (LamT Lu60)) Bt))
        < GenP.genForm (gparams 2 1 Lu60 (by norm_num) (TT (scaleUp 2 1 Lu60)) flatCfg a (LamT Lu60))
          (WithLp.toLp 2 (GenP.genC (gparams 2 1 Lu60 (by norm_num) (TT (scaleUp 2 1 Lu60)) flatCfg a (LamT Lu60)) Bt)) := by
  refine ⟨Ubad_off_b1, ?_, ?_, fun α₀ hα => ⟨classCoupled_bad hα, classCoupled_flat hα⟩, ?_⟩
  · simp only [TT, OmA, if_pos]; decide
  · simp only [TT, OmA, if_pos]; decide
  · obtain ⟨-, -, -, -, -, -, ⟨Bt, h1, h2, hE⟩⟩ := AdalyFormal.DirichletMono.tt_hypotheses hLu60
    refine ⟨Bt, h1, h2, ?_⟩
    have hflat := AdalyFormal.DirichletMono.tt_instIneq hLu60 (by norm_num) a ha Bt h1 h2
    have hg := genForm_bad a (WithLp.toLp 2 (GenP.genC (Pbad a) Bt))
    have hpos : 0 ≤ ⟪(WithLp.toLp 2 (GenP.genC (Pbad a) Bt) : BondFnL2 Lu60), WithLp.toLp 2 (GenP.genC (Pbad a) Bt)⟫ :=
      real_inner_self_nonneg
    have hb : GenP.genForm (Pbad a) (WithLp.toLp 2 (GenP.genC (Pbad a) Bt)) ≤ 0 := by rw [hg]; nlinarith
    have : 0 < (1 / 1728 : ℝ) * bondEnergy Bt := mul_pos (by norm_num) hE
    exact lt_of_le_of_lt hb (lt_of_lt_of_le this hflat)

/-- `WellDef` (invertibility of `H₀`, `G₁⁻¹`, `N`) is not local either. -/
theorem wellDef_not_local {a : ℝ} (ha : 0 < a) :
    GenP.WellDef (gparams 2 1 Lu60 (by norm_num) (TT (scaleUp 2 1 Lu60)) flatCfg a (LamT Lu60)) ∧
    ¬ GenP.WellDef (gparams 2 1 Lu60 (by norm_num) (TT (scaleUp 2 1 Lu60)) Ubad a (LamT Lu60)) := by
  obtain ⟨h4, hd, hRM, hadm, -, -, -⟩ := AdalyFormal.DirichletMono.tt_hypotheses hLu60
  exact ⟨AdalyFormal.DirichletMono.proper_wellDef h4 hd hRM (by norm_num) a ha _ hadm _,
    fun h => Nmat_bad_not_unit a h.2.2⟩

#print axioms QlinB_one_bad
#print axioms Nmat_bad_not_unit
#print axioms genForm_bad
#print axioms classCoupled_bad
#print axioms instIneq_bad_false
#print axioms not_P428Genuine6_TT
#print axioms genForm_not_local
#print axioms wellDef_not_local

end AdalyFormal.URLocality
