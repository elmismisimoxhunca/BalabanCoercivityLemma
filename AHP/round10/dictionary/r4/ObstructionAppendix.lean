
/-! A genuine zero-jet charged vector in every canonical geometry. It is NOT a crossing vector. -/
noncomputable section
namespace AdalyFormal.Round10.Dictionary.ColorObstruction
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_coe_apply)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Round10.Dictionary.Source
open AdalyFormal.Round10.Dictionary.FreeSource
open AdalyFormal.Round10.Dictionary.Color
open AdalyFormal.Round10.Dictionary.ColorResponse
open AdalyFormal.D1Literal (sing sing_apply sing_apply_self)

/-- Physical fine site on the left face of Omega0. -/
def interiorSite {q : ℕ} (hq : 0 < q) (R : ℕ) :
    PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) :=
  fun μ => ⟨if μ = 0 then 4*q else 0,
    by rw [dil_fine_size hq]; split_ifs <;> omega⟩

theorem interiorSite_mem {q : ℕ} (hq : 0 < q) (R : ℕ) :
    interiorSite hq R ∈ (dilTower q R).Om 0 := by
  change 4*q ≤ _ ∧ _ < 12*(R*q)+12*q
  simp only [interiorSite, ↓reduceIte]
  omega

def oneColor {q : ℕ} (hq : 0 < q) (R : ℕ) : TwistSpace q R :=
  ⟨sing (interiorSite hq R, (0 : Fin 3)) pauliE1,
    AdalyFormal.D1Literal.sing_mem_bondSupp _ (interiorSite_mem hq R) pauliE1⟩

theorem oneColor_ne_zero {q : ℕ} (hq : 0 < q) (R : ℕ) : oneColor hq R ≠ 0 := by
  intro h
  have he := congrArg (fun u : TwistSpace q R => (u : BondFnL2 _) (interiorSite hq R, 0)) h
  change sing _ pauliE1 _ = 0 at he
  rw [sing_apply_self] at he
  have hi := hsInner_e1_e1
  rw [he] at hi
  norm_num [hsInner] at hi

theorem half_pauliE1 : RMap (AdalyFormal.D1Literal.uθ (Real.pi / 2)) pauliE1 = -pauliE1 := by
  apply Subtype.ext
  rw [RMap_coe_apply, AdalyFormal.Round10.Dictionary.half_rotation_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliE1, pauliE1Val, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]

theorem flip_pauliE1 : RMap flipElt pauliE1 = -pauliE1 := by
  apply Subtype.ext
  rw [flip_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliE1, pauliE1Val]

theorem oneColor_charged {q : ℕ} (hq : 0 < q) (R : ℕ) :
    halfE (geomOf 2 1 (dilTower q R)) (oneColor hq R) = -oneColor hq R := by
  classical
  apply Subtype.ext
  apply PiLp.ext
  intro b
  change RMap _ (sing _ pauliE1 b) = -(sing _ pauliE1 b)
  rw [sing_apply]
  split_ifs
  · exact half_pauliE1
  · simp

theorem oneColor_flip {q : ℕ} (hq : 0 < q) (R : ℕ) :
    flipE (geomOf 2 1 (dilTower q R)) (oneColor hq R) = -oneColor hq R := by
  classical
  apply Subtype.ext
  apply PiLp.ext
  intro b
  change RMap _ (sing _ pauliE1 b) = -(sing _ pauliE1 b)
  rw [sing_apply]
  split_ifs
  · exact flip_pauliE1
  · simp

theorem oneColor_jet_zero {q : ℕ} (hq : 0 < q) (R : ℕ) : vacJet q R (oneColor hq R) = 0 :=
  flatJet_single_color_zero _ 1 _ (oneColor_charged hq R) (Or.inr (oneColor_flip hq R))

theorem oneColor_all_profiles_zero {q : ℕ} (hq : 0 < q) (R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) : profileCoupling q R f (oneColor hq R) = 0 :=
  profileCoupling_zero_of_flip_eigen q R f _ (Or.inr (oneColor_flip hq R))

/-- Nonzero and charged is not enough for jet detection, even for the actual frozen operators. -/
theorem exists_charged_invisible {q : ℕ} (hq : 0 < q) (R : ℕ) :
    ∃ u : TwistSpace q R, u ≠ 0 ∧ halfE (geomOf 2 1 (dilTower q R)) u = -u ∧
      vacJet q R u = 0 ∧ (∀ f, profileCoupling q R f u = 0) :=
  ⟨oneColor hq R, oneColor_ne_zero hq R, oneColor_charged hq R,
    oneColor_jet_zero hq R, oneColor_all_profiles_zero hq R⟩

end AdalyFormal.Round10.Dictionary.ColorObstruction
