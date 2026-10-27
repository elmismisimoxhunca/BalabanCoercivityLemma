import BC10

/-!
# BC11 -- NON-VACUITY: the class hypotheses of `ginv_coercive_BC_sup` (`hsup`, `hr`, `hεs`) are met by a background `U ≠ 1`

`U = constU (exp(iθσ₃))` (every link the same small non-identity element): then `Ū^j = constU (g^(ell^j))`
(tree `ubarTowerSU2_constU`), `frobSupBond (Ū^j) ≤ ell^j · √2 θ`, and `θ` can be chosen so that all thresholds hold.
(This `U` is a flat connection, so it witnesses `U ≠ 1` and nonzero link defect, not curvature.)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.BondComposite

open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.CovariantFibreTransfer (constU)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Angle)
open AdalyFormal.Balaban.Bch2 (IsSu2 nu nu_sq nu_nonneg angle_exp su2Angle_one)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobSq)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond)
open AdalyFormal.Balaban.BlockedBackground (ubarTowerSU2_constU frobSupBond_constU frobNorm_pow_sub_one_le)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.NonflatJet (r0 r0_pos)
open SmallnessBridge.Assemble (loopFactorBound)

/-- the diagonal generator (copy of NJ17Witness `Xθ`; NJ17Witness itself imports the R2-clashing NJ14Final). -/
def Xθ (θ : ℝ) : M2 := toM2 ![θ, 0, 0]

theorem Xθ_isSu2 (θ : ℝ) : IsSu2 (Xθ θ) := toM2_mem _

theorem nu_Xθ (θ : ℝ) (hθ : 0 ≤ θ) : nu (Xθ θ) = θ := by
  have h : nu (Xθ θ) ^ 2 = θ ^ 2 := by
    rw [nu_sq]
    unfold frobSq Xθ toM2
    simp [Complex.normSq_apply]
    ring
  nlinarith [nu_nonneg (Xθ θ)]

theorem angle_Xθ (θ : ℝ) (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi) : su2Angle (su2Exp (Xθ θ)) = θ := by
  rw [angle_exp (Xθ_isSu2 θ) (by rw [nu_Xθ θ hθ]; exact hπ), nu_Xθ θ hθ]

theorem frob_Xθ_le (θ : ℝ) (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    frobNorm (((su2Exp (Xθ θ) : SU2) : M2) - 1) ≤ Real.sqrt 2 * θ := by
  rw [AdalyFormal.Balaban.BlockingLinkEstimate.frobNorm_sub_one_eq, angle_Xθ θ hθ hπ]
  have hsin : Real.sin (θ / 2) ≤ θ / 2 := Real.sin_le (by linarith)
  have : 0 < Real.sqrt 2 := by positivity
  nlinarith

theorem exists_small_nonflat (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) :
    ∃ U : Cfg (scaleUp ell k Lu), U ≠ trivialU _ ∧ ∃ ε : ℕ → ℝ, (∀ j, 0 ≤ ε j) ∧
      (∀ j, j < k → frobSupBond (bgTower (GF ell k Lu) U j) ≤ ε j) ∧
      (∀ j, j < k → Real.pi / 2 * ((loopFactorBound ell : ℝ) * ε j) < r0) ∧
      (∀ j, j < k → ε j ≤ 1 / (1000 * (ell : ℝ) ^ 4)) := by
  have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hr0 := r0_pos
  set A : ℝ := (ell : ℝ) ^ k with hA
  have hApos : 0 < A := by positivity
  set c : ℝ := (loopFactorBound ell : ℝ) with hc
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  set P : ℝ := Real.pi / 2 * c * A * (3 / 2) with hP
  have hP0 : 0 ≤ P := by have := Real.pi_pos; positivity
  have h4 : (0 : ℝ) < 1000 * (ell : ℝ) ^ 4 * (3 / 2 * A) := by positivity
  set θ : ℝ := min (min 1 (1 / (1000 * (ell : ℝ) ^ 4 * (3 / 2 * A)))) (r0 / (2 * (P + 1))) with hθ
  have hθpos : 0 < θ := lt_min (lt_min one_pos (by positivity)) (by positivity)
  have hθ1 : θ ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hθ2 : θ ≤ 1 / (1000 * (ell : ℝ) ^ 4 * (3 / 2 * A)) := (min_le_left _ _).trans (min_le_right _ _)
  have hθ3 : θ ≤ r0 / (2 * (P + 1)) := min_le_right _ _
  have hπ : θ ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  set g : SU2 := su2Exp (Xθ θ) with hg
  refine ⟨constU g _, ?_, fun j => (ell : ℝ) ^ j * (Real.sqrt 2 * θ), ?_, ?_, ?_, ?_⟩
  · intro h
    let e0 : PeriodicLatticeEdge (scaleUp ell k Lu) := ((fun _ => 0 : PeriodicLatticeSite (scaleUp ell k Lu)), (0 : Fin 3))
    have h1 : g = (trivialU (scaleUp ell k Lu) e0 : SU2) := congrFun h e0
    have h2 : su2Angle g = su2Angle (trivialU (scaleUp ell k Lu) e0 : SU2) := by rw [h1]
    rw [hg, angle_Xθ θ hθpos.le hπ] at h2
    have : (trivialU (scaleUp ell k Lu) e0 : SU2) = 1 := rfl
    rw [this, su2Angle_one] at h2
    linarith
  · intro j; positivity
  · intro j hj
    have hbg : bgTower (GF ell k Lu) (constU g _) j = constU (g ^ ell ^ j) _ := ubarTowerSU2_constU ell g j
    rw [hbg, frobSupBond_constU]
    refine (frobNorm_pow_sub_one_le g (ell ^ j)).trans ?_
    rw [Nat.cast_pow]
    exact mul_le_mul_of_nonneg_left (frob_Xθ_le θ hθpos.le hπ) (by positivity)
  · intro j hj
    have hj1 : (ell : ℝ) ^ j ≤ A := pow_le_pow_right₀ hellR hj.le
    have hbound : (ell : ℝ) ^ j * (Real.sqrt 2 * θ) ≤ A * (3 / 2) * θ := by
      have h1 : Real.sqrt 2 * θ ≤ 3 / 2 * θ := mul_le_mul_of_nonneg_right hs2 hθpos.le
      calc (ell : ℝ) ^ j * (Real.sqrt 2 * θ) ≤ A * (3 / 2 * θ) :=
            mul_le_mul hj1 h1 (by positivity) hApos.le
        _ = A * (3 / 2) * θ := by ring
    have hPθ : P * θ ≤ r0 / 2 := by
      calc P * θ ≤ P * (r0 / (2 * (P + 1))) := mul_le_mul_of_nonneg_left hθ3 hP0
        _ = r0 / 2 * (P / (P + 1)) := by field_simp
        _ ≤ r0 / 2 * 1 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [div_le_one (by linarith)]; linarith
        _ = r0 / 2 := by ring
    have : Real.pi / 2 * (c * ((ell : ℝ) ^ j * (Real.sqrt 2 * θ))) ≤ P * θ := by
      calc Real.pi / 2 * (c * ((ell : ℝ) ^ j * (Real.sqrt 2 * θ))) ≤ Real.pi / 2 * (c * (A * (3 / 2) * θ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbound hc0) (by positivity)
        _ = P * θ := by rw [hP]; ring
    linarith
  · intro j hj
    have hj1 : (ell : ℝ) ^ j ≤ A := pow_le_pow_right₀ hellR hj.le
    have hbound : (ell : ℝ) ^ j * (Real.sqrt 2 * θ) ≤ A * (3 / 2) * θ := by
      have h1 : Real.sqrt 2 * θ ≤ 3 / 2 * θ := mul_le_mul_of_nonneg_right hs2 hθpos.le
      calc (ell : ℝ) ^ j * (Real.sqrt 2 * θ) ≤ A * (3 / 2 * θ) :=
            mul_le_mul hj1 h1 (by positivity) hApos.le
        _ = A * (3 / 2) * θ := by ring
    have h5 : A * (3 / 2) * θ ≤ 1 / (1000 * (ell : ℝ) ^ 4) := by
      calc A * (3 / 2) * θ = (3 / 2 * A) * θ := by ring
        _ ≤ (3 / 2 * A) * (1 / (1000 * (ell : ℝ) ^ 4 * (3 / 2 * A))) :=
            mul_le_mul_of_nonneg_left hθ2 (by positivity)
        _ = 1 / (1000 * (ell : ℝ) ^ 4) := by field_simp
    exact hbound.trans h5

#print axioms frob_Xθ_le
#print axioms exists_small_nonflat

end AdalyFormal.BondComposite
