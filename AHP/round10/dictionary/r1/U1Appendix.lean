/-! Requires Core.lean, concatenated to Gauge.lean by assemble.py. -/
noncomputable section
namespace AdalyFormal.Round10.Dictionary
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap RMap_coe_apply BondFnL2)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

/-- A phase background uses the frozen uθ, not a substitute operator. -/
def phaseCfg {L : PeriodicLatticeExtent} (f : Bond L → ℝ) : LinkCfg L := fun e => uθ (f e)

def diagonalGauge {L : PeriodicLatticeExtent} (α : ℝ) : GaugeFn L := fun _ => uθ α

/-- Verbatim matrix calculation from round 9. -/
theorem uθ_comm (α s : ℝ) :
    AdalyFormal.D1Literal.uθ α * AdalyFormal.D1Literal.uθ s =
      AdalyFormal.D1Literal.uθ s * AdalyFormal.D1Literal.uθ α := by
  apply Subtype.ext
  show AdalyFormal.D1Literal.uMat α * AdalyFormal.D1Literal.uMat s =
    AdalyFormal.D1Literal.uMat s * AdalyFormal.D1Literal.uMat α
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AdalyFormal.D1Literal.uMat, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem phaseCfg_fixed {L : PeriodicLatticeExtent} (f : Bond L → ℝ) (α : ℝ) :
    periodicGaugeTransform (diagonalGauge α) (phaseCfg f) = phaseCfg f := by
  funext e
  change uθ α * uθ (f e) * (uθ α)⁻¹ = uθ (f e)
  rw [uθ_comm, mul_assoc, mul_inv_cancel, mul_one]

section Diagonal
variable {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (f : Bond (scaleUp ell k Lu) → ℝ) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (α : ℝ)

/-- No invertibility, admissibility, radius, or scale hypotheses. -/
theorem phase_all_comm (x : ↥(bondSupp (geomOf ell k S))) :
    (dataS selAll selAll (gparams ell k Lu hell S (phaseCfg f) a Lam)).Ginv
      (adEL (diagonalGauge α) (geomOf ell k S) x) =
    adEL (diagonalGauge α) (geomOf ell k S)
      ((dataS selAll selAll (gparams ell k Lu hell S (phaseCfg f) a Lam)).Ginv x) :=
  all_comm hell S (phaseCfg f) a Lam (diagonalGauge α) (phaseCfg_fixed f α) x

theorem phase_localized_comm (x : ↥(bondSupp (geomOf ell k S))) :
    (gparams ell k Lu hell S (phaseCfg f) a Lam).data.Ginv
      (adEL (diagonalGauge α) (geomOf ell k S) x) =
    adEL (diagonalGauge α) (geomOf ell k S)
      ((gparams ell k Lu hell S (phaseCfg f) a Lam).data.Ginv x) :=
  localized_comm hell S (phaseCfg f) a Lam (diagonalGauge α) (phaseCfg_fixed f α) x

theorem phase_correction_comm (x : ↥(bondSupp (geomOf ell k S))) :
    localCorrection hell S (phaseCfg f) a Lam (adEL (diagonalGauge α) (geomOf ell k S) x) =
    adEL (diagonalGauge α) (geomOf ell k S) (localCorrection hell S (phaseCfg f) a Lam x) :=
  correction_comm hell S (phaseCfg f) a Lam (diagonalGauge α) (phaseCfg_fixed f α) x
end Diagonal

theorem phase_deriv_comm {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (f : ℝ → Bond (scaleUp ell k Lu) → ℝ) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (α t : ℝ) (x : ↥(bondSupp (geomOf ell k S))) :
    deriv (fun s : ℝ => localCorrection hell S (phaseCfg (f s)) a Lam) t
      (adEL (diagonalGauge α) (geomOf ell k S) x) =
    adEL (diagonalGauge α) (geomOf ell k S)
      (deriv (fun s : ℝ => localCorrection hell S (phaseCfg (f s)) a Lam) t x) :=
  correction_deriv_comm hell S (fun s => phaseCfg (f s)) a Lam (diagonalGauge α)
    (fun s => phaseCfg_fixed (f s) α) t x

/-- The adjoint half turn fixes the diagonal and negates the off-diagonal
entries. This is the neutral/charged involution of the real carrier. -/
theorem half_rotation_matrix : (uθ (Real.pi / 2) : Matrix (Fin 2) (Fin 2) ℂ) =
    !![Complex.I, 0; 0, -Complex.I] := by
  change uMat (Real.pi / 2) = _
  simp only [uMat, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.exp_pi_div_two_mul_I]
  rw [show -((Real.pi : ℂ) / 2 * Complex.I) = -Real.pi / 2 * Complex.I by ring,
    Complex.exp_neg_pi_div_two_mul_I]

theorem half_RMap_twice (X : SuTwo) : RMap (uθ (Real.pi / 2)) (RMap (uθ (Real.pi / 2)) X) = X := by
  apply Subtype.ext
  rw [RMap_coe_apply, RMap_coe_apply, half_rotation_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, mul_assoc] <;> ring_nf <;> simp [Complex.I_sq]

theorem half_carrier_twice {L : PeriodicLatticeExtent} (G : TowerGeom L) (x : ↥(bondSupp G)) :
    adEL (diagonalGauge (Real.pi / 2)) G (adEL (diagonalGauge (Real.pi / 2)) G x) = x := by
  apply Subtype.ext
  apply PiLp.ext
  intro e
  exact half_RMap_twice ((x : BondFnL2 L) e)

theorem carrier_neutral_charged_split {L : PeriodicLatticeExtent} (G : TowerGeom L)
    (x : ↥(bondSupp G)) :
    ∃ xp xm : ↥(bondSupp G), x = xp + xm ∧
      adEL (diagonalGauge (Real.pi / 2)) G xp = xp ∧
      adEL (diagonalGauge (Real.pi / 2)) G xm = -xm ∧ ⟪xp, xm⟫ = 0 :=
  involution_split _ (half_carrier_twice G) x

theorem phase_kernel_neutral_charged_split {ell k : ℕ} {Lu : PeriodicLatticeExtent}
    (hell : 0 < ell) (S : Tower (scaleUp ell k Lu)) (f : Bond (scaleUp ell k Lu) → ℝ)
    (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (x : ↥(bondSupp (geomOf ell k S)))
    (hx : (dataS selAll selAll (gparams ell k Lu hell S (phaseCfg f) a Lam)).Ginv x = 0) :
    ∃ xp xm : ↥(bondSupp (geomOf ell k S)), x = xp + xm ∧
      adEL (diagonalGauge (Real.pi / 2)) (geomOf ell k S) xp = xp ∧
      adEL (diagonalGauge (Real.pi / 2)) (geomOf ell k S) xm = -xm ∧ ⟪xp, xm⟫ = 0 ∧
      (dataS selAll selAll (gparams ell k Lu hell S (phaseCfg f) a Lam)).Ginv xp = 0 ∧
      (dataS selAll selAll (gparams ell k Lu hell S (phaseCfg f) a Lam)).Ginv xm = 0 :=
  involution_kernel_split _ _ (half_carrier_twice _) (phase_all_comm hell S f a Lam _) hx

#print axioms phaseCfg
#print axioms diagonalGauge
#print axioms uθ_comm
#print axioms phaseCfg_fixed
#print axioms phase_all_comm
#print axioms phase_localized_comm
#print axioms phase_correction_comm
#print axioms phase_deriv_comm
#print axioms half_rotation_matrix
#print axioms half_RMap_twice
#print axioms half_carrier_twice
#print axioms carrier_neutral_charged_split
#print axioms phase_kernel_neutral_charged_split
end AdalyFormal.Round10.Dictionary
