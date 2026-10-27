import DK2DepthTransportCore

set_option autoImplicit false
noncomputable section
namespace Prop1.ScaleFittedRepair

open AdalyFormal.Balaban.SuTwoLogExp
  (SU2 M2 su2Log su2Exp adMap adMap_apply su2_log_conj su2_exp_ad)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.BlockingLinkEstimate (frobNorm_conj_sub_one)
open DepthUniformity.Strided (frobNorm_inv_sub_one)
open Prop1.ScaleFittedProof (log_inv isSu2_weighted_sum)
open AdalyFormal.Balaban.Bch2 (isSu2_su2Log exp_mul_exp_neg)

/-- Exponential of a weighted average of CLOSED loop logarithms. This helper
is not a replacement for ubarSU2; the latter is matched in raw_relative_exact. -/
def loopMean {ι : Type*} (S : Finset ι) (w : ι → ℝ) (W : ι → SU2) : SU2 :=
  su2Exp (∑ x ∈ S, w x • su2Log (W x))

theorem loopMean_conj {ι : Type*} (S : Finset ι) (w : ι → ℝ)
    (W : ι → SU2) (g : SU2) :
    loopMean S w (fun x => g * W x * g⁻¹) = g * loopMean S w W * g⁻¹ := by
  unfold loopMean
  simp only [su2_log_conj]
  rw [← su2_exp_ad]
  congr 1
  simp only [adMap_apply, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

theorem loopMean_inv {ι : Type*} (S : Finset ι) (w : ι → ℝ) (W : ι → SU2) :
    loopMean S w (fun x => (W x)⁻¹) = (loopMean S w W)⁻¹ := by
  unfold loopMean
  simp only [log_inv, smul_neg, Finset.sum_neg_distrib]
  apply eq_inv_of_mul_eq_one_right
  apply Subtype.ext
  exact exp_mul_exp_neg (isSu2_weighted_sum S w _ (fun x _ => isSu2_su2Log _))

/-- Full analytic averaging theorem for a plaquette of open contours, allowing
arbitrarily large individual coarse bonds. Only the contractible loops,
whole coarse plaquette and translated contour plaquettes are small. -/
theorem contour_mean_plaquette_bound {ι : Type*} (S : Finset ι) (w : ι → ℝ)
    (hw : ∀ x ∈ S, 0 ≤ w x) (hsum : ∑ x ∈ S, w x = 1)
    (C : Fin 4 → SU2) (G : Fin 4 → ι → SU2) (b : ℝ)
    (hb : 0 ≤ b) (hsmall : b ≤ 1/400)
    (hloop : ∀ i x, x ∈ S → frobNorm (((G i x * (C i)⁻¹ : SU2) : M2)-1) ≤ 3*b)
    (hP : frobNorm (((C 0 * C 1 * (C 2)⁻¹ * (C 3)⁻¹ : SU2) : M2)-1) ≤ b)
    (hrect : ∀ x ∈ S,
      frobNorm (((G 0 x * G 1 x * (G 2 x)⁻¹ * (G 3 x)⁻¹ : SU2) : M2)-1) ≤ b) :
    let B := fun i : Fin 4 => loopMean S w (fun x => G i x * (C i)⁻¹) * C i
    frobNorm (((B 0 * B 1 * (B 2)⁻¹ * (B 3)⁻¹ : SU2) : M2)-1) ≤ b+44465*b^2 := by
  let R := fun i x => G i x * (C i)⁻¹
  let P := C 0 * C 1 * (C 2)⁻¹ * (C 3)⁻¹
  let K := C 0 * C 1 * (C 2)⁻¹
  let W : Fin 4 → ι → SU2 := ![
    R 0,
    fun x => C 0 * R 1 x * (C 0)⁻¹,
    fun x => K * (R 2 x)⁻¹ * K⁻¹,
    fun x => P * (R 3 x)⁻¹ * P⁻¹]
  have hW : ∀ i x, x ∈ S → frobNorm ((W i x : M2)-1) ≤ 3*b := by
    intro i x hx
    fin_cases i
    · exact hloop 0 x hx
    · change frobNorm (((C 0 * R 1 x * (C 0)⁻¹ : SU2) : M2)-1) ≤ _
      rw [frobNorm_conj_sub_one]
      exact hloop 1 x hx
    · change frobNorm (((K * (R 2 x)⁻¹ * K⁻¹ : SU2) : M2)-1) ≤ _
      rw [frobNorm_conj_sub_one, frobNorm_inv_sub_one]
      exact hloop 2 x hx
    · change frobNorm (((P * (R 3 x)⁻¹ * P⁻¹ : SU2) : M2)-1) ≤ _
      rw [frobNorm_conj_sub_one, frobNorm_inv_sub_one]
      exact hloop 3 x hx
  have hpoint : ∀ x, W 0 x * W 1 x * W 2 x * W 3 x * P =
      G 0 x * G 1 x * (G 2 x)⁻¹ * (G 3 x)⁻¹ := by
    intro x
    change R 0 x * (C 0 * R 1 x * (C 0)⁻¹) *
      (K * (R 2 x)⁻¹ * K⁻¹) * (P * (R 3 x)⁻¹ * P⁻¹) * P = _
    dsimp only [R, K, P]
    group
  have h := transported_average_prop1_shape S w hw hsum W P b hb hsmall hW hP (by
    intro x hx
    rw [hpoint]
    exact hrect x hx)
  change frobNorm (((loopMean S w (W 0) * loopMean S w (W 1) *
    loopMean S w (W 2) * loopMean S w (W 3) * P : SU2) : M2)-1) ≤ _ at h
  have h1 : loopMean S w (W 1) = C 0 * loopMean S w (R 1) * (C 0)⁻¹ :=
    loopMean_conj S w (R 1) (C 0)
  have h2 : loopMean S w (W 2) = K * (loopMean S w (R 2))⁻¹ * K⁻¹ := by
    change loopMean S w (fun x => K * (R 2 x)⁻¹ * K⁻¹) = _
    rw [loopMean_conj, loopMean_inv]
  have h3 : loopMean S w (W 3) = P * (loopMean S w (R 3))⁻¹ * P⁻¹ := by
    change loopMean S w (fun x => P * (R 3 x)⁻¹ * P⁻¹) = _
    rw [loopMean_conj, loopMean_inv]
  rw [h1, h2, h3] at h
  have heq := plaquette_transport (C 0) (C 1) (C 2) (C 3)
    (loopMean S w (R 0)) (loopMean S w (R 1))
    (loopMean S w (R 2)) (loopMean S w (R 3))
  change frobNorm (((loopMean S w (R 0) * (C 0) * (loopMean S w (R 1) * C 1) *
    (loopMean S w (R 2) * C 2)⁻¹ * (loopMean S w (R 3) * C 3)⁻¹ : SU2) : M2)-1) ≤ _
  rw [heq]
  exact h

/-- Exact Stokes cancellation of the four tree transports, before estimates.
This is valid even for nontrivial winding and requires no periodic tree gauge. -/
theorem contour_rectangle_cancellation {G : Type*} [Group G]
    (t0 t1 t2 t3 b0 b1 b2 b3 : G) :
    (t0*b0*t1⁻¹) * (t1*b1*t2⁻¹) * (t3*b2*t2⁻¹)⁻¹ * (t0*b3*t3⁻¹)⁻¹ =
      t0 * (b0*b1*b2⁻¹*b3⁻¹) * t0⁻¹ := by
  group

end Prop1.ScaleFittedRepair

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[`Prop1.ScaleFittedRepair.loopMean_conj,
      `Prop1.ScaleFittedRepair.loopMean_inv,
      `Prop1.ScaleFittedRepair.contour_mean_plaquette_bound,
      `Prop1.ScaleFittedRepair.contour_rectangle_cancellation] do
    let axioms ← Lean.collectAxioms n
    Lean.logInfo m!"TRANSPORT_MEAN_AXIOMS {n}: {axioms}"
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Nonstandard axiom in {n}: {ax}"
  Lean.logInfo "TRANSPORT_MEAN_COMPLETE"
