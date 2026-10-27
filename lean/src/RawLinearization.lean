import QuadraticRemainder

set_option autoImplicit false
noncomputable section
namespace Prop1.ScaleFittedProof

open AdalyFormal.Balaban.SuTwoLogExp
  (SU2 M2 su2Log su2Exp su2Kappa coe_inv)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobNorm_nonneg)
open AdalyFormal.Balaban.Bch2
  (IsSu2 isSu2_su2Log bch2_seven frobNorm_smul frobNorm_add_le)
open AdalyFormal.Balaban.BlockingLinkEstimate (frobNorm_sum_le)
open DepthUniformity.Strided (frobNorm_inv_sub_one)

/-- The principal-log totalization is odd under inversion, even at its junk
point; branch recovery elsewhere is separately enforced below. -/
theorem log_inv (g : SU2) : su2Log g⁻¹ = -su2Log g := by
  have hk : su2Kappa g⁻¹ = su2Kappa g := by
    unfold su2Kappa
    rw [SmallnessBridge.ProdBound.su2Angle_inv]
  unfold su2Log
  rw [hk, coe_inv, Matrix.conjTranspose_conjTranspose, ← neg_sub, smul_neg]

/-- Convex weighted Frobenius bound. No dimension-dependent norm conversion. -/
theorem convex_norm_bound {ι : Type*} (S : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hsum : ∑ i ∈ S, w i = 1)
    (F : ι → M2) (B : ℝ) (hF : ∀ i ∈ S, frobNorm (F i) ≤ B) :
    frobNorm (∑ i ∈ S, w i • F i) ≤ B := by
  calc
    _ ≤ ∑ i ∈ S, frobNorm (w i • F i) := frobNorm_sum_le S _
    _ = ∑ i ∈ S, w i * frobNorm (F i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [frobNorm_smul, abs_of_nonneg (hw i hi)]
    _ ≤ ∑ i ∈ S, w i * B := Finset.sum_le_sum (fun i hi =>
      mul_le_mul_of_nonneg_left (hF i hi) (hw i hi))
    _ = B := by rw [← Finset.sum_mul, hsum, one_mul]

theorem isSu2_weighted_sum {ι : Type*} (S : Finset ι) (w : ι → ℝ)
    (F : ι → M2) (hF : ∀ i ∈ S, IsSu2 (F i)) :
    IsSu2 (∑ i ∈ S, w i • F i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using IsSu2.zero
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi]
      exact ((hF i (by simp)).smul _).add
        (ih (fun j hj => hF j (by simp [hj])))

/-- Analytic core of printed (47) at one bond: the logarithm of the actual
logarithmic raw averaging formula agrees with the average of contour logs to
quadratic order. Its branch and BCH-domain obligations follow from explicit
group-deviation hypotheses. The contour-smallness hypotheses still require the
local tree-gauge geometry; they are NOT inferred from plaquette smallness here. -/
theorem logarithmic_average_linearization {ι : Type*} (S : Finset ι)
    (w : ι → ℝ) (hw : ∀ i ∈ S, 0 ≤ w i) (hsum : ∑ i ∈ S, w i = 1)
    (G : ι → SU2) (C : SU2) (r : ℝ) (hr : 0 ≤ r) (hrsmall : r ≤ 1/64)
    (hG : ∀ i ∈ S, frobNorm ((G i : M2) - 1) ≤ r)
    (hC : frobNorm ((C : M2) - 1) ≤ r) :
    frobNorm
      (su2Log (su2Exp (∑ i ∈ S, w i • su2Log (G i * C⁻¹)) * C) -
        ∑ i ∈ S, w i • su2Log (G i)) ≤ 84 * r ^ 2 := by
  let H : M2 := ∑ i ∈ S, w i • su2Log (G i * C⁻¹)
  let A : M2 := ∑ i ∈ S, w i • su2Log (G i)
  have hr2 : r ≤ 2 := by linarith
  have hCi : frobNorm (((C⁻¹ : SU2) : M2) - 1) ≤ r := by
    rw [frobNorm_inv_sub_one]; exact hC
  have hlogC : frobNorm (su2Log C) ≤ 2 * r :=
    (log_branch_and_bound C (hC.trans hr2)).2.trans
      (mul_le_mul_of_nonneg_left hC (by norm_num))
  have hlogCi : frobNorm (su2Log C⁻¹) ≤ 2 * r :=
    (log_branch_and_bound C⁻¹ (hCi.trans hr2)).2.trans
      (mul_le_mul_of_nonneg_left hCi (by norm_num))
  have hlogG : ∀ i ∈ S, frobNorm (su2Log (G i)) ≤ 2 * r := by
    intro i hi
    exact (log_branch_and_bound (G i) ((hG i hi).trans hr2)).2.trans
      (mul_le_mul_of_nonneg_left (hG i hi) (by norm_num))
  have hloopdev : ∀ i ∈ S, frobNorm (((G i * C⁻¹ : SU2) : M2) - 1) ≤ 2 * r := by
    intro i hi
    have h := AdalyFormal.Balaban.RegularUQChain.frobNorm_su_mul_sub_one_le (G i) C⁻¹
    linarith [hG i hi]
  have hlooplog : ∀ i ∈ S, frobNorm (su2Log (G i * C⁻¹)) ≤ 4 * r := by
    intro i hi
    have h := (log_branch_and_bound (G i * C⁻¹) ((hloopdev i hi).trans (by linarith))).2
    linarith [hloopdev i hi]
  have hH : frobNorm H ≤ 4 * r := convex_norm_bound S w hw hsum _ _ hlooplog
  have hlooperr : ∀ i ∈ S,
      frobNorm (su2Log (G i * C⁻¹) - (su2Log (G i) - su2Log C)) ≤ 28 * r ^ 2 := by
    intro i hi
    have h := bch2_seven (isSu2_su2Log (G i)) (isSu2_su2Log C⁻¹)
      (by linarith [hlogG i hi])
    rw [(log_branch_and_bound (G i) ((hG i hi).trans hr2)).1,
      (log_branch_and_bound C⁻¹ (hCi.trans hr2)).1, log_inv, ← sub_eq_add_neg] at h
    have hp := mul_le_mul (hlogG i hi) hlogCi (frobNorm_nonneg _)
      (mul_nonneg (by norm_num) hr)
    rw [log_inv, AdalyFormal.Balaban.RegularityGap.frobNorm_neg] at hp
    rw [AdalyFormal.Balaban.RegularityGap.frobNorm_neg] at h
    nlinarith
  have hweighted : frobNorm (H - (A - su2Log C)) ≤ 28 * r ^ 2 := by
    have heq : H - (A - su2Log C) =
        ∑ i ∈ S, w i • (su2Log (G i * C⁻¹) - (su2Log (G i) - su2Log C)) := by
      simp only [smul_sub, Finset.sum_sub_distrib]
      rw [← Finset.sum_smul, hsum, one_smul]
    rw [heq]
    exact convex_norm_bound S w hw hsum _ _ hlooperr
  have halg : IsSu2 H := isSu2_weighted_sum S w _ (fun i _ => isSu2_su2Log _)
  have hbch := bch2_seven halg (isSu2_su2Log C) (by linarith)
  rw [(log_branch_and_bound C (hC.trans hr2)).1] at hbch
  have hp := mul_le_mul hH hlogC (frobNorm_nonneg _)
    (mul_nonneg (by norm_num) hr)
  have htri : frobNorm (su2Log (su2Exp H * C) - A) ≤
      frobNorm (su2Log (su2Exp H * C) - (H + su2Log C)) +
      frobNorm (H - (A - su2Log C)) := by
    have heq : su2Log (su2Exp H * C) - A =
        (su2Log (su2Exp H * C) - (H + su2Log C)) + (H - (A - su2Log C)) := by abel
    rw [heq]
    exact frobNorm_add_le _ _
  change frobNorm (su2Log (su2Exp H * C) - A) ≤ _
  nlinarith

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (gammaVarStrided coarseBondVar loopVar stridedBlockedGauge)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2)

/-- Specialization to the EXACT imported raw operator and its actual complete
stride-scaled block. Only the contour/coarse-bond smallness remains conditional.
Neither the operator nor its weights have been substituted. -/
theorem raw_bond_log_linearization {L : PeriodicLatticeExtent}
    (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, s * ell ∣ (L μ + 1))
    (V : PeriodicLinkConfiguration SU2 L)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L (s * ell)) (μ : Fin 3)
    (r : ℝ) (hr : 0 ≤ r) (hrsmall : r ≤ 1/64)
    (hG : ∀ x ∈ stepBlockOf y s ell,
      frobNorm (((gammaVarStrided s ell V (y, μ) x : SU2) : M2) - 1) ≤ r)
    (hC : frobNorm (((coarseBondVar s ell V (y, μ) : SU2) : M2) - 1) ≤ r) :
    frobNorm (su2Log (ubarSU2 s ell V (y, μ)) -
      ∑ x ∈ stepBlockOf y s ell,
        ((ell : ℚ)^3)⁻¹ • su2Log (gammaVarStrided s ell V (y, μ) x)) ≤ 84 * r ^ 2 := by
  have hcard := output_block_card s ell hs hdvd y hy
  have hn : (ell : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hell)
  let w : ℝ := (((ell : ℚ)^3)⁻¹ : ℚ)
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hsum : ∑ _x ∈ stepBlockOf y s ell, w = 1 := by
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
    dsimp [w]
    push_cast
    field_simp
  have h := logarithmic_average_linearization (stepBlockOf y s ell) (fun _ => w)
    (fun _ _ => hw) hsum (gammaVarStrided s ell V (y, μ))
    (coarseBondVar s ell V (y, μ)) r hr hrsmall hG hC
  dsimp [w] at h
  simp only [Rat.cast_smul_eq_qsmul] at h
  exact h

end Prop1.ScaleFittedProof

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[`Prop1.ScaleFittedProof.log_inv,
      `Prop1.ScaleFittedProof.convex_norm_bound,
      `Prop1.ScaleFittedProof.isSu2_weighted_sum,
      `Prop1.ScaleFittedProof.logarithmic_average_linearization,
      `Prop1.ScaleFittedProof.raw_bond_log_linearization] do
    let axioms ← Lean.collectAxioms n
    Lean.logInfo m!"RAW_LINEARIZATION_AXIOMS {n}: {axioms}"
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Nonstandard axiom in {n}: {ax}"
