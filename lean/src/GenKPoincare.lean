import CarrierBridge
import AdalyFormal.Balaban.SuTwoGeomU1
import AdalyFormal.Balaban.RegularUGamma0
/-! The source's block-two inequality on arbitrary periodic unit extents.
The frozen scalar/SuTwo proofs are consumed from the read-only dependency cache;
no frozen source is compiled. The new interfaces use campaign Hilbert norms. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace HConstruction.GenK
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators (SuTwo curlCovariantLM)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue curlCovariantLM_trivialU_eq_flatCurlLM)
open AdalyFormal.Balaban.LineIntegralCovariant
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.DeltaKUnified (BFL2 bfl2Equiv)
open AdalyFormal.Balaban.SuTwoInner (inner_eq_hsInner)
open AdalyFormal.Balaban.CovariantHj (covBondInner covPlaqInner)
open AdalyFormal.Balaban.CovariantHjFaithful (covCoarseBondInner)
open HConstruction.Carrier
variable {L : PeriodicLatticeExtent}

def Axial (B : Bond L → SuTwo) : Prop :=
  ∀ y ∈ CoarseLattice L 2, ∀ x ∈ blockOf y 2, ∀ b ∈ staircasePath y x, B b = 0

def curlEnergy (B : Bond L → SuTwo) : ℝ :=
  ∑ p : PeriodicLatticePlaquette L, ‖flatCurlValue B p‖^2

def bondEnergy (B : Bond L → SuTwo) : ℝ := ∑ b : Bond L, ‖B b‖^2

def qEnergy (B : Bond L → SuTwo) : ℝ :=
  ∑ c : CoarseBond L 2, ‖lineCoarseRestrictSuTwo 2 B c‖^2

lemma norm_sq_coordinates {ι : Type*} [Fintype ι] (v : PiLp 2 (fun _ : ι => SuTwo)) :
    ‖v‖^2 = ∑ i, ‖v i‖^2 := by
  rw [← real_inner_self_eq_norm_sq]
  change (∑ i, inner ℝ (v i) (v i)) = _
  simp only [real_inner_self_eq_norm_sq]

lemma bondEnergy_norm (B : BFL2 L) : bondEnergy (bfl2Equiv B) = ‖B‖^2 :=
  (norm_sq_coordinates B).symm

/-- CMP96 (2.128), d=3 and blocking ratio two, on every compatible torus.
The constant is independent of extent and incoming RG depth. -/
theorem lemma24 (hL : ∀ μ : Fin 3, 4 ≤ L μ)
    (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1))
    (B : Bond L → SuTwo) (hB : Axial B) :
    (1/1728 : ℝ) * bondEnergy B ≤ 2*qEnergy B + curlEnergy B := by
  have h := AdalyFormal.Balaban.SuTwoGeomU1.suTwoGeomAdditive_trivialU_of_admissible hL hdvd B hB
  unfold AdalyFormal.Balaban.CoercivityTargetsCorrected.SuTwoGeomAdditiveInequality at h
  have hc : curlCovariantLM (trivialU L) B = flatCurlValue B := by
    rw [curlCovariantLM_trivialU_eq_flatCurlLM]; rfl
  have hq : lineCoarseRestrictCovLM (trivialU L) 2 B = lineCoarseRestrictSuTwo 2 B := by
    funext c
    exact lineCoarseRestrictCov_trivialU 2 B c
  rw [hc,hq] at h
  simp only [covBondInner,covPlaqInner,covCoarseBondInner, ← inner_eq_hsInner,
    real_inner_self_eq_norm_sq] at h
  norm_num only [Nat.cast_ofNat] at h
  norm_num [bondEnergy,qEnergy,curlEnergy] at h ⊢
  exact h

/-- The outgoing raw map is twice the normalized average; its kernel is the same. -/
theorem lemma24_kernel (hL : ∀ μ : Fin 3, 4 ≤ L μ)
    (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1))
    (B : Bond L → SuTwo) (hB : Axial B)
    (hQ : ∀ c, lineCoarseRestrictSuTwo 2 B c = 0) :
    (1/1728 : ℝ) * bondEnergy B ≤ curlEnergy B := by
  have h := lemma24 hL hdvd B hB
  have hz : qEnergy B = 0 := by simp only [qEnergy,hQ,norm_zero,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero]
  simpa only [hz,mul_zero,zero_add] using h

#print axioms lemma24
#print axioms lemma24_kernel
#print axioms AdalyFormal.Balaban.HrefReduction.lemma24_unconditional_U1_ell2_uncond
#print axioms AdalyFormal.Balaban.RegularUGamma0.ell_coarseCurlEnergy_le_plaqEnergy_trivialU
end HConstruction.GenK
