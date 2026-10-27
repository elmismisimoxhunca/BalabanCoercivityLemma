import MI20
import MI21

/-!
# MI22 -- W1 (`ginvIMS_of`) and W4 (`ginv_weighted_coercive`) on the genuine operator (M1 lane E, 2026-10-13)

* `CTc`, `etaC`, `nuC` : the explicit constants of MI16 / MI19.
* **`ginvIMS_of`** : MI2's `GinvIMS ε e` with `ε = (1+η)(1+ε₂)/(1−η) − 1`, `e = (1+η)(1+ε₂)·2ν/(1−η) + (1+η)·C1 + 2ν`,
  `C1 = (1+1/ε₂)·12ℓ²KG + 2(1+1/ε₂)·CT + (1+1/ε₂)·CM`.
* **`ginv_weighted_coercive`** (W4): with `PatchCoercive cP` (W3, real tower) in addition,
  `((cP − e)/(1+ε)) · wnormSq A ≤ ⟪A, Ginv A⟫` for every `A ∈ bondSupp`.
Inputs: admissible tower and partition geometry, `HatPack` (hatted chain with smallness), `Gi`, the sharp row bound `hγ`,
the holonomy regime, `MassComm CM`, `PatchCoercive cP`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.M1IMS

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer
open AdalyFormal.M1Site
open AdalyFormal.StatementLane (Tower Admissible bigSide scaleUp)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap BondFnL2 curlValueCovariant)
open AdalyFormal.Balaban.CovariantHjMinimizer (PlaqFnL2)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.StatementLaneR6 (plaqMask plaqMask_apply deltaPrimeBilL2NormLoc)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantLM_L2)

/-- the gauge-fixing IMS constant of MI16. -/
noncomputable def CTc (ell M κ c W : ℕ) (a cs γ : ℝ) : ℝ :=
  (5 * ((ell * Real.sqrt (48 / cs)) ^ 2 * (3 * KG ell M κ c)
      + (4 * ell / cs) ^ 2 * (3 * (ell : ℝ) ^ 4 * KG ell M κ c) *
          ((ell * (Real.sqrt (12 / cs) + Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1) * (4 / cs)))
            * Real.sqrt (max a 1) * γ) ^ 2
      + (4 * ell / cs) ^ 2 * (max a 1 * (9 * a * KG ell M κ c))
      + (4 * ell / cs) ^ 2 * (9 * a * KG ell M κ c * max a 1)
      + (4 * ell / cs) ^ 2 * (9 * a * KG ell M κ c * γ ^ 2)))
    * ((ell * (Real.sqrt (12 / cs) + Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1) * (4 / cs)))
        * Real.sqrt (max a 1) * γ) ^ 2
    + 3 * KG ell M κ c

/-- the curvature coupling constant `ν` of MI19. -/
noncomputable def nuC (ell : ℕ) (ρ : ℝ) : ℝ := (17 / Real.sqrt 2) * 12 * (ρ * (ell : ℝ) ^ 4)

/-- the sandwich constant `η` of MI19. -/
noncomputable def etaC (ell W : ℕ) (cs ρ ε1 : ℝ) : ℝ :=
  ε1 + (1 + 1 / ε1) * (12 * ρ ^ 2 * (ell : ℝ) ^ 8 * (4 * ell / cs) ^ 2)
    + 2 * nuC ell ρ * ((ell : ℝ) * (Real.sqrt (12 / cs)
        + Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1) * (4 / cs))) ^ 2

/-- the IMS remainder constant `C1`. -/
noncomputable def C1c (ell M κ c W : ℕ) (a cs γ CM ε2 : ℝ) : ℝ :=
  (1 + 1 / ε2) * (12 * (ell : ℝ) ^ 2 * KG ell M κ c) + 2 * (1 + 1 / ε2) * CTc ell M κ c W a cs γ + (1 + 1 / ε2) * CM

section main
variable {ell M R k κ c : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) {S : Tower (scaleUp ell k Lu)}
  (hS : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M) (hell : 2 ≤ ell) (hR1 : 1 ≤ R)
  (hR : (c + 3) * κ * ell ≤ R) (hc : 5 ≤ c) {W : ℕ} (hW : 1 ≤ W) (hWR : W ≤ R * M * ell)
include hell0 hS hκ hM hell hR1 hR hc hW hWR

/-- **W1 `ginvIMS_of`**. -/
theorem ginvIMS_of (U : LinkCfg (scaleUp ell k Lu)) (a cs : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs)
    (Gi : YP (geomOf ell k S) →L[ℝ] YP (geomOf ell k S))
    (hG1 : ∀ u, (ContinuousLinearMap.adjoint (Xop (geomOf ell k S) U a) ∘L Xop (geomOf ell k S) U a) (Gi u) = u)
    (hG2 : ∀ u, Gi ((ContinuousLinearMap.adjoint (Xop (geomOf ell k S) U a) ∘L Xop (geomOf ell k S) U a) u) = u)
    (γ : ℝ) (hγ0 : 0 ≤ γ)
    (hγ : ∀ u, ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) u‖ ≤ γ * ‖Xop (geomOf ell k S) U a u‖)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hreg : HolRegime S ell k U ρ)
    (CM : ℝ) (hCM : 0 ≤ CM) (hMass : MassComm ell M k κ c S U a CM)
    (ε1 ε2 : ℝ) (hε1 : 0 < ε1) (hε2 : 0 < ε2) (hη : etaC ell W cs ρ ε1 < 1) :
    GinvIMS ell M k κ c Lu hell0 S U a Lam
      ((1 + etaC ell W cs ρ ε1) * (1 + ε2) / (1 - etaC ell W cs ρ ε1) - 1)
      ((1 + etaC ell W cs ρ ε1) * (1 + ε2) * (2 * nuC ell ρ) / (1 - etaC ell W cs ρ ε1)
        + (1 + etaC ell W cs ρ ε1) * C1c ell M κ c W a cs γ CM ε2 + 2 * nuC ell ρ) := by
  intro A
  have ha0 : 0 ≤ a := hp.ha.le
  set B : BondFnL2 (scaleUp ell k Lu) := (A : BondFnL2 (scaleUp ell k Lu)) with hBdef
  set η := etaC ell W cs ρ ε1
  set ν := nuC ell ρ
  have hcs := hp.hcs
  have hν0 : 0 ≤ ν := by
    unfold ν nuC; have : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num); positivity
  have hη0 : 0 ≤ η := by
    unfold η etaC
    have := dD_nonneg hS hW hell hR1 (by omega) hWR
    have : 0 ≤ nuC ell ρ := hν0
    positivity
  -- the forms
  have hF : ∀ p, ginvForm ell k Lu hell0 S U a Lam (locB ell M k κ c Lu hell0 S U a Lam p A)
      = Fform S ell k U a (bondMul (hbond ell M k κ c S p) B) := by
    intro p
    unfold ginvForm
    rw [ginv_form hell0 S U a Lam ha0 hp.hu]
    rfl
  have hFA : ginvForm ell k Lu hell0 S U a Lam A = Fform S ell k U a B := by
    unfold ginvForm
    rw [ginv_form hell0 S U a Lam ha0 hp.hu]
    rfl
  have hsand := fun X => sandwich hS hell hR1 (by omega) hW hWR U a cs hp ρ hρ hreg ε1 hε1 X
  -- IMS for the three squares
  have hCC := ims_sq_upper' (fun X : BondFnL2 (scaleUp ell k Lu) => plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U X))
    (fun p X => bondMul (hbond ell M k κ c S p) X)
    (fun p y => plaqMul (fun q => AdalyFormal.M1.hpart ell M k κ c S p q.1) y) B
    (plaq_partition hS hκ hM hell hR1 hR hc (curlCovariantLM_L2 U B)) ε2 hε2
  have hCCe := cC_sum hS hκ hM hell hR1 hR hc U B
  have hMM := ims_sq_upper' (fun X : BondFnL2 (scaleUp ell k Lu) => Ymass (geomOf ell k S) U a X)
    (fun p X => bondMul (hbond ell M k κ c S p) X)
    (fun p y => rowMul (geomOf ell k S) (hrow ell M k κ c S p) y) B
    (row_partition hS hc hκ hM hell0 (Ymass (geomOf ell k S) U a B)) ε2 hε2
  have hMMe := hMass B
  have hTT := T_ims_concrete hS hκ hM hell hR1 hR hc hW hWR U a cs hp Gi hG1 hG2 γ hγ0 hγ B ε2 hε2
  set NB := ‖bondWt (-sigG (geomOf ell k S)) B‖ ^ 2
  have hNB : 0 ≤ NB := sq_nonneg _
  have hK0 := KG_nonneg ell M κ c
  have hε2' : 0 ≤ 1 + 1 / ε2 := by positivity
  have hims : ∑ p, G0form S ell k U a (bondMul (hbond ell M k κ c S p) B)
      ≤ (1 + ε2) * G0form S ell k U a B + C1c ell M κ c W a cs γ CM ε2 * NB := by
    unfold G0form
    simp only [Finset.sum_add_distrib]
    have e1 : ∑ p, ‖plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U (bondMul (hbond ell M k κ c S p) B))
          - plaqMul (fun q => AdalyFormal.M1.hpart ell M k κ c S p q.1) (plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U B))‖ ^ 2
        ≤ 12 * (ell : ℝ) ^ 2 * KG ell M κ c * NB := by
      refine le_trans (le_of_eq (Finset.sum_congr rfl (fun p _ => by rw [norm_sub_rev]))) hCCe
    have e2 : ∑ p, ‖Ymass (geomOf ell k S) U a (bondMul (hbond ell M k κ c S p) B)
          - rowMul (geomOf ell k S) (hrow ell M k κ c S p) (Ymass (geomOf ell k S) U a B)‖ ^ 2 ≤ CM * NB := by
      refine le_trans (le_of_eq (Finset.sum_congr rfl (fun p _ => by rw [norm_sub_rev]))) hMMe
    have t1 := mul_le_mul_of_nonneg_left e1 hε2'
    have t2 := mul_le_mul_of_nonneg_left e2 hε2'
    have hTT' : ∑ p, ‖Tfull (geomOf ell k S) U (bondMul (hbond ell M k κ c S p) B)‖ ^ 2
        ≤ (1 + ε2) * ‖Tfull (geomOf ell k S) U B‖ ^ 2 + 2 * (1 + 1 / ε2) * CTc ell M κ c W a cs γ * NB := hTT
    unfold C1c
    nlinarith [hCC, hMM, hTT', t1, t2]
  have hN := nsum_partition hS hc hκ hM hell0 B (fun b hb => A.2 b hb)
  have key := sandwich_ims
    (fun p => ginvForm ell k Lu hell0 S U a Lam (locB ell M k κ c Lu hell0 S U a Lam p A))
    (fun p => G0form S ell k U a (bondMul (hbond ell M k κ c S p) B))
    (fun p => ‖bondWt (-sigG (geomOf ell k S)) (bondMul (hbond ell M k κ c S p) B)‖ ^ 2)
    (ginvForm ell k Lu hell0 S U a Lam A) (G0form S ell k U a B) NB η (2 * ν) (C1c ell M κ c W a cs γ CM ε2) ε2
    hη0 hη hε2.le (by positivity) hNB
    (fun p => by rw [hF p]; exact (hsand _).2)
    (by rw [hFA]; exact (hsand B).1)
    hims hN
  have hNw : NB ≤ wN ell k Lu hell0 S U a Lam A := N_le_wnorm hS hell0 B
  have hC10 : 0 ≤ C1c ell M κ c W a cs γ CM ε2 := by
    unfold C1c CTc
    have := dD_nonneg hS hW hell hR1 (by omega) hWR
    have := hp.ha
    positivity
  have hpos : 0 < 1 - η := by linarith
  have he0 : 0 ≤ (1 + η) * (1 + ε2) * (2 * ν) / (1 - η) + (1 + η) * C1c ell M κ c W a cs γ CM ε2 + 2 * ν := by
    positivity
  refine key.trans ?_
  have h1 : ((1 + η) * (1 + ε2) / (1 - η)) * ginvForm ell k Lu hell0 S U a Lam A
      = (1 + ((1 + η) * (1 + ε2) / (1 - η) - 1)) * ginvForm ell k Lu hell0 S U a Lam A := by ring
  rw [h1]
  refine add_le_add le_rfl ?_
  calc ((1 + η) * (1 + ε2) * (2 * ν) / (1 - η) + (1 + η) * C1c ell M κ c W a cs γ CM ε2 + 2 * ν) * NB
      ≤ ((1 + η) * (1 + ε2) * (2 * ν) / (1 - η) + (1 + η) * C1c ell M κ c W a cs γ CM ε2 + 2 * ν)
          * wN ell k Lu hell0 S U a Lam A := mul_le_mul_of_nonneg_left hNw he0

/-- **W4 `ginv_weighted_coercive`**: W1 (`ginvIMS_of`) + W3 (`PatchCoercive cP`, real tower) ⇒ stratified coercivity. -/
theorem ginv_weighted_coercive (U : LinkCfg (scaleUp ell k Lu)) (a cs : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs)
    (Gi : YP (geomOf ell k S) →L[ℝ] YP (geomOf ell k S))
    (hG1 : ∀ u, (ContinuousLinearMap.adjoint (Xop (geomOf ell k S) U a) ∘L Xop (geomOf ell k S) U a) (Gi u) = u)
    (hG2 : ∀ u, Gi ((ContinuousLinearMap.adjoint (Xop (geomOf ell k S) U a) ∘L Xop (geomOf ell k S) U a) u) = u)
    (γ : ℝ) (hγ0 : 0 ≤ γ)
    (hγ : ∀ u, ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) u‖ ≤ γ * ‖Xop (geomOf ell k S) U a u‖)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hreg : HolRegime S ell k U ρ)
    (CM : ℝ) (hCM : 0 ≤ CM) (hMass : MassComm ell M k κ c S U a CM)
    (ε1 ε2 : ℝ) (hε1 : 0 < ε1) (hε2 : 0 < ε2) (hη : etaC ell W cs ρ ε1 < 1)
    (cP : ℝ) (hP : PatchCoercive ell M k κ c Lu hell0 S U a Lam cP)
    (A : ↥(bondSupp (gparams ell k Lu hell0 S U a Lam).G)) :
    ((cP - ((1 + etaC ell W cs ρ ε1) * (1 + ε2) * (2 * nuC ell ρ) / (1 - etaC ell W cs ρ ε1)
        + (1 + etaC ell W cs ρ ε1) * C1c ell M κ c W a cs γ CM ε2 + 2 * nuC ell ρ))
      / (1 + ((1 + etaC ell W cs ρ ε1) * (1 + ε2) / (1 - etaC ell W cs ρ ε1) - 1)))
      * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))
      ≤ ⟪A, (gparams ell k Lu hell0 S U a Lam).data.Ginv A⟫ := by
  have hη0 : 0 ≤ etaC ell W cs ρ ε1 := by
    unfold etaC nuC
    have := dD_nonneg hS hW hell hR1 (by omega) hWR
    have := hp.hcs
    have : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    positivity
  have hε : 0 ≤ (1 + etaC ell W cs ρ ε1) * (1 + ε2) / (1 - etaC ell W cs ρ ε1) - 1 := by
    have hpos : 0 < 1 - etaC ell W cs ρ ε1 := by linarith
    rw [sub_nonneg, le_div_iff₀ hpos]
    nlinarith
  exact ginv_weighted_coercive_of ell M k κ c Lu hell0 S U a Lam hc hκ hM _ _ cP hε
    (ginvIMS_of hell0 hS hκ hM hell hR1 hR hc hW hWR U a cs Lam hp Gi hG1 hG2 γ hγ0 hγ ρ hρ hreg CM hCM hMass
      ε1 ε2 hε1 hε2 hη) hP A

end main

end AdalyFormal.M1IMS

#print axioms AdalyFormal.M1IMS.ginvIMS_of
#print axioms AdalyFormal.M1IMS.ginv_weighted_coercive
#print axioms AdalyFormal.M1IMS.CTc
#print axioms AdalyFormal.M1IMS.nuC
#print axioms AdalyFormal.M1IMS.etaC
#print axioms AdalyFormal.M1IMS.C1c
