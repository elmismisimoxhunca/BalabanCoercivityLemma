import AdalyFormal.Balaban.LemmaAssembly
import AdalyFormal.Balaban.AlphaAnalyticity
import AdalyFormal.Balaban.DeltaPrimeOperator

/-!
# GC1 -- matrix-level gauge covariance of the plaquette form `bilPlaq` (the `Δ'` summand)
`bilPlaq (U^γ) p (A^γ) (B^γ) = bilPlaq U p A B`, `A^γ b = R(γ b₋) A b`.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.GaugeCov
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_mul_apply RMap_coe_apply)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn gaugeActA gaugeActA_apply curlValueCovariant_gauge)
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.SuTwoInner (conjTranspose_mul_self)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

variable {L : PeriodicLatticeExtent}

abbrev SU2g := Matrix.specialUnitaryGroup (Fin 2) ℂ
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

/-- matrix conjugation by `g`. -/
def cjM (g : SU2g) (M : Mat2) : Mat2 := (g : Mat2) * M * (g : Mat2)ᴴ

theorem mul_conjT (g : SU2g) : (g : Mat2) * (g : Mat2)ᴴ = 1 := by
  have h := Matrix.mem_unitaryGroup_iff.mp g.2.1
  rwa [Matrix.star_eq_conjTranspose] at h

theorem cjM_mul (g : SU2g) (X Y : Mat2) : cjM g X * cjM g Y = cjM g (X * Y) := by
  have h := conjTranspose_mul_self g
  unfold cjM
  calc (g : Mat2) * X * (g : Mat2)ᴴ * ((g : Mat2) * Y * (g : Mat2)ᴴ)
      = (g : Mat2) * X * ((g : Mat2)ᴴ * (g : Mat2)) * Y * (g : Mat2)ᴴ := by noncomm_ring
    _ = (g : Mat2) * (X * Y) * (g : Mat2)ᴴ := by rw [h]; noncomm_ring

theorem trace_cjM (g : SU2g) (X : Mat2) : Matrix.trace (cjM g X) = Matrix.trace X := by
  have h := conjTranspose_mul_self g
  unfold cjM
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, h, Matrix.mul_one]

theorem cjM_smul (g : SU2g) (c : ℂ) (X : Mat2) : cjM g (c • X) = c • cjM g X := by
  unfold cjM; rw [Matrix.mul_smul, Matrix.smul_mul]

theorem cjM_add (g : SU2g) (X Y : Mat2) : cjM g (X + Y) = cjM g X + cjM g Y := by
  unfold cjM; rw [Matrix.mul_add, Matrix.add_mul]

theorem cjM_sub (g : SU2g) (X Y : Mat2) : cjM g (X - Y) = cjM g X - cjM g Y := by
  unfold cjM; rw [Matrix.mul_sub, Matrix.sub_mul]

theorem cjM_one (g : SU2g) : cjM g 1 = 1 := by
  unfold cjM; rw [Matrix.mul_one]; exact mul_conjT g

theorem cjM_neg (g : SU2g) (X : Mat2) : cjM g (-X) = - cjM g X := by
  unfold cjM; rw [Matrix.mul_neg, Matrix.neg_mul]

theorem coe_RMap_gauge (g : SU2g) (X : SuTwo) :
    ((RMap g X : SuTwo) : Mat2) = cjM g (X : Mat2) := RMap_coe_apply g X

theorem coe_inv_g (x : SU2g) : ((x⁻¹ : SU2g) : Mat2) = (x : Mat2)ᴴ := by
  rfl

theorem coe_conj_g (g h : SU2g) : ((g * h * g⁻¹ : SU2g) : Mat2) = cjM g (h : Mat2) := by
  unfold cjM
  rw [Submonoid.coe_mul, Submonoid.coe_mul, coe_inv_g]

theorem hol_inv_gauge (γ : GaugeFn L) (U : PeriodicLinkConfiguration SU2g L)
    (p : PeriodicLatticePlaquette L) :
    holonomyElemInv (periodicGaugeTransform γ U) p = γ p.1 * holonomyElemInv U p * (γ p.1)⁻¹ := by
  unfold holonomyElemInv
  rw [AdalyFormal.Balaban.LemmaAssembly.holonomyElem_gauge]
  group

theorem reHol_gauge (γ : GaugeFn L) (U : PeriodicLinkConfiguration SU2g L)
    (p : PeriodicLatticePlaquette L) :
    reHolonomy (periodicGaugeTransform γ U) p = cjM (γ p.1) (reHolonomy U p) := by
  unfold reHolonomy
  rw [AdalyFormal.Balaban.LemmaAssembly.holonomyElem_gauge, hol_inv_gauge, coe_conj_g, coe_conj_g,
    cjM_smul, cjM_add]

theorem imHol_gauge (γ : GaugeFn L) (U : PeriodicLinkConfiguration SU2g L)
    (p : PeriodicLatticePlaquette L) :
    imHolonomy (periodicGaugeTransform γ U) p = cjM (γ p.1) (imHolonomy U p) := by
  unfold imHolonomy
  rw [AdalyFormal.Balaban.LemmaAssembly.holonomyElem_gauge, hol_inv_gauge, coe_conj_g, coe_conj_g,
    cjM_smul, cjM_sub]

theorem curlMat_gauge (γ : GaugeFn L) (U : PeriodicLinkConfiguration SU2g L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    curlMatLM (periodicGaugeTransform γ U) p (gaugeActA γ A) = cjM (γ p.1) (curlMatLM U p A) := by
  rw [curlMatLM_apply, curlMatLM_apply, curlValueCovariant_gauge, coe_RMap_gauge]

theorem a3_gauge (γ : GaugeFn L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    a3LM p (gaugeActA γ A) = cjM (γ p.1) (a3LM p A) := by
  show ((RMap (γ p.1) (A (p.1, p.2.1.1)) : SuTwo) : Mat2) = _
  rw [coe_RMap_gauge]; rfl

theorem a2_gauge (γ : GaugeFn L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    a2LM p (gaugeActA γ A) = cjM (γ p.1) (a2LM p A) := by
  show - ((RMap (γ p.1) (A (p.1, p.2.1.2)) : SuTwo) : Mat2) = _
  rw [coe_RMap_gauge, show a2LM p A = - ((A (p.1, p.2.1.2) : SuTwo) : Mat2) from rfl, cjM_neg]

theorem a4_gauge (γ : GaugeFn L) (U : PeriodicLinkConfiguration SU2g L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    a4LM (periodicGaugeTransform γ U) p (gaugeActA γ A) = cjM (γ p.1) (a4LM U p A) := by
  show ((RMap (periodicGaugeTransform γ U (p.1, p.2.1.1))
      (RMap (γ (periodicLatticeShift p.1 p.2.1.1)) (A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2))) : SuTwo) : Mat2)
    = cjM (γ p.1) ((RMap (U (p.1, p.2.1.1)) (A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)) : SuTwo) : Mat2)
  rw [← coe_RMap_gauge, RMap_mul_apply, RMap_mul_apply]
  congr 3
  show γ p.1 * U (p.1, p.2.1.1) * (γ (periodicLatticeShift p.1 p.2.1.1))⁻¹
    * γ (periodicLatticeShift p.1 p.2.1.1) = γ p.1 * U (p.1, p.2.1.1)
  group

theorem a1_gauge (γ : GaugeFn L) (U : PeriodicLinkConfiguration SU2g L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    a1LM (periodicGaugeTransform γ U) p (gaugeActA γ A) = cjM (γ p.1) (a1LM U p A) := by
  show - ((RMap (periodicGaugeTransform γ U (p.1, p.2.1.2))
      (RMap (γ (periodicLatticeShift p.1 p.2.1.2)) (A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))) : SuTwo) : Mat2)
    = cjM (γ p.1) (- ((RMap (U (p.1, p.2.1.2)) (A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)) : SuTwo) : Mat2))
  rw [cjM_neg, ← coe_RMap_gauge, RMap_mul_apply, RMap_mul_apply]
  congr 4
  show γ p.1 * U (p.1, p.2.1.2) * (γ (periodicLatticeShift p.1 p.2.1.2))⁻¹
    * γ (periodicLatticeShift p.1 p.2.1.2) = γ p.1 * U (p.1, p.2.1.2)
  group

theorem cjM_sub_one (g : SU2g) (R : Mat2) : cjM g R - 1 = cjM g (R - 1) := by
  rw [cjM_sub, cjM_one]

/-- **`bilPlaq` is gauge invariant**: `bilPlaq (U^γ) p (A^γ) (B^γ) = bilPlaq U p A B`. -/
theorem bilPlaq_gauge (γ : GaugeFn L) (U : PeriodicLinkConfiguration SU2g L)
    (p : PeriodicLatticePlaquette L) (A B : Bond L → SuTwo) :
    bilPlaq (periodicGaugeTransform γ U) p (gaugeActA γ A) (gaugeActA γ B) = bilPlaq U p A B := by
  rw [bilPlaq_atoms, bilPlaq_atoms]
  simp only [b1LM, b2LM, b3LM, b4LM, LinearMap.comp_apply, smulILM_apply,
    a1_gauge, a2_gauge, a3_gauge, a4_gauge, curlMat_gauge, reHol_gauge, imHol_gauge,
    ← cjM_smul, cjM_sub_one, cjM_mul, trace_cjM]

#print axioms bilPlaq_gauge
#print axioms reHol_gauge
#print axioms imHol_gauge
#print axioms curlMat_gauge
#print axioms a1_gauge
#print axioms a4_gauge

end AdalyFormal.GaugeCov
