import CvO33
import CvO15
import CvO18

/-!
# CvOU1 -- unit level: `Q₁` and `C̃⁽²⁾` of a sigma_3 Z-field on a temporal unit background (lane omega)

For a temporal unit background `V0` (`IsTemporal 1 V0 a`) satisfying `RegBg2 1 ell V0`, and a profile `g` with vanishing `ell`-block sums:
`Q1jet ell V0 (zfield g) = 0` at every coarse bond and `C2tilde ell V0 (zfield g) = 0`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega

open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.IngredientFamilyR2

variable {L : PeriodicLatticeExtent}

/-- angles of a temporal configuration. -/
def phiT (a : ℕ → ℝ) : PeriodicLatticeEdge L → ℝ := fun e => if e.2 = 0 then a (e.1 0).val else 0

theorem cartanOf_phiT {V : PeriodicLinkConfiguration SU2 L} {a : ℕ → ℝ} (hV : IsTemporal 1 V a) : V = cartanOf (phiT a) := by
  funext e
  obtain ⟨y, μ⟩ := e
  obtain ⟨h0, h1, h2⟩ := hV y (fun μ => one_dvd _)
  fin_cases μ
  · simpa [cartanOf, phiT] using h0
  · simp only [cartanOf, phiT]; simp [h1, cartan_zero]
  · simp only [cartanOf, phiT]; simp [h2, cartan_zero]

theorem pathAngG_phiT (s : ℕ) (a : ℕ → ℝ) (p : List (Fin 3)) : ∀ y : PeriodicLatticeSite L, pathAngG s (phiT a) y p = tAng s a y p := by
  induction p with
  | nil => intro y; rfl
  | cons μ rest ih => intro y; simp only [pathAngG, tAng, ih, phiT]

theorem loopAngG_phiT (s ell : ℕ) (a : ℕ → ℝ) (y : PeriodicLatticeSite L) (μ : Fin 3) (x : PeriodicLatticeSite L)
    (hx : x ∈ stepBlockOf y s ell) : loopAngG s ell (phiT a) y μ x = 0 := by
  unfold loopAngG
  rw [pathAngG_phiT, pathAngG_phiT, pathAngG_phiT, pathAngG_phiT]
  exact tAng_loop_expr a μ hx

theorem suCoordF_zfield (f : ℕ → ℝ) : suCoordF (zfun f : Bond L → SuTwo) = aF (thetaF f) := by
  funext b
  show fromM2 ((zfun f b : SuTwo) : M2) = _
  unfold zfun thetaF aF
  by_cases h : b.2 = 1
  · simp only [if_pos h]; rw [dgS_coe, fromM2_dg]
  · simp only [if_neg h]
    show fromM2 ((0 : SuTwo) : M2) = _
    simp [fromM2]

theorem suCoordFInv_aF (θ : PeriodicLatticeEdge L → ℝ) (b : PeriodicLatticeEdge L) : (suCoordFInv (aF θ) : Bond L → SuTwo) b = dgS (θ b) := by
  show (⟨toM2 (aF θ b), toM2_mem _⟩ : SuTwo) = dgS (θ b)
  apply Subtype.ext
  show toM2 (aF θ b) = ((dgS (θ b) : SuTwo) : M2)
  rw [dgS_coe]; exact toM2_aF _

/-- **`Q₁` kills a sigma_3 Z-field with vanishing block sums.** -/
theorem Q1jet_zfield_zero {ell : ℕ} (hell : 0 < ell) (hdiv : ∀ μ, ell ∣ L μ + 1) {V0 : PeriodicLinkConfiguration SU2 L} {a : ℕ → ℝ}
    (hV : IsTemporal 1 V0 a) (hreg : RegBg2 1 ell V0) (g : ℕ → ℝ) (hblk : ∀ q : ℕ, ∑ n ∈ Finset.range ell, g (ell * q + n) = 0)
    (c : CoarseBond L ell) : Q1jet ell V0 (zfun g) c = 0 := by
  have hV' := cartanOf_phiT hV
  have hφ : ∀ cc : PeriodicLatticeEdge L, ∀ x ∈ stepBlockOf cc.1 1 ell, |loopAngG 1 ell (phiT a) cc.1 cc.2 x| < Real.pi := by
    intro cc x hx
    rw [loopAngG_phiT 1 ell a cc.1 cc.2 x hx, abs_zero]; exact Real.pi_pos
  have hreg' : RegBg2 1 ell (cartanOf (phiT a) : PeriodicLinkConfiguration SU2 L) := by rw [← hV']; exact hreg
  have hQ : QlinStepL 1 ell V0 (aF (thetaF g)) = aF (Rsig 1 ell (thetaF g)) := by
    rw [QlinStepL_eq_of_reg2 1 ell V0 hreg, hV']
    exact QlinStepX_sigma3 1 ell (phiT a) hφ hreg' (thetaF g)
  show ((ell : ℝ)⁻¹) • (suCoordFInv (QlinStepL 1 ell V0 (suCoordF (zfun g)))) (c.1.1, c.2) = 0
  rw [suCoordF_zfield, hQ, suCoordFInv_aF]
  have hy : Crs (1 * ell) c.1.1 := by
    intro μ
    have := (AdalyFormal.Balaban.AdmissibleSubspace.mem_CoarseLattice.mp c.1.2) μ
    rw [one_mul]; exact Nat.dvd_of_mod_eq_zero this
  have hdiv' : ∀ μ, 1 * ell ∣ L μ + 1 := fun μ => by rw [one_mul]; exact hdiv μ
  rw [Rsig_formF one_pos hell hdiv' (formF_thetaF g) c.1.1 hy c.2]
  by_cases h1 : c.2 = 1
  · rw [if_pos h1]
    obtain ⟨q, hq⟩ := hy 0
    rw [one_mul] at hq
    have : ∑ n ∈ Finset.range ell, g ((c.1.1 0).val + 1 * n) = 0 := by
      rw [hq]; simpa using hblk q
    rw [this, dgS_zero, smul_zero]
  · rw [if_neg h1, dgS_zero, smul_zero]

/-- **`C̃⁽²⁾` kills any sigma_3 Z-field**. -/
theorem C2tilde_zfield_zero {ell : ℕ} {V0 : PeriodicLinkConfiguration SU2 L} {a : ℕ → ℝ}
    (hV : IsTemporal 1 V0 a) (hreg : RegBg2 1 ell V0) (g : ℕ → ℝ) (c : CoarseBond L ell) :
    C2tilde ell V0 (zfun g) c = 0 := by
  have hV' := cartanOf_phiT hV
  have hφ : ∀ cc : PeriodicLatticeEdge L, ∀ x ∈ stepBlockOf cc.1 1 ell, |loopAngG 1 ell (phiT a) cc.1 cc.2 x| < Real.pi := by
    intro cc x hx
    rw [loopAngG_phiT 1 ell a cc.1 cc.2 x hx, abs_zero]; exact Real.pi_pos
  have hreg' : RegBg2 1 ell (cartanOf (phiT a) : PeriodicLinkConfiguration SU2 L) := by rw [← hV']; exact hreg
  have hC : C2StepL 1 ell V0 (aF (thetaF g)) = 0 := by
    rw [C2StepL_eq_C2StepX2 1 ell V0 hreg, hV']
    exact C2StepX_sigma3 1 ell (phiT a) hφ hreg' (thetaF g)
  show (suCoordFInv (C2StepL 1 ell V0 (suCoordF (zfun g)))) (c.1.1, c.2) = 0
  rw [suCoordF_zfield, hC]
  have : (suCoordFInv (0 : XS L)) = (0 : Bond L → SuTwo) := by
    funext b; apply Subtype.ext
    show toM2 ((0 : XS L) b) = ((0 : Bond L → SuTwo) b : SuTwo)
    rw [show (0 : XS L) b = 0 from rfl, map_zero]; rfl
  rw [this]; rfl

#print axioms Q1jet_zfield_zero
#print axioms C2tilde_zfield_zero

end AdalyFormal.CoverOmega
