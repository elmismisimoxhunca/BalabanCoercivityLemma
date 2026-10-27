import MC3
import MF9
import GCz3

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000

/-!
# MC4 -- the M0 theorem (`instIneq_M0_class`, MF9) applied to the printed class: hypotheses of MF9 from `GlobalRegular2`,
conclusion = the headline's inner claim at (fullTower, Lam).  Gauge step by `GaugeCov.instIneq_gauge_iff`.
-/
namespace AdalyFormal.M0Corollary

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLaneG AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.AsmM0
open AdalyFormal.CurvBlock (dv)
open AdalyFormal.RegBgKU (KUSmall)
open AdalyFormal.M0Finish

/-- the two D-layer premises of MF9/MF7 at a configuration `U'` (stated verbatim as in `instIneq_M0_class`). -/
def DLayer (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (ε2s εJ : ℝ) : Prop :=
  ‖(PU ell k Lu hell U a Lam).data.Delta2 (PU ell k Lu hell U a Lam).data_laws‖ ≤ ε2s / ((ell : ℝ) ^ k) ^ 2 ∧
  ∀ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt → OnLambdaT Lam Bt →
        |⟪(PU ell k Lu hell U a Lam).H1in ((PU ell k Lu hell U a Lam).D2in
            (WithLp.toLp 2 (Cop Lam (PU ell k Lu hell U a Lam).Q1 Bt))), (PU ell k Lu hell U a Lam).Jf⟫|
          ≤ εJ * ‖(WithLp.toLp 2 (Cop Lam (PU ell k Lu hell U a Lam).Q1 Bt) : BondFnL2 Lu)‖ ^ 2

/-- **M0 on the printed class.**  `U` in the whole-torus single-gauge class `GlobalRegular2 .. 12 ..`; with `α := 12 M α₀`, `ᾱ := (4π+4) α`, the
M0 theorem (MF9) applies to the class gauge `U^g` (links `≤ ᾱ/ellᵏ`, plaquettes `≤ ᾱ/ell²ᵏ` are PROVED from clauses 1, 2; clause 3 is not used), and
`InstIneq` at `U` follows by gauge invariance.  Remaining premises: the `k`-free numeric smallness of `ᾱ` (functions of `(ell, a, t, ᾱ)` only) and the two
D-layer premises at every regime-configuration. -/
theorem M0_class_conclusion (ell M k : ℕ) (hell2 : 2 ≤ ell) (Lu : PeriodicLatticeExtent) (hT : TorusOK ell M Lu)
    (U : LinkCfg (scaleUp ell k Lu)) (a t α₀ ᾱ : ℝ) (hle : (4 * Real.pi + 4) * (12 * M * α₀) ≤ ᾱ) (ha : 0 < a) (ht : 0 < t) (hα₀ : 0 < α₀)
    (Lam : Set (PeriodicLatticeSite Lu)) (hLB : LamBlockSum ell Lam)
    (hU : GlobalRegular2 ell M 12 k α₀ ((ell : ℝ) ^ k)⁻¹ U)
    (hcb : 4000000 * (ell : ℝ) ^ 2 * ᾱ ≤ 1)
    (h216 : 216 * ((1 + 3 * Real.pi) * ᾱ) ^ 2 < 1)
    (h1000 : (1 + 3 * Real.pi) * ᾱ ≤ 1 / (1000 * (ell : ℝ) ^ 3))
    (hsmallU : ThetaM0 ell a t ((1 + 3 * Real.pi) * ᾱ) < min a 1 / 1000)
    (H : KUSmall ell ((1 + 3 * Real.pi) * ᾱ))
    (HU : UnitSmall ell ((1 + 3 * Real.pi) * ᾱ))
    (ε2s εJ : ℝ) (hε2s : 0 ≤ ε2s) (hεJ : 0 ≤ εJ)
    (hε' : ε2s * KhatM0 ell a t ((1 + 3 * Real.pi) * ᾱ) < 1)
    (hD : ∀ g : PeriodicLatticeSite (scaleUp ell k Lu) → Matrix.specialUnitaryGroup (Fin 2) ℂ,
      (∀ b, dv (periodicGaugeTransform g U b) ≤ ᾱ / (ell : ℝ) ^ k) →
      (∀ p : PeriodicLatticePlaquette (scaleUp ell k Lu),
        dv (periodicPlaquetteHolonomy (periodicGaugeTransform g U) p)
          ≤ ᾱ / ((ell : ℝ) ^ k) ^ 2) →
      DLayer ell k Lu (by omega) (periodicGaugeTransform g U) a Lam ε2s εJ) :
    InstIneq ell k (by omega) a Lu
      (gam0M0 ell a t ((1 + 3 * Real.pi) * ᾱ) ε2s εJ
        (dCM0 ell ((1 + 3 * Real.pi) * ᾱ))
        (cBM0 ell ((1 + 3 * Real.pi) * ᾱ)))
      (fullTower ell k Lu) Lam U := by
  have hell : 0 < ell := by omega
  set α : ℝ := 12 * M * α₀ with hαdef
  have hα0 : 0 ≤ α := by positivity
  have hpi := Real.pi_pos
  have hαᾱ' : α ≤ (4 * Real.pi + 4) * α := by nlinarith
  have hαᾱ : α ≤ ᾱ := hαᾱ'.trans hle
  have hᾱ0 : 0 ≤ ᾱ := hα0.trans hαᾱ
  have hell3 : (0 : ℝ) < (ell : ℝ) ^ 3 := by positivity
  have hᾱ1 : ᾱ ≤ 1 := by
    have h1 : (1 + 3 * Real.pi) * ᾱ ≤ 1 / (1000 * (ell : ℝ) ^ 3) := h1000
    have h2 : 1 / (1000 * (ell : ℝ) ^ 3) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (1 : ℝ) ≤ (ell : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast hell)
      linarith
    nlinarith
  have hα1 : α ≤ 1 := hαᾱ.trans hᾱ1
  have hcast : ((12 : ℕ) : ℝ) * M * α₀ = α := by rw [hαdef]; norm_num
  obtain ⟨g, hl, hp⟩ := regime_of_regular12 hell (f := 12) (hU.toRegular12) (by rw [hcast]; exact hα0) (by rw [hcast]; exact hα1)
  rw [hcast] at hl hp
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := pow_pos (by exact_mod_cast hell) k
  have hn1 : (1 : ℝ) ≤ (ell : ℝ) ^ k := one_le_pow₀ (by exact_mod_cast hell)
  have hl' : ∀ b, dv (periodicGaugeTransform g U b) ≤ ᾱ / (ell : ℝ) ^ k := fun b =>
    (hl b).trans (div_le_div_of_nonneg_right hαᾱ hn.le)
  have hp' : ∀ p : PeriodicLatticePlaquette (scaleUp ell k Lu),
      dv (periodicPlaquetteHolonomy (periodicGaugeTransform g U) p) ≤ ᾱ / ((ell : ℝ) ^ k) ^ 2 := by
    intro p
    refine (hp p).trans (div_le_div_of_nonneg_right ?_ (by positivity))
    nlinarith [sq_nonneg α, mul_nonneg hα0 (sub_nonneg.mpr hα1)]
  obtain ⟨hD2, hJ⟩ := hD g hl' hp'
  have key := instIneq_M0_class ell k Lu hell hell2 (periodicGaugeTransform g U) a t ᾱ ha ht hᾱ0
    (fun μ => hT.2.1 μ) (fun μ => hT.1 μ) Lam hLB hl' hp' hcb h216 h1000 hsmallU H HU ε2s εJ hε2s hεJ hε' hD2 hJ
  exact (AdalyFormal.GaugeCov.instIneq_gauge_iff g).mp key

#print axioms M0_class_conclusion

end AdalyFormal.M0Corollary
