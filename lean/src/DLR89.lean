import DLR88
import MC8e
import MC3
import GCz3

/-!
# DL89 -- the NON-VACUITY WITNESS of `instIneq_M0_class_unconditional`, every `k`, and two corollaries

* `instIneq_mono` : `InstIneq` at `γ` implies `InstIneq` at every `γ' ≤ γ` (`bondEnergy ≥ 0`).
* `ufield_regime` : an abelian field `U = exp(iηχσ₃)` whose `χ` obeys the two class bounds (`|χ|√2 < c1`,
  `|η⁻¹∇χ|√2 < c2`) has, IN ITS OWN GAUGE (chart `g = 1`, `A = χσ₃`; CB9 `cube_link`/`cube_plaq`),
  links `dv ≤ ηc1` and plaquettes `dv ≤ 2η²c2 + (4π+2)(ηc1)²`.
* `sine_bounds` : the sine profile of MC8 obeys them with `c1 = c2 = α` (amplitude `α/2`, wavelength `Lu 0 + 1 ≥ 16`).
* `instIneq_M0_class_rho` : DL84 restated at a `k`-free `ρ` (`rhoM0 ℓ k e q0 = ρ`).
* `instIneq_globalRegular2_unconditional` : every `U` in the whole-torus printed class `GlobalRegular2 ℓ M 12 k α₀ ℓ⁻ᵏ`
  satisfies the frozen r7 `InstIneq` at `(fullTower, Λ)` — M0 regime in the class gauge (MC3), class gauge-invariant (ZR2A),
  `InstIneq` gauge-invariant (GCz3) — with NO D-layer hypothesis (the M0 analogue of MC4 `M0_class_conclusion` minus `hD`).
* **`M0Core_two`** : `M0Core 2 M _ 1` (MC2's M0 inner claim) for EVERY `M`, with `a₀ = epsB·10⁻³⁰⁰`, `γ₀ = 9·10⁻⁵`.
* **`witness_all_k`** : for EVERY `k`, the smooth abelian sine field `Uw k` (ℓ = 2, M = 1, f = 12, α₀ = epsB·10⁻³⁰⁰,
  `Lu = (15,15,15)`) satisfies EVERY hypothesis of `instIneq_M0_class_unconditional` (M0RegimeR for `Uw k` itself,
  KUSmall, UnitSmall, torus, LamBlockSum, the printed class `PerCubeRegular2` (all three clauses) and the whole-torus
  `GlobalRegular2`, `4fMα₀ ≤ 1`, the numerics package), and is CURVED (a plaquette with `dv > 0`).
* **`witness_instIneq`** : `InstIneq 2 k _ 1 Lu16 (9·10⁻⁵) (fullTower) univ (Uw k)` for every `k`, obtained by
  applying `instIneq_M0_class_unconditional` itself to `Uw k`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option exponentiation.threshold 1000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp TorusOK)
open AdalyFormal.StatementLane2 (PerCubeRegular2 Ufield sig Xm gauge_one smul_sig_eq frobNorm_rsmul_sig HT_rsmul_sig
  perCubeRegular2_gauge)
open AdalyFormal.StatementLaneG (LamBlockSum InstIneq lamBlockSum_univ)
open AdalyFormal.IngredientFamilyR2 (fullTower)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.CurvBlock (dv)
open AdalyFormal.AsmM0 (M0RegimeR rhoM0 KhatM0 ThetaM0)
open AdalyFormal.RegBgKU (KUSmall kapHat)
open AdalyFormal.M0Finish (UnitSmall dCM0 cBM0)
open AdalyFormal.M0Corollary (GlobalRegular2)

local notation "θ₀" => ((1 : ℝ) / 10 ^ 45)

/-- `InstIneq` is monotone in the constant -/
theorem instIneq_mono {ell k : ℕ} {hell : 0 < ell} {a : ℝ} {Lu : PeriodicLatticeExtent} {γ γ' : ℝ}
    {S : AdalyFormal.StatementLane.Tower (scaleUp ell k Lu)} {Lam : Set (PeriodicLatticeSite Lu)}
    {U : LinkCfg (scaleUp ell k Lu)} (hγ : γ' ≤ γ) (h : InstIneq ell k hell a Lu γ S Lam U) :
    InstIneq ell k hell a Lu γ' S Lam U := by
  intro Bt h1 h2
  have hE := AdalyFormal.Balaban.RegularUPerturbation.bondEnergy_nonneg Bt
  exact le_trans (mul_le_mul_of_nonneg_right hγ hE) (h Bt h1 h2)

/-- an abelian field obeying the two class bounds is in the M0 regime IN ITS OWN GAUGE -/
theorem ufield_regime {L : PeriodicLatticeExtent} (η c1 c2 : ℝ) (hη : 0 < η) (χ : Bond L → ℝ)
    (h1 : ∀ e, |χ e| * Real.sqrt 2 < c1)
    (h2 : ∀ (μ ν : Fin 3) (x : PeriodicLatticeSite L),
      |η⁻¹ * (χ (periodicLatticeShift x μ, ν) - χ (x, ν))| * Real.sqrt 2 < c2)
    (hsmall : η * c1 ≤ 1) :
    (∀ b, dv (Ufield η χ b) ≤ η * c1) ∧
    (∀ p : PeriodicLatticePlaquette L,
      dv (periodicPlaquetteHolonomy (Ufield η χ) p) ≤ 2 * (η ^ 2 * c2) + (4 * Real.pi + 2) * (η * c1) ^ 2) := by
  let K : AdalyFormal.CurvBlock.CubeChart (Ufield η χ) (fun _ => True) η c1 c2 :=
    { g := fun _ => 1
      A := fun e => χ e • sig
      hA := fun e _ => by
        refine ⟨HT_rsmul_sig _, ?_, ?_⟩
        · rw [gauge_one]
          show NormedSpace.exp (Xm (η * χ e)) = _
          rw [smul_sig_eq]
        · show AdalyFormal.Balaban.RMapLipschitz.frobNorm (χ e • sig) < c1
          rw [frobNorm_rsmul_sig]; exact h1 e
      hD := fun μ ν x _ _ => by
        have e1 : (η⁻¹ : ℝ) • (χ (periodicLatticeShift x μ, ν) • sig - χ (x, ν) • sig)
            = (η⁻¹ * (χ (periodicLatticeShift x μ, ν) - χ (x, ν))) • sig := by module
        show AdalyFormal.Balaban.RMapLipschitz.frobNorm
          ((η⁻¹ : ℝ) • (χ (periodicLatticeShift x μ, ν) • sig - χ (x, ν) • sig)) < c2
        rw [e1, frobNorm_rsmul_sig]
        exact h2 μ ν x }
  have hg : periodicGaugeTransform K.g (Ufield η χ) = Ufield η χ := gauge_one _
  refine ⟨fun b => ?_, ?_⟩
  · have := AdalyFormal.CurvBlock.cube_link hη K b trivial
    rwa [hg] at this
  · have hpw : ∀ y ν μ, dv (AdalyFormal.CurvBlock.pw 1 (periodicGaugeTransform K.g (Ufield η χ)) y ν μ)
        ≤ 2 * (η ^ 2 * c2) + (4 * Real.pi + 2) * (η * c1) ^ 2 := fun y ν μ =>
      AdalyFormal.CurvBlock.cube_plaq hη K hsmall (y, ν, μ) ⟨trivial, trivial, trivial, trivial⟩
    have := AdalyFormal.CurvBlock.plaq_of_pw_one _ _ hpw
    rwa [hg] at this

/-- the sine profile (MC8) obeys the two class bounds with `c1 = c2 = α` -/
theorem sine_bounds (ell k : ℕ) (hell : 0 < ell) (Lu : PeriodicLatticeExtent) (h16 : 16 ≤ Lu 0 + 1)
    (α : ℝ) (hα : 0 < α) :
    (∀ e, |AdalyFormal.M0Corollary.chiP (scaleUp ell k Lu) (α / 2) e| * Real.sqrt 2 < α) ∧
    (∀ (μ ν : Fin 3) (x : PeriodicLatticeSite (scaleUp ell k Lu)),
      |((ell : ℝ) ^ k)⁻¹⁻¹ * (AdalyFormal.M0Corollary.chiP (scaleUp ell k Lu) (α / 2) (periodicLatticeShift x μ, ν)
        - AdalyFormal.M0Corollary.chiP (scaleUp ell k Lu) (α / 2) (x, ν))| * Real.sqrt 2 < α) := by
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := pow_pos (by exact_mod_cast hell) k
  set Ac : ℝ := α / 2 with hAc
  have hAc0 : 0 < Ac := by positivity
  have hN0 : (((scaleUp ell k Lu) 0 + 1 : ℕ) : ℝ) = ((Lu 0 + 1 : ℕ) : ℝ) * (ell : ℝ) ^ k := by
    rw [AdalyFormal.IngredientFamilyR2.scaleUp_succ ell k Lu hell 0]; push_cast; ring
  set θ : ℝ := 2 * Real.pi / ((Lu 0 + 1 : ℕ) : ℝ) with hθ
  have h16r : (16 : ℝ) ≤ ((Lu 0 + 1 : ℕ) : ℝ) := by exact_mod_cast h16
  have hpi := Real.pi_lt_d2
  have hθ0 : 0 < θ := by rw [hθ]; positivity
  have hθ1 : θ ≤ 0.4 := by
    rw [hθ, div_le_iff₀ (by linarith)]; nlinarith
  have hh : (2 * Real.pi / (((scaleUp ell k Lu) 0 + 1 : ℕ) : ℝ)) = ((ell : ℝ) ^ k)⁻¹ * θ := by
    rw [hN0, hθ]; field_simp
  have hs2 : Real.sqrt 2 < 1.5 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs0 : 0 < Real.sqrt 2 := by positivity
  constructor
  · intro e
    have := AdalyFormal.M0Corollary.chiP_abs (scaleUp ell k Lu) Ac e
    rw [abs_of_pos hAc0] at this
    nlinarith
  · intro μ ν x
    rw [AdalyFormal.M0Corollary.chiP_diff (scaleUp ell k Lu) Ac x μ ν]
    have hD := AdalyFormal.M0Corollary.Dd_abs (scaleUp ell k Lu) Ac x
    rw [abs_of_pos hAc0, hh] at hD
    have key : |((ell : ℝ) ^ k)⁻¹⁻¹ * (if ν = 1 then (if μ = 0 then AdalyFormal.M0Corollary.Dd (scaleUp ell k Lu) Ac x
        else 0) else 0)| ≤ Ac * θ := by
      rw [inv_inv]
      split_ifs
      · rw [abs_mul, abs_of_pos hn]
        calc _ ≤ (ell : ℝ) ^ k * (Ac * (((ell : ℝ) ^ k)⁻¹ * θ)) := mul_le_mul_of_nonneg_left hD hn.le
          _ = Ac * θ := by field_simp
      all_goals simp; positivity
    have : |((ell : ℝ) ^ k)⁻¹⁻¹ * (if ν = 1 then (if μ = 0 then AdalyFormal.M0Corollary.Dd (scaleUp ell k Lu) Ac x
        else 0) else 0)| * Real.sqrt 2 ≤ Ac * θ * 1.5 :=
      mul_le_mul key hs2.le hs0.le (by positivity)
    nlinarith

/-- DL84 at a `k`-free value `ρ` of `rhoM0 ℓ k e q0` -/
theorem instIneq_M0_class_rho (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (U : LinkCfg (scaleUp ell k Lu)) (a t e q0 ρ : ℝ) (hρ : rhoM0 ell k e q0 = ρ) (R : M0RegimeR ell k Lu U a t e q0)
    (H : KUSmall ell ρ) (HU : UnitSmall ell ρ)
    (hstrict : ∀ μ : Fin 3, ell < Lu μ + 1) (hd : ∀ μ, ell ∣ Lu μ + 1)
    (Lam : Set (PeriodicLatticeSite Lu)) (hLB : LamBlockSum ell Lam)
    (M f : ℕ) (α₀ : ℝ) (hM : 0 < M) (hf : 4 ≤ f)
    (hP : PerCubeRegular2 ell M f k (fullTower ell k Lu) α₀ ((ell : ℝ) ^ k)⁻¹ U)
    (hsm : 4 * ((f : ℝ) * M * α₀) ≤ 1)
    (θ : ℝ) (Num : M0ClassNum ell a t ρ ((f : ℝ) * M * α₀) θ) :
    InstIneq ell k hell a Lu (gam0M0f ell a t ρ (eps2free Num) (epsJfree Num) (dCM0 ell ρ) (cBM0 ell ρ))
      (fullTower ell k Lu) Lam U := by
  subst hρ
  exact instIneq_M0_class_unconditional ell k Lu hell U a t e q0 R H HU hstrict hd Lam hLB M f α₀ hM hf hP hsm θ Num

/-- the M0 regime from link/plaquette bounds at scale `ᾱ` (MF9's construction) -/
theorem regime_of_bounds (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell2 : 2 ≤ ell) (U : LinkCfg (scaleUp ell k Lu))
    (a t ᾱ : ℝ) (ha : 0 < a) (ht : 0 < t) (hᾱ : 0 ≤ ᾱ) (hstrict : ∀ μ : Fin 3, ell < Lu μ + 1)
    (hlinks : ∀ b, dv (U b) ≤ ᾱ / (ell : ℝ) ^ k)
    (hplaq : ∀ p : PeriodicLatticePlaquette (scaleUp ell k Lu), dv (periodicPlaquetteHolonomy U p) ≤ ᾱ / ((ell : ℝ) ^ k) ^ 2)
    (hcb : 4000000 * (ell : ℝ) ^ 2 * ᾱ ≤ 1)
    (h216 : 216 * ((1 + 3 * Real.pi) * ᾱ) ^ 2 < 1)
    (h1000 : (1 + 3 * Real.pi) * ᾱ ≤ 1 / (1000 * (ell : ℝ) ^ 3))
    (hsmallU : ThetaM0 ell a t ((1 + 3 * Real.pi) * ᾱ) < min a 1 / 1000) :
    M0RegimeR ell k Lu U a t (ᾱ / (ell : ℝ) ^ k) (ᾱ / ((ell : ℝ) ^ k) ^ 2) := by
  have hell : 0 < ell := by omega
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := pow_pos (by exact_mod_cast hell) k
  have hρ := AdalyFormal.M0Finish.rhoM0_class ell k hell ᾱ
  refine ⟨hell2, ha, ht, by positivity, by positivity, ?_, hlinks, hplaq, ?_, by rw [hρ]; exact h216,
    by rw [hρ]; exact h1000, by rw [hρ]; exact hsmallU⟩
  · intro ρ'
    have h1 : scaleUp ell k Lu ρ' + 1 = (Lu ρ' + 1) * ell ^ k :=
      AdalyFormal.IngredientFamilyR2.scaleUp_succ ell k Lu hell ρ'
    have h2 : 3 ≤ Lu ρ' + 1 := by have := hstrict ρ'; omega
    have h3 := Nat.mul_le_mul_right (ell ^ k) h2
    have h4 : 0 < ell ^ k := pow_pos hell k
    omega
  · have e1 : ((ell : ℝ) ^ 2) ^ k * (ᾱ / ((ell : ℝ) ^ k) ^ 2) = ᾱ := by
      rw [← pow_mul, mul_comm 2 k, pow_mul]; field_simp
    rw [e1]; exact hcb

/-- **`InstIneq` on the whole-torus printed class, NO D-layer hypothesis** (MC4 `M0_class_conclusion` with `hD` discharged) -/
theorem instIneq_globalRegular2_unconditional (ell M k : ℕ) (hell2 : 2 ≤ ell) (Lu : PeriodicLatticeExtent)
    (hT : TorusOK ell M Lu) (U : LinkCfg (scaleUp ell k Lu)) (a t α₀ ᾱ : ℝ)
    (hle : (4 * Real.pi + 4) * ((12 : ℝ) * M * α₀) ≤ ᾱ) (ha : 0 < a) (ht : 0 < t) (hα₀ : 0 < α₀)
    (hsm : 4 * ((12 : ℝ) * M * α₀) ≤ 1)
    (Lam : Set (PeriodicLatticeSite Lu)) (hLB : LamBlockSum ell Lam)
    (hU : GlobalRegular2 ell M 12 k α₀ ((ell : ℝ) ^ k)⁻¹ U)
    (hcb : 4000000 * (ell : ℝ) ^ 2 * ᾱ ≤ 1)
    (h216 : 216 * ((1 + 3 * Real.pi) * ᾱ) ^ 2 < 1)
    (h1000 : (1 + 3 * Real.pi) * ᾱ ≤ 1 / (1000 * (ell : ℝ) ^ 3))
    (hsmallU : ThetaM0 ell a t ((1 + 3 * Real.pi) * ᾱ) < min a 1 / 1000)
    (H : KUSmall ell ((1 + 3 * Real.pi) * ᾱ)) (HU : UnitSmall ell ((1 + 3 * Real.pi) * ᾱ))
    (θ : ℝ) (Num : M0ClassNum ell a t ((1 + 3 * Real.pi) * ᾱ) (((12 : ℕ) : ℝ) * M * α₀) θ) :
    InstIneq ell k (by omega) a Lu
      (gam0M0f ell a t ((1 + 3 * Real.pi) * ᾱ) (eps2free Num) (epsJfree Num)
        (dCM0 ell ((1 + 3 * Real.pi) * ᾱ)) (cBM0 ell ((1 + 3 * Real.pi) * ᾱ)))
      (fullTower ell k Lu) Lam U := by
  have hell : 0 < ell := by omega
  have hM : 0 < M := Nat.pos_of_dvd_of_pos (hT.2.2 0) (Nat.succ_pos _)
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hα0 : 0 ≤ (12 : ℝ) * M * α₀ := by positivity
  have hpi := Real.pi_pos
  have hαᾱ : (12 : ℝ) * M * α₀ ≤ ᾱ := by nlinarith
  have hα1 : (12 : ℝ) * M * α₀ ≤ 1 := by linarith
  have hᾱ0 : 0 ≤ ᾱ := hα0.trans hαᾱ
  have hcast : ((12 : ℕ) : ℝ) * M * α₀ = (12 : ℝ) * M * α₀ := by norm_num
  obtain ⟨g, hl, hp⟩ := AdalyFormal.M0Corollary.regime_of_regular12 hell (f := 12) hU.toRegular12
    (by rw [hcast]; exact hα0) (by rw [hcast]; exact hα1)
  rw [hcast] at hl hp
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := pow_pos (by exact_mod_cast hell) k
  have hl' : ∀ b, dv (periodicGaugeTransform g U b) ≤ ᾱ / (ell : ℝ) ^ k := fun b =>
    (hl b).trans (div_le_div_of_nonneg_right hαᾱ hn.le)
  have hp' : ∀ p : PeriodicLatticePlaquette (scaleUp ell k Lu),
      dv (periodicPlaquetteHolonomy (periodicGaugeTransform g U) p) ≤ ᾱ / ((ell : ℝ) ^ k) ^ 2 := by
    intro p
    refine (hp p).trans (div_le_div_of_nonneg_right ?_ (by positivity))
    nlinarith [sq_nonneg ((12 : ℝ) * M * α₀), mul_nonneg hα0 (sub_nonneg.mpr hα1)]
  have R := regime_of_bounds ell k Lu hell2 (periodicGaugeTransform g U) a t ᾱ ha ht hᾱ0 (fun μ => hT.2.1 μ)
    hl' hp' hcb h216 h1000 hsmallU
  have hPV : PerCubeRegular2 ell M 12 k (fullTower ell k Lu) α₀ ((ell : ℝ) ^ k)⁻¹ (periodicGaugeTransform g U) :=
    perCubeRegular2_gauge (AdalyFormal.M0Corollary.perCube_of_global hU) g
  have key := instIneq_M0_class_rho ell k Lu hell (periodicGaugeTransform g U) a t _ _ _
    (AdalyFormal.M0Finish.rhoM0_class ell k hell ᾱ) R H HU (fun μ => hT.2.1 μ) (fun μ => hT.1 μ) Lam hLB
    M 12 α₀ hM (by norm_num) hPV (by rw [hcast]; exact hsm) θ Num
  exact (AdalyFormal.GaugeCov.instIneq_gauge_iff g).mp key

/-! ## the numerics of the witness amplitude (ℓ = 2, a = t = 1, θ₀) -/

theorem unitSmall_two (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1 / 10 ^ 130) (h2 : ρ ≤ AdalyFormal.RegBgKU.epsB / 10 ^ 6) :
    UnitSmall 2 ρ := by
  have h14 : ρ ≤ 1e-14 := h1.trans (by norm_num)
  have hk := AdalyFormal.M0Finish.kapHat_two_le ρ h0 (h14.trans (by norm_num))
  have hk0 : 0 ≤ kapHat 2 ρ := by
    unfold AdalyFormal.RegBgKU.kapHat; have := AdalyFormal.RegBgKU.Kc_pos 2 le_rfl; positivity
  have hLFB : (SmallnessBridge.Assemble.loopFactorBound 2 : ℝ) = 10 := by
    norm_num [SmallnessBridge.Assemble.loopFactorBound]
  have hr0 := AdalyFormal.NonflatJet.r0_pos
  have hε2 := AdalyFormal.RegBgKU.epsB_le2
  have hpi := Real.pi_lt_d2
  refine ⟨?_, ?_, ?_⟩
  · have : kapHat 2 ρ ≤ 45000 * 1e-14 := by nlinarith
    norm_num; linarith
  · rw [hLFB]
    have hκB : kapHat 2 ρ ≤ 45000 * (AdalyFormal.RegBgKU.epsB / 10 ^ 6) := by nlinarith
    have : (45000 : ℝ) * (AdalyFormal.RegBgKU.epsB / 10 ^ 6) ≤ 45000 * (AdalyFormal.NonflatJet.r0 / 10 ^ 10 / 10 ^ 6) := by
      have := div_le_div_of_nonneg_right hε2 (by norm_num : (0 : ℝ) ≤ 10 ^ 6)
      nlinarith
    nlinarith
  · have := AdalyFormal.M0Finish.dCM0_two_le ρ h0 h14; linarith

theorem kuSmall_two (ρ : ℝ) (h0 : 0 ≤ ρ) (h2 : ρ ≤ AdalyFormal.RegBgKU.epsB / 10 ^ 6) : KUSmall 2 ρ := by
  have := AdalyFormal.RegBgKU.epsB_pos
  exact AdalyFormal.RegBgKU.KU_of_le ρ h0 (h2.trans (by nlinarith))

/-- the amplitude scale `β = 12 M α₀` in terms of which the regime numerics are uniform -/
theorem regime_numerics_two (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ AdalyFormal.RegBgKU.epsB / 10 ^ 300) :
    let ᾱ := (4 * Real.pi + 4) * β
    4000000 * ((2 : ℕ) : ℝ) ^ 2 * ᾱ ≤ 1 ∧
    216 * ((1 + 3 * Real.pi) * ᾱ) ^ 2 < 1 ∧
    (1 + 3 * Real.pi) * ᾱ ≤ 1 / (1000 * ((2 : ℕ) : ℝ) ^ 3) ∧
    ThetaM0 2 1 1 ((1 + 3 * Real.pi) * ᾱ) < min (1 : ℝ) 1 / 1000 ∧
    KUSmall 2 ((1 + 3 * Real.pi) * ᾱ) ∧ UnitSmall 2 ((1 + 3 * Real.pi) * ᾱ) ∧
    0 ≤ (1 + 3 * Real.pi) * ᾱ ∧ (1 + 3 * Real.pi) * ᾱ ≤ 1 / 10 ^ 130 ∧ β ≤ 1 / 10 ^ 250 ∧ 4 * β ≤ 1 := by
  intro ᾱ
  have hε := AdalyFormal.RegBgKU.epsB_pos
  have hε1 := AdalyFormal.RegBgKU.epsB_le1
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have hβs : β ≤ 1 / 10 ^ 313 := by
    have : AdalyFormal.RegBgKU.epsB / 10 ^ 300 ≤ (1 / 10 ^ 13) / 10 ^ 300 :=
      div_le_div_of_nonneg_right hε1 (by norm_num)
    have e : (1 / 10 ^ 13 : ℝ) / 10 ^ 300 = 1 / 10 ^ 313 := by norm_num
    linarith
  have hᾱ0 : 0 ≤ ᾱ := by positivity
  have hᾱ : ᾱ ≤ 17 * β := by show (4 * Real.pi + 4) * β ≤ 17 * β; nlinarith
  have hρ0 : 0 ≤ (1 + 3 * Real.pi) * ᾱ := by positivity
  have hρ : (1 + 3 * Real.pi) * ᾱ ≤ 200 * β := by
    have : (1 + 3 * Real.pi) * ᾱ ≤ (1 + 3 * 3.15) * (17 * β) :=
      mul_le_mul (by linarith) hᾱ hᾱ0 (by norm_num)
    nlinarith
  have hρs : (1 + 3 * Real.pi) * ᾱ ≤ 1 / 10 ^ 130 := by
    have : (200 : ℝ) * (1 / 10 ^ 313) ≤ 1 / 10 ^ 130 := by norm_num
    nlinarith
  have hρε : (1 + 3 * Real.pi) * ᾱ ≤ AdalyFormal.RegBgKU.epsB / 10 ^ 6 := by
    have : 200 * β ≤ 200 * (AdalyFormal.RegBgKU.epsB / 10 ^ 300) := by nlinarith
    have : (200 : ℝ) * (AdalyFormal.RegBgKU.epsB / 10 ^ 300) ≤ AdalyFormal.RegBgKU.epsB / 10 ^ 6 := by
      have e1 : (200 : ℝ) * (AdalyFormal.RegBgKU.epsB / 10 ^ 300) = AdalyFormal.RegBgKU.epsB * (200 / 10 ^ 300) := by ring
      have e2 : AdalyFormal.RegBgKU.epsB / 10 ^ 6 = AdalyFormal.RegBgKU.epsB * (1 / 10 ^ 6) := by ring
      rw [e1, e2]; exact mul_le_mul_of_nonneg_left (by norm_num) hε.le
    linarith
  refine ⟨?_, ?_, ?_, AdalyFormal.AsmM0.Theta_num _ hρ0 (hρs.trans (by norm_num)), kuSmall_two _ hρ0 hρε,
    unitSmall_two _ hρ0 hρs hρε, hρ0, hρs, hβs.trans (by norm_num), by nlinarith⟩
  · push_cast; nlinarith
  · have : ((1 + 3 * Real.pi) * ᾱ) ^ 2 ≤ (1 / 10 ^ 130) ^ 2 := pow_le_pow_left₀ hρ0 hρs 2
    norm_num at this ⊢; nlinarith
  · push_cast; refine hρs.trans (by norm_num)

/-- **the M0 inner claim (MC2 `M0Core`) holds at `ℓ = 2`, `a = 1`, for EVERY `M`**: `a₀ = epsB·10⁻³⁰⁰`, `γ₀ = 9·10⁻⁵`.
No D-layer hypothesis. (`epsB = min(10⁻¹³, r0/10¹⁰)` carries the tree's log-regularity radius `r0`.) -/
theorem M0Core_two (M : ℕ) : AdalyFormal.M0Corollary.M0Core 2 M (by norm_num) 1 := by
  refine ⟨AdalyFormal.RegBgKU.epsB / 10 ^ 300, by have := AdalyFormal.RegBgKU.epsB_pos; positivity, 9e-5,
    by norm_num, ?_⟩
  intro k _ Lu hT α₀ hα₀ hsm U hU
  have hM : 0 < M := Nat.pos_of_dvd_of_pos (hT.2.2 0) (Nat.succ_pos _)
  have hβ0 : 0 ≤ (12 : ℝ) * M * α₀ := by positivity
  obtain ⟨hcb, h216, h1000, hsU, H, HU, hρ0, hρs, hβs, h4⟩ := regime_numerics_two ((12 : ℝ) * M * α₀) hβ0 hsm
  have hcast : ((12 : ℕ) : ℝ) * M * α₀ = (12 : ℝ) * M * α₀ := by norm_num
  have Num : M0ClassNum 2 1 1 ((1 + 3 * Real.pi) * ((4 * Real.pi + 4) * ((12 : ℝ) * M * α₀)))
      (((12 : ℕ) : ℝ) * M * α₀) θ₀ :=
    m0ClassNum_two _ _ hρ0 hρs (by rw [hcast]; exact hβ0) (by rw [hcast]; exact hβs)
  have key := instIneq_globalRegular2_unconditional 2 M k le_rfl Lu hT U 1 1 α₀
    ((4 * Real.pi + 4) * ((12 : ℝ) * M * α₀)) le_rfl one_pos one_pos hα₀ h4 Set.univ
    (lamBlockSum_univ 2 (by norm_num)) hU hcb h216 h1000 hsU H HU θ₀ Num
  exact instIneq_mono (gam0_two_pos _ _ hρ0 hρs (by rw [hcast]; exact hβ0) (by rw [hcast]; exact hβs) Num) key

/-! ## the explicit witness: the smooth abelian sine field, every `k` -/

/-- the witness amplitude (positive, `k`-free) -/
noncomputable def α₀w : ℝ := AdalyFormal.RegBgKU.epsB / 10 ^ 300 / 12

/-- the unit torus `16 × 16 × 16` -/
def Lu16 : PeriodicLatticeExtent := fun _ => 15

/-- the witness field at level `k`: `U = exp(i 2^{-k} χ σ₃)`, `χ_(x,1) = 6α₀ sin(2π x₀/(16·2ᵏ))` -/
noncomputable def Uw (k : ℕ) : LinkCfg (scaleUp 2 k Lu16) :=
  Ufield (((2 : ℕ) : ℝ) ^ k)⁻¹ (AdalyFormal.M0Corollary.chiP (scaleUp 2 k Lu16) ((12 : ℝ) * ((1 : ℕ) : ℝ) * α₀w / 2))

/-- the `k`-free regime scale of the witness: `ᾱ = (4π+4)·12α₀` -/
noncomputable def αbw : ℝ := (4 * Real.pi + 4) * ((12 : ℝ) * ((1 : ℕ) : ℝ) * α₀w)

/-- the `k`-free value of `ρ = rhoM0` at the witness -/
noncomputable def ρw : ℝ := (1 + 3 * Real.pi) * αbw

theorem α₀w_pos : 0 < α₀w := by unfold α₀w; have := AdalyFormal.RegBgKU.epsB_pos; positivity

theorem βw_eq : (12 : ℝ) * ((1 : ℕ) : ℝ) * α₀w = AdalyFormal.RegBgKU.epsB / 10 ^ 300 := by
  unfold α₀w; push_cast; ring

/-- the witness numerics -/
theorem witness_numerics :
    4000000 * ((2 : ℕ) : ℝ) ^ 2 * αbw ≤ 1 ∧ 216 * ρw ^ 2 < 1 ∧ ρw ≤ 1 / (1000 * ((2 : ℕ) : ℝ) ^ 3) ∧
    ThetaM0 2 1 1 ρw < min (1 : ℝ) 1 / 1000 ∧ KUSmall 2 ρw ∧ UnitSmall 2 ρw ∧ 0 ≤ ρw ∧ ρw ≤ 1 / 10 ^ 130 ∧
    (12 : ℝ) * ((1 : ℕ) : ℝ) * α₀w ≤ 1 / 10 ^ 250 ∧ 4 * ((12 : ℝ) * ((1 : ℕ) : ℝ) * α₀w) ≤ 1 :=
  regime_numerics_two ((12 : ℝ) * ((1 : ℕ) : ℝ) * α₀w) (by have := α₀w_pos; positivity) (le_of_eq βw_eq)

theorem Numw : M0ClassNum 2 1 1 ρw (((12 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) * α₀w) θ₀ := by
  obtain ⟨-, -, -, -, -, -, h0, h1, hβ, -⟩ := witness_numerics
  have hcast : ((12 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) * α₀w = (12 : ℝ) * ((1 : ℕ) : ℝ) * α₀w := by norm_num
  exact m0ClassNum_two _ _ h0 h1 (by rw [hcast]; have := α₀w_pos; positivity) (by rw [hcast]; exact hβ)

/-- the M0 regime of the witness field ITSELF (its own gauge), every `k` -/
theorem witness_regime (k : ℕ) :
    M0RegimeR 2 k Lu16 (Uw k) 1 1 (αbw / ((2 : ℕ) : ℝ) ^ k) (αbw / (((2 : ℕ) : ℝ) ^ k) ^ 2) := by
  obtain ⟨hcb, h216, h1000, hsU, -, -, -, -, -, h4⟩ := witness_numerics
  have hα : 0 < (12 : ℝ) * ((1 : ℕ) : ℝ) * α₀w := by have := α₀w_pos; positivity
  set α := (12 : ℝ) * ((1 : ℕ) : ℝ) * α₀w with hαdef
  have hα1 : α ≤ 1 := by linarith
  have hn : (0 : ℝ) < ((2 : ℕ) : ℝ) ^ k := by positivity
  have hn1 : (1 : ℝ) ≤ ((2 : ℕ) : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hη : 0 < (((2 : ℕ) : ℝ) ^ k)⁻¹ := by positivity
  obtain ⟨b1, b2⟩ := sine_bounds 2 k (by norm_num) Lu16 (by show 16 ≤ 15 + 1; norm_num) α hα
  have hsmall : (((2 : ℕ) : ℝ) ^ k)⁻¹ * α ≤ 1 := by
    have : (((2 : ℕ) : ℝ) ^ k)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn1
    nlinarith
  obtain ⟨hl, hp⟩ := ufield_regime (((2 : ℕ) : ℝ) ^ k)⁻¹ α α hη _ b1 b2 hsmall
  have hpi := Real.pi_pos
  have hαᾱ : α ≤ αbw := by show α ≤ (4 * Real.pi + 4) * α; nlinarith
  have hᾱ0 : 0 ≤ αbw := hα.le.trans hαᾱ
  refine regime_of_bounds 2 k Lu16 le_rfl (Uw k) 1 1 αbw one_pos one_pos hᾱ0 (fun μ => by show 2 < 15 + 1; norm_num)
    ?_ ?_ hcb h216 h1000 hsU
  · intro b
    have := hl b
    calc dv (Uw k b) ≤ (((2 : ℕ) : ℝ) ^ k)⁻¹ * α := this
      _ = α / ((2 : ℕ) : ℝ) ^ k := by rw [div_eq_inv_mul]
      _ ≤ αbw / ((2 : ℕ) : ℝ) ^ k := div_le_div_of_nonneg_right hαᾱ hn.le
  · intro p
    have := hp p
    have e : 2 * ((((2 : ℕ) : ℝ) ^ k)⁻¹ ^ 2 * α) + (4 * Real.pi + 2) * ((((2 : ℕ) : ℝ) ^ k)⁻¹ * α) ^ 2
        = (2 * α + (4 * Real.pi + 2) * α ^ 2) / (((2 : ℕ) : ℝ) ^ k) ^ 2 := by field_simp
    rw [e] at this
    refine this.trans (div_le_div_of_nonneg_right ?_ (by positivity))
    show 2 * α + (4 * Real.pi + 2) * α ^ 2 ≤ (4 * Real.pi + 4) * α
    nlinarith [sq_nonneg α, mul_nonneg hα.le (sub_nonneg.mpr hα1)]

theorem witness_rho (k : ℕ) : rhoM0 2 k (αbw / ((2 : ℕ) : ℝ) ^ k) (αbw / (((2 : ℕ) : ℝ) ^ k) ^ 2) = ρw :=
  AdalyFormal.M0Finish.rhoM0_class 2 k (by norm_num) αbw

/-- **the witness lies in the printed class** (all three clauses: whole-torus single gauge AND per class cube) -/
theorem witness_class (k : ℕ) :
    GlobalRegular2 2 1 12 k α₀w (((2 : ℕ) : ℝ) ^ k)⁻¹ (Uw k) ∧
    PerCubeRegular2 2 1 12 k (fullTower 2 k Lu16) α₀w (((2 : ℕ) : ℝ) ^ k)⁻¹ (Uw k) := by
  have hG := AdalyFormal.M0Corollary.sine_globalRegular2 2 1 k (by norm_num) Lu16 (by show 16 ≤ 15 + 1; norm_num) α₀w
    (by have := α₀w_pos; positivity)
  exact ⟨hG, AdalyFormal.M0Corollary.perCube_of_global hG⟩

/-- **the witness is curved**, every `k` -/
theorem witness_curved (k : ℕ) :
    ∃ p : PeriodicLatticePlaquette (scaleUp 2 k Lu16), 0 < dv (periodicPlaquetteHolonomy (Uw k) p) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h4⟩ := witness_numerics
  have hα : 0 < (12 : ℝ) * ((1 : ℕ) : ℝ) * α₀w := by have := α₀w_pos; positivity
  have hn1 : (1 : ℝ) ≤ ((2 : ℕ) : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hAc1 : (12 : ℝ) * ((1 : ℕ) : ℝ) * α₀w / 2 < 1 := by push_cast at h4 ⊢; linarith
  refine AdalyFormal.M0Corollary.sine_curved (scaleUp 2 k Lu16) _ _ (by positivity) hAc1 (by positivity)
    (inv_le_one_of_one_le₀ hn1) ?_
  have := AdalyFormal.IngredientFamilyR2.scaleUp_succ 2 k Lu16 (by norm_num) 0
  have h2 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  show 3 ≤ scaleUp 2 k Lu16 0 + 1
  rw [this]; show 3 ≤ (15 + 1) * 2 ^ k; omega

/-- **NON-VACUITY: every hypothesis of `instIneq_M0_class_unconditional` holds at the witness, every `k`** -/
theorem witness_all_k (k : ℕ) :
    M0RegimeR 2 k Lu16 (Uw k) 1 1 (αbw / ((2 : ℕ) : ℝ) ^ k) (αbw / (((2 : ℕ) : ℝ) ^ k) ^ 2) ∧
    KUSmall 2 (rhoM0 2 k (αbw / ((2 : ℕ) : ℝ) ^ k) (αbw / (((2 : ℕ) : ℝ) ^ k) ^ 2)) ∧
    UnitSmall 2 (rhoM0 2 k (αbw / ((2 : ℕ) : ℝ) ^ k) (αbw / (((2 : ℕ) : ℝ) ^ k) ^ 2)) ∧
    (∀ μ : Fin 3, 2 < Lu16 μ + 1) ∧ (∀ μ, 2 ∣ Lu16 μ + 1) ∧
    LamBlockSum 2 (Set.univ : Set (PeriodicLatticeSite Lu16)) ∧
    PerCubeRegular2 2 1 12 k (fullTower 2 k Lu16) α₀w (((2 : ℕ) : ℝ) ^ k)⁻¹ (Uw k) ∧
    4 * (((12 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) * α₀w) ≤ 1 ∧
    M0ClassNum 2 1 1 (rhoM0 2 k (αbw / ((2 : ℕ) : ℝ) ^ k) (αbw / (((2 : ℕ) : ℝ) ^ k) ^ 2))
      (((12 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) * α₀w) θ₀ ∧
    GlobalRegular2 2 1 12 k α₀w (((2 : ℕ) : ℝ) ^ k)⁻¹ (Uw k) ∧
    0 < α₀w ∧
    (∃ p : PeriodicLatticePlaquette (scaleUp 2 k Lu16), 0 < dv (periodicPlaquetteHolonomy (Uw k) p)) := by
  obtain ⟨-, -, -, -, H, HU, -, -, -, h4⟩ := witness_numerics
  have hρ := witness_rho k
  have hcast : ((12 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) * α₀w = (12 : ℝ) * ((1 : ℕ) : ℝ) * α₀w := by norm_num
  obtain ⟨hG, hP⟩ := witness_class k
  refine ⟨witness_regime k, by rw [hρ]; exact H, by rw [hρ]; exact HU, fun μ => by show 2 < 15 + 1; norm_num,
    fun μ => by show 2 ∣ 15 + 1; norm_num, lamBlockSum_univ 2 (by norm_num), hP, by rw [hcast]; exact h4,
    by rw [hρ]; exact Numw, hG, α₀w_pos, witness_curved k⟩

/-- the witness constant (`k`-free) -/
noncomputable def γw : ℝ := gam0M0f 2 1 1 ρw (eps2free Numw) (epsJfree Numw) (dCM0 2 ρw) (cBM0 2 ρw)

theorem γw_ge : 9e-5 ≤ γw := by
  obtain ⟨-, -, -, -, -, -, h0, h1, hβ, -⟩ := witness_numerics
  have hcast : ((12 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) * α₀w = (12 : ℝ) * ((1 : ℕ) : ℝ) * α₀w := by norm_num
  exact gam0_two_pos _ _ h0 h1 (by rw [hcast]; have := α₀w_pos; positivity) (by rw [hcast]; exact hβ) Numw

/-- **the conclusion at the witness, every `k`, by `instIneq_M0_class_unconditional` itself** (via the `k`-free-`ρ` form) -/
theorem witness_instIneq (k : ℕ) :
    InstIneq 2 k (by norm_num) 1 Lu16 γw (fullTower 2 k Lu16) Set.univ (Uw k) ∧
    InstIneq 2 k (by norm_num) 1 Lu16 9e-5 (fullTower 2 k Lu16) Set.univ (Uw k) := by
  obtain ⟨-, -, -, -, H, HU, -, -, -, h4⟩ := witness_numerics
  have hcast : ((12 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) * α₀w = (12 : ℝ) * ((1 : ℕ) : ℝ) * α₀w := by norm_num
  have h := instIneq_M0_class_rho 2 k Lu16 (by norm_num) (Uw k) 1 1 _ _ ρw (witness_rho k) (witness_regime k) H HU
    (fun μ => by show 2 < 15 + 1; norm_num) (fun μ => by show 2 ∣ 15 + 1; norm_num) Set.univ
    (lamBlockSum_univ 2 (by norm_num)) 1 12 α₀w one_pos (by norm_num) (witness_class k).2 (by rw [hcast]; exact h4)
    θ₀ Numw
  exact ⟨h, instIneq_mono γw_ge h⟩

/-- the literal application of `instIneq_M0_class_unconditional` (no restatement) at the witness, every `k` -/
theorem witness_direct (k : ℕ) :
    InstIneq 2 k (by norm_num) 1 Lu16
      (gam0M0f 2 1 1 (rhoM0 2 k (αbw / ((2 : ℕ) : ℝ) ^ k) (αbw / (((2 : ℕ) : ℝ) ^ k) ^ 2))
        (eps2free (witness_all_k k).2.2.2.2.2.2.2.2.1) (epsJfree (witness_all_k k).2.2.2.2.2.2.2.2.1)
        (dCM0 2 (rhoM0 2 k (αbw / ((2 : ℕ) : ℝ) ^ k) (αbw / (((2 : ℕ) : ℝ) ^ k) ^ 2)))
        (cBM0 2 (rhoM0 2 k (αbw / ((2 : ℕ) : ℝ) ^ k) (αbw / (((2 : ℕ) : ℝ) ^ k) ^ 2))))
      (fullTower 2 k Lu16) Set.univ (Uw k) :=
  instIneq_M0_class_unconditional 2 k Lu16 (by norm_num) (Uw k) 1 1 _ _ (witness_all_k k).1 (witness_all_k k).2.1
    (witness_all_k k).2.2.1 (witness_all_k k).2.2.2.1 (witness_all_k k).2.2.2.2.1 Set.univ (witness_all_k k).2.2.2.2.2.1
    1 12 α₀w one_pos (by norm_num) (witness_all_k k).2.2.2.2.2.2.1 (witness_all_k k).2.2.2.2.2.2.2.1 θ₀
    (witness_all_k k).2.2.2.2.2.2.2.2.1

#print axioms instIneq_mono
#print axioms ufield_regime
#print axioms sine_bounds
#print axioms instIneq_globalRegular2_unconditional
#print axioms M0Core_two
#print axioms witness_all_k
#print axioms witness_instIneq
#print axioms witness_direct

end AdalyFormal.DLayer
