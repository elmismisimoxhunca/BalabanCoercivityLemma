import ASC2
import ASC3

/-!
# ASC4 -- `ginv_coercive_M0_pinned` (see ASC3 header).  Constants are pinned by equations, exactly as in PB6.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
namespace AdalyFormal.AsmM0

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond frobNorm_le_frobSupBond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.SuTwoLogExp (M2 SU2)
open AdalyFormal.Balaban.ClassPropagationUbar (blkConstOf)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.SliceCoerc
open AdalyFormal.PortSlice
open AdalyFormal.BondComposite
open AdalyFormal.CurvBlock (dv pw pw_one_of_plaq)
open AdalyFormal.NonflatJet (r0 mem_LogReg_of_frob_lt)
open AdalyFormal.FlatExt (aFE bFE)

/-- the smallness quantity of the chain's `hsmall` (FE4), named. -/
noncomputable def Sexp (ell k : ℕ) (δ P q ε0 : ℝ) : ℝ :=
  ((((bFE ell k + δ * aFE ell k) / (1 - ε0 * aFE ell k)) * q) * (δ * P
    + (((bFE ell k + δ * aFE ell k) / (1 - ε0 * aFE ell k)) * q) * P ^ 2
      * (δ + ((bFE ell k + δ * aFE ell k) / (1 - ε0 * aFE ell k)) * ε0)) + δ)

theorem ginv_coercive_M0_pinned (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 2 ≤ ell)
    (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (ha : 0 < a) (Lam : Set (PeriodicLatticeSite Lu)) (t : ℝ) (ht : 0 < t)
    (e q0 : ℝ) (he0 : 0 ≤ e) (hq0 : 0 ≤ q0)
    (hN : ∀ ρ', 2 * ell ^ k < scaleUp ell k Lu ρ' + 1)
    (hlinks : ∀ b, dv (U b) ≤ e)
    (hplaq : ∀ p : PeriodicLatticePlaquette (scaleUp ell k Lu), dv (periodicPlaquetteHolonomy U p) ≤ q0)
    (hcb : 4000000 * (ell : ℝ) ^ 2 * (((ell : ℝ) ^ 2) ^ k * q0) ≤ 1)
    (η ρ : ℝ) (hη : η = e + 3 * Real.pi * (((ell : ℝ) ^ k) * q0)) (hρ : ρ = (ell : ℝ) ^ k * η)
    (hρ216 : 216 * ρ ^ 2 < 1) (hρ1000 : ρ ≤ 1 / (1000 * (ell : ℝ) ^ 3))
    (hregthr : ∀ j, j < k → (8 * (ell : ℝ) - 6) * (blkConstOf ell ^ j * e) < r0)
    (nsq c1 θ δm e' P PU δ q ε0 : ℝ)
    (hnsq : nsq = (ell : ℝ) ^ (2 * k)) (hc1 : c1 = min a 1 / 1000)
    (hθ : θ = 272 * (q0 / (4 * Real.sqrt 2)))
    (hδm : δm = Real.sqrt a * phiC ell (3600 * (ell : ℝ) * ρ) / (ell : ℝ) ^ k)
    (he' : e' = (1 + t) * θ + (1 + 1 / t) * ((4 * Real.sqrt 2 * (ρ / (ell : ℝ) ^ k)) ^ 2 + δm ^ 2))
    (hP : P = Real.sqrt (max 6 (16 / (3 * a)) * ((ell : ℝ) ^ k) ^ 2))
    (hPU : PU = Real.sqrt (max 6 (16 / (3 * a)) * ((ell : ℝ) ^ k) ^ 2 / (1 - 216 * ρ ^ 2)))
    (hδ : δ = Real.sqrt 12 * (ρ / (ell : ℝ) ^ k))
    (hq : q = Real.sqrt (1 / ((ell : ℝ) ^ k) ^ 3))
    (hε0 : ε0 = 6 * ρ * q)
    (hsmall : nsq * Sexp ell k δ P q ε0 ^ 2 + nsq * e' < c1)
    (x : ↥(bondSupp (GF ell k Lu))) :
    ‖x‖ ^ 2 ≤ max (2 / ((c1 - nsq * Sexp ell k δ P q ε0 ^ 2 - nsq * e') / (1 + t) / nsq)) (2 * PU ^ 2) *
      ⟪x, (IngrBParams.data ⟨ell, k, Lu, (by omega : 0 < ell), fullTower ell k Lu, U, a, Lam⟩).Ginv x⟫ := by
  have hell0 : 0 < ell := by omega
  have hellR : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hellpos : (0 : ℝ) < ell := by linarith
  set n : ℝ := (ell : ℝ) ^ k with hn
  have hnpos : 0 < n := by positivity
  have hpi := Real.pi_pos
  have hηnn : 0 ≤ η := by rw [hη]; positivity
  have hρnn : 0 ≤ ρ := by rw [hρ]; positivity
  have hηρ : η = ρ / n := by rw [hρ]; field_simp
  have hρk : 0 ≤ ρ / n := by positivity
  -- the class
  set ε : ℕ → ℝ := fun j => (ell : ℝ) ^ j * e + 3 * Real.pi * (((ell : ℝ) ^ 2) ^ j * q0) with hεdef
  have hεnn : ∀ j, 0 ≤ ε j := fun j => by simp only [hεdef]; positivity
  have hεη : ∀ j, j < k → ε j ≤ (ell : ℝ) ^ j * η := fun j hj => by
    have := eps_class_le ell k (by omega) e q0 hq0 j hj.le
    rw [hη]; exact this
  have hεs : ∀ j, j < k → ε j ≤ 1 / (1000 * (ell : ℝ) ^ 4) := by
    intro j hj
    have h1 : (ell : ℝ) ^ j * ell ≤ n := by
      rw [hn, ← pow_succ]; exact pow_le_pow_right₀ (by linarith) hj
    have h2 : (ell : ℝ) ^ j * η ≤ ρ / ell := by
      rw [hηρ, mul_div_assoc', div_le_div_iff₀ hnpos hellpos]
      nlinarith [mul_le_mul_of_nonneg_left h1 hρnn]
    have h3 : ρ / ell ≤ 1 / (1000 * (ell : ℝ) ^ 4) := by
      calc ρ / ell ≤ (1 / (1000 * (ell : ℝ) ^ 3)) / ell := div_le_div_of_nonneg_right hρ1000 hellpos.le
        _ = 1 / (1000 * (ell : ℝ) ^ 4) := by field_simp
    exact (hεη j hj).trans (h2.trans h3)
  have h0 := pw_one_of_plaq U q0 hq0 hplaq
  have hcl : TowerClass ell k Lu U ε :=
    towerClass_of_blocking ell k Lu hell U q0 e hq0 h0 hlinks hN hcb
  have hU : frobSupBond U ≤ ρ / n := by
    refine (frobSupBond_le_of U hlinks).trans ?_
    rw [← hηρ, hη]
    nlinarith [mul_nonneg hnpos.le hq0, hpi]
  have hAl : ∀ i, i < k → AlignedLinkBound (ell ^ i) (bgTower (GF ell k Lu) U i) (ρ * (ell : ℝ) ^ i / n) := by
    intro i hi z hz μ
    refine (hcl i hi z hz μ).trans ?_
    refine (hεη i hi).trans (le_of_eq ?_)
    rw [hηρ]; ring
  have hpos : 72 * ρ ^ 2 + 4 * (6 * ρ) ^ 2 < 1 := by nlinarith
  have hE := AdalyFormal.SiteCoercivity.geom_tower_sum ell k hell ρ hρnn
  have hu := hu_al ell k Lu hell U a ha ρ (6 * ρ) hpos hU (fun i => ρ * (ell : ℝ) ^ i / n) hAl hE
  have hPoincU := poincare_al ell k Lu hell U a ha ρ (6 * ρ) hpos hU (fun i => ρ * (ell : ℝ) ^ i / n) hAl hE
  have hPoinc1 := poincare_flat ell k Lu hell a ha
  -- regularity (crude all-edge tree bound)
  have hB0 : 0 ≤ blkConstOf ell := by
    unfold blkConstOf
    have : (0 : ℝ) ≤ 8 * (ell : ℝ) - 6 := by linarith
    positivity
  have hreg : RegTower ell (bgTower (GF ell k Lu) U) k :=
    regTower_of_frobSup hell0 (bgTower (GF ell k Lu) U) k (fun j => blkConstOf ell ^ j * e)
      (fun j _ => (frobSup_bgTower_le (GF ell k Lu) hell0 U j).trans
        (mul_le_mul_of_nonneg_left (frobSupBond_le_of U hlinks) (pow_nonneg hB0 j)))
      r0 (fun g h => mem_LogReg_of_frob_lt h) hregthr
  -- C1
  have hsm : ∀ j, j < k → AdalyFormal.NonflatJet.rhoOf ell (ε j) < Real.pi / 2 :=
    fun j hj => hsm_of_le ell hell0 (ε j) (hεnn j) (hεs j hj)
  have hmraw := fun x => hm_of_tower ell k Lu hell0 U a ha.le ε hreg hcl (fun j _ => hεnn j) hsm x
  have hdM : deltaM ell k a ε ≤ δm := by
    have h := class_n_deltaM_bound ell k hell a ha.le e q0 he0 hq0 (fun j hj => hεs j hj)
    have h' : n * deltaM ell k a ε ≤ Real.sqrt a * phiC ell (3600 * (ell : ℝ) * ρ) := by
      have e1 : ρ = n * (e + 3 * Real.pi * (n * q0)) := by rw [hρ, hη]
      unfold phiC
      rw [e1]
      exact h
    rw [hδm, le_div_iff₀ hnpos, mul_comm]
    exact h'
  have hC1 : ∀ x : BondFnL2 (scaleUp ell k Lu),
      ∑ p : BIdx (GF ell k Lu), a * ((GF ell k Lu).ell : ℝ) ^ (p.1 : ℕ) *
        ‖(bondSectorOf (GF ell k Lu) (trivialU _)).Qfull x p - (bondSectorOf (GF ell k Lu) U).Qfull x p‖ ^ 2
        ≤ δm ^ 2 * ‖x‖ ^ 2 := fun x =>
    (hmraw x).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (deltaM_nonneg ell k hell0 a ha.le ε (fun j _ => hεnn j)) hdM 2) (sq_nonneg _))
  -- Q' drift and norm
  have hε0le : eps0Of ell k ε ≤ ε0 := by
    have h := class_eps0_bound ell k hell e q0 he0 hq0
    have e1 : ε0 = 6 * ((ell : ℝ) ^ k * (e + 3 * Real.pi * ((ell : ℝ) ^ k * q0))) * Real.sqrt (1 / ((ell : ℝ) ^ k) ^ 3) := by
      rw [hε0, hq, hρ, hη]
    rw [e1]; exact h
  have hq0' : 0 ≤ q := by rw [hq]; exact Real.sqrt_nonneg _
  have hε00 : 0 ≤ ε0 := by rw [hε0]; positivity
  have hQdrift : ∀ f, ‖Qtop (GF ell k Lu) U f - Qtop (GF ell k Lu) (trivialU _) f‖ ≤ ε0 * ‖f‖ := fun f =>
    (hQdrift_of_tower ell k Lu hell0 U ε hcl f).trans (mul_le_mul_of_nonneg_right hε0le (norm_nonneg f))
  have hQq : ∀ f, ‖Qtop (GF ell k Lu) U f‖ ≤ q * ‖f‖ := by
    intro f; rw [hq]; exact hQq_ported ell k Lu hell0 U f
  -- plaquette defect
  have hα₀ : 0 ≤ q0 / (4 * Real.sqrt 2) := by positivity
  have hpl : AdalyFormal.NonflatHunit.PlaqDef (q0 / (4 * Real.sqrt 2)) U := by
    intro p
    have h := hplaq p
    have e1 : 4 * Real.sqrt 2 * (q0 / (4 * Real.sqrt 2)) = q0 := by
      have : Real.sqrt 2 ≠ 0 := by positivity
      field_simp
    rw [e1]; exact h
  have hdp : ∀ x : BondFnL2 (scaleUp ell k Lu),
      |AdalyFormal.StatementLaneR6.deltaPrimeBilL2NormLoc U (plaqIn (GF ell k Lu).Om0) x x| ≤ θ * ‖x‖ ^ 2 := by
    intro x; rw [hθ]; exact theta_ported ell k Lu U hα₀ hpl x
  have hc' : ∀ x : BondFnL2 (scaleUp ell k Lu),
      ‖AdalyFormal.StatementLaneR6.plaqMask (plaqIn (GF ell k Lu).Om0) (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (trivialU _) x)
        - AdalyFormal.StatementLaneR6.plaqMask (plaqIn (GF ell k Lu).Om0) (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 U x)‖
        ≤ (4 * Real.sqrt 2 * (ρ / n)) * ‖x‖ := by
    intro x
    refine le_trans (hc_of_frobSup U _ x) ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hU (by positivity)) (norm_nonneg _)
  have hdrift : ∀ x : BondFnL2 (scaleUp ell k Lu),
      PhiF ell k Lu a (trivialU _) x ≤ (1 + t) * PhiF ell k Lu a U x + e' * ‖x‖ ^ 2 := by
    intro x
    rw [he']
    exact phi_drift_decomp ell k Lu U a ha.le t ht (4 * Real.sqrt 2 * (ρ / n)) θ δm hc' hdp hC1 x
  have hd : ∀ f, ‖gradL2 (trivialU (scaleUp ell k Lu)) f - gradL2 U f‖ ≤ δ * ‖f‖ := by
    intro f; rw [hδ]; exact hd_of_frobSup U hρk hU f
  have hflat : ∀ y : BondFnL2 (scaleUp ell k Lu),
      c1 * ‖y‖ ^ 2 ≤ nsq * (PhiF ell k Lu a (trivialU (scaleUp ell k Lu)) y
        + ‖Rproj (GF ell k Lu) (trivialU (scaleUp ell k Lu)) (gradAdj (trivialU (scaleUp ell k Lu)) y)‖ ^ 2) := by
    intro y; rw [hc1, hnsq]; exact hflat_ported ell k Lu hell0 a ha y
  have hnn : 0 < nsq := by rw [hnsq]; positivity
  have hP0 : 0 ≤ P := by rw [hP]; exact Real.sqrt_nonneg _
  have hPU0 : 0 ≤ PU := by rw [hPU]; exact Real.sqrt_nonneg _
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hPoincU' : ∀ ν ∈ NQp (GF ell k Lu) U, ‖ν‖ ≤ PU * ‖gradL2 U ν‖ := by
    intro ν hν
    have h := hPoincU ν hν
    have e1 : (1 : ℝ) - 72 * ρ ^ 2 - 4 * (6 * ρ) ^ 2 = 1 - 216 * ρ ^ 2 := by ring
    rw [e1] at h
    rw [hPU]; exact h
  have hPoinc1' : ∀ ν ∈ NQp (GF ell k Lu) (trivialU (scaleUp ell k Lu)),
      ‖ν‖ ≤ P * ‖gradL2 (trivialU (scaleUp ell k Lu)) ν‖ := by
    intro ν hν; rw [hP]; exact hPoinc1 ν hν
  have hεa : ε0 * aFE ell k < 1 := by
    have e1 : ε0 * aFE ell k = 6 * ρ * 27 := by
      rw [hε0, hq]
      have := aFE_mul_q ell k hell0
      calc 6 * ρ * Real.sqrt (1 / ((ell : ℝ) ^ k) ^ 3) * aFE ell k
          = 6 * ρ * (aFE ell k * Real.sqrt (1 / ((ell : ℝ) ^ k) ^ 3)) := by ring
        _ = 6 * ρ * 27 := by rw [this]
    rw [e1]
    have : 1000 * (ell : ℝ) ^ 3 ≥ 8000 := by nlinarith [pow_le_pow_left₀ (by norm_num) hellR 3]
    have h8 : ρ ≤ 1 / 8000 := hρ1000.trans (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
    linarith
  exact AdalyFormal.FlatExt.ginv_coercive_FE ell k Lu hell0 U a Lam hreg hu PU hPU0 hPoincU' nsq c1 t e' P δ q ε0 hnn ht.le hP0 hδ0 hq0'
    hε00 hεa hsmall hflat hdrift hPoinc1' hd hQdrift hQq x

#print axioms ginv_coercive_M0_pinned

end AdalyFormal.AsmM0
