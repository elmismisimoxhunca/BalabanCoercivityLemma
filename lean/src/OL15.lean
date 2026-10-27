import OL14

/-!
# OL15 -- the residual premise in GAUGE-FREE Q-only form (lane m2_oplayer_20261015)

* **`ClassRightInvCov`** : at every printed-class configuration (thick torus, `Λ ≠ ∅`, `U = 1` off class bonds) the bond `Q`
  has a right inverse with the two W6-shaped bounds `wnormSq x ≤ cW nD u` and `gradWU U x ν ≤ cG nD u` (covariant gradients,
  OL14), `cW, cG ≥ 0` chosen after `m`, before `R`.  This is W6's `bond_rightinv_strat` statement with `gradW` replaced by its
  gauge-covariant version — no `Ginv`, no W4, no sandwich.
* `etaB`, `etaS_le_etaB` : an explicit `k`-, `W`-, `α₀`-free bound of the sandwich constant `etaS ℓ W cs ρ 1` for `0 ≤ ρ ≤ 1`,
  `cs ≥ c̄ > 0`, `W ≥ 1`.
* **`classRightInv_of_cov : BallChartsG → ClassRightInvCov → ClassRightInv`** (F1 at the configuration from the ball charts gives
  `HatPack`; `holRegime_rho1`; OL14 `hext_of_rightinv_cov`).
* **`target8_of_rightInvCov : ClassRightInvCov → ThinTori → P428Target8`**.
-/
set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.M2OpLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp TorusOK)
open AdalyFormal.StatementLane2 (ClassCoupled)
open AdalyFormal.StatementLaneG (gparams LambdaOK2)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.M1IMS AdalyFormal.M1GaugeW4 AdalyFormal.TowerLoc
open AdalyFormal.M1Site
open AdalyFormal.M1DStrat (gradWU etaS hext_of_rightinv_cov)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)
open AdalyFormal.M2Skel (SiteS1 alpha1)

/-- **the covariant right inverse of `Q` at the printed class** (thick tori, `Λ ≠ ∅`) -/
def ClassRightInvCov : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a → ∃ m₁ : ℕ, ∀ m : ℕ, m₁ ≤ m → ∃ cW cG : ℝ, 0 ≤ cW ∧ 0 ≤ cG ∧
    ∃ R₁ : ℕ, ∀ R : ℕ, R₁ ≤ R → ∃ s : ℝ, 0 < s ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ s →
    TorusOK ell (ell ^ m) Lu → ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
    (∀ σ : Fin 3, 13 * ell ^ m ≤ Lu σ + 1) →
    ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam → Lam.Nonempty →
    ∀ (U : LinkCfg (scaleUp ell k Lu)), ClassCoupled ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    (∀ e : Bond (scaleUp ell k Lu), ¬ AdalyFormal.StatementLaneR8.ClassBond ell (ell ^ m) 12 k S e → U e = 1) →
    ∀ u : FSp (geomOf ell k S), ∃ x : ↥(bondSupp (geomOf ell k S)),
      (gparams ell k Lu (by omega) S U a Lam).data.Q x = u ∧
      AdalyFormal.M1.wnormSq S ell k (x : BondFnL2 (scaleUp ell k Lu)) ≤ cW * AdalyFormal.W6.nD u ∧
      ∀ ν : Fin 3, gradWU U (x : BondFnL2 (scaleUp ell k Lu)) ν ≤ cG * AdalyFormal.W6.nD u

/-- an explicit bound of the sandwich constant -/
noncomputable def etaB (ell : ℕ) (cb : ℝ) : ℝ :=
  1 + (1 + 1 / 1) * (12 * 1 ^ 2 * (ell : ℝ) ^ 8 * (4 * ell / cb) ^ 2)
    + 2 * ((17 / Real.sqrt 2) * 12 * (1 * (ell : ℝ) ^ 4)) *
      ((ell : ℝ) * (Real.sqrt (12 / cb) + Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell) - 1) * (4 / cb))) ^ 2

theorem etaS_le_etaB (ell W : ℕ) (hell : 1 ≤ ell) (hW : 1 ≤ W) {cs ρ cb : ℝ} (hcb : 0 < cb) (hcs : cb ≤ cs)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) : etaS ell W cs ρ 1 ≤ etaB ell cb := by
  have hlR : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hlg : 0 ≤ Real.log ell := Real.log_nonneg hlR
  have hcs0 : 0 < cs := lt_of_lt_of_le hcb hcs
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hq : 2 * (ell : ℝ) ^ 2 * Real.log ell / W ≤ 2 * (ell : ℝ) ^ 2 * Real.log ell :=
    div_le_self (by positivity) hWr
  have hq0 : 0 ≤ 2 * (ell : ℝ) ^ 2 * Real.log ell / W := by positivity
  have he0 : 0 ≤ Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1 := by
    linarith [Real.add_one_le_exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W)]
  have he : Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1 ≤ Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell) - 1 := by
    have := Real.exp_le_exp.mpr hq; linarith
  have h1 : (4 * ell / cs) ^ 2 ≤ (4 * ell / cb) ^ 2 := by
    have : 4 * (ell : ℝ) / cs ≤ 4 * ell / cb := div_le_div_of_nonneg_left (by positivity) hcb hcs
    exact pow_le_pow_left₀ (by positivity) this 2
  have h2 : Real.sqrt (12 / cs) ≤ Real.sqrt (12 / cb) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_left (by norm_num) hcb hcs)
  have h3 : 4 / cs ≤ 4 / cb := div_le_div_of_nonneg_left (by norm_num) hcb hcs
  have hρ2 : ρ ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ hρ0 hρ1 2
  unfold etaS etaB
  have hA : 12 * ρ ^ 2 * (ell : ℝ) ^ 8 * (4 * ell / cs) ^ 2 ≤ 12 * 1 ^ 2 * (ell : ℝ) ^ 8 * (4 * ell / cb) ^ 2 := by
    gcongr
  have hB : (ell : ℝ) * (Real.sqrt (12 / cs) + Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1) * (4 / cs))
      ≤ (ell : ℝ) * (Real.sqrt (12 / cb) + Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell) - 1) * (4 / cb)) := by
    have hE : 0 ≤ Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell) - 1 := le_trans he0 he
    gcongr
  have hB0 : 0 ≤ (ell : ℝ) * (Real.sqrt (12 / cs) + Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1)
      * (4 / cs)) := by positivity
  have hB2 := pow_le_pow_left₀ hB0 hB 2
  have hC : 2 * ((17 / Real.sqrt 2) * 12 * (ρ * (ell : ℝ) ^ 4)) ≤ 2 * ((17 / Real.sqrt 2) * 12 * (1 * (ell : ℝ) ^ 4)) := by
    gcongr
  have hC0 : 0 ≤ 2 * ((17 / Real.sqrt 2) * 12 * (ρ * (ell : ℝ) ^ 4)) := by positivity
  have hD := mul_le_mul hC hB2 (by positivity) (by positivity)
  nlinarith

theorem classRightInv_of_cov (hB : AdalyFormal.OneGap.BallChartsG) (hcov : ClassRightInvCov) : ClassRightInv := by
  intro ell hell2 a ha
  have hell0 : 0 < ell := by omega
  have hell1 : 1 ≤ ell := by omega
  have hlR : (1 : ℝ) ≤ ell := by exact_mod_cast hell1
  have hpi := Real.pi_pos
  obtain ⟨m₁B, hBm⟩ := AdalyFormal.OneGap.ballCharts_of_G hB ell hell2
  obtain ⟨m₁c, hcm⟩ := hcov ell hell2 a ha
  obtain ⟨s0, hs0, hwin⟩ := AdalyFormal.M2F123.window ell hell2
  obtain ⟨W₀, hW₀, ε1, hε1, a₁, ha₁, hN⟩ := AdalyFormal.M1W4Num.w4Num_exists ell hell2 a ha
  set cb : ℝ := (1 / 2) / max 6 (16 / (3 * a)) with hcbdef
  have hmx : (0 : ℝ) < max 6 (16 / (3 * a)) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hcb : 0 < cb := by rw [hcbdef]; positivity
  refine ⟨m₁B + m₁c + 11, fun m hm => ?_⟩
  have hm11 : 11 ≤ m := by omega
  set M : ℕ := ell ^ m with hMdef
  have hM2002 : 2002 ≤ M := by
    have h1 : 2 ^ 11 ≤ ell ^ 11 := Nat.pow_le_pow_left hell2 11
    have h2 : ell ^ 11 ≤ ell ^ m := Nat.pow_le_pow_right hell0 hm11
    omega
  have hM0 : 0 < M := by omega
  have hM1 : 1 ≤ M := by omega
  obtain ⟨R₁B, hRB⟩ := hBm m (by omega)
  obtain ⟨cW, cG, hcW, hcG, R₁c, hRc⟩ := hcm m (by omega)
  set ηb : ℝ := etaB ell cb with hηb
  set νb : ℝ := 2 * ((17 / Real.sqrt 2) * 12 * (1 * (ell : ℝ) ^ 4)) with hνb
  have hηb0 : 0 ≤ ηb := by
    rw [hηb]; unfold etaB
    have : 0 ≤ Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell) - 1 := by
      have : 0 ≤ 2 * (ell : ℝ) ^ 2 * Real.log ell := by have := Real.log_nonneg hlR; positivity
      linarith [Real.add_one_le_exp (2 * (ell : ℝ) ^ 2 * Real.log ell)]
    positivity
  have hνb0 : 0 ≤ νb := by rw [hνb]; positivity
  refine ⟨(1 + ηb) * (45 * cG) / a + νb * cW / a + (1 + ηb), add_pos_of_nonneg_of_pos (add_nonneg
    (div_nonneg (mul_nonneg (by linarith) (by positivity)) ha.le) (div_nonneg (mul_nonneg hνb0 hcW) ha.le)) (by linarith),
    R₁B + R₁c + W₀ + 1000 * ell + 17 * ell,
    fun R hR => ?_⟩
  have hR1 : 1 ≤ R := by omega
  have hR8 : 8 * ell ≤ R := by omega
  have hRW : W₀ ≤ R := by omega
  have hR1000 : 1000 * ell ≤ R := by omega
  obtain ⟨C, hC1, sB, hsB, hBf⟩ := hRB R (by omega)
  obtain ⟨sc, hsc, hcf⟩ := hRc R (by omega)
  have hCpos : (0 : ℝ) < C := by linarith
  set K : ℝ := (ell : ℝ) ^ 3 * C with hKdef
  have hKpos : 0 < K := by positivity
  have hRM1000 : 1000 * ell ≤ R * M := le_trans hR1000 (Nat.le_mul_of_pos_right R hM0)
  have hRM18 : 18 ≤ R * M := by omega
  set c₁ : ℝ := (4 * Real.pi + 4) * (2 * (ell : ℝ) ^ 3 * K) with hc₁
  set c₂ : ℝ := 30 * ((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) with hc₂
  have hc₁0 : 0 < c₁ := by positivity
  have hc₂0 : 0 < c₂ := by positivity
  refine ⟨min sc (min sB (min (s0 / K) (min (a₁ / (2 * (ell : ℝ) ^ 3 * K)) (1 / (c₂ * c₁))))),
    lt_min hsc (lt_min hsB (lt_min (by positivity) (lt_min (by positivity) (by positivity)))), ?_⟩
  intro k hk Lu α₀ hα hsα hT S hS hthick Lam hL hLne U hU hloc
  set t : ℝ := (12 : ℝ) * (M : ℝ) * α₀ with htdef
  have hsα0 : t ≤ min sc (min sB (min (s0 / K) (min (a₁ / (2 * (ell : ℝ) ^ 3 * K)) (1 / (c₂ * c₁))))) := hsα
  have ht0 : 0 ≤ t := by positivity
  have hsc' : t ≤ sc := hsα0.trans (min_le_left _ _)
  have hsB' : t ≤ sB := hsα0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hs3 : t ≤ s0 / K := hsα0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hs4 : t ≤ a₁ / (2 * (ell : ℝ) ^ 3 * K) :=
    hsα0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hs5 : t ≤ 1 / (c₂ * c₁) :=
    hsα0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  set β : ℝ := (ell : ℝ) ^ 3 * (C * α₀) with hβdef
  have hβpos : 0 < β := by positivity
  have hβK : β = K * α₀ := by rw [hβdef, hKdef]; ring
  have htβ : (12 : ℝ) * M * β = K * t := by rw [hβK, htdef]; ring
  set α1 : ℝ := alpha1 ell β with hα1def
  have hα1pos : 0 < α1 := by rw [hα1def]; unfold alpha1; positivity
  have htα1 : (12 : ℝ) * M * α1 = 2 * (ell : ℝ) ^ 3 * K * t := by
    rw [hα1def]; unfold alpha1; rw [hβK, htdef]; ring
  have hβs0 : (12 : ℝ) * M * β ≤ s0 := by
    rw [htβ]; have := (le_div_iff₀ hKpos).1 hs3; linarith
  have hα1a₁ : (12 : ℝ) * M * α1 ≤ a₁ := by
    rw [htα1]; have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (ell : ℝ) ^ 3 * K)).1 hs4; linarith
  have hr_eq : rho1 12 M α1 = c₁ * t := by
    unfold rho1; rw [hc₁]; push_cast; rw [show (12 : ℝ) * M * α1 = 2 * (ell : ℝ) ^ 3 * K * t from htα1]; ring
  have hr0 : 0 ≤ rho1 12 M α1 := rho1_nonneg 12 M α1 hα1pos.le
  have hct : c₁ * t ≤ 1 / c₂ := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < c₂ * c₁)).1 hs5
    rw [le_div_iff₀ hc₂0]; nlinarith
  have hc₂1 : (1 : ℝ) ≤ c₂ := by
    rw [hc₂]; have : (1 : ℝ) ≤ ell := hlR; nlinarith [sq_nonneg (ell : ℝ)]
  have hr1 : rho1 12 M α1 ≤ 1 := by
    rw [hr_eq]; refine hct.trans ?_; rw [div_le_one hc₂0]; exact hc₂1
  have hrT : rhoT ell 12 M α1 ≤ 1 / 30 := by
    unfold rhoT
    rw [hr_eq]
    have e : ((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) * (c₁ * t) = c₂ * (c₁ * t) / 30 := by rw [hc₂]; ring
    rw [e, div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 30)]
    have := mul_le_mul_of_nonneg_left hct hc₂0.le
    rw [mul_one_div_cancel hc₂0.ne'] at this
    linarith
  have hrT0 : 0 ≤ rhoT ell 12 M α1 := rhoT_nonneg ell 12 M α1 hα1pos.le
  have hcs : cb ≤ csOf a (rhoT ell 12 M α1) := by
    unfold csOf
    rw [hcbdef]
    apply div_le_div_of_nonneg_right _ hmx.le
    have : rhoT ell 12 M α1 ^ 2 ≤ (1 / 30) ^ 2 := pow_le_pow_left₀ hrT0 hrT 2
    nlinarith
  obtain ⟨h5, hLs⟩ := AdalyFormal.M2F123.torus_facts (k := k) hell2 (by omega : 6 ≤ m) hT
  have hη : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by positivity
  have hBat := hBf k hk Lu α₀ hα hsB' hT S hS Lam hL U hU hloc hLne
  obtain ⟨ha1w, hsm4, -, -⟩ := hwin M β hβpos.le hβs0
  have hbc := AdalyFormal.OneGap.blockCharts_ball hell2 hS hM2002 hRM1000 hLs hC1 hα hη hBat
  obtain ⟨-, -, hNum⟩ := hN M R hM0 hRW α1 hα1pos.le hα1a₁
  have hHc : SiteS1 ell k S U a (csOf a (rhoT ell 12 M α1)) :=
    AdalyFormal.OneGap12.siteS1_of_charts12 hell2 hS hRM18 (AdalyFormal.M1GaugeW4.hbig_of ell k Lu h5) hLs hη
      hβpos.le ha1w hsm4 U hbc a ha
  have h216 := (rhoT_smalls ell 12 M α1 hα1pos.le hell1 hsm4).1
  have hW1 : 1 ≤ R * M * ell := by
    have : 1 ≤ R * M := by nlinarith
    nlinarith
  have hp := AdalyFormal.M2Skel.hatPack_of_S1 (W := R * M * ell) hell1 ha hNum h216 hHc
  have hK1 : (1 : ℝ) ≤ K := by
    have : (1 : ℝ) ≤ (ell : ℝ) ^ 3 := one_le_pow₀ hlR
    rw [hKdef]; nlinarith
  have hαβ : α₀ ≤ β := by rw [hβK]; nlinarith
  have hUb := AdalyFormal.OneGap.classCoupled_mono hη.le hαβ hU
  have hb1 : ((12 : ℕ) : ℝ) * M * β ≤ 1 := by
    have h1 : (12 : ℝ) * M * β ≤ 12 * M * ((ell : ℝ) ^ 3 * (2 * β)) := by
      have : β ≤ (ell : ℝ) ^ 3 * (2 * β) := by
        have : (1 : ℝ) ≤ (ell : ℝ) ^ 3 := one_le_pow₀ hlR
        nlinarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have := h1.trans ha1w
    simpa using this
  have hreg : HolRegime S ell k U (rho1 12 M α1) := AdalyFormal.M2Skel.holRegime_rho1 hell1 hS hη hβpos.le hb1 hUb
  have hR := hcf k hk Lu α₀ hα hsc' hT S hS hthick Lam hL hLne U hU hloc
  intro v
  obtain ⟨g, hg, hE⟩ := hext_of_rightinv_cov hS hell2 hR1 hM1 hW1 le_rfl hell0 U a _ hp (rho1 12 M α1) hr0 hreg 1
    one_pos Lam cW cG hcW hcG hR v
  refine ⟨g, hg, hE.trans ?_⟩
  have hηle := etaS_le_etaB ell (R * M * ell) hell1 hW1 hcb hcs hr0 hr1
  have hνle : 2 * ((17 / Real.sqrt 2) * 12 * (rho1 12 M α1 * (ell : ℝ) ^ 4)) ≤ νb := by
    rw [hνb]; gcongr
  have hN0 : 0 ≤ ‖diagW (geomOf ell k S) (fun p => Real.sqrt (massW (geomOf ell k S) a p)) v‖ ^ 2 := sq_nonneg _
  refine mul_le_mul_of_nonneg_right ?_ hN0
  have h1 : (1 + etaS ell (R * M * ell) (csOf a (rhoT ell 12 M α1)) (rho1 12 M α1) 1) * (45 * cG) / a
      ≤ (1 + ηb) * (45 * cG) / a := by
    apply div_le_div_of_nonneg_right _ ha.le
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have h2 : 2 * ((17 / Real.sqrt 2) * 12 * (rho1 12 M α1 * (ell : ℝ) ^ 4)) * cW / a ≤ νb * cW / a := by
    apply div_le_div_of_nonneg_right _ ha.le
    exact mul_le_mul_of_nonneg_right hνle hcW
  linarith

/-- **the frozen r8 headline from the covariant right inverse and the thin-torus case** -/
theorem target8_of_rightInvCov (hcov : ClassRightInvCov) (hThin : AdalyFormal.OneGap.ThinTori) :
    AdalyFormal.StatementLaneG.P428Target8 :=
  target8_of_rightInv (classRightInv_of_cov AdalyFormal.M2BallCharts.ballChartsG hcov) hThin

end AdalyFormal.M2OpLayer

#print axioms AdalyFormal.M2OpLayer.ClassRightInvCov
#print axioms AdalyFormal.M2OpLayer.etaB
#print axioms AdalyFormal.M2OpLayer.etaS_le_etaB
#print axioms AdalyFormal.M2OpLayer.classRightInv_of_cov
#print axioms AdalyFormal.M2OpLayer.target8_of_rightInvCov
