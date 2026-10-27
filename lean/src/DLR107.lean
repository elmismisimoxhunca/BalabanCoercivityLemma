import DLR106

/-!
# DL107 -- package-free M0 theorems on a window, every `ℓ ≥ 2`, `a > 0`, `t > 0`, and the window's non-vacuity

(r8 copy: DLR107.)  Built on `stageB2` (DL106).
* **`instIneq_M0_class_window ℓ a t`** : DL84 WITHOUT the numerics package (and without KUSmall/UnitSmall): ∃ `ε₀ > 0`,
  `γm > 0` such that every `U` in M0RegimeR ∩ PerCubeRegular2 (full tower) with `rhoM0 < ε₀` and `fMα₀ < ε₀` (and `0 ≤ α₀`,
  `4fMα₀ ≤ 1`, the torus conditions, `LamBlockSum`) satisfies the frozen r7 `InstIneq` at `γm`.
* **`M0_class_window_WD ℓ a t`** : on the same window, the m0_finish route (MF11 `wellDef_M0`, MF7 `instIneq_M0_kuniform`, with
  `hD2`/`hJ` from DL100 and `eps2op·K̂ < 1` from `stageB2`): `GenP.WellDef (PU …)` AND `InstIneq … γm …`.
* `window_domain_curved ℓ M a t ε₀` : for EVERY `ε₀ > 0` the window's domain contains a CURVED field (the MC8 sine field
  `UwA` on `(16ℓM)³` at a small amplitude, M0 regime in its own gauge, both printed classes), every `k`.
* **`M0_class_window_witnessed ℓ a t`** : `M0_class_window_WD` together with, at ITS `ε₀` and `γm`, for every `M ≥ 1` and `k`, a
  curved field of the domain at which `WellDef ∧ InstIneq` hold and the printed form is strictly positive on a nonzero `Λ̃` field.
-/
set_option autoImplicit false
set_option maxHeartbeats 32000000

namespace AdalyFormal.DLayer

open Filter Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.AsmM0 (KhatM0 ThetaM0 M0RegimeR rhoM0)
open AdalyFormal.RegBgKU (kapHat KUSmall)
open AdalyFormal.BondComposite (rr)
open AdalyFormal.NonflatJet (rhoOf r0)
open EstimatesLayer.E1E3 (e2Majorant)
open AdalyFormal.M0Finish (dCM0 cBM0 EbarM0 gam0Form gam0M0 UnitSmall PU)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLane2 (PerCubeRegular2 Ufield OnLambdaT)
open AdalyFormal.StatementLaneG (InstIneq LamBlockSum gparams)
open AdalyFormal.IngredientFamilyR2 (fullTower Cfg)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.CurvBlock (dv)
open AdalyFormal.M0Corollary (GlobalRegular2)

/-- **DL84 without the numerics package (and without KUSmall/UnitSmall): every `ℓ ≥ 2`, `a > 0`, `t > 0`, in a window** -/
theorem instIneq_M0_class_window (ell : ℕ) (hell : 2 ≤ ell) (a t : ℝ) (ha : 0 < a) (ht : 0 < t) :
    ∃ ε₀ > 0, ∃ γm > 0, ∀ (k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) (e q0 : ℝ),
      M0RegimeR ell k Lu U a t e q0 → rhoM0 ell k e q0 < ε₀ →
      (∀ μ : Fin 3, ell < Lu μ + 1) → (∀ μ, ell ∣ Lu μ + 1) →
      ∀ (Lam : Set (PeriodicLatticeSite Lu)), LamBlockSum ell Lam →
      ∀ (M f : ℕ) (α₀ : ℝ), 0 < M → 4 ≤ f → 0 ≤ α₀ →
      PerCubeRegular2 ell M f k (fullTower ell k Lu) α₀ ((ell : ℝ) ^ k)⁻¹ U →
      4 * ((f : ℝ) * M * α₀) ≤ 1 → (f : ℝ) * M * α₀ < ε₀ →
      InstIneq ell k (by omega) a Lu γm (fullTower ell k Lu) Lam U := by
  obtain ⟨θ₁, -, ε₀, hε₀, γm, hγm, hB⟩ := stageB2 ell hell a t ha ht
  refine ⟨ε₀, hε₀, γm, hγm, ?_⟩
  intro k Lu U e q0 R hρ1 hstrict hd Lam hLB M f α₀ hM hf hα₀ hP hsm hβ1
  have hρ0 := m0_rho_nonneg ell k Lu U a t e q0 R
  obtain ⟨H, HU, Num, hγ, -, -⟩ := hB _ _ hρ0 hρ1 (mul_nonneg (by positivity) hα₀) hβ1
  exact instIneq_mono hγ (instIneq_M0_class_unconditional ell k Lu (by omega) U a t e q0 R H HU hstrict hd Lam hLB
    M f α₀ hM hf hP hsm θ₁ Num)

/-- **the m0_finish route on the same window**: MF11's `WellDef` AND MF7's `InstIneq` (hD2/hJ from DL100, `eps2op·K̂ < 1`
from `stageB2`) -/
theorem M0_class_window_WD (ell : ℕ) (hell : 2 ≤ ell) (a t : ℝ) (ha : 0 < a) (ht : 0 < t) :
    ∃ ε₀ > 0, ∃ γm > 0, ∀ (k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) (e q0 : ℝ),
      M0RegimeR ell k Lu U a t e q0 → rhoM0 ell k e q0 < ε₀ →
      (∀ μ : Fin 3, ell < Lu μ + 1) → (∀ μ, ell ∣ Lu μ + 1) →
      ∀ (Lam : Set (PeriodicLatticeSite Lu)), LamBlockSum ell Lam →
      ∀ (M f : ℕ) (α₀ : ℝ), 0 < M → 4 ≤ f → 0 ≤ α₀ →
      PerCubeRegular2 ell M f k (fullTower ell k Lu) α₀ ((ell : ℝ) ^ k)⁻¹ U →
      4 * ((f : ℝ) * M * α₀) ≤ 1 → (f : ℝ) * M * α₀ < ε₀ →
      AdalyFormal.StatementLaneG.GenP.WellDef (PU ell k Lu (by omega) U a Lam) ∧
      InstIneq ell k (by omega) a Lu γm (fullTower ell k Lu) Lam U := by
  obtain ⟨θ₁, -, ε₀, hε₀, γm, hγm, hB⟩ := stageB2 ell hell a t ha ht
  refine ⟨ε₀, hε₀, γm, hγm, ?_⟩
  intro k Lu U e q0 R hρ1 hstrict hd Lam hLB M f α₀ hM hf hα₀ hP hsm hβ1
  have hρ0 := m0_rho_nonneg ell k Lu U a t e q0 R
  obtain ⟨H, HU, Num, -, hop, hγop⟩ := hB _ _ hρ0 hρ1 (mul_nonneg (by positivity) hα₀) hβ1
  exact ⟨wellDef_M0_discharged ell k Lu (by omega) U a t e q0 R H HU hd Lam M f α₀ hM hf hP hsm θ₁ Num hop,
    instIneq_mono hγop (instIneq_M0_kuniform_discharged ell k Lu (by omega) U a t e q0 R H HU hstrict hd Lam hLB
      M f α₀ hM hf hP hsm θ₁ Num hop)⟩

/-! ## the window's domain is never empty -/

/-- the sine field of MC8 on `(16ℓM)³` at amplitude `A/2` (`A = 12 M α₀`), `η = ℓ⁻ᵏ` -/
noncomputable def UwA (ell M k : ℕ) (A : ℝ) : LinkCfg (scaleUp ell k (LuLM ell M)) :=
  Ufield ((ell : ℝ) ^ k)⁻¹ (AdalyFormal.M0Corollary.chiP (scaleUp ell k (LuLM ell M)) (A / 2))

/-- for EVERY `ε₀ > 0` the window contains a curved field (own gauge), every `k` -/
theorem window_domain_curved (ell M : ℕ) (hell : 2 ≤ ell) (hM : 1 ≤ M) (a t : ℝ) (ha : 0 < a) (ht : 0 < t)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    ∃ A : ℝ, 0 < A ∧ ∀ k : ℕ,
      M0RegimeR ell k (LuLM ell M) (UwA ell M k A) a t
        ((4 * Real.pi + 4) * A / (ell : ℝ) ^ k) ((4 * Real.pi + 4) * A / ((ell : ℝ) ^ k) ^ 2) ∧
      rhoM0 ell k ((4 * Real.pi + 4) * A / (ell : ℝ) ^ k) ((4 * Real.pi + 4) * A / ((ell : ℝ) ^ k) ^ 2) < ε₀ ∧
      (∀ μ : Fin 3, ell < LuLM ell M μ + 1) ∧ (∀ μ, ell ∣ LuLM ell M μ + 1) ∧
      PerCubeRegular2 ell M 12 k (fullTower ell k (LuLM ell M)) (A / (12 * M)) ((ell : ℝ) ^ k)⁻¹ (UwA ell M k A) ∧
      GlobalRegular2 ell M 12 k (A / (12 * M)) ((ell : ℝ) ^ k)⁻¹ (UwA ell M k A) ∧
      0 ≤ A / (12 * M) ∧ 4 * (((12 : ℕ) : ℝ) * M * (A / (12 * M))) ≤ 1 ∧ ((12 : ℕ) : ℝ) * M * (A / (12 * M)) < ε₀ ∧
      (∃ p : PeriodicLatticePlaquette (scaleUp ell k (LuLM ell M)),
        0 < dv (periodicPlaquetteHolonomy (UwA ell M k A) p)) := by
  have hell0 : 0 < ell := by omega
  have hell1 : 1 ≤ ell := by omega
  have hl : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hpi := Real.pi_pos
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  -- ThetaM0 is small near ρ = 0
  have hT := tTheta (tendsto_id (x := 𝓝 (0 : ℝ))) ell hell1 a t
  rw [Theta_zero] at hT
  have hTe : ∀ᶠ ρ in 𝓝 (0 : ℝ), ThetaM0 ell a t ρ < min a 1 / 1000 :=
    hT.eventually_lt tendsto_const_nhds (by have := lt_min ha one_pos; positivity)
  obtain ⟨δ, hδ, hTδ⟩ := Metric.eventually_nhds_iff.mp hTe
  -- the constants (opaque names with defining equations)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (1 + 3 * Real.pi) * (4 * Real.pi + 4) := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; positivity
  have hcne : c ≠ 0 := hc0.ne'
  have hc1 : 1 ≤ c := by rw [hc]; nlinarith
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = min (min (δ / (2 * c)) (ε₀ / (2 * c)))
      (min (1 / (4000000 * (ell : ℝ) ^ 2 * (4 * Real.pi + 4))) (1 / (1000 * (ell : ℝ) ^ 3 * c))) / 2 := ⟨_, rfl⟩
  have hA0 : 0 < A := by rw [hAdef]; positivity
  have hAδ : A ≤ δ / (2 * c) / 2 := by
    rw [hAdef]; gcongr; exact (min_le_left _ _).trans (min_le_left _ _)
  have hAε : A ≤ ε₀ / (2 * c) / 2 := by
    rw [hAdef]; gcongr; exact (min_le_left _ _).trans (min_le_right _ _)
  have hAcb : A ≤ 1 / (4000000 * (ell : ℝ) ^ 2 * (4 * Real.pi + 4)) / 2 := by
    rw [hAdef]; gcongr; exact (min_le_right _ _).trans (min_le_left _ _)
  have hA1000 : A ≤ 1 / (1000 * (ell : ℝ) ^ 3 * c) / 2 := by
    rw [hAdef]; gcongr; exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨A, hA0, fun k => ?_⟩
  -- the regime scale ᾱ = (4π+4)A, ρ = (1+3π)ᾱ = cA
  have hᾱ0 : 0 < (4 * Real.pi + 4) * A := by positivity
  have hρw : (1 + 3 * Real.pi) * ((4 * Real.pi + 4) * A) = c * A := by rw [hc]; ring
  have hcA_δ : c * A < δ := by
    have h1 : c * A ≤ c * (δ / (2 * c) / 2) := mul_le_mul_of_nonneg_left hAδ hc0.le
    have e : c * (δ / (2 * c) / 2) = δ / 4 := by field_simp <;> ring
    linarith
  have hcA_ε : c * A < ε₀ := by
    have h1 : c * A ≤ c * (ε₀ / (2 * c) / 2) := mul_le_mul_of_nonneg_left hAε hc0.le
    have e : c * (ε₀ / (2 * c) / 2) = ε₀ / 4 := by field_simp <;> ring
    linarith
  have hcA_1000 : c * A ≤ 1 / (1000 * (ell : ℝ) ^ 3) / 2 := by
    have h1 : c * A ≤ c * (1 / (1000 * (ell : ℝ) ^ 3 * c) / 2) := mul_le_mul_of_nonneg_left hA1000 hc0.le
    have e : c * (1 / (1000 * (ell : ℝ) ^ 3 * c) / 2) = 1 / (1000 * (ell : ℝ) ^ 3) / 2 := by field_simp <;> ring
    linarith
  have hl3 : (1 : ℝ) ≤ (ell : ℝ) ^ 3 := one_le_pow₀ (by linarith)
  have hinv : 1 / (1000 * (ell : ℝ) ^ 3) ≤ 1 / 1000 := by
    apply one_div_le_one_div_of_le (by norm_num); nlinarith
  have hinv0 : (0 : ℝ) < 1 / (1000 * (ell : ℝ) ^ 3) := by positivity
  have hcA_small : c * A < 1 / 1000 := by linarith
  have hAsmall : A < 1 / 1000 := by
    have : A ≤ c * A := le_mul_of_one_le_left hA0.le hc1
    linarith
  have hcb : 4000000 * (ell : ℝ) ^ 2 * ((4 * Real.pi + 4) * A) ≤ 1 := by
    have h4 : (0 : ℝ) < 4000000 * (ell : ℝ) ^ 2 * (4 * Real.pi + 4) := by positivity
    have h1 : (4000000 * (ell : ℝ) ^ 2 * (4 * Real.pi + 4)) * A
        ≤ (4000000 * (ell : ℝ) ^ 2 * (4 * Real.pi + 4)) * (1 / (4000000 * (ell : ℝ) ^ 2 * (4 * Real.pi + 4)) / 2) :=
      mul_le_mul_of_nonneg_left hAcb h4.le
    have e : (4000000 * (ell : ℝ) ^ 2 * (4 * Real.pi + 4)) * (1 / (4000000 * (ell : ℝ) ^ 2 * (4 * Real.pi + 4)) / 2)
        = 1 / 2 := by field_simp <;> ring
    have e2 : 4000000 * (ell : ℝ) ^ 2 * ((4 * Real.pi + 4) * A) = (4000000 * (ell : ℝ) ^ 2 * (4 * Real.pi + 4)) * A := by
      ring
    linarith
  have h1000 : (1 + 3 * Real.pi) * ((4 * Real.pi + 4) * A) ≤ 1 / (1000 * (ell : ℝ) ^ 3) := by
    rw [hρw]; linarith
  have h216 : 216 * ((1 + 3 * Real.pi) * ((4 * Real.pi + 4) * A)) ^ 2 < 1 := by
    rw [hρw]
    have h0 : 0 ≤ c * A := by positivity
    nlinarith
  have hsmallU : ThetaM0 ell a t ((1 + 3 * Real.pi) * ((4 * Real.pi + 4) * A)) < min a 1 / 1000 := by
    apply hTδ
    rw [Real.dist_eq, sub_zero, hρw, abs_of_pos (mul_pos hc0 hA0)]
    exact hcA_δ
  -- the field and its bounds (own gauge)
  have hAhalf : A < 1 := by linarith
  have h16 : 16 ≤ LuLM ell M 0 + 1 := by rw [LuLM_succ ell M hell1 hM 0]; nlinarith
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := by positivity
  have hn1 : (1 : ℝ) ≤ (ell : ℝ) ^ k := one_le_pow₀ (by linarith)
  have hη : 0 < ((ell : ℝ) ^ k)⁻¹ := by positivity
  obtain ⟨b1, b2⟩ := sine_bounds ell k hell0 (LuLM ell M) h16 A hA0
  have hsmall : ((ell : ℝ) ^ k)⁻¹ * A ≤ 1 := by
    have : ((ell : ℝ) ^ k)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn1
    nlinarith
  obtain ⟨hl, hp⟩ := ufield_regime ((ell : ℝ) ^ k)⁻¹ A A hη _ b1 b2 hsmall
  have hAᾱ : A ≤ (4 * Real.pi + 4) * A := by nlinarith
  have hstrict : ∀ μ : Fin 3, ell < LuLM ell M μ + 1 := fun μ => by rw [LuLM_succ ell M hell1 hM μ]; nlinarith
  have hR : M0RegimeR ell k (LuLM ell M) (UwA ell M k A) a t
      ((4 * Real.pi + 4) * A / (ell : ℝ) ^ k) ((4 * Real.pi + 4) * A / ((ell : ℝ) ^ k) ^ 2) := by
    refine regime_of_bounds ell k (LuLM ell M) hell (UwA ell M k A) a t ((4 * Real.pi + 4) * A) ha ht hᾱ0.le hstrict
      ?_ ?_ hcb h216 h1000 hsmallU
    · intro b
      have := hl b
      calc dv (UwA ell M k A b) ≤ ((ell : ℝ) ^ k)⁻¹ * A := this
        _ = A / (ell : ℝ) ^ k := by rw [div_eq_inv_mul]
        _ ≤ (4 * Real.pi + 4) * A / (ell : ℝ) ^ k := div_le_div_of_nonneg_right hAᾱ hn.le
    · intro p
      have := hp p
      have e : 2 * ((((ell : ℝ) ^ k)⁻¹) ^ 2 * A) + (4 * Real.pi + 2) * (((ell : ℝ) ^ k)⁻¹ * A) ^ 2
          = (2 * A + (4 * Real.pi + 2) * A ^ 2) / ((ell : ℝ) ^ k) ^ 2 := by field_simp
      rw [e] at this
      refine this.trans (div_le_div_of_nonneg_right ?_ (by positivity))
      nlinarith [sq_nonneg A, mul_nonneg hA0.le (sub_nonneg.mpr hAhalf.le)]
  have hρk : rhoM0 ell k ((4 * Real.pi + 4) * A / (ell : ℝ) ^ k) ((4 * Real.pi + 4) * A / ((ell : ℝ) ^ k) ^ 2)
      = (1 + 3 * Real.pi) * ((4 * Real.pi + 4) * A) :=
    AdalyFormal.M0Finish.rhoM0_class ell k hell0 _
  have hβeq' : (12 : ℝ) * M * (A / (12 * M)) = A := by field_simp
  have hβeq : ((12 : ℕ) : ℝ) * M * (A / (12 * M)) = A := by push_cast; exact hβeq'
  have hG : GlobalRegular2 ell M 12 k (A / (12 * M)) ((ell : ℝ) ^ k)⁻¹ (UwA ell M k A) := by
    have hpos : 0 < (12 : ℝ) * M * (A / (12 * M)) := by rw [hβeq']; exact hA0
    have h := AdalyFormal.M0Corollary.sine_globalRegular2 ell M k hell0 (LuLM ell M) h16 (A / (12 * M)) hpos
    rw [hβeq'] at h
    exact h
  have hcurv : ∃ p : PeriodicLatticePlaquette (scaleUp ell k (LuLM ell M)),
      0 < dv (periodicPlaquetteHolonomy (UwA ell M k A) p) := by
    have hAc1 : A / 2 < 1 := by linarith
    refine AdalyFormal.M0Corollary.sine_curved (scaleUp ell k (LuLM ell M)) _ _ (by positivity) hAc1 (by positivity)
      (inv_le_one_of_one_le₀ hn1) ?_
    have := AdalyFormal.IngredientFamilyR2.scaleUp_succ ell k (LuLM ell M) hell0 0
    have h2 : 1 ≤ ell ^ k := Nat.one_le_pow _ _ hell0
    rw [this, LuLM_succ ell M hell1 hM 0]
    have h3 : 3 ≤ 16 * ell * M := by nlinarith
    calc 3 ≤ 16 * ell * M := h3
      _ ≤ 16 * ell * M * ell ^ k := Nat.le_mul_of_pos_right _ (by positivity)
  refine ⟨hR, ?_, hstrict, fun μ => by rw [LuLM_succ ell M hell1 hM μ]; exact ⟨16 * M, by ring⟩,
    AdalyFormal.M0Corollary.perCube_of_global hG, hG, by positivity, ?_, ?_, hcurv⟩
  · rw [hρk, hρw]; exact hcA_ε
  · rw [hβeq]; linarith
  · rw [hβeq]
    have : A ≤ c * A := le_mul_of_one_le_left hA0.le hc1
    linarith

/-- **the window theorem with its own non-vacuity**: at the `(ε₀, γm)` it provides, for every `M ≥ 1` and `k`, a curved field
of the window's domain at which `WellDef ∧ InstIneq` hold and the printed form is strictly positive on a nonzero `Λ̃` field -/
theorem M0_class_window_witnessed (ell : ℕ) (hell : 2 ≤ ell) (a t : ℝ) (ha : 0 < a) (ht : 0 < t) :
    ∃ ε₀ > 0, ∃ γm > 0,
      (∀ (k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) (e q0 : ℝ),
        M0RegimeR ell k Lu U a t e q0 → rhoM0 ell k e q0 < ε₀ →
        (∀ μ : Fin 3, ell < Lu μ + 1) → (∀ μ, ell ∣ Lu μ + 1) →
        ∀ (Lam : Set (PeriodicLatticeSite Lu)), LamBlockSum ell Lam →
        ∀ (M f : ℕ) (α₀ : ℝ), 0 < M → 4 ≤ f → 0 ≤ α₀ →
        PerCubeRegular2 ell M f k (fullTower ell k Lu) α₀ ((ell : ℝ) ^ k)⁻¹ U →
        4 * ((f : ℝ) * M * α₀) ≤ 1 → (f : ℝ) * M * α₀ < ε₀ →
        AdalyFormal.StatementLaneG.GenP.WellDef (PU ell k Lu (by omega) U a Lam) ∧
        InstIneq ell k (by omega) a Lu γm (fullTower ell k Lu) Lam U) ∧
      ∀ (M : ℕ), 1 ≤ M → ∃ A : ℝ, 0 < A ∧ ∀ k : ℕ,
        M0RegimeR ell k (LuLM ell M) (UwA ell M k A) a t
          ((4 * Real.pi + 4) * A / (ell : ℝ) ^ k) ((4 * Real.pi + 4) * A / ((ell : ℝ) ^ k) ^ 2) ∧
        rhoM0 ell k ((4 * Real.pi + 4) * A / (ell : ℝ) ^ k) ((4 * Real.pi + 4) * A / ((ell : ℝ) ^ k) ^ 2) < ε₀ ∧
        PerCubeRegular2 ell M 12 k (fullTower ell k (LuLM ell M)) (A / (12 * M)) ((ell : ℝ) ^ k)⁻¹ (UwA ell M k A) ∧
        ((12 : ℕ) : ℝ) * M * (A / (12 * M)) < ε₀ ∧
        (∃ p : PeriodicLatticePlaquette (scaleUp ell k (LuLM ell M)),
          0 < dv (periodicPlaquetteHolonomy (UwA ell M k A) p)) ∧
        AdalyFormal.StatementLaneG.GenP.WellDef (PU ell k (LuLM ell M) (by omega) (UwA ell M k A) a Set.univ) ∧
        InstIneq ell k (by omega) a (LuLM ell M) γm (fullTower ell k (LuLM ell M)) Set.univ (UwA ell M k A) ∧
        ∃ Bt : Bond (LuLM ell M) → SuTwo,
          AdalyFormal.StatementLane.OnLambdaTildeIn (Set.univ : Set (PeriodicLatticeSite (LuLM ell M))) ell Bt ∧
          OnLambdaT (Set.univ : Set (PeriodicLatticeSite (LuLM ell M))) Bt ∧ 0 < bondEnergy Bt ∧
          0 < AdalyFormal.StatementLaneG.GenP.genForm
            (gparams ell k (LuLM ell M) (by omega) (fullTower ell k (LuLM ell M)) (UwA ell M k A) a Set.univ)
            (WithLp.toLp 2 (AdalyFormal.StatementLaneG.GenP.genC
              (gparams ell k (LuLM ell M) (by omega) (fullTower ell k (LuLM ell M)) (UwA ell M k A) a Set.univ) Bt)) := by
  obtain ⟨ε₀, hε₀, γm, hγm, hW⟩ := M0_class_window_WD ell hell a t ha ht
  refine ⟨ε₀, hε₀, γm, hγm, hW, fun M hM => ?_⟩
  obtain ⟨A, hA0, hk⟩ := window_domain_curved ell M hell hM a t ha ht ε₀ hε₀
  refine ⟨A, hA0, fun k => ?_⟩
  obtain ⟨hR, hρ, hstrict, hd, hP, -, hα₀, hsm, hβ, hcurv⟩ := hk k
  have hLB := AdalyFormal.StatementLaneG.lamBlockSum_univ (Lu := LuLM ell M) ell (by omega)
  obtain ⟨hWD, hI⟩ := hW k (LuLM ell M) (UwA ell M k A) _ _ hR hρ hstrict hd Set.univ hLB M 12 (A / (12 * M))
    (by omega) (by norm_num) hα₀ hP hsm hβ
  have hdvd : ∀ μ : Fin 3, ell ∣ (LuLM ell M μ + 1) := hd
  obtain ⟨Bt, hBt, hpB⟩ := AdalyFormal.Balaban.CoercUMainDesigned.lambdaTilde_nonvacuous (L := LuLM ell M) (ell := ell)
    hell hdvd
  have h1 : AdalyFormal.StatementLane.OnLambdaTildeIn (Set.univ : Set (PeriodicLatticeSite (LuLM ell M))) ell Bt :=
    (AdalyFormal.StatementLane.onLambdaTildeIn_univ ell Bt).mpr hBt
  have h2 : OnLambdaT (Set.univ : Set (PeriodicLatticeSite (LuLM ell M))) Bt :=
    fun b hb => absurd (Or.inl (Set.mem_univ _)) hb
  exact ⟨hR, hρ, hP, hβ, hcurv, hWD, hI, Bt, h1, h2, hpB, lt_of_lt_of_le (by positivity) (hI Bt h1 h2)⟩

#print axioms instIneq_M0_class_window
#print axioms M0_class_window_WD
#print axioms window_domain_curved
#print axioms M0_class_window_witnessed

end AdalyFormal.DLayer
