import PW8

/-!
# WN1 (renamed from NF1: module-name collision with deps/base/NF4) -- the M0 slice route (slice_coercivity GN7/GN8/GN12) on a GENERAL tower geometry with `Ω₀ = univ`

The full-tower statements GN7 (`slice_coercive_cond`), GN8 (`ginv_coercive_fullTower_named`) and GN12
(`phi_drift_decomp`) are re-stated for any `G : TowerGeom L` with `G.Om0 = univ` and an ARBITRARY constraint map
`QU : SiteL2 L →L[ℝ] C` whose kernel lies in `N(Q'(U))` (GN7 used the top-level map `Qtop`, valid only on the full
tower).  Proofs: the same abstract lemmas (SL1–SL4, GN3, GN4, GN6) with `GF ell k Lu` replaced by `G`.

* `PhiG G a V y = ⟪y, Δ(V) y⟫ + ⟪y, Q(V)* a Q(V) y⟫` (genuine `Delta`, `MassFull`, bond sector at `V`).
* `slice_coercive_gen` : GN7 for `G`, `QU`.
* `ginv_coercive_gen`  : GN8 for `G` (B0 as the hypothesis `hB0`), any bond-sector `Jf`.
* `phi_drift_gen`      : GN12 for `G`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.W3NF

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantLM_L2)
open AdalyFormal.SliceCoerc

variable {L : PeriodicLatticeExtent}

/-- `Φ_V(y) = ⟪y, Δ(V) y⟫ + ⟪y, Q(V)* a Q(V) y⟫` on a general geometry. -/
noncomputable def PhiG (G : TowerGeom L) (a : ℝ) (V : Cfg L) (y : BondFnL2 L) : ℝ :=
  ⟪y, Delta G V y⟫ + ⟪y, MassFull G a (bondSectorOf G V) y⟫

/-- the slice constant `γ = κ (δP + κ P² (δ + b ε)) + δ`, `κ = b q` (GN7). -/
noncomputable def gamS (P δ b ε q : ℝ) : ℝ := (b * q) * (δ * P + (b * q) * P ^ 2 * (δ + b * ε)) + δ

theorem gamS_nonneg {P δ b ε q : ℝ} (hP : 0 ≤ P) (hδ : 0 ≤ δ) (hb : 0 ≤ b) (hε : 0 ≤ ε) (hq : 0 ≤ q) :
    0 ≤ gamS P δ b ε q := by
  unfold gamS
  have := mul_nonneg hb hε
  positivity

/-- **GN7 on a general geometry.** -/
theorem slice_coercive_gen {C : Type*} [NormedAddCommGroup C] [InnerProductSpace ℝ C]
    (G : TowerGeom L) (hOm : G.Om0 = Set.univ) (U : Cfg L) (a : ℝ) (QU : SiteL2 L →L[ℝ] C)
    (nsq c1 t e P δ b ε q : ℝ) (hn : 0 ≤ nsq) (ht : 0 ≤ t) (hP : 0 ≤ P) (hδ : 0 ≤ δ) (hb : 0 ≤ b)
    (hε : 0 ≤ ε) (hq : 0 ≤ q)
    (hflat : ∀ y : BondFnL2 L,
      c1 * ‖y‖ ^ 2 ≤ nsq * (PhiG G a (trivialU L) y + ‖Rproj G (trivialU L) (gradAdj (trivialU L) y)‖ ^ 2))
    (hdrift : ∀ x : BondFnL2 L, PhiG G a (trivialU L) x ≤ (1 + t) * PhiG G a U x + e * ‖x‖ ^ 2)
    (hPoinc1 : ∀ ν ∈ NQp G (trivialU L), ‖ν‖ ≤ P * ‖gradL2 (trivialU L) ν‖)
    (hd : ∀ f, ‖gradL2 (trivialU L) f - gradL2 U f‖ ≤ δ * ‖f‖)
    (hNU : ∀ f, QU f = 0 → f ∈ NQp G U)
    (hext : ∀ w : C, ∃ f, QU f = w ∧ ‖gradL2 U f‖ ≤ b * ‖w‖)
    (hQq : ∀ f, ‖QU f‖ ≤ q * ‖f‖)
    (hQN1 : ∀ ν ∈ NQp G (trivialU L), ‖QU ν‖ ≤ ε * ‖ν‖)
    (x : BondFnL2 L) (hx : Rproj G U (gradAdj U x) = 0) :
    (c1 - nsq * gamS P δ b ε q ^ 2 - nsq * e) / (1 + t) * ‖x‖ ^ 2 ≤ nsq * PhiG G a U x := by
  have hx' := (Rproj_eq_zero_iff G hOm U _).mp hx
  have hharm : ∀ s, (∀ ν ∈ NQp G U, ⟪gradL2 U s, gradL2 U ν⟫ = 0) → ‖gradL2 U s‖ ≤ b * q * ‖s‖ :=
    fun s hs => harmonic_energy_of_ext (gradL2 U) QU (NQp G U) hNU b q hb hext hQq s hs
  have hκ : 0 ≤ b * q := mul_nonneg hb hq
  have hS1 := slice_div_small_of_harm (gradL2 U) (gradAdj U) (NQp G U) (gradAdj_adj U) (b * q) hκ hharm x hx'
  have hS2 := hharm (gradAdj U x) hx'
  have hR := R1_on_slice_le (gradL2 (trivialU L)) (gradL2 U) (gradAdj (trivialU L)) (gradAdj U)
    (Rproj G (trivialU L)) QU (NQp G (trivialU L)) (NQp G U)
    (gradAdj_adj (trivialU L)) (gradAdj_adj U)
    (Rproj_norm_sq G (trivialU L)) (Rproj_mem_lap G hOm (trivialU L))
    P δ b ε (b * q) hP hδ hb hε hκ hPoinc1 hd hext hNU hQN1 x hx' hS1 hS2
  have hγ0 := gamS_nonneg hP hδ hb hε hq
  have hR2 : ‖Rproj G (trivialU L) (gradAdj (trivialU L) x)‖ ^ 2 ≤ gamS P δ b ε q ^ 2 * ‖x‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hR 2
  exact slice_from_flat nsq c1 _ e t (‖x‖ ^ 2) _ _ _ hn ht (hflat x) hR2 (hdrift x)

/-- the GN8 coercivity constant `cs = (c1 − n²γ² − n²e)/((1+t) n²)`. -/
noncomputable def csS (nsq c1 t e γ : ℝ) : ℝ := (c1 - nsq * γ ^ 2 - nsq * e) / (1 + t) / nsq

/-- **GN8 on a general geometry**, genuine base data `baseData G U a (bondSectorOf G U) Jf`. -/
theorem ginv_coercive_gen {C : Type*} [NormedAddCommGroup C] [InnerProductSpace ℝ C]
    (G : TowerGeom L) (hOm : G.Om0 = Set.univ) (U : Cfg L) (a : ℝ) (Jf : BondFnL2 L)
    (hu : IsUnit (DelpA G U a + (1 - siteMask G.Om0)))
    (hB0 : ∀ ν ∈ NQp G U, (bondSectorOf G U).Qfull (gradL2 U ν) = 0)
    (PU : ℝ) (hPU : 0 ≤ PU) (hPoincU : ∀ ν ∈ NQp G U, ‖ν‖ ≤ PU * ‖gradL2 U ν‖)
    (QU : SiteL2 L →L[ℝ] C)
    (nsq c1 t e P δ b ε q : ℝ) (hn : 0 < nsq) (ht : 0 ≤ t) (hP : 0 ≤ P) (hδ : 0 ≤ δ) (hb : 0 ≤ b)
    (hε : 0 ≤ ε) (hq : 0 ≤ q)
    (hsmall : nsq * gamS P δ b ε q ^ 2 + nsq * e < c1)
    (hflat : ∀ y : BondFnL2 L,
      c1 * ‖y‖ ^ 2 ≤ nsq * (PhiG G a (trivialU L) y + ‖Rproj G (trivialU L) (gradAdj (trivialU L) y)‖ ^ 2))
    (hdrift : ∀ x : BondFnL2 L, PhiG G a (trivialU L) x ≤ (1 + t) * PhiG G a U x + e * ‖x‖ ^ 2)
    (hPoinc1 : ∀ ν ∈ NQp G (trivialU L), ‖ν‖ ≤ P * ‖gradL2 (trivialU L) ν‖)
    (hd : ∀ f, ‖gradL2 (trivialU L) f - gradL2 U f‖ ≤ δ * ‖f‖)
    (hNU : ∀ f, QU f = 0 → f ∈ NQp G U)
    (hext : ∀ w : C, ∃ f, QU f = w ∧ ‖gradL2 U f‖ ≤ b * ‖w‖)
    (hQq : ∀ f, ‖QU f‖ ≤ q * ‖f‖)
    (hQN1 : ∀ ν ∈ NQp G (trivialU L), ‖QU ν‖ ≤ ε * ‖ν‖)
    (x : ↥(bondSupp G)) :
    ‖x‖ ^ 2 ≤ max (2 / csS nsq c1 t e (gamS P δ b ε q)) (2 * PU ^ 2) *
      ⟪x, (baseData G U a (bondSectorOf G U) Jf).Ginv x⟫ := by
  have h1 : 0 < 1 + t := by linarith
  have h2 : 0 < c1 - nsq * gamS P δ b ε q ^ 2 - nsq * e := by linarith
  have hcs : 0 < csS nsq c1 t e (gamS P δ b ε q) := div_pos (div_pos h2 h1) hn
  refine ginv_coercive_cond G hOm U a (bondSectorOf G U) Jf hu hB0 PU hPU hPoincU _ hcs (fun y hy => ?_) x
  have h := slice_coercive_gen G hOm U a QU nsq c1 t e P δ b ε q hn.le ht hP hδ hb hε hq hflat hdrift
    hPoinc1 hd hNU hext hQq hQN1 y hy
  unfold PhiG at h
  unfold csS
  rw [div_mul_eq_mul_div, div_le_iff₀ hn]
  linarith

/-- **GN12 on a general geometry.** -/
theorem phi_drift_gen (G : TowerGeom L) (U : Cfg L) (a : ℝ) (ha : 0 ≤ a) (t : ℝ) (ht : 0 < t) (δc θ δm : ℝ)
    (hc : ∀ x : BondFnL2 L,
      ‖AdalyFormal.StatementLaneR6.plaqMask (plaqIn G.Om0) (curlCovariantLM_L2 (trivialU L) x)
        - AdalyFormal.StatementLaneR6.plaqMask (plaqIn G.Om0) (curlCovariantLM_L2 U x)‖ ≤ δc * ‖x‖)
    (hdp : ∀ x : BondFnL2 L,
      |AdalyFormal.StatementLaneR6.deltaPrimeBilL2NormLoc U (plaqIn G.Om0) x x| ≤ θ * ‖x‖ ^ 2)
    (hm : ∀ x : BondFnL2 L,
      ∑ p : BIdx G, a * (G.ell : ℝ) ^ (p.1 : ℕ) *
        ‖(bondSectorOf G (trivialU L)).Qfull x p - (bondSectorOf G U).Qfull x p‖ ^ 2 ≤ δm ^ 2 * ‖x‖ ^ 2)
    (x : BondFnL2 L) :
    PhiG G a (trivialU L) x ≤ (1 + t) * PhiG G a U x + ((1 + t) * θ + (1 + 1 / t) * (δc ^ 2 + δm ^ 2)) * ‖x‖ ^ 2 := by
  unfold PhiG Delta
  rw [AdalyFormal.StatementLaneR6.inner_deltaKLocCLM, AdalyFormal.StatementLaneR6.inner_deltaKLocCLM,
    inner_MassFull, inner_MassFull]
  have h0 : AdalyFormal.StatementLaneR6.deltaPrimeBilL2NormLoc (trivialU L) (plaqIn G.Om0) x x = 0 :=
    AdalyFormal.StatementLaneR6.deltaPrimeBilNormLoc_trivialU _ _ _
  rw [h0, add_zero, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  set c1 := AdalyFormal.StatementLaneR6.plaqMask (plaqIn G.Om0) (curlCovariantLM_L2 (trivialU L) x)
  set cU := AdalyFormal.StatementLaneR6.plaqMask (plaqIn G.Om0) (curlCovariantLM_L2 U x)
  have hy := young_sq c1 cU t ht
  have hc2 : ‖c1 - cU‖ ^ 2 ≤ δc ^ 2 * ‖x‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hc x) 2
  have hmw := young_wsum Finset.univ (fun p : BIdx G => a * (G.ell : ℝ) ^ (p.1 : ℕ))
    (fun p _ => by positivity) (fun p => (bondSectorOf G (trivialU L)).Qfull x p)
    (fun p => (bondSectorOf G U).Qfull x p) t ht
  have hmx := hm x
  have hdx := hdp x
  have hd' := neg_abs_le (AdalyFormal.StatementLaneR6.deltaPrimeBilL2NormLoc U (plaqIn G.Om0) x x)
  have h1t : 0 ≤ 1 + 1 / t := by positivity
  have hA : (1 + 1 / t) * ‖c1 - cU‖ ^ 2 ≤ (1 + 1 / t) * (δc ^ 2 * ‖x‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hc2 h1t
  have hB : (1 + 1 / t) * ∑ p : BIdx G, a * (G.ell : ℝ) ^ (p.1 : ℕ) *
        ‖(bondSectorOf G (trivialU L)).Qfull x p - (bondSectorOf G U).Qfull x p‖ ^ 2
      ≤ (1 + 1 / t) * (δm ^ 2 * ‖x‖ ^ 2) := mul_le_mul_of_nonneg_left hmx h1t
  have hC : -(1 + t) * AdalyFormal.StatementLaneR6.deltaPrimeBilL2NormLoc U (plaqIn G.Om0) x x
      ≤ (1 + t) * (θ * ‖x‖ ^ 2) := by nlinarith
  linarith [hy, hmw, hA, hB, hC]

#print axioms gamS_nonneg
#print axioms slice_coercive_gen
#print axioms ginv_coercive_gen
#print axioms phi_drift_gen

end AdalyFormal.W3NF
