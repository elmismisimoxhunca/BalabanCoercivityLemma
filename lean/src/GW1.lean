import MI34
import GCz3

/-!
# GW1 -- gauge transfer of the W4 / W5 conclusions (M1 gauge lane, 2026-10-13)

For a fine gauge `γ` and `P = gparams … U …`, `P' = gparams … (U^γ) …` (`= gaugeP P γ`, definitionally), the r8 transfer lane's
`genFormHyps_gauge` gives `BaseEqv (adEL γ G) (adSL γ) (adFL γ G) P.data P'.data`.  From it:
* `wnormSq_adBL` : the stratum-weighted norm is invariant under the bondwise rotation `adBL γ`;
* `ginv_gauge` : `⟪Ad A, Ginv_{U^γ} (Ad A)⟫ = ⟪A, Ginv_U A⟫`;
* `coercive_of_gauge` : a W4-type bound `c · wnormSq ≤ ⟪·, Ginv ·⟫` at `U^γ` gives the same bound, same `c`, at `U`;
* `delta2_gauge` : the quadratic form of `Δ⁽²⁾` is invariant; `dlayer_form_gauge` transfers the stratified `hD2` bound;
* `qs_injective_gauge_iff`, `hb_gauge_iff`, `wellDef_gauge_iff` : `Q*` injectivity, `hb` and `GenP.WellDef` are gauge invariant;
* `patchCoercive_gauge` : lane E's `PatchCoercive` at `U` gives it at `U^γ` (same constant).
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.M1GaugeW4

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower scaleUp)
open AdalyFormal.StatementLaneG (gparams GenP.WellDef GenP.Nmat)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn gaugeActA)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.GaugeCov

section gen
variable {L : PeriodicLatticeExtent}

theorem norm_adBL_apply (γ : GaugeFn L) (x : BondFnL2 L) (b : Bond L) :
    ‖(WithLp.ofLp (adBL γ x)) b‖ = ‖(WithLp.ofLp x) b‖ := by
  have h := AdalyFormal.Balaban.SuTwoInner.inner_RMap (γ b.1) ((WithLp.ofLp x) b) ((WithLp.ofLp x) b)
  have e : (WithLp.ofLp (adBL γ x)) b = RMap (γ b.1) ((WithLp.ofLp x) b) := rfl
  rw [e]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  have h1 := norm_nonneg (RMap (γ b.1) ((WithLp.ofLp x) b))
  have h2 := norm_nonneg ((WithLp.ofLp x) b)
  nlinarith [sq_nonneg (‖RMap (γ b.1) ((WithLp.ofLp x) b)‖ - ‖(WithLp.ofLp x) b‖),
    sq_nonneg (‖RMap (γ b.1) ((WithLp.ofLp x) b)‖ + ‖(WithLp.ofLp x) b‖)]

theorem ne_zero_adBL_iff (γ : GaugeFn L) (x : BondFnL2 L) (b : Bond L) :
    (WithLp.ofLp (adBL γ x)) b ≠ 0 ↔ (WithLp.ofLp x) b ≠ 0 := by
  rw [← norm_ne_zero_iff, ← norm_ne_zero_iff (a := (WithLp.ofLp x) b), norm_adBL_apply]

theorem wnormSq_adBL {ell k : ℕ} (S : Tower L) (γ : GaugeFn L) (x : BondFnL2 L) :
    AdalyFormal.M1.wnormSq S ell k (adBL γ x) = AdalyFormal.M1.wnormSq S ell k x := by
  unfold AdalyFormal.M1.wnormSq
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [norm_adBL_apply]

end gen

section params
variable {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell) (S : Tower (scaleUp ell k Lu)) (a : ℝ)
  (Lam : Set (PeriodicLatticeSite Lu))

theorem baseEqv_gparams (U : LinkCfg (scaleUp ell k Lu)) (γ : GaugeFn (scaleUp ell k Lu)) :
    BaseEqv (adEL γ (gparams ell k Lu hell S U a Lam).G) (adSL γ) (adFL γ (gparams ell k Lu hell S U a Lam).G)
      (gparams ell k Lu hell S U a Lam).data (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam).data :=
  (genFormHyps_gauge (gparams ell k Lu hell S U a Lam) γ).data

theorem ginv_gauge (U : LinkCfg (scaleUp ell k Lu)) (γ : GaugeFn (scaleUp ell k Lu))
    (A : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G)) :
    ⟪adEL γ (gparams ell k Lu hell S U a Lam).G A,
        (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam).data.Ginv
          (adEL γ (gparams ell k Lu hell S U a Lam).G A)⟫
      = ⟪A, (gparams ell k Lu hell S U a Lam).data.Ginv A⟫ := by
  have h2 : (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam).data.Ginv
        (adEL γ (gparams ell k Lu hell S U a Lam).G A)
      = adEL γ (gparams ell k Lu hell S U a Lam).G ((gparams ell k Lu hell S U a Lam).data.Ginv A) :=
    (baseEqv_gparams hell S a Lam U γ).Ginv A
  rw [h2, LinearIsometryEquiv.inner_map_map]

theorem wnormSq_adEL (U : LinkCfg (scaleUp ell k Lu)) (γ : GaugeFn (scaleUp ell k Lu))
    (A : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G)) :
    AdalyFormal.M1.wnormSq S ell k
        ((adEL γ (gparams ell k Lu hell S U a Lam).G A : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G))
          : BondFnL2 (scaleUp ell k Lu))
      = AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu)) := by
  rw [adEL_coe]
  exact wnormSq_adBL S γ _

/-- **W4 transfer**: a stratum-weighted coercivity bound at `U^γ` is the same bound at `U`. -/
theorem coercive_of_gauge (U : LinkCfg (scaleUp ell k Lu)) (γ : GaugeFn (scaleUp ell k Lu)) (c : ℝ)
    (h : ∀ A' : ↥(bondSupp (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam).G),
      c * AdalyFormal.M1.wnormSq S ell k (A' : BondFnL2 (scaleUp ell k Lu))
        ≤ ⟪A', (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam).data.Ginv A'⟫)
    (A : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G)) :
    c * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))
      ≤ ⟪A, (gparams ell k Lu hell S U a Lam).data.Ginv A⟫ := by
  have h1 := h (adEL γ (gparams ell k Lu hell S U a Lam).G A)
  rw [wnormSq_adEL hell S a Lam U γ A] at h1
  rw [← ginv_gauge hell S a Lam U γ A]
  exact h1

/-- the quadratic form of `Δ⁽²⁾` is gauge invariant. -/
theorem delta2_gauge (U : LinkCfg (scaleUp ell k Lu)) (γ : GaugeFn (scaleUp ell k Lu))
    (A : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G)) :
    ⟪adEL γ (gparams ell k Lu hell S U a Lam).G A,
        (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam).data.Delta2
          (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam).data_laws
          (adEL γ (gparams ell k Lu hell S U a Lam).G A)⟫
      = ⟪A, (gparams ell k Lu hell S U a Lam).data.Delta2 (gparams ell k Lu hell S U a Lam).data_laws A⟫ := by
  have hB := baseEqv_gparams hell S a Lam U γ
  rw [((gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam).data.Delta2_spec
      (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam).data_laws).2,
    ((gparams ell k Lu hell S U a Lam).data.Delta2_spec (gparams ell k Lu hell S U a Lam).data_laws).2]
  have hC : (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam).data.C2
        (adEL γ (gparams ell k Lu hell S U a Lam).G A)
      = adFL γ (gparams ell k Lu hell S U a Lam).G ((gparams ell k Lu hell S U a Lam).data.C2 A) := hB.C2 A
  rw [hC, hB.H, hB.J, LinearIsometryEquiv.inner_map_map]

/-- **stratified D-layer bound transfer** (`hD2` of W5): the bound at `U` gives it at `U^γ`. -/
theorem dlayer_form_gauge (U : LinkCfg (scaleUp ell k Lu)) (γ : GaugeFn (scaleUp ell k Lu)) (ε : ℝ)
    (hD2 : ∀ A : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G),
      |⟪A, (gparams ell k Lu hell S U a Lam).data.Delta2 (gparams ell k Lu hell S U a Lam).data_laws A⟫|
        ≤ ε * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu)))
    (A' : ↥(bondSupp (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam).G)) :
    |⟪A', (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam).data.Delta2
        (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam).data_laws A'⟫|
      ≤ ε * AdalyFormal.M1.wnormSq S ell k (A' : BondFnL2 (scaleUp ell k Lu)) := by
  set A : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G) :=
    (adEL γ (gparams ell k Lu hell S U a Lam).G).symm A' with hA
  have hA' : A' = adEL γ (gparams ell k Lu hell S U a Lam).G A := by
    rw [hA, LinearIsometryEquiv.apply_symm_apply]
  rw [hA', delta2_gauge hell S a Lam U γ A, wnormSq_adEL hell S a Lam U γ A]
  exact hD2 A

theorem qs_injective_gauge_iff (U : LinkCfg (scaleUp ell k Lu)) (γ : GaugeFn (scaleUp ell k Lu)) :
    Function.Injective (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam).data.Qs
      ↔ Function.Injective (gparams ell k Lu hell S U a Lam).data.Qs := by
  have hB := baseEqv_gparams hell S a Lam U γ
  have hQ : ∀ f, (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam).data.Qs
      (adFL γ (gparams ell k Lu hell S U a Lam).G f)
        = adEL γ (gparams ell k Lu hell S U a Lam).G ((gparams ell k Lu hell S U a Lam).data.Qs f) := hB.Qs
  constructor
  · intro hi f1 f2 he
    have := hi (a₁ := adFL γ (gparams ell k Lu hell S U a Lam).G f1)
      (a₂ := adFL γ (gparams ell k Lu hell S U a Lam).G f2) (by rw [hQ, hQ, he])
    exact (adFL γ (gparams ell k Lu hell S U a Lam).G).injective this
  · intro hi f1 f2 he
    obtain ⟨g1, rfl⟩ := (adFL γ (gparams ell k Lu hell S U a Lam).G).surjective f1
    obtain ⟨g2, rfl⟩ := (adFL γ (gparams ell k Lu hell S U a Lam).G).surjective f2
    rw [hQ, hQ] at he
    rw [hi ((adEL γ (gparams ell k Lu hell S U a Lam).G).injective he)]

/-- **W5 transfer**: `GenP.WellDef` is gauge invariant. -/
theorem wellDef_gauge_iff (U : LinkCfg (scaleUp ell k Lu)) (γ : GaugeFn (scaleUp ell k Lu)) :
    GenP.WellDef (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam)
      ↔ GenP.WellDef (gparams ell k Lu hell S U a Lam) := by
  have hF := genFormHyps_gauge (gparams ell k Lu hell S U a Lam) γ
  have hQ := fun B c => Q1_gauge_pt (gparams ell k Lu hell S U a Lam) γ B c
  have hb := H0_bijective_iff (Lam := Lam) hQ
  have hG : IsUnit (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam).G1inv
      ↔ IsUnit (gparams ell k Lu hell S U a Lam).G1inv :=
    isUnit_intertwine (adEL γ (gparams ell k Lu hell S U a Lam).G)
      (fun x => hF.data.G1inv (gparams ell k Lu hell S U a Lam).G1inv_spec
        (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam).G1inv_spec x)
  have hN : IsUnit (GenP.Nmat (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam))
      ↔ IsUnit (GenP.Nmat (gparams ell k Lu hell S U a Lam)) :=
    isUnit_intertwine (adFL γ (gparams ell k Lu hell S U a Lam).G) (fun f => hF.Nmat f)
  unfold GenP.WellDef
  exact and_congr hb (and_congr hG hN)

theorem hb_gauge_iff (U : LinkCfg (scaleUp ell k Lu)) (γ : GaugeFn (scaleUp ell k Lu)) :
    Function.Bijective (H0 (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam).Lam
        (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam).Q1)
      ↔ Function.Bijective (H0 (gparams ell k Lu hell S U a Lam).Lam (gparams ell k Lu hell S U a Lam).Q1) :=
  H0_bijective_iff (Lam := Lam) (fun B c => Q1_gauge_pt (gparams ell k Lu hell S U a Lam) γ B c)

/-- **`PatchCoercive` transfer** (lane E's W3 interface): at `U` gives the same statement at `U^γ`. -/
theorem patchCoercive_gauge {M κ c : ℕ} (U : LinkCfg (scaleUp ell k Lu)) (γ : GaugeFn (scaleUp ell k Lu)) (cP : ℝ)
    (hP : AdalyFormal.M1IMS.PatchCoercive ell M k κ c Lu hell S U a Lam cP) :
    AdalyFormal.M1IMS.PatchCoercive ell M k κ c Lu hell S (periodicGaugeTransform γ U) a Lam cP := by
  intro j w hw A' hsupp
  set A : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G) :=
    (adEL γ (gparams ell k Lu hell S U a Lam).G).symm A' with hA
  have hA' : A' = adEL γ (gparams ell k Lu hell S U a Lam).G A := by
    rw [hA, LinearIsometryEquiv.apply_symm_apply]
  have hs : ∀ b : Bond (scaleUp ell k Lu), (WithLp.ofLp (A : BondFnL2 (scaleUp ell k Lu))) b ≠ 0 →
      b.1 ∈ AdalyFormal.M1.patch ell M κ c j w ∨
        periodicLatticeShift b.1 b.2 ∈ AdalyFormal.M1.patch ell M κ c j w := by
    intro b hb
    apply hsupp b
    rw [hA', adEL_coe, ne_zero_adBL_iff]
    exact hb
  have h1 := hP j w hw A hs
  unfold AdalyFormal.M1IMS.wN AdalyFormal.M1IMS.ginvForm at h1 ⊢
  rw [hA', wnormSq_adEL hell S a Lam U γ A, ginv_gauge hell S a Lam U γ A]
  exact h1

end params

end AdalyFormal.M1GaugeW4

#print axioms AdalyFormal.M1GaugeW4.norm_adBL_apply
#print axioms AdalyFormal.M1GaugeW4.ne_zero_adBL_iff
#print axioms AdalyFormal.M1GaugeW4.wnormSq_adBL
#print axioms AdalyFormal.M1GaugeW4.baseEqv_gparams
#print axioms AdalyFormal.M1GaugeW4.ginv_gauge
#print axioms AdalyFormal.M1GaugeW4.wnormSq_adEL
#print axioms AdalyFormal.M1GaugeW4.coercive_of_gauge
#print axioms AdalyFormal.M1GaugeW4.delta2_gauge
#print axioms AdalyFormal.M1GaugeW4.dlayer_form_gauge
#print axioms AdalyFormal.M1GaugeW4.qs_injective_gauge_iff
#print axioms AdalyFormal.M1GaugeW4.wellDef_gauge_iff
#print axioms AdalyFormal.M1GaugeW4.hb_gauge_iff
#print axioms AdalyFormal.M1GaugeW4.patchCoercive_gauge
