
/-!
Round 8: sign-free separation.

The carrier guard asks only that the all-plaquette carrier A be a UNIT; it does
not ask that A be positive semidefinite.  Along the exterior twist the carrier
passes its first crossing and stays an indefinite unit until the next one,
and every such angle is in the class.  Consequently the sign of the correction
on the crossing kernel is irrelevant for separation: a positive pairing makes
A-D singular before the crossing (where A is PSD), a negative pairing makes
A-D singular after it (where A is an indefinite unit).  The round-5 bridge
needed the positive sign; the premises below need neither sign.

Nothing here proves a pinned goal.  The family premises are explicit,
unproved hypotheses; the abstract lemmas are finite-dimensional facts.
-/
namespace AdalyFormal.Round8.Guarded.SignFree

open scoped RealInnerProductSpace
open Set
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.D1Literal (PSD)

section Abstract
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- Sign-free separation.  If the carrier path stays a unit on `[t₀,t₁]` while
the corrected path goes from PSD to having a negative direction, some angle in
`[t₀,t₁)` has a unit carrier and a non-unit corrected carrier.  The carrier may
be indefinite on the whole interval. -/
theorem separation_of_sign_change
    (A : ℝ → E →L[ℝ] E) (D : E →L[ℝ] E) (hc : Continuous A)
    (hsA : ∀ t x y, ⟪A t x, y⟫ = ⟪x, A t y⟫)
    (hsD : ∀ x y, ⟪D x, y⟫ = ⟪x, D y⟫)
    (t₀ t₁ : ℝ) (h01 : t₀ ≤ t₁)
    (hguard : ∀ t, t₀ ≤ t → t ≤ t₁ → IsUnit (A t))
    (h₀ : PSD (A t₀ - D)) (w : E) (h₁ : ⟪w, (A t₁ - D) w⟫ < 0) :
    ∃ t : ℝ, t₀ ≤ t ∧ t < t₁ ∧ IsUnit (A t) ∧ ¬ IsUnit (A t - D) := by
  have hlt : t₀ < t₁ := by
    rcases h01.lt_or_eq with h | h
    · exact h
    · exfalso
      have := h₀ w
      rw [h] at this
      linarith
  let F : ℝ → E →L[ℝ] E := fun s => A (t₀ + s) - D
  have hFc : Continuous F :=
    (hc.comp (continuous_const.add continuous_id)).sub continuous_const
  have hFs : ∀ s x y, ⟪F s x, y⟫ = ⟪x, F s y⟫ := by
    intro s x y
    simp only [F, sub_apply, inner_sub_left, inner_sub_right, hsA, hsD]
  have hF0 : PSD (F 0) := by
    intro v
    simpa [F] using h₀ v
  have hFT : ⟪w, F (t₁ - t₀) w⟫ < 0 := by
    simpa [F] using h₁
  obtain ⟨s, hs0, hsT, hnu⟩ := AdalyFormal.D1Literal.exists_nonunit_path F hFc hFs hF0
    (t₁ - t₀) (by linarith) w hFT
  refine ⟨t₀ + s, by linarith, by linarith, hguard _ (by linarith) (by linarith), ?_⟩
  simpa [F] using hnu

omit [FiniteDimensional ℝ E] in
/-- The round-5 positive-kernel data produce a sign-change interval, so the
sign-free premise is implied by the old one (it is weaker, not stronger). -/
theorem sign_change_of_kernel_positive
    (A : ℝ → E →L[ℝ] E) (D : E →L[ℝ] E) (hc : Continuous A)
    (T : ℝ) (hT : 0 < T)
    (hguard : ∀ t, 0 ≤ t → t < T → IsUnit (A t))
    (v : E) (hker : A T v = 0) (hpositive : 0 < ⟪v, D v⟫) :
    ∃ t₁ : ℝ, 0 ≤ t₁ ∧ t₁ < T ∧ (∀ t, 0 ≤ t → t ≤ t₁ → IsUnit (A t)) ∧
      ⟪v, (A t₁ - D) v⟫ < 0 := by
  let f : ℝ → ℝ := fun t => ⟪v, (A t - D) v⟫
  have hf : Continuous f := by
    have : Continuous fun t => (A t - D) v :=
      (hc.sub continuous_const).clm_apply continuous_const
    exact continuous_const.inner this
  have hfT : f T < 0 := by
    simp only [f, sub_apply, hker, zero_sub, inner_neg_right]
    linarith
  have hev : ∀ᶠ t in nhds T, f t < 0 :=
    Filter.Tendsto.eventually (hf.tendsto T) (gt_mem_nhds hfT)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  let t₁ : ℝ := max 0 (T - δ/2)
  have ht₁0 : 0 ≤ t₁ := le_max_left _ _
  have ht₁T : t₁ < T := max_lt hT (by linarith)
  have hdist : dist t₁ T < δ := by
    rw [Real.dist_eq, abs_lt]
    constructor
    · have : T - δ/2 ≤ t₁ := le_max_right _ _
      linarith
    · linarith
  refine ⟨t₁, ht₁0, ht₁T, fun t ht0 ht1 => hguard t ht0 (lt_of_le_of_lt ht1 ht₁T), ?_⟩
  exact hball hdist

omit [FiniteDimensional ℝ E] in
/-- In the post-crossing regime the separating interval starts at an
INDEFINITE carrier unit, and the correction is negative on the witness. -/
theorem post_crossing_witness (X D : E →L[ℝ] E) (h₀ : PSD (X - D))
    (x : E) (hx : ⟪x, X x⟫ < 0) : ¬ PSD X ∧ ⟪x, D x⟫ < 0 := by
  refine ⟨fun hp => (not_lt_of_ge (hp x)) hx, ?_⟩
  have := h₀ x
  simp only [sub_apply, inner_sub_right] at this
  linarith

#print axioms separation_of_sign_change
#print axioms sign_change_of_kernel_positive
#print axioms post_crossing_witness

end Abstract

/-! Certificates for the interval guard.  On the post-crossing interval the
carrier is indefinite, so positivity cannot certify the guard.  A symmetric
operator that is negative definite on one subspace and positive definite on
another of complementary dimension is a unit (no spectral theorem needed), and
along the exterior sine/cosine pencil the rescaled carrier `A t / sin t` is
Loewner-nonincreasing on `(0, pi/2]` once its constant and cosine parts are
PSD.  Together these reduce the interval guard to two endpoint certificates. -/
section Certificates
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

theorem unit_of_definite_complements (X : E →L[ℝ] E)
    (hs : ∀ x y, ⟪X x, y⟫ = ⟪x, X y⟫) (U V : Submodule ℝ E)
    (hU : ∀ x ∈ U, x ≠ 0 → ⟪x, X x⟫ < 0)
    (hV : ∀ x ∈ V, x ≠ 0 → 0 < ⟪x, X x⟫)
    (hdim : Module.finrank ℝ E ≤ Module.finrank ℝ U + Module.finrank ℝ V) :
    IsUnit X := by
  have hinj : Function.Injective X := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    have hxU : x ∉ U := by
      intro hm
      have h := hU x hm hx0
      rw [hx, inner_zero_right] at h
      exact lt_irrefl 0 h
    let U' : Submodule ℝ E := U ⊔ Submodule.span ℝ {x}
    have hneg : ∀ y ∈ U', ⟪y, X y⟫ ≤ 0 := by
      intro y hy
      obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.mp hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
      have hcross : ⟪c • x, X u⟫ = 0 := by
        rw [real_inner_smul_left, ← hs x u, hx, inner_zero_left, mul_zero]
      have heq : ⟪u + c • x, X (u + c • x)⟫ = ⟪u, X u⟫ := by
        rw [map_add, map_smul, hx, smul_zero, add_zero, inner_add_left, hcross, add_zero]
      rw [heq]
      by_cases hu0 : u = 0
      · rw [hu0, map_zero, inner_zero_right]
      · exact (hU u hu hu0).le
    have hlt : U < U' := SetLike.lt_iff_le_and_exists.mpr
      ⟨le_sup_left, x, Submodule.mem_sup_right (Submodule.mem_span_singleton_self x), hxU⟩
    have hrk : Module.finrank ℝ U < Module.finrank ℝ U' := Submodule.finrank_lt_finrank_of_lt hlt
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq U' V
    have hle : Module.finrank ℝ ↥(U' ⊔ V) ≤ Module.finrank ℝ E := Submodule.finrank_le _
    have hpos : Module.finrank ℝ ↥(U' ⊓ V) ≠ 0 := by omega
    have hne : U' ⊓ V ≠ ⊥ := fun h => hpos (Submodule.finrank_eq_zero.mpr h)
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have h1 := hneg y (Submodule.mem_inf.mp hy).1
    have h2 := hV y (Submodule.mem_inf.mp hy).2 hy0
    linarith
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hinj, (LinearMap.injective_iff_surjective (f := (X : E →ₗ[ℝ] E))).mp hinj⟩

/-- A positively rescaled Loewner-nonincreasing path: a negative-definite
subspace at the left end and a positive-definite subspace at the right end,
of complementary dimension, certify a unit at every intermediate point. -/
theorem units_of_scaled_certificates (A : ℝ → E →L[ℝ] E) (g : ℝ → ℝ)
    (hs : ∀ t x y, ⟪A t x, y⟫ = ⟪x, A t y⟫) (t₀ t₁ : ℝ)
    (hg : ∀ t, t₀ ≤ t → t ≤ t₁ → 0 < g t)
    (hmono : ∀ s t, t₀ ≤ s → s ≤ t → t ≤ t₁ → ∀ x, ⟪x, A t x⟫ / g t ≤ ⟪x, A s x⟫ / g s)
    (U V : Submodule ℝ E)
    (hU : ∀ x ∈ U, x ≠ 0 → ⟪x, A t₀ x⟫ < 0)
    (hV : ∀ x ∈ V, x ≠ 0 → 0 < ⟪x, A t₁ x⟫)
    (hdim : Module.finrank ℝ E ≤ Module.finrank ℝ U + Module.finrank ℝ V) :
    ∀ t, t₀ ≤ t → t ≤ t₁ → IsUnit (A t) := by
  intro t ht0 ht1
  have h01 : t₀ ≤ t₁ := le_trans ht0 ht1
  have hgt := hg t ht0 ht1
  refine unit_of_definite_complements (A t) (hs t) U V ?_ ?_ hdim
  · intro x hx hx0
    have hn : ⟪x, A t₀ x⟫ / g t₀ < 0 := div_neg_of_neg_of_pos (hU x hx hx0) (hg t₀ le_rfl h01)
    have hq : ⟪x, A t x⟫ / g t < 0 := lt_of_le_of_lt (hmono t₀ t le_rfl ht0 ht1 x) hn
    have := mul_neg_of_neg_of_pos hq hgt
    rwa [div_mul_cancel₀ _ hgt.ne'] at this
  · intro x hx hx0
    have hp : 0 < ⟪x, A t₁ x⟫ / g t₁ := div_pos (hV x hx hx0) (hg t₁ h01 le_rfl)
    have hq : 0 < ⟪x, A t x⟫ / g t := lt_of_lt_of_le hp (hmono t t₁ ht0 ht1 le_rfl x)
    have := mul_pos hq hgt
    rwa [div_mul_cancel₀ _ hgt.ne'] at this

omit [FiniteDimensional ℝ E] in
/-- The exterior sine/cosine pencil, rescaled by `1/sin`, is nonincreasing on
`(0, pi/2]` when its constant part and its cosine part are PSD.  The sine part
is arbitrary (it is indefinite along the twist). -/
theorem pencil_rescaled_antitone (B Θ₀ Θ₁ : E →L[ℝ] E) (hB : PSD B) (hΘ : PSD Θ₀)
    {s t : ℝ} (hs0 : 0 < s) (hst : s ≤ t) (htπ : t ≤ Real.pi/2) (x : E) :
    ⟪x, (B + Real.cos t • Θ₀ + Real.sin t • Θ₁) x⟫ / Real.sin t ≤
      ⟪x, (B + Real.cos s • Θ₀ + Real.sin s • Θ₁) x⟫ / Real.sin s := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsin_s : 0 < Real.sin s := Real.sin_pos_of_pos_of_lt_pi hs0 (by linarith)
  have hsin_t : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hsin_le : Real.sin s ≤ Real.sin t :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) htπ hst
  have hcos_le : Real.cos t ≤ Real.cos s :=
    Real.cos_le_cos_of_nonneg_of_le_pi hs0.le (by linarith) hst
  have hcos_t : 0 ≤ Real.cos t := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) htπ
  have hb := hB x
  have hθ := hΘ x
  have expand : ∀ r : ℝ, ⟪x, (B + Real.cos r • Θ₀ + Real.sin r • Θ₁) x⟫ =
      ⟪x, B x⟫ + Real.cos r * ⟪x, Θ₀ x⟫ + Real.sin r * ⟪x, Θ₁ x⟫ := by
    intro r
    simp only [add_apply, smul_apply, inner_add_right,
      real_inner_smul_right]
  rw [expand t, expand s, div_le_div_iff₀ hsin_t hsin_s]
  have h1 : ⟪x, B x⟫ * Real.sin s ≤ ⟪x, B x⟫ * Real.sin t := mul_le_mul_of_nonneg_left hsin_le hb
  have h2 : Real.cos t * Real.sin s ≤ Real.cos s * Real.sin t :=
    mul_le_mul hcos_le hsin_le hsin_s.le (le_trans hcos_t hcos_le)
  have h3 := mul_le_mul_of_nonneg_left h2 hθ
  nlinarith [h1, h3]

/-- Pencil form plus two endpoint certificates give the whole interval guard. -/
theorem pencil_units_of_certificates (A : ℝ → E →L[ℝ] E) (B Θ₀ Θ₁ : E →L[ℝ] E)
    (hA : ∀ t, A t = B + Real.cos t • Θ₀ + Real.sin t • Θ₁)
    (hs : ∀ t x y, ⟪A t x, y⟫ = ⟪x, A t y⟫)
    (hB : PSD B) (hΘ : PSD Θ₀) (t₀ t₁ : ℝ) (h0 : 0 < t₀) (h1 : t₁ ≤ Real.pi/2)
    (U V : Submodule ℝ E)
    (hU : ∀ x ∈ U, x ≠ 0 → ⟪x, A t₀ x⟫ < 0)
    (hV : ∀ x ∈ V, x ≠ 0 → 0 < ⟪x, A t₁ x⟫)
    (hdim : Module.finrank ℝ E ≤ Module.finrank ℝ U + Module.finrank ℝ V) :
    ∀ t, t₀ ≤ t → t ≤ t₁ → IsUnit (A t) := by
  refine units_of_scaled_certificates A Real.sin hs t₀ t₁ ?_ ?_ U V hU hV hdim
  · intro t ht0 ht1
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  · intro s t hs0 hst ht1 x
    rw [hA s, hA t]
    exact pencil_rescaled_antitone B Θ₀ Θ₁ hB hΘ (by linarith) hst (le_trans ht1 h1) x

#print axioms unit_of_definite_complements
#print axioms units_of_scaled_certificates
#print axioms pencil_rescaled_antitone
#print axioms pencil_units_of_certificates

end Certificates

/-- The weakest premise along the actual curved twist family (mass a = 1):
some exterior angle has a unit carrier and a non-unit corrected carrier. -/
def TwistSeparation (q R : ℕ) (ε : ℝ) : Prop :=
  ∃ t : ℝ, IsUnit (twistA q R ε 1 t) ∧ ¬ IsUnit (twistA q R ε 1 t - twistD q R ε 1 t)

/-- Sign-free spectral premise on the actual curved family.  It asks for an
interval of carrier units on which the corrected form passes from PSD to a
negative direction.  No sign of the kernel correction and no positivity of the
carrier on the interval is required.  This proposition is NOT proved here. -/
def SignChangeControl (q R : ℕ) (ε : ℝ) : Prop :=
  ∃ t₀ t₁ : ℝ, t₀ ≤ t₁ ∧
    (∀ t, t₀ ≤ t → t ≤ t₁ → IsUnit (twistA q R ε 1 t)) ∧
    PSD (twistA q R ε 1 t₀ - twistD q R ε 1 0) ∧
    ∃ w : ↥(bondSupp (geomOf 2 1 (dilTower q R))),
      ⟪w, (twistA q R ε 1 t₁ - twistD q R ε 1 0) w⟫ < 0

theorem twistSeparation_of_signChange {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {ε : ℝ} (h : SignChangeControl q R ε) :
    TwistSeparation q R ε := by
  obtain ⟨t₀, t₁, h01, hguard, h₀, w, h₁⟩ := h
  have hsA : ∀ t x y, ⟪twistA q R ε 1 t x, y⟫ = ⟪x, twistA q R ε 1 t y⟫ := by
    intro t x y
    exact (dataS selAll selAll (twistP q R ε 1 t)).Ginv_symm (dataS_laws selAll selAll _) x y
  have hsD : ∀ x y, ⟪twistD q R ε 1 0 x, y⟫ = ⟪x, twistD q R ε 1 0 y⟫ := by
    intro x y
    exact ((dataS selIn selIn (twistP q R ε 1 0)).Delta2_spec (dataS_laws selIn selIn _)).1 x y
  obtain ⟨t, -, -, hu, hnu⟩ := separation_of_sign_change (twistA q R ε 1) (twistD q R ε 1 0)
    (twistA_continuous hq hR hroom ε 1) hsA hsD t₀ t₁ h01 hguard h₀ w h₁
  refine ⟨t, hu, ?_⟩
  rwa [twistD_constant hq hR hroom ε 1 t]

/-- The round-5 kernel premise implies the sign-free premise. -/
theorem signChange_of_kernelPositiveCrossing {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {ε : ℝ} (h : KernelPositiveCrossing q R ε) :
    SignChangeControl q R ε := by
  obtain ⟨h0, T, hT, hguard, v, hker, hpos⟩ := h
  obtain ⟨t₁, ht₁0, _, hg, hneg⟩ := sign_change_of_kernel_positive (twistA q R ε 1)
    (twistD q R ε 1 0) (twistA_continuous hq hR hroom ε 1) T hT hguard v hker hpos
  exact ⟨0, t₁, ht₁0, fun t ht0 ht1 => hg t ht0 ht1, h0, v, hneg⟩

theorem signChange_of_initialKernelControl {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {ε : ℝ} (h : InitialKernelControl q R ε) :
    SignChangeControl q R ε :=
  signChange_of_kernelPositiveCrossing hq hR hroom
    (kernelPositiveCrossing_of_endpoint_signs hq hR hroom
      (endpoint_control_of_initial_kernel hq hR hroom h))

/-- Cofinal bookkeeping with the weakest family premise.  Same witnesses as
the round-5 bridge: m = m₀+1, q = 2^m₀, R = 2(R₀+18) chosen BEFORE the cap,
then ε below min(a₀/(3840 q), 1) and α = 160 ε. -/
theorem goalNeg2_of_twist_separation
    (hsep : ∀ q : ℕ, 0 < q → ∀ R : ℕ, 2 ∣ R → 18 ≤ R →
      ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ TwistSeparation q R ε) :
    GoalNeg2 := by
  apply cofinalPencilFailure_implies_goalNeg2
  refine ⟨2, by norm_num, 1, by norm_num, ?_⟩
  intro m₀
  refine ⟨m₀+1, by omega, by omega, ?_⟩
  intro R₀
  let R := 2*(R₀+18)
  let q := 2^m₀
  have hq : 0 < q := by dsimp [q]; positivity
  have hpow : 2^(m₀+1) = 2*q := by dsimp [q]; rw [pow_succ]; omega
  have hR : 2 ∣ R := ⟨R₀+18, rfl⟩
  have hR18 : 18 ≤ R := by dsimp [R]; omega
  refine ⟨R, by dsimp [R]; omega, ?_⟩
  intro a₀ ha₀
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  let δ : ℝ := min (a₀/(3840*q)) 1
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨ε, hε0, hεδ, t, hu, hnu⟩ := hsep q hq R hR hR18 δ hδ
  let α : ℝ := 160*ε
  have hα : 0 < α := by dsimp [α]; positivity
  have hcap : (12 : ℝ)*(2*q : ℕ)*α ≤ a₀ := by
    have he : ε < a₀/(3840*q) := lt_of_lt_of_le hεδ (min_le_left _ _)
    have hh := (lt_div_iff₀ (by positivity : (0 : ℝ) < 3840*q)).mp he
    dsimp [α]; push_cast; nlinarith
  have heps : |ε| ≤ α/80 := by rw [abs_of_pos hε0]; dsimp [α]; linarith
  have hclass : ClassCoupled 2 (2*q) 12 1 (dilTower q R) α ((2 : ℝ)^1)⁻¹
      (twistU q R ε t) :=
    ⟨dil_coverage hq hR (by omega), dil_regular hq hR hα heps _⟩
  obtain ⟨hBt1, hBt2, hE⟩ := dil_competitor hq hR
  rw [hpow]
  exact ⟨1, by norm_num, dilLu q R, α, hα, hcap, dil_torus hq R,
    dilTower q R, dil_admissible hq hR, dilLam q R, dil_lambda hq hR,
    twistU q R ε t, hclass, dilBt hq R, hBt1, hBt2, hE, hu, hnu⟩

theorem goalNeg1_of_twist_separation
    (hsep : ∀ q : ℕ, 0 < q → ∀ R : ℕ, 2 ∣ R → 18 ≤ R →
      ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ TwistSeparation q R ε) :
    GoalNeg1 :=
  goalNeg1_iff_goalNeg2.mpr (goalNeg2_of_twist_separation hsep)

/-- Sign-free cofinal bridge.  Its premise is weaker than the round-5
`InitialKernelControl` premise (`signChange_of_initialKernelControl`), and it
is also met in the negative-sign (post-crossing) regime.  It is NOT proved. -/
theorem goalNeg2_of_sign_change_control
    (hcontrol : ∀ q : ℕ, 0 < q → ∀ R : ℕ, 2 ∣ R → 18 ≤ R →
      ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ SignChangeControl q R ε) :
    GoalNeg2 := by
  apply goalNeg2_of_twist_separation
  intro q hq R hR hR18 δ hδ
  obtain ⟨ε, hε, hεδ, hc⟩ := hcontrol q hq R hR hR18 δ hδ
  exact ⟨ε, hε, hεδ, twistSeparation_of_signChange hq hR (by nlinarith) hc⟩

/-- What the positive reading demands of this family.  If `GoalPos1` holds
then, at every large scale and radius and every small enough curvature, NO
exterior angle separates: every crossing of A-D along the twist is a crossing
of A.  This is the contrapositive content of the bridge, stated directly. -/
theorem goalPos1_forces_no_twist_separation (h : GoalPos1) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 2 ∣ R → 18 ≤ R →
      ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → ¬ TwistSeparation (2^(m-1)) R ε := by
  obtain ⟨m₀, hm₀, hm⟩ := h 2 le_rfl 1 one_pos
  refine ⟨m₀, hm₀, fun m hm' => ?_⟩
  obtain ⟨R₀, hR₀⟩ := hm m hm'
  refine ⟨R₀, fun R hR hR2 hR18 => ?_⟩
  obtain ⟨a₀, ha₀, hcpen⟩ := hR₀ R hR
  have hm1 : 1 ≤ m := le_trans hm₀ hm'
  let q := 2^(m-1)
  have hq : 0 < q := by dsimp [q]; positivity
  have hpow : 2^m = 2*q := by
    dsimp [q]
    rw [← pow_succ', Nat.sub_add_cancel hm1]
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  refine ⟨min (a₀/(3840*q)) 1, by positivity, fun ε hε0 hεδ => ?_⟩
  rintro ⟨t, hu, hnu⟩
  let α : ℝ := 160*ε
  have hα : 0 < α := by dsimp [α]; positivity
  have hcap : (12 : ℝ)*((2^m : ℕ) : ℝ)*α ≤ a₀ := by
    have he : ε < a₀/(3840*q) := lt_of_lt_of_le hεδ (min_le_left _ _)
    have hh := (lt_div_iff₀ (by positivity : (0 : ℝ) < 3840*q)).mp he
    rw [hpow]
    dsimp [α]; push_cast; nlinarith
  have heps : |ε| ≤ α/80 := by rw [abs_of_pos hε0]; dsimp [α]; linarith
  obtain ⟨hBt1, hBt2, hE⟩ := dil_competitor hq hR2
  have hT := dil_torus hq R
  have hS := dil_admissible hq hR2
  have hL := dil_lambda hq hR2
  have hcl : ClassCoupled 2 (2*q) 12 1 (dilTower q R) α ((2 : ℝ)^1)⁻¹ (twistU q R ε t) :=
    ⟨dil_coverage hq hR2 (by omega), dil_regular hq hR2 hα heps _⟩
  rw [← hpow] at hT hS hL hcl
  have key := hcpen 1 le_rfl (dilLu q R) α hα hcap hT (dilTower q R) hS (dilLam q R) hL
    (twistU q R ε t) hcl ⟨dilBt hq R, hBt1, hBt2, hE⟩ hu
  exact hnu key

/-- The exterior pencil identity on the actual family, with PSD constant and
cosine parts.  Checked numerically (round-6 path_identity.py at 80 digits;
sepcheck.py, error below 1e-400 at 400 digits) and algebraically derivable
from the plaquette formula; NOT proved here. -/
def TwistPencil (q R : ℕ) (ε : ℝ) : Prop :=
  ∃ B Θ₀ Θ₁ : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))),
    PSD B ∧ PSD Θ₀ ∧ ∀ t : ℝ, twistA q R ε 1 t = B + Real.cos t • Θ₀ + Real.sin t • Θ₁

/-- Pointwise data at two angles in `(0, pi/2]` that imply `SignChangeControl`:
the pencil identity, a negative-definite subspace of the carrier at `t₀`, a
positive-definite subspace at `t₁` of complementary dimension, the corrected
form PSD at `t₀` and negative somewhere at `t₁`.  NOT proved here. -/
def PencilCertificates (q R : ℕ) (ε : ℝ) : Prop :=
  TwistPencil q R ε ∧
  ∃ t₀ t₁ : ℝ, 0 < t₀ ∧ t₀ ≤ t₁ ∧ t₁ ≤ Real.pi/2 ∧
    (∃ U V : Submodule ℝ ↥(bondSupp (geomOf 2 1 (dilTower q R))),
      (∀ x ∈ U, x ≠ 0 → ⟪x, twistA q R ε 1 t₀ x⟫ < 0) ∧
      (∀ x ∈ V, x ≠ 0 → 0 < ⟪x, twistA q R ε 1 t₁ x⟫) ∧
      Module.finrank ℝ ↥(bondSupp (geomOf 2 1 (dilTower q R))) ≤
        Module.finrank ℝ U + Module.finrank ℝ V) ∧
    PSD (twistA q R ε 1 t₀ - twistD q R ε 1 0) ∧
    ∃ w : ↥(bondSupp (geomOf 2 1 (dilTower q R))),
      ⟪w, (twistA q R ε 1 t₁ - twistD q R ε 1 0) w⟫ < 0

theorem signChange_of_pencilCertificates {q R : ℕ} {ε : ℝ} (h : PencilCertificates q R ε) :
    SignChangeControl q R ε := by
  obtain ⟨⟨B, Θ₀, Θ₁, hB, hΘ, hA⟩, t₀, t₁, h0, h01, h1, ⟨U, V, hU, hV, hdim⟩, hC0, w, hw⟩ := h
  have hs : ∀ t x y, ⟪twistA q R ε 1 t x, y⟫ = ⟪x, twistA q R ε 1 t y⟫ := by
    intro t x y
    exact (dataS selAll selAll (twistP q R ε 1 t)).Ginv_symm (dataS_laws selAll selAll _) x y
  exact ⟨t₀, t₁, h01, pencil_units_of_certificates (twistA q R ε 1) B Θ₀ Θ₁ hA hs hB hΘ
    t₀ t₁ h0 h1 U V hU hV hdim, hC0, w, hw⟩

theorem goalNeg2_of_pencil_certificates
    (hcert : ∀ q : ℕ, 0 < q → ∀ R : ℕ, 2 ∣ R → 18 ≤ R →
      ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ PencilCertificates q R ε) :
    GoalNeg2 := by
  apply goalNeg2_of_sign_change_control
  intro q hq R hR hR18 δ hδ
  obtain ⟨ε, hε, hεδ, hc⟩ := hcert q hq R hR hR18 δ hδ
  exact ⟨ε, hε, hεδ, signChange_of_pencilCertificates hc⟩

/-- The weakest cofinal premise on the twist family, matching the pinned
quantifiers: infinitely many dyadic scales `q = 2^j`, for each of them
infinitely many even radii `R ≥ 18` (room condition included), and for each
such pair arbitrarily small curvature with a separating exterior angle.
NOT proved here. -/
def CofinalTwistSeparation : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ TwistSeparation (2^j) R ε

/-- The same with the sign-free interval premise in place of the bare separation. -/
def CofinalSignChange : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ SignChangeControl (2^j) R ε

/-- Main bridge, with the weakest cofinal premise. -/
theorem goalNeg2_of_cofinalTwistSeparation (h : CofinalTwistSeparation) : GoalNeg2 := by
  apply cofinalPencilFailure_implies_goalNeg2
  refine ⟨2, by norm_num, 1, by norm_num, ?_⟩
  intro m₀
  obtain ⟨j, hj, hRs⟩ := h m₀
  refine ⟨j+1, by omega, by omega, ?_⟩
  intro R₀
  obtain ⟨R, hRR, hR, hR18, hsep⟩ := hRs R₀
  refine ⟨R, hRR, ?_⟩
  intro a₀ ha₀
  let q := 2^j
  have hq : 0 < q := by dsimp [q]; positivity
  have hpow : 2^(j+1) = 2*q := by dsimp [q]; rw [pow_succ]; omega
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  let δ : ℝ := min (a₀/(3840*q)) 1
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨ε, hε0, hεδ, t, hu, hnu⟩ := hsep δ hδ
  let α : ℝ := 160*ε
  have hα : 0 < α := by dsimp [α]; positivity
  have hcap : (12 : ℝ)*(2*q : ℕ)*α ≤ a₀ := by
    have he : ε < a₀/(3840*q) := lt_of_lt_of_le hεδ (min_le_left _ _)
    have hh := (lt_div_iff₀ (by positivity : (0 : ℝ) < 3840*q)).mp he
    dsimp [α]; push_cast; nlinarith
  have heps : |ε| ≤ α/80 := by rw [abs_of_pos hε0]; dsimp [α]; linarith
  have hclass : ClassCoupled 2 (2*q) 12 1 (dilTower q R) α ((2 : ℝ)^1)⁻¹
      (twistU q R ε t) :=
    ⟨dil_coverage hq hR (by omega), dil_regular hq hR hα heps _⟩
  obtain ⟨hBt1, hBt2, hE⟩ := dil_competitor hq hR
  rw [hpow]
  exact ⟨1, by norm_num, dilLu q R, α, hα, hcap, dil_torus hq R,
    dilTower q R, dil_admissible hq hR, dilLam q R, dil_lambda hq hR,
    twistU q R ε t, hclass, dilBt hq R, hBt1, hBt2, hE, hu, hnu⟩

/-- Restricted to this family the open question is exactly this proposition:
the positive pinned reading refutes it, and it refutes the positive reading. -/
theorem not_cofinalTwistSeparation_of_goalPos1 (h : GoalPos1) : ¬ CofinalTwistSeparation :=
  fun h' => goalNeg2_of_cofinalTwistSeparation h' (goalPos2_iff_goalPos1.mpr h)

theorem cofinalTwistSeparation_of_cofinalSignChange (h : CofinalSignChange) :
    CofinalTwistSeparation := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hc⟩ := hRs R₀
  refine ⟨R, hRR, hR, hR18, fun δ hδ => ?_⟩
  obtain ⟨ε, hε, hεδ, hs⟩ := hc δ hδ
  have hq : 0 < 2^j := by positivity
  exact ⟨ε, hε, hεδ, twistSeparation_of_signChange hq hR (by nlinarith) hs⟩

theorem goalNeg2_of_cofinalSignChange (h : CofinalSignChange) : GoalNeg2 :=
  goalNeg2_of_cofinalTwistSeparation (cofinalTwistSeparation_of_cofinalSignChange h)

#print axioms TwistSeparation
#print axioms SignChangeControl
#print axioms twistSeparation_of_signChange
#print axioms signChange_of_kernelPositiveCrossing
#print axioms signChange_of_initialKernelControl
#print axioms goalNeg2_of_twist_separation
#print axioms goalNeg1_of_twist_separation
#print axioms goalNeg2_of_sign_change_control
#print axioms goalPos1_forces_no_twist_separation
#print axioms TwistPencil
#print axioms PencilCertificates
#print axioms signChange_of_pencilCertificates
#print axioms goalNeg2_of_pencil_certificates
#print axioms CofinalTwistSeparation
#print axioms CofinalSignChange
#print axioms goalNeg2_of_cofinalTwistSeparation
#print axioms not_cofinalTwistSeparation_of_goalPos1
#print axioms cofinalTwistSeparation_of_cofinalSignChange
#print axioms goalNeg2_of_cofinalSignChange

end AdalyFormal.Round8.Guarded.SignFree
