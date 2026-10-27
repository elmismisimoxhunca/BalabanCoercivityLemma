import CB8
/-!
# CB9 -- per-cube tower class from the (3.35) clauses of ONE class cube (in that cube's gauge)

Hypotheses = the first two clauses of the statement lane's `PerCubeRegular2` for one cube, written
out (same shapes: `B` = `CubeBond sites`, chart `U^g e = exp((η i)•A e)` with `A e` Hermitian
traceless, `‖A e‖ < c1`, `‖η⁻¹(A(x+μ,ν) − A(x,ν))‖ < c2` when both bonds are in the cube).

* `cube_link`, `cube_plaq`: fine link defect `< η c1`, fine plaquette defect
  `≤ 2 η² c2 + (4π+2)(η c1)²` (gauge invariant) on plaquettes with all four bonds in the cube.
* `cube_tower`: for every level `l` and every bond whose dependency cones lie in the cube,
  `dv (Ū^l(U^g) c) ≤ ell^l η c1 + KC ell (ell²)^l (2η²c2 + (4π+2)(η c1)²)`.
* `cube_tower_class`: with the printed scales `c1 = a (ell^j η)⁻¹`, `c2 = a (ell^j η)⁻²`
  (`a = f M α₀`), `a ≤ 1`, `l ≤ j`:
  `dv (Ū^l(U^g) c) ≤ a (1 + (4π+4) KC ell) · ell^l / ell^j`  — the per-cube tower class;
  for `ell ≥ 14` the constant is `≤ 1 + 60(4π+4)` (`KC_le_sixty`), independent of `ell`, `l`, `j`,
  `k` and the volume.

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Log su2Exp)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobSq frobSq_nonneg frobNorm_nonneg)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.BlockedBackground (ubarTowerSU2)
open AdalyFormal.Balaban.ClassPropagationUbar (blkConstOf)
open AdalyFormal.Balaban.Bch2 (IsSu2)
open scoped Matrix

variable {L : PeriodicLatticeExtent}

/-- Hermitian traceless (the statement lane's `HT`). -/
def HTm (X : M2) : Prop := Xᴴ = X ∧ Matrix.trace X = 0

theorem frobNorm_csmul (c : ℂ) (X : M2) : frobNorm (c • X) = ‖c‖ * frobNorm X := by
  unfold frobNorm frobSq
  simp only [Matrix.smul_apply, smul_eq_mul, Complex.normSq_mul]
  rw [show Complex.normSq c * Complex.normSq (X 0 0) + Complex.normSq c * Complex.normSq (X 0 1)
      + Complex.normSq c * Complex.normSq (X 1 0) + Complex.normSq c * Complex.normSq (X 1 1)
      = Complex.normSq c * (Complex.normSq (X 0 0) + Complex.normSq (X 0 1)
      + Complex.normSq (X 1 0) + Complex.normSq (X 1 1)) by ring,
    Real.sqrt_mul (Complex.normSq_nonneg c), Complex.normSq_eq_norm_sq,
    Real.sqrt_sq (norm_nonneg c)]

/-- The chart field `(η i)•A` is in `𝔰𝔲(2)`, its exponential is the tree's `su2Exp`, and its norm is
`η ‖A‖`. -/
theorem chart (η : ℝ) (hη : 0 ≤ η) (A : M2) (hA : HTm A) :
    IsSu2 (((η : ℂ) * Complex.I) • A) ∧
      frobNorm (((η : ℂ) * Complex.I) • A) = η * frobNorm A := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Matrix.conjTranspose_smul, hA.1]
    have : star ((η : ℂ) * Complex.I) = -((η : ℂ) * Complex.I) := by
      simp [Complex.conj_ofReal]
    rw [this, neg_smul]
  · rw [Matrix.trace_smul, hA.2, smul_zero]
  · rw [frobNorm_csmul]
    congr 1
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hη]

theorem chart_exp (X : M2) (hX : IsSu2 X) (g : SU2) (h : (g : M2) = NormedSpace.exp X) :
    g = su2Exp X := by
  apply Subtype.ext
  rw [h, AdalyFormal.Balaban.SuTwoLogExp.su2Exp_of_mem
    (AdalyFormal.Balaban.ClassPropagationUbar.exp_mem_special hX.1 hX.2)]

/-- One cube's data, in the shape of `PerCubeRegular2`'s first two clauses. -/
structure CubeChart (U : PeriodicLinkConfiguration SU2 L) (B : PeriodicLatticeEdge L → Prop)
    (η c1 c2 : ℝ) where
  g : PeriodicLatticeSite L → SU2
  A : PeriodicLatticeEdge L → M2
  hA : ∀ e, B e → HTm (A e) ∧
    ((periodicGaugeTransform g U e : SU2) : M2) = NormedSpace.exp (((η : ℂ) * Complex.I) • A e) ∧
    frobNorm (A e) < c1
  hD : ∀ (μ ν : Fin 3) (x : PeriodicLatticeSite L), B (x, ν) → B (periodicLatticeShift x μ, ν) →
    frobNorm ((η⁻¹ : ℝ) • (A (periodicLatticeShift x μ, ν) - A (x, ν))) < c2

/-- plaquette words with all four bonds in `B` -/
def plaqIn (B : PeriodicLatticeEdge L → Prop) (t : PlaqT L) : Prop :=
  B (t.1, t.2.1) ∧ B (coarseShift t.1 1 t.2.1, t.2.2) ∧ B (coarseShift t.1 1 t.2.2, t.2.1)
    ∧ B (t.1, t.2.2)

theorem cube_link {U : PeriodicLinkConfiguration SU2 L} {B : PeriodicLatticeEdge L → Prop}
    {η c1 c2 : ℝ} (hη : 0 < η) (K : CubeChart U B η c1 c2) (e : PeriodicLatticeEdge L) (he : B e) :
    dv (periodicGaugeTransform K.g U e) ≤ η * c1 := by
  obtain ⟨hHT, hexp, hn⟩ := K.hA e he
  obtain ⟨hX, hXn⟩ := chart η hη.le (K.A e) hHT
  rw [chart_exp _ hX _ hexp]
  refine le_trans (dv_exp_le hX) ?_
  rw [hXn]; exact mul_le_mul_of_nonneg_left hn.le hη.le

theorem diff_chart (η : ℝ) (hη : 0 < η) (A1 A2 : M2) (c2 : ℝ)
    (h : frobNorm ((η⁻¹ : ℝ) • (A1 - A2)) < c2) :
    frobNorm (((η : ℂ) * Complex.I) • A1 - ((η : ℂ) * Complex.I) • A2) ≤ η ^ 2 * c2 := by
  rw [← smul_sub, frobNorm_csmul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hη]
  have hr : frobNorm ((η⁻¹ : ℝ) • (A1 - A2)) = η⁻¹ * frobNorm (A1 - A2) := by
    rw [AdalyFormal.Balaban.Bch2.frobNorm_smul, abs_of_pos (inv_pos.mpr hη)]
  rw [hr] at h
  have h2 : frobNorm (A1 - A2) ≤ η * c2 := by
    have := mul_lt_mul_of_pos_left h hη
    rw [← mul_assoc, mul_inv_cancel₀ hη.ne', one_mul] at this
    exact this.le
  nlinarith [h2, hη]

theorem cube_plaq {U : PeriodicLinkConfiguration SU2 L} {B : PeriodicLatticeEdge L → Prop}
    {η c1 c2 : ℝ} (hη : 0 < η) (K : CubeChart U B η c1 c2) (hsmall : η * c1 ≤ 1)
    (t : PlaqT L) (ht : plaqIn B t) :
    dv (pw 1 (periodicGaugeTransform K.g U) t.1 t.2.1 t.2.2)
      ≤ 2 * (η ^ 2 * c2) + (4 * Real.pi + 2) * (η * c1) ^ 2 := by
  obtain ⟨y, ν, μ⟩ := t
  obtain ⟨b1, b2, b3, b4⟩ := ht
  set X : PeriodicLatticeEdge L → M2 := fun e => ((η : ℂ) * Complex.I) • K.A e
  have hX : ∀ e, B e → IsSu2 (X e) ∧ periodicGaugeTransform K.g U e = su2Exp (X e) ∧
      frobNorm (X e) ≤ η * c1 := by
    intro e he
    obtain ⟨hHT, hexp, hn⟩ := K.hA e he
    obtain ⟨hXs, hXn⟩ := chart η hη.le (K.A e) hHT
    exact ⟨hXs, chart_exp _ hXs _ hexp, by rw [hXn]; exact mul_le_mul_of_nonneg_left hn.le hη.le⟩
  obtain ⟨ia, va, na⟩ := hX _ b1
  obtain ⟨ib, vb, nb⟩ := hX _ b2
  obtain ⟨ic, vc, nc⟩ := hX _ b3
  obtain ⟨ie, ve, ne⟩ := hX _ b4
  have dac : frobNorm (X (y, ν) - X (coarseShift y 1 μ, ν)) ≤ η ^ 2 * c2 := by
    have h := diff_chart η hη _ _ c2 (K.hD μ ν y b1 b3)
    have hs : frobNorm (X (y, ν) - X (coarseShift y 1 μ, ν))
        = frobNorm (X (coarseShift y 1 μ, ν) - X (y, ν)) := by
      rw [← neg_sub, AdalyFormal.Balaban.RegularityGap.frobNorm_neg]
    rw [hs]; exact h
  have dbe : frobNorm (X (coarseShift y 1 ν, μ) - X (y, μ)) ≤ η ^ 2 * c2 :=
    diff_chart η hη _ _ c2 (K.hD ν μ y b4 b2)
  exact dv_pw_of_chart _ y ν μ _ _ _ _ (η * c1) (η ^ 2 * c2) ia ib ic ie va vb vc ve na nb nc ne
    hsmall dac dbe

/-- **Per-cube tower bound** (cube gauge `U^g`). -/
theorem cube_tower (ell : ℕ) (hell : 0 < ell) (hr : blkConstOf ell < (ell : ℝ) ^ 2)
    {U : PeriodicLinkConfiguration SU2 L} {B : PeriodicLatticeEdge L → Prop}
    {η c1 c2 : ℝ} (hη : 0 < η) (K : CubeChart U B η c1 c2) (hsmall : η * c1 ≤ 1)
    (hc2 : 0 ≤ c2) (l : ℕ) (c : PeriodicLatticeEdge L)
    (hB : goodB ell (plaqIn B) l c) (hL : goodL ell B l c) :
    dv (ubarTowerSU2 ell (periodicGaugeTransform K.g U) l c)
      ≤ (ell : ℝ) ^ l * (η * c1)
        + KC ell * ((ell : ℝ) ^ 2) ^ l * (2 * (η ^ 2 * c2) + (4 * Real.pi + 2) * (η * c1) ^ 2) := by
  have hpi := Real.pi_pos
  have hq0 : 0 ≤ 2 * (η ^ 2 * c2) + (4 * Real.pi + 2) * (η * c1) ^ 2 := by positivity
  exact link_tower_loc ell hell hr _ (plaqIn B) B _ _ hq0 (fun t ht => cube_plaq hη K hsmall t ht)
    (fun e he => cube_link hη K e he) l c hB hL

/-- **Per-cube tower class** at the printed scales. -/
theorem cube_tower_class (ell : ℕ) (hell : 0 < ell) (hr : blkConstOf ell < (ell : ℝ) ^ 2)
    {U : PeriodicLinkConfiguration SU2 L} {B : PeriodicLatticeEdge L → Prop} {η a : ℝ} (j : ℕ)
    (hη : 0 < η) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (K : CubeChart U B η (a * (((ell : ℝ) ^ j * η)⁻¹ ^ 1)) (a * (((ell : ℝ) ^ j * η)⁻¹ ^ 2)))
    (l : ℕ) (hlj : l ≤ j) (c : PeriodicLatticeEdge L)
    (hB : goodB ell (plaqIn B) l c) (hL : goodL ell B l c) :
    dv (ubarTowerSU2 ell (periodicGaugeTransform K.g U) l c)
      ≤ a * (1 + (4 * Real.pi + 4) * KC ell) * ((ell : ℝ) ^ l / (ell : ℝ) ^ j) := by
  have hpi := Real.pi_pos
  have hK := KC_nonneg ell hell hr
  have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hPj : 0 < (ell : ℝ) ^ j := by positivity
  have hPl : 0 < (ell : ℝ) ^ l := by positivity
  have hlej : (ell : ℝ) ^ l ≤ (ell : ℝ) ^ j := pow_le_pow_right₀ hellR hlj
  set t : ℝ := (ell : ℝ) ^ l / (ell : ℝ) ^ j
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by rw [div_le_one hPj]; exact hlej
  have e1 : η * (a * (((ell : ℝ) ^ j * η)⁻¹ ^ 1)) = a / (ell : ℝ) ^ j := by
    field_simp
  have e2 : η ^ 2 * (a * (((ell : ℝ) ^ j * η)⁻¹ ^ 2)) = a / ((ell : ℝ) ^ j) ^ 2 := by
    field_simp
  have hsmall : η * (a * (((ell : ℝ) ^ j * η)⁻¹ ^ 1)) ≤ 1 := by
    rw [e1, div_le_one hPj]
    calc a ≤ 1 := ha1
      _ ≤ (ell : ℝ) ^ j := one_le_pow₀ hellR
  have hc2 : 0 ≤ a * (((ell : ℝ) ^ j * η)⁻¹ ^ 2) := by positivity
  have h := cube_tower ell hell hr hη K hsmall hc2 l c hB hL
  rw [e1, e2] at h
  refine le_trans h ?_
  -- ell^l · a/ell^j = a t ;  (ell²)^l (2a/ell^{2j} + (4π+2) a²/ell^{2j}) ≤ (4π+4) a t² ≤ (4π+4) a t
  have hA : (ell : ℝ) ^ l * (a / (ell : ℝ) ^ j) = a * t := by simp only [t]; ring
  have hB2 : ((ell : ℝ) ^ 2) ^ l * (2 * (a / ((ell : ℝ) ^ j) ^ 2)
      + (4 * Real.pi + 2) * (a / (ell : ℝ) ^ j) ^ 2) = t ^ 2 * (2 * a + (4 * Real.pi + 2) * a ^ 2) := by
    simp only [t]; field_simp; ring
  have hq : t ^ 2 * (2 * a + (4 * Real.pi + 2) * a ^ 2) ≤ t * ((4 * Real.pi + 4) * a) := by
    have h1 : a ^ 2 ≤ a := by nlinarith
    have h2 : t ^ 2 ≤ t := by nlinarith
    have h3 : 0 ≤ 2 * a + (4 * Real.pi + 2) * a ^ 2 := by positivity
    calc t ^ 2 * (2 * a + (4 * Real.pi + 2) * a ^ 2)
        ≤ t * (2 * a + (4 * Real.pi + 2) * a ^ 2) := mul_le_mul_of_nonneg_right h2 h3
      _ ≤ t * ((4 * Real.pi + 4) * a) := by
          apply mul_le_mul_of_nonneg_left _ ht0; nlinarith
  rw [hA, mul_assoc (KC ell), hB2]
  have := mul_le_mul_of_nonneg_left hq hK
  nlinarith [this]

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.chart
#print axioms AdalyFormal.CurvBlock.cube_link
#print axioms AdalyFormal.CurvBlock.cube_plaq
#print axioms AdalyFormal.CurvBlock.cube_tower
#print axioms AdalyFormal.CurvBlock.cube_tower_class
