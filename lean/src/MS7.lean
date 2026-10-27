import MS6
import GCb2
import GCa3

/-!
# MS7 -- bridges: admissible towers are `ProperTower`s, `stratG` vs the `Ω_j`-stratum, S1 in any global gauge

* **`properTower_geomOf`** : `Admissible ℓ M R k S`, `0 < ℓ`, `0 < M` ⇒ `ProperTower (geomOf ℓ k S) ℓ k` — so S1–S4 apply to the
  geometry of every admissible tower of the statement (`geomOf`, ZXR2Wire1), with `hdvd_of_admissible : ℓ^k ∣ L_μ + 1`.
* **`stratG_geomOf`** (equivalence target for lane B): `stratG (geomOf ℓ k S) x = sSup {j | j ≤ k ∧ x ∈ S.Om j}` under
  `Admissible` — i.e. the plan's `strat S k x` (PLAN §1.1 sketch) IS this lane's `stratG`.
* **`site_coercive_weighted_gauge`** : S1's conclusion for `U` whenever its hypotheses hold for `γ·U` for SOME site gauge `γ`
  (`DelpA_gauge`, GCb2; `wNormSq` is invariant).
* **`site_coercive_weighted_perblock`** : S1 with a SEPARATE gauge `γ_q` on every constraint block: the blocks partition `Ω₀`, so
  the `γ_q` glue to one `γ`; `hU` reads only in-block links and `hT` (MSal form) only in-block averaged links, whose gauge
  transforms (`bgTower_gauge`, GCa3) involve `γ` only at the two endpoints, both in the block.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1Site

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.StatementLane (Tower Admissible bigSide BlockClosed)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap BondFnL2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)

variable {Lf : PeriodicLatticeExtent}

theorem aligned_eq (n a x : ℕ) (hn : 0 < n) (ha : n ∣ a) (h1 : a ≤ x) (h2 : x < a + n) : a = n * (x / n) := by
  obtain ⟨t, rfl⟩ := ha
  have : x / n = t := Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith)
  rw [this]

theorem hdvd_of_admissible {ell M R k : ℕ} {S : Tower Lf} (hS : Admissible ell M R k S) :
    ∀ μ, ell ^ k ∣ Lf μ + 1 := by
  intro μ
  obtain ⟨-, -, hdv, -⟩ := hS
  exact Dvd.dvd.trans (Dvd.intro_left M rfl) (hdv k le_rfl μ)

/-- a level-`j` block and a deeper level-`j'` block of an admissible tower never meet -/
theorem lower_block_out {ell M R k : ℕ} (hell : 0 < ell) {S : Tower Lf} (hS : Admissible ell M R k S)
    {j j' : ℕ} (hjj : j < j') (hj' : j' ≤ k)
    {y y' : PeriodicLatticeSite Lf} (hy : y ∈ (geomOf ell k S).Lam j) (hy' : y' ∈ (geomOf ell k S).Lam j')
    {x : PeriodicLatticeSite Lf} (hx : x ∈ blockOf y (ell ^ j)) (hx' : x ∈ blockOf y' (ell ^ j')) : False := by
  obtain ⟨hnest, -, -, hblk, -, -⟩ := hS
  obtain ⟨hydiv, hyOm, hyOut⟩ := hy
  obtain ⟨hy'div, hy'Om, -⟩ := hy'
  rw [mem_blockOf] at hx hx'
  -- x ∈ Ω_{j'}
  have hxj' : x ∈ S.Om j' := by
    refine hblk j' hj' y' hy'Om x (fun μ => ?_)
    obtain ⟨h1, h2⟩ := hx' μ
    have := blk_div (ell ^ j') M (y' μ).val (x μ).val (pow_pos hell j') (hy'div μ) h1 h2
    show (x μ).val / (M * ell ^ j') = (y' μ).val / (M * ell ^ j')
    rw [mul_comm M]; exact this.symm
  have hxj1 : x ∈ S.Om (j + 1) := om_antitone S hnest (by omega) hxj'
  -- then y ∈ Ω_{j+1}
  apply hyOut
  refine hblk (j + 1) (by omega) x hxj1 y (fun μ => ?_)
  obtain ⟨h1, h2⟩ := hx μ
  have := blk_div (ell ^ j) (M * ell) (y μ).val (x μ).val (pow_pos hell j) (hydiv μ) h1 h2
  have e : ell ^ j * (M * ell) = bigSide M ell (j + 1) := by unfold bigSide; ring
  rw [e] at this
  exact this

/-- **admissible towers are proper towers** -/
theorem properTower_geomOf {ell M R k : ℕ} (hell : 0 < ell) {S : Tower Lf} (hS : Admissible ell M R k S) :
    ProperTower (geomOf ell k S) ell k where
  ell_eq := rfl
  k_eq := rfl
  coarse := by
    intro j _ y hy
    rw [mem_CoarseLattice]
    intro μ
    exact Nat.mod_eq_zero_of_dvd (hy.1 μ)
  disj := by
    intro j j' hj hj' y hy y' hy' hne
    rw [Finset.disjoint_left]
    intro x hx hx'
    rcases lt_trichotomy j j' with hlt | heq | hgt
    · exact lower_block_out hell hS hlt hj' hy hy' hx hx'
    · subst heq
      have hne' : y ≠ y' := hne.resolve_left (fun h => h rfl)
      apply hne'
      funext μ
      apply Fin.ext
      have hxm := (mem_blockOf.mp hx) μ
      have hxm' := (mem_blockOf.mp hx') μ
      rw [aligned_eq (ell ^ j) _ _ (pow_pos hell j) (hy.1 μ) hxm.1 hxm.2,
        aligned_eq (ell ^ j) _ _ (pow_pos hell j) (hy'.1 μ) hxm'.1 hxm'.2]
    · exact lower_block_out hell hS hgt hj hy' hy hx' hx
  cover := by
    intro x
    have h := omGe_iff_om ell M R k hell S hS 0 x
    constructor
    · intro hx
      obtain ⟨i, -, hik, y, hy, hxy⟩ := h.mpr hx
      exact ⟨i, hik, y, hy, mem_blockOf.mpr hxy⟩
    · rintro ⟨i, hik, y, hy, hxy⟩
      exact h.mp ⟨i, Nat.zero_le i, hik, y, hy, mem_blockOf.mp hxy⟩

/-- **equivalence target for lane B**: the stratum read off the tower sets equals `stratG` of the tower geometry. -/
theorem stratG_geomOf {ell M R k : ℕ} (hell : 0 < ell) {S : Tower Lf} (hS : Admissible ell M R k S)
    (x : PeriodicLatticeSite Lf) :
    stratG (geomOf ell k S) x = sSup {j | j ≤ k ∧ x ∈ S.Om j} := by
  unfold stratG
  congr 1
  ext j
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hj, hO⟩; exact ⟨hj, (omGe_iff_om ell M R k hell S hS j x).mp hO⟩
  · rintro ⟨hj, hO⟩; exact ⟨hj, (omGe_iff_om ell M R k hell S hS j x).mpr hO⟩

variable {L : PeriodicLatticeExtent}

theorem adSL_apply (γ : GaugeFn L) (f : SiteL2 L) (x : PeriodicLatticeSite L) :
    (AdalyFormal.GaugeCov.adSL γ f) x = RMap (γ x) (f x) := rfl

theorem wNormSq_gauge (G : TowerGeom L) (γ : GaugeFn L) (f : SiteL2 L) :
    wNormSq G (AdalyFormal.GaugeCov.adSL γ f) = wNormSq G f := by
  unfold wNormSq
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [AdalyFormal.GaugeCov.siteMask_adSL, adSL_apply, AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap]

/-- **S1 in any global site gauge**. -/
theorem site_coercive_weighted_gauge (ell k : ℕ) (hell : 2 ≤ ell) (hdvd : ∀ μ, ell ^ k ∣ L μ + 1)
    {G : TowerGeom L} (hP : ProperTower G ell k) (U : Cfg L) (γ : GaugeFn L) (a : ℝ) (ha : 0 < a) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hU : ∀ j, j ≤ k → ∀ y ∈ G.Lam j, ∀ b ∈ inBlockBonds y (ell ^ j),
      frobNorm ((((periodicGaugeTransform γ U b : Matrix.specialUnitaryGroup (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
        ≤ ρ / (ell : ℝ) ^ j)
    (hT : ∀ j, j ≤ k → ∀ y ∈ G.Lam j, ∀ i, i < j → ∀ z ∈ blockOf y (ell ^ j), z ∈ CoarseLattice L (ell ^ i) → ∀ μ : Fin 3,
      coarseShift z (ell ^ i) μ ∈ blockOf y (ell ^ j) →
      frobNorm ((bgTower G (periodicGaugeTransform γ U) i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
        ≤ ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ j)
    (f : SiteL2 L) :
    (1 - 216 * ρ ^ 2) * wNormSq G f ≤ max 6 (16 / (3 * a)) * ⟪f, DelpA G U a f⟫ := by
  have h := site_coercive_weighted ell k hell hdvd hP (periodicGaugeTransform γ U) a ha ρ hρ hU hT
    (AdalyFormal.GaugeCov.adSL γ f)
  rw [wNormSq_gauge, AdalyFormal.GaugeCov.DelpA_gauge, LinearIsometryEquiv.inner_map_map] at h
  exact h

#print axioms aligned_eq
#print axioms hdvd_of_admissible
#print axioms lower_block_out
#print axioms properTower_geomOf
#print axioms stratG_geomOf
#print axioms wNormSq_gauge
#print axioms site_coercive_weighted_gauge

/-- **S1 with PER-BLOCK gauges**: each constraint block `B_q` (level `j_q`) carries its own site gauge `γ_q`; the in-block
links of `γ_q·U` and the in-block aligned averaged links of `γ_q·U` satisfy the stratum-scaled bounds. -/
theorem site_coercive_weighted_perblock (ell k : ℕ) (hell : 2 ≤ ell) (hdvd : ∀ μ, ell ^ k ∣ L μ + 1)
    {G : TowerGeom L} (hP : ProperTower G ell k) (U : Cfg L) (γB : QIdx G → GaugeFn L) (a : ℝ) (ha : 0 < a)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hU : ∀ q : QIdx G, ∀ b ∈ inBlockBonds (yq q) (ell ^ jq q),
      frobNorm ((((periodicGaugeTransform (γB q) U b : Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ / (ell : ℝ) ^ jq q)
    (hT : ∀ q : QIdx G, ∀ i, i < jq q → ∀ z ∈ blockOf (yq q) (ell ^ jq q), z ∈ CoarseLattice L (ell ^ i) →
      ∀ μ : Fin 3, coarseShift z (ell ^ i) μ ∈ blockOf (yq q) (ell ^ jq q) →
      frobNorm ((bgTower G (periodicGaugeTransform (γB q) U) i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
        ≤ ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ jq q)
    (f : SiteL2 L) :
    (1 - 216 * ρ ^ 2) * wNormSq G f ≤ max 6 (16 / (3 * a)) * ⟪f, DelpA G U a f⟫ := by
  classical
  set γ : GaugeFn L := fun x =>
    if h : ∃ q : QIdx G, x ∈ blockOf (yq q) (ell ^ jq q) then γB (Classical.choose h) x else 1 with hγdef
  have hγ : ∀ q : QIdx G, ∀ x ∈ blockOf (yq q) (ell ^ jq q), γ x = γB q x := by
    intro q x hx
    have h : ∃ q : QIdx G, x ∈ blockOf (yq q) (ell ^ jq q) := ⟨q, hx⟩
    simp only [hγdef, dif_pos h]
    have hq' := Classical.choose_spec h
    by_cases hqq : Classical.choose h = q
    · rw [hqq]
    · exact absurd hx (Finset.disjoint_left.mp (disj_q hP hqq) hq')
  -- the row of a level-`j` base point
  have mkq : ∀ j, j ≤ k → ∀ y ∈ G.Lam j, ∃ q : QIdx G, jq q = j ∧ yq q = y := by
    intro j hj y hy
    exact ⟨⟨(⟨j, by rw [hP.k_eq]; omega⟩, y), hy⟩, rfl, rfl⟩
  refine site_coercive_weighted_gauge ell k hell hdvd hP U γ a ha ρ hρ ?_ ?_ f
  · intro j hj y hy b hb
    obtain ⟨q, hqj, hqy⟩ := mkq j hj y hy
    subst hqj; subst hqy
    rw [mem_inBlockBonds] at hb
    have e : periodicGaugeTransform γ U b = periodicGaugeTransform (γB q) U b := by
      show γ b.1 * U b * (γ (periodicLatticeShift b.1 b.2))⁻¹
        = γB q b.1 * U b * (γB q (periodicLatticeShift b.1 b.2))⁻¹
      rw [hγ q b.1 hb.1, hγ q _ hb.2]
    rw [e]
    exact hU q b (mem_inBlockBonds.mpr hb)
  · intro j hj y hy i hi z hz hzal μ hzs
    obtain ⟨q, hqj, hqy⟩ := mkq j hj y hy
    subst hqj; subst hqy
    have e : bgTower G (periodicGaugeTransform γ U) i (z, μ)
        = bgTower G (periodicGaugeTransform (γB q) U) i (z, μ) := by
      rw [AdalyFormal.GaugeCov.bgTower_gauge, AdalyFormal.GaugeCov.bgTower_gauge]
      show γ z * bgTower G U i (z, μ) * (γ (coarseShift z (G.ell ^ i) μ))⁻¹
        = γB q z * bgTower G U i (z, μ) * (γB q (coarseShift z (G.ell ^ i) μ))⁻¹
      rw [hP.ell_eq, hγ q z hz, hγ q _ hzs]
    rw [e]
    exact hT q i hi z hz hzal μ hzs

#print axioms site_coercive_weighted_perblock

#print axioms adSL_apply

end AdalyFormal.M1Site
