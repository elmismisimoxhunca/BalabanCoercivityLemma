import MS1
import MSal

/-!
# MS2 -- S1 (PLAN.md §1.2 Layer S): STRATUM-WEIGHTED proper-tower site coercivity, k-free constant

`stratG G x := sSup {j | j ≤ k ∧ OmGe G j x}` (the stratum of a fine site, read off the tower geometry exactly as `OmGe`
(ZXR2Ops3) reads `x ∈ Ω_j`); `wNormSq G f := Σ_x ‖(Ω₀ f) x‖² / (ℓ^{stratG x})²` (the plan's `‖siteMask Ω₀ f‖_w²`, weight
`ℓ^{-2 strat}`).

**`site_coercive_weighted`**: for a `ProperTower G ℓ k` (`Ω₀ = ⊔_j B^j(Λ_j)`), `a > 0`, `0 ≤ ρ`, and
* `hU` : every IN-BLOCK link of a level-`j` block (both endpoints in the same block `B(y, ℓ^j)`, `y ∈ Λ_j`) has
  `‖U_b − 1‖_F ≤ ρ/ℓ^j` (the stratum-scaled link size; for an in-block bond `bstrat b = j`);
* `hT` : the averaged backgrounds on the level-`i` links `(z, μ)` of a level-`j` block (`i < j`) — `z` `ℓ^i`-ALIGNED and BOTH
  coarse endpoints `z`, `z + ℓ^i e_μ` in the block — satisfy the stratum tower class `‖Ū^{(i)}(z,μ) − 1‖_F ≤ ρ ℓ^i/ℓ^j`
  (aligned: the form the blocking estimates supply; in-block: so a per-block gauge can be used, MS7);
we have `(1 − 216ρ²) · wNormSq G f ≤ max 6 (16/(3a)) · ⟪f, Δ'_a f⟫` for EVERY site field `f`.  The constant does not depend
on `k`, `L`, `Λ_j`, or the tower.

Route: per level `j`, `level_data_al` (MSal: PSiteC15 `level_data` with the tower hypothesis on in-block aligned links of the
level-`j` blocks only); the flat in-block gradient is
compared with the covariant one only on in-block bonds; each level inequality is divided by `ℓ^{2j}` BEFORE summing (the
single-`n²` proof of SiteC16 bounds every `ℓ^j` by `ℓ^k` instead).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1Site

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.QjComposite (Qcomposite)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap gradValueCovariant)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)

variable {L : PeriodicLatticeExtent}

/-! ## 1. stratum and weighted norm -/

/-- the stratum of a fine site: the largest `j ≤ k` with `x ∈ Ω_j` (read as `OmGe`). -/
noncomputable def stratG (G : TowerGeom L) (x : PeriodicLatticeSite L) : ℕ :=
  sSup {j | j ≤ G.k ∧ OmGe G j x}

/-- `‖Ω₀ f‖_w² = Σ_x ℓ^{-2 strat x} ‖(Ω₀ f)(x)‖²` -/
noncomputable def wNormSq (G : TowerGeom L) (f : SiteL2 L) : ℝ :=
  ∑ x, ‖siteMask G.Om0 f x‖ ^ 2 / ((G.ell : ℝ) ^ stratG G x) ^ 2

theorem stratG_eq {G : TowerGeom L} {ell k : ℕ} (hP : ProperTower G ell k) {j : ℕ} (hj : j ≤ k)
    {y : PeriodicLatticeSite L} (hy : y ∈ G.Lam j) {x : PeriodicLatticeSite L} (hx : x ∈ blockOf y (ell ^ j)) :
    stratG G x = j := by
  have hmem : x ∈ blockOf y (ell ^ j) := hx
  rw [mem_blockOf] at hx
  have hOm : OmGe G j x := ⟨j, le_rfl, by rw [hP.k_eq]; exact hj, y, hy, by rw [hP.ell_eq]; exact hx⟩
  have hub : ∀ i, i ≤ G.k ∧ OmGe G i x → i ≤ j := by
    rintro i ⟨-, i', hii', hi'k, y', hy', hxy'⟩
    by_contra hlt
    push Not at hlt
    have hi'k' : i' ≤ k := by rw [← hP.k_eq]; exact hi'k
    have hd := hP.disj j i' hj hi'k' y hy y' hy' (Or.inl (by omega))
    have hx' : x ∈ blockOf y' (ell ^ i') := by
      rw [mem_blockOf]; rw [hP.ell_eq] at hxy'; exact hxy'
    exact Finset.disjoint_left.mp hd hmem hx'
  unfold stratG
  refine IsGreatest.csSup_eq ⟨⟨by rw [hP.k_eq]; exact hj, hOm⟩, fun i hi => hub i hi⟩

/-- the weighted norm as a block sum. -/
theorem wNormSq_blocks {G : TowerGeom L} {ell k : ℕ} (hP : ProperTower G ell k) (f : SiteL2 L) :
    wNormSq G f = ∑ j ∈ Finset.range (k + 1), ∑ y ∈ LamF G j, ∑ x ∈ blockOf y (ell ^ j),
      ‖siteMask G.Om0 f x‖ ^ 2 / ((ell : ℝ) ^ j) ^ 2 := by
  unfold wNormSq
  rw [sum_partition hP (fun x => ‖siteMask G.Om0 f x‖ ^ 2 / ((G.ell : ℝ) ^ stratG G x) ^ 2)
    (fun x hx => by rw [siteMask_off _ _ _ hx]; simp)]
  refine Finset.sum_congr rfl (fun j hj => Finset.sum_congr rfl (fun y hy => Finset.sum_congr rfl (fun x hx => ?_)))
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [stratG_eq hP hjk (mem_LamF.mp hy) hx, hP.ell_eq]

theorem wNormSq_nonneg (G : TowerGeom L) (f : SiteL2 L) : 0 ≤ wNormSq G f :=
  Finset.sum_nonneg (fun x _ => div_nonneg (sq_nonneg _) (sq_nonneg _))

/-! ## 2. the one-level geometry -/

open Classical in
/-- level `j` alone: `Λ'_j = Λ_j`, `Λ'_i = ∅` (`i ≠ j`), `Ω'₀ = R_j`, height `j`. -/
noncomputable def levelGeom (G : TowerGeom L) (j : ℕ) : TowerGeom L where
  ell := G.ell
  k := j
  Om0 := {x | x ∈ Rj G G.ell j}
  Lam := fun i => if i = j then G.Lam j else ∅

theorem levelGeom_proper {G : TowerGeom L} {ell k : ℕ} (hP : ProperTower G ell k) {j : ℕ} (hj : j ≤ k) :
    ProperTower (levelGeom G j) ell j where
  ell_eq := hP.ell_eq
  k_eq := rfl
  coarse := by
    intro i _ y hy
    have h1 : y ∈ (if i = j then G.Lam j else ∅) := hy
    by_cases hij : i = j
    · rw [if_pos hij] at h1; rw [hij]; exact hP.coarse j hj y h1
    · rw [if_neg hij] at h1; exact absurd h1 (Set.notMem_empty y)
  disj := by
    intro i i' _ _ y hy y' hy' hne
    have h1 : y ∈ (if i = j then G.Lam j else ∅) := hy
    have h2 : y' ∈ (if i' = j then G.Lam j else ∅) := hy'
    by_cases hij : i = j
    · by_cases hij' : i' = j
      · rw [if_pos hij] at h1; rw [if_pos hij'] at h2
        rw [hij, hij']
        exact hP.disj j j hj hj y h1 y' h2 (Or.inr (hne.resolve_left (by omega)))
      · rw [if_neg hij'] at h2; exact absurd h2 (Set.notMem_empty y')
    · rw [if_neg hij] at h1; exact absurd h1 (Set.notMem_empty y)
  cover := by
    intro x
    constructor
    · intro hx
      have hx' : x ∈ Rj G G.ell j := hx
      unfold Rj at hx'
      rw [Finset.mem_biUnion] at hx'
      obtain ⟨y, hy, hxy⟩ := hx'
      refine ⟨j, le_rfl, y, ?_, ?_⟩
      · show y ∈ (if j = j then G.Lam j else ∅)
        rw [if_pos rfl]; exact mem_LamF.mp hy
      · rw [← hP.ell_eq]; exact hxy
    · rintro ⟨i, _, y, hy, hxy⟩
      have hy' : y ∈ (if i = j then G.Lam j else ∅) := hy
      by_cases hij : i = j
      · rw [if_pos hij] at hy'
        show x ∈ Rj G G.ell j
        unfold Rj
        rw [Finset.mem_biUnion]
        refine ⟨y, mem_LamF.mpr hy', ?_⟩
        rw [hP.ell_eq, ← hij]; exact hxy
      · rw [if_neg hij] at hy'; exact absurd hy' (Set.notMem_empty y)

theorem levelGeom_LamF (G : TowerGeom L) (j : ℕ) : LamF (levelGeom G j) j = LamF G j := by
  ext y
  rw [mem_LamF, mem_LamF]
  show y ∈ (if j = j then G.Lam j else ∅) ↔ _
  rw [if_pos rfl]

theorem levelGeom_Rj (G : TowerGeom L) (ell j : ℕ) : Rj (levelGeom G j) ell j = Rj G ell j := by
  unfold Rj; rw [levelGeom_LamF]

theorem levelGeom_bg (G : TowerGeom L) (j : ℕ) (U : Cfg L) : bgTower (levelGeom G j) U = bgTower G U := rfl

/-! ## 3. counting and drift on in-block bonds -/

theorem shift_injective (μ : Fin 3) : Function.Injective (fun x : PeriodicLatticeSite L => periodicLatticeShift x μ) := by
  intro x x' h
  funext ν
  have h1 := congrFun h ν
  simp only [periodicLatticeShift] at h1
  by_cases hν : ν = μ
  · subst hν
    simp only [Function.update_self] at h1
    exact add_right_cancel h1
  · simpa [Function.update_of_ne hν] using h1

theorem sum_inBlock_head_le (y : PeriodicLatticeSite L) (n : ℕ) (φ : PeriodicLatticeSite L → ℝ) (hφ : ∀ x, 0 ≤ φ x) :
    ∑ b ∈ inBlockBonds y n, φ (periodicLatticeShift b.1 b.2) ≤ 3 * ∑ x ∈ blockOf y n, φ x := by
  classical
  set e : Bond L → PeriodicLatticeSite L × Fin 3 := fun b => (periodicLatticeShift b.1 b.2, b.2) with he
  have hinj : Set.InjOn e ↑(inBlockBonds y n) := by
    intro b _ b' _ h
    have h' : (periodicLatticeShift b.1 b.2, b.2) = (periodicLatticeShift b'.1 b'.2, b'.2) := h
    have h2 : b.2 = b'.2 := (Prod.mk.inj h').2
    have h1 : periodicLatticeShift b.1 b.2 = periodicLatticeShift b'.1 b'.2 := (Prod.mk.inj h').1
    rw [h2] at h1
    exact Prod.ext (shift_injective b'.2 h1) h2
  have hs : ∑ b ∈ inBlockBonds y n, φ (periodicLatticeShift b.1 b.2)
      = ∑ p ∈ (inBlockBonds y n).image e, φ p.1 := by
    rw [Finset.sum_image hinj]
  have hsub : (inBlockBonds y n).image e ⊆ blockOf y n ×ˢ (Finset.univ : Finset (Fin 3)) := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨b, hb, rfl⟩ := hp
    rw [mem_inBlockBonds] at hb
    exact Finset.mem_product.mpr ⟨hb.2, Finset.mem_univ _⟩
  rw [hs]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hφ p.1)) ?_
  rw [Finset.sum_product]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.mul_sum]
  norm_num

theorem gradL2_apply' (U : Cfg L) (g : SiteL2 L) (b : Bond L) :
    gradL2 U g b = RMap (U b) (g (periodicLatticeShift b.1 b.2)) - g b.1 := rfl

/-- flat in-block gradient vs covariant, one bond -/
theorem flat_le_cov (U : Cfg L) (g : SiteL2 L) (b : Bond L) (δ : ℝ) (_hδ : 0 ≤ δ)
    (hb : frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ δ) :
    ‖g (periodicLatticeShift b.1 b.2) - g b.1‖ ^ 2
      ≤ 2 * ‖gradL2 U g b‖ ^ 2 + 8 * δ ^ 2 * ‖g (periodicLatticeShift b.1 b.2)‖ ^ 2 := by
  set h := g (periodicLatticeShift b.1 b.2)
  have e : h - g b.1 = gradL2 U g b - (RMap (U b) h - h) := by rw [gradL2_apply']; abel
  have h1 : ‖RMap (U b) h - h‖ ≤ 2 * δ * ‖h‖ := by
    refine (AdalyFormal.Balaban.RMapLipschitz.norm_RMap_sub_self_le (U b) h).trans ?_
    gcongr
  have h2 : ‖h - g b.1‖ ≤ ‖gradL2 U g b‖ + 2 * δ * ‖h‖ := by
    rw [e]; exact (norm_sub_le _ _).trans (by linarith)
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  nlinarith [sq_nonneg (‖gradL2 U g b‖ - 2 * δ * ‖h‖), norm_nonneg (gradL2 U g b), norm_nonneg h]

/-! ## 4. the weighted inequality -/

theorem site_coercive_weighted_core (ell k : ℕ) (hell : 2 ≤ ell) (hdvd : ∀ μ, ell ^ k ∣ L μ + 1)
    {G : TowerGeom L} (hP : ProperTower G ell k) (U : Cfg L) (a : ℝ) (ha : 0 < a) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hU : ∀ j, j ≤ k → ∀ y ∈ G.Lam j, ∀ b ∈ inBlockBonds y (ell ^ j),
      frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ / (ell : ℝ) ^ j)
    (hT : ∀ j, j ≤ k → ∀ y ∈ G.Lam j, ∀ i, i < j → ∀ z ∈ blockOf y (ell ^ j), z ∈ CoarseLattice L (ell ^ i) → ∀ μ : Fin 3,
      coarseShift z (ell ^ i) μ ∈ blockOf y (ell ^ j) →
      frobNorm ((bgTower G U i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ j)
    (g : SiteL2 L) :
    (1 - 216 * ρ ^ 2) * (∑ j ∈ Finset.range (k + 1), ∑ x ∈ Rj G ell j, ‖g x‖ ^ 2 / ((ell : ℝ) ^ j) ^ 2)
      ≤ max 6 (16 / (3 * a)) * (‖gradL2 U g‖ ^ 2 + ⟪g, Qpa G U a g⟫) := by
  have hell0 : 0 < ell := by omega
  have hellR : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  set gf : PeriodicLatticeSite L → SuTwo := WithLp.ofLp g with hgf
  -- per-level inequality, divided by n_j^2
  have hlev : ∀ j ∈ Finset.range (k + 1),
      (1 - 216 * ρ ^ 2) * (∑ x ∈ Rj G ell j, ‖g x‖ ^ 2 / ((ell : ℝ) ^ j) ^ 2)
        ≤ 6 * ∑ y ∈ LamF G j, ∑ b ∈ inBlockBonds y (ell ^ j), ‖gradL2 U g b‖ ^ 2
          + (16 / (3 * a)) * (ajSeq a ell j * (ell : ℝ) ^ j *
              ∑ y ∈ LamF G j, ‖Qcomposite (bgTower G U) ell j gf y‖ ^ 2) := by
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hdvdj : ∀ μ, ell ^ j ∣ L μ + 1 := fun μ => Dvd.dvd.trans (pow_dvd_pow ell hjk) (hdvd μ)
    set δj : ℕ → ℝ := fun i => ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ j with hδj
    have hδ0 : ∀ i, 0 ≤ δj i := fun i => by
      have : (0 : ℝ) ≤ (ell : ℝ) ^ i / (ell : ℝ) ^ j := by positivity
      have e : ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ j = ρ * ((ell : ℝ) ^ i / (ell : ℝ) ^ j) := by ring
      show 0 ≤ ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ j
      rw [e]; positivity
    have hTj : ∀ i, i < j → ∀ y0 ∈ G.Lam j, ∀ z ∈ blockOf y0 (ell ^ j), z ∈ CoarseLattice L (ell ^ i) → ∀ μ : Fin 3,
        coarseShift z (ell ^ i) μ ∈ blockOf y0 (ell ^ j) →
        frobNorm ((bgTower G U i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ δj i :=
      fun i hi y0 hy0 z hz hzal μ hzs => hT j hjk y0 hy0 i hi z hz hzal μ hzs
    have hE := geom_tower_sum ell j hell ρ hρ
    obtain ⟨h1, h2⟩ := level_data_al ell k hell hdvd hP U δj hδ0 hjk hTj (6 * ρ) hE gf
    -- flat in-block gradient vs covariant
    set nj : ℝ := (ell : ℝ) ^ j with hnj
    have hnjpos : 0 < nj := by positivity
    set S0 := ∑ y ∈ LamF G j, ∑ b ∈ inBlockBonds y (ell ^ j), ‖gf (periodicLatticeShift b.1 b.2) - gf b.1‖ ^ 2 with hS0
    set SU := ∑ y ∈ LamF G j, ∑ b ∈ inBlockBonds y (ell ^ j), ‖gradL2 U g b‖ ^ 2 with hSU
    set R2 := ∑ x ∈ Rj G ell j, ‖gf x‖ ^ 2 with hR2
    have hS0U : S0 ≤ 2 * SU + 24 * (ρ / nj) ^ 2 * R2 := by
      have hb : ∀ y ∈ LamF G j, ∑ b ∈ inBlockBonds y (ell ^ j), ‖gf (periodicLatticeShift b.1 b.2) - gf b.1‖ ^ 2
          ≤ 2 * ∑ b ∈ inBlockBonds y (ell ^ j), ‖gradL2 U g b‖ ^ 2
            + 24 * (ρ / nj) ^ 2 * ∑ x ∈ blockOf y (ell ^ j), ‖gf x‖ ^ 2 := by
        intro y hy
        have hδ : 0 ≤ ρ / nj := div_nonneg hρ hnjpos.le
        have hper : ∀ b ∈ inBlockBonds y (ell ^ j), ‖gf (periodicLatticeShift b.1 b.2) - gf b.1‖ ^ 2
            ≤ 2 * ‖gradL2 U g b‖ ^ 2 + 8 * (ρ / nj) ^ 2 * ‖gf (periodicLatticeShift b.1 b.2)‖ ^ 2 :=
          fun b hb => flat_le_cov U g b (ρ / nj) hδ (hU j hjk y (mem_LamF.mp hy) b hb)
        have hs := Finset.sum_le_sum hper
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
        have hc := sum_inBlock_head_le y (ell ^ j) (fun x => ‖gf x‖ ^ 2) (fun x => sq_nonneg _)
        have hq : 0 ≤ (ρ / nj) ^ 2 := sq_nonneg _
        nlinarith [mul_le_mul_of_nonneg_left hc (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hq)]
      have hs := Finset.sum_le_sum hb
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
      have hR : ∑ y ∈ LamF G j, ∑ x ∈ blockOf y (ell ^ j), ‖gf x‖ ^ 2 = R2 := by
        rw [hR2, sum_Rj hP hjk]
      rw [hR] at hs
      exact hs
    -- telescoping and mass
    set NF := NsZ (ell ^ j) (LamF G j) (Qcomposite (fun _ => trivialU L) ell j gf) with hNF
    set q := NsZ (ell ^ j) (LamF G j) (Qcomposite (bgTower G U) ell j gf) with hq
    set ρn := NsZ 1 (Rj G ell j) gf with hρn
    have hρsq : ρn ^ 2 = R2 := by rw [hρn, NsZ_sq]; simp [hR2]
    have hNF0 : 0 ≤ NF := NsZ_nonneg _ _ _
    have hq0 : 0 ≤ q := NsZ_nonneg _ _ _
    have hρ0 : 0 ≤ ρn := NsZ_nonneg _ _ _
    have h3 : NF ^ 2 ≤ 2 * q ^ 2 + 2 * ((6 * ρ) ^ 2 * ρn ^ 2) := by
      have := pow_le_pow_left₀ hNF0 h2 2
      nlinarith [sq_nonneg (q - 6 * ρ * ρn)]
    rw [hρsq] at h3
    -- h1 : R2 ≤ 3 n_j^2 S0 + 2 NF^2
    have hnc : (((ell ^ j : ℕ)) : ℝ) = nj := by push_cast; rfl
    have hqsq : q ^ 2 = nj ^ 3 * ∑ y ∈ LamF G j, ‖Qcomposite (bgTower G U) ell j gf y‖ ^ 2 := by
      rw [hq, NsZ_sq, hnc]
    set SQ := ∑ y ∈ LamF G j, ‖Qcomposite (bgTower G U) ell j gf y‖ ^ 2 with hSQ
    have hSQ0 : 0 ≤ SQ := Finset.sum_nonneg (fun y _ => sq_nonneg _)
    have hSU0 : 0 ≤ SU := Finset.sum_nonneg (fun y _ => Finset.sum_nonneg (fun b _ => sq_nonneg _))
    have hR20 : 0 ≤ R2 := Finset.sum_nonneg (fun x _ => sq_nonneg _)
    -- combine: R2 ≤ 6 n^2 SU + 72 ρ^2 R2 + 4 n^3 SQ + 144 ρ^2 R2
    have hcomb : (1 - 216 * ρ ^ 2) * R2 ≤ 6 * nj ^ 2 * SU + 4 * (nj ^ 3 * SQ) := by
      have e1 : 3 * nj ^ 2 * (24 * (ρ / nj) ^ 2 * R2) = 72 * ρ ^ 2 * R2 := by field_simp; ring
      have hh1 : R2 ≤ 3 * nj ^ 2 * S0 + 2 * NF ^ 2 := h1
      have hh2 : 3 * nj ^ 2 * S0 ≤ 3 * nj ^ 2 * (2 * SU + 24 * (ρ / nj) ^ 2 * R2) :=
        mul_le_mul_of_nonneg_left hS0U (by positivity)
      rw [hqsq] at h3
      nlinarith [hh1, hh2, h3, e1]
    -- the level-j row weight
    have hak := ajSeq_ge ell j hell ha
    have hmass : 4 * nj * SQ ≤ (16 / (3 * a)) * (ajSeq a ell j * nj * SQ) := by
      have h16 : (16 / (3 * a)) * ((3 / 4 : ℝ) * a) = 4 := by field_simp; norm_num
      have hnS : 0 ≤ nj * SQ := mul_nonneg hnjpos.le hSQ0
      have : (16 / (3 * a)) * (((3 / 4 : ℝ) * a) * (nj * SQ)) ≤ (16 / (3 * a)) * (ajSeq a ell j * (nj * SQ)) := by
        gcongr
      nlinarith [this, h16]
    -- divide by n_j^2
    have hdiv : ∑ x ∈ Rj G ell j, ‖g x‖ ^ 2 / ((ell : ℝ) ^ j) ^ 2 = R2 / nj ^ 2 := by
      rw [hR2, Finset.sum_div]
    rw [hdiv]
    have hn2 : 0 < nj ^ 2 := by positivity
    rw [mul_div_assoc', div_le_iff₀ hn2]
    have e2 : 4 * (nj ^ 3 * SQ) = 4 * nj * SQ * nj ^ 2 := by ring
    nlinarith [hcomb, hmass, e2, mul_le_mul_of_nonneg_right hmass hn2.le]
  have hsum := Finset.sum_le_sum hlev
  rw [← Finset.mul_sum] at hsum
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  -- aggregate the in-block covariant energies
  have hagg := sum_blockbonds_le hP (fun b => ‖gradL2 U g b‖ ^ 2) (fun b => sq_nonneg _)
  have hgrad : ∑ b, ‖gradL2 U g b‖ ^ 2 = ‖gradL2 U g‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
  rw [hgrad] at hagg
  -- the mass identity
  have hmassid : ⟪g, Qpa G U a g⟫ = ∑ j ∈ Finset.range (k + 1), ajSeq a ell j * (ell : ℝ) ^ j *
      ∑ y ∈ LamF G j, ‖Qcomposite (bgTower G U) ell j gf y‖ ^ 2 := by
    rw [inner_Qpa, hP.k_eq, hP.ell_eq]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    unfold LamF
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    split_ifs
    · rw [Qlev_apply, hP.ell_eq]
    · rfl
  have hM0 : 0 ≤ ⟪g, Qpa G U a g⟫ := by
    rw [hmassid]
    refine Finset.sum_nonneg (fun j _ => ?_)
    have hak := ajSeq_ge ell j hell ha
    have : 0 ≤ ajSeq a ell j := by linarith
    have hSn : 0 ≤ ∑ y ∈ LamF G j, ‖Qcomposite (bgTower G U) ell j gf y‖ ^ 2 :=
      Finset.sum_nonneg (fun y _ => sq_nonneg _)
    positivity
  have hm1 : (6 : ℝ) ≤ max 6 (16 / (3 * a)) := le_max_left _ _
  have hm2 : 16 / (3 * a) ≤ max 6 (16 / (3 * a)) := le_max_right _ _
  rw [← hmassid] at hsum
  have hG0 : 0 ≤ ‖gradL2 U g‖ ^ 2 := sq_nonneg _
  have hx1 : 6 * (∑ j ∈ Finset.range (k + 1), ∑ y ∈ LamF G j, ∑ b ∈ inBlockBonds y (ell ^ j), ‖gradL2 U g b‖ ^ 2)
      ≤ max 6 (16 / (3 * a)) * ‖gradL2 U g‖ ^ 2 := by
    calc _ ≤ 6 * ‖gradL2 U g‖ ^ 2 := by linarith [hagg]
      _ ≤ _ := mul_le_mul_of_nonneg_right hm1 hG0
  have hx2 : 16 / (3 * a) * ⟪g, Qpa G U a g⟫ ≤ max 6 (16 / (3 * a)) * ⟪g, Qpa G U a g⟫ :=
    mul_le_mul_of_nonneg_right hm2 hM0
  nlinarith [hsum, hx1, hx2]

/-- **S1 `site_coercive_weighted`**: `(1 − 216ρ²)‖Ω₀f‖_w² ≤ max(6, 16/(3a)) ⟪f, Δ'_a f⟫`, k-free. -/
theorem site_coercive_weighted (ell k : ℕ) (hell : 2 ≤ ell) (hdvd : ∀ μ, ell ^ k ∣ L μ + 1)
    {G : TowerGeom L} (hP : ProperTower G ell k) (U : Cfg L) (a : ℝ) (ha : 0 < a) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hU : ∀ j, j ≤ k → ∀ y ∈ G.Lam j, ∀ b ∈ inBlockBonds y (ell ^ j),
      frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ / (ell : ℝ) ^ j)
    (hT : ∀ j, j ≤ k → ∀ y ∈ G.Lam j, ∀ i, i < j → ∀ z ∈ blockOf y (ell ^ j), z ∈ CoarseLattice L (ell ^ i) → ∀ μ : Fin 3,
      coarseShift z (ell ^ i) μ ∈ blockOf y (ell ^ j) →
      frobNorm ((bgTower G U i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ j)
    (f : SiteL2 L) :
    (1 - 216 * ρ ^ 2) * wNormSq G f ≤ max 6 (16 / (3 * a)) * ⟪f, DelpA G U a f⟫ := by
  have h := site_coercive_weighted_core ell k hell hdvd hP U a ha ρ hρ hU hT (siteMask G.Om0 f)
  have hw : wNormSq G f = ∑ j ∈ Finset.range (k + 1), ∑ x ∈ Rj G ell j,
      ‖siteMask G.Om0 f x‖ ^ 2 / ((ell : ℝ) ^ j) ^ 2 := by
    rw [wNormSq_blocks hP]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [sum_Rj hP (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
  have hD : ⟪f, DelpA G U a f⟫ = ‖gradL2 U (siteMask G.Om0 f)‖ ^ 2 + ⟪siteMask G.Om0 f, Qpa G U a (siteMask G.Om0 f)⟫ := by
    unfold DelpA
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← siteMask_symm,
      ContinuousLinearMap.add_apply, inner_add_right, inner_lapFull]
  rw [hw, hD]
  exact h

#print axioms stratG_eq
#print axioms wNormSq_blocks
#print axioms levelGeom_proper
#print axioms shift_injective
#print axioms sum_inBlock_head_le
#print axioms flat_le_cov
#print axioms site_coercive_weighted_core
#print axioms site_coercive_weighted

#print axioms wNormSq_nonneg
#print axioms levelGeom_LamF
#print axioms levelGeom_Rj
#print axioms levelGeom_bg
#print axioms gradL2_apply'

end AdalyFormal.M1Site
