import PSiteC15

/-!
# SiteC16 -- PROPER-TOWER (Dirichlet) site coercivity of the genuine `DelpA`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
namespace AdalyFormal.SiteCoercivity

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf stepAverage Qcomposite)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap gradValueCovariant)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond frobNorm_le_frobSupBond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.GeneralUHodgeDrift (siteEnergy)

variable {L : PeriodicLatticeExtent}

/-- gradient drift for a field supported in `R`, controlled only by the links whose HEAD is in `R` -/
theorem gradL2_drift_local (U : Cfg L) (R : Set (PeriodicLatticeSite L)) {δ0 : ℝ} (hδ0 : 0 ≤ δ0)
    (h : ∀ b : Bond L, periodicLatticeShift b.1 b.2 ∈ R → frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ δ0)
    (g : SiteL2 L) (hg : ∀ x, x ∉ R → g x = 0) :
    ‖gradL2 U g - gradL2 (trivialU L) g‖ ^ 2 ≤ 12 * δ0 ^ 2 * ‖g‖ ^ 2 := by
  have hp : ∀ b : Bond L, ‖(gradL2 U g - gradL2 (trivialU L) g) b‖ ^ 2
      ≤ 4 * δ0 ^ 2 * ‖g (periodicLatticeShift b.1 b.2)‖ ^ 2 := by
    intro b
    have e : (gradL2 U g - gradL2 (trivialU L) g) b
        = RMap (U b) (g (periodicLatticeShift b.1 b.2)) - g (periodicLatticeShift b.1 b.2) := by
      show gradValueCovariant U (WithLp.ofLp g) b - gradValueCovariant (trivialU L) (WithLp.ofLp g) b = _
      simp [gradValueCovariant, trivialU, AdalyFormal.Balaban.CovariantOperators.RMap_one]
    rw [e]
    by_cases hb : periodicLatticeShift b.1 b.2 ∈ R
    · have h1 := AdalyFormal.Balaban.RMapLipschitz.norm_RMap_sub_self_le (U b) (g (periodicLatticeShift b.1 b.2))
      have h2 := h b hb
      have h3 : ‖RMap (U b) (g (periodicLatticeShift b.1 b.2)) - g (periodicLatticeShift b.1 b.2)‖
          ≤ 2 * δ0 * ‖g (periodicLatticeShift b.1 b.2)‖ := by
        refine h1.trans ?_
        gcongr
      have h4 := pow_le_pow_left₀ (norm_nonneg _) h3 2
      nlinarith [h4]
    · rw [hg _ hb]
      simp
  rw [PiLp.norm_sq_eq_of_L2]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun b _ => hp b)
  rw [← Finset.mul_sum] at hs
  have hh := AdalyFormal.Balaban.DeltaPrimeBound.sum_lam_head_sq_eq (fun x : PeriodicLatticeSite L => g x)
  rw [hh] at hs
  unfold siteEnergy at hs
  rw [norm_sq_site]
  nlinarith [hs]


theorem site_coercive_proper_core (ell k : ℕ) (hell : 2 ≤ ell) (hdvd : ∀ μ, ell ^ k ∣ L μ + 1)
    {G : TowerGeom L} (hP : ProperTower G ell k) (U : Cfg L) (a : ℝ) (ha : 0 < a) (α E : ℝ) (hα : 0 ≤ α)
    (hU : ∀ b : Bond L, periodicLatticeShift b.1 b.2 ∈ G.Om0 →
      frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α / (ell : ℝ) ^ k)
    (δ : ℕ → ℝ) (hδ0 : ∀ i, 0 ≤ δ i)
    (hT : ∀ i, i < k → ∀ z ∈ G.Om0, ∀ μ : Fin 3,
      frobNorm ((bgTower G U i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ δ i)
    (hE : ∑ i ∈ Finset.range k, 6 * ((ell : ℝ) - 1) * δ i ≤ E)
    (g : SiteL2 L) (hg : ∀ x, x ∉ G.Om0 → g x = 0) :
    (1 - 72 * α ^ 2 - 4 * E ^ 2) * ‖g‖ ^ 2
      ≤ max 6 (16 / (3 * a)) * ((ell : ℝ) ^ k) ^ 2 * (‖gradL2 U g‖ ^ 2 + ⟪g, Qpa G U a g⟫) := by
  have hell0 : 0 < ell := by omega
  have hellR : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  set n : ℝ := (ell : ℝ) ^ k with hn
  have hnpos : 0 < n := by positivity
  set gf : PeriodicLatticeSite L → SuTwo := WithLp.ofLp g with hgf
  have hgf0 : ∀ x, x ∉ G.Om0 → gf x = 0 := hg
  have hE0 : 0 ≤ E := by
    refine le_trans ?_ hE
    refine Finset.sum_nonneg (fun i _ => ?_)
    have : (0 : ℝ) ≤ (ell : ℝ) - 1 := by linarith
    have := hδ0 i
    positivity
  -- partition
  have hpart : ‖g‖ ^ 2 = ∑ j ∈ Finset.range (k + 1), ∑ x ∈ Rj G ell j, ‖gf x‖ ^ 2 := by
    rw [norm_sq_site]
    have := sum_partition hP (fun x => ‖gf x‖ ^ 2) (fun x hx => by rw [hgf0 x hx]; simp)
    rw [this]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [sum_Rj hP (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
  -- per-level inequality
  have hlev : ∀ j ∈ Finset.range (k + 1),
      ∑ x ∈ Rj G ell j, ‖gf x‖ ^ 2 ≤
        3 * ((ell : ℝ) ^ j) ^ 2 * ∑ y ∈ LamF G j, ∑ b ∈ inBlockBonds y (ell ^ j),
            ‖gf (periodicLatticeShift b.1 b.2) - gf b.1‖ ^ 2
        + 4 * NsZ (ell ^ j) (LamF G j) (Qcomposite (bgTower G U) ell j gf) ^ 2
        + 4 * (E ^ 2 * ∑ x ∈ Rj G ell j, ‖gf x‖ ^ 2) := by
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hEj : ∑ i ∈ Finset.range j, 6 * ((ell : ℝ) - 1) * δ i ≤ E := by
      refine le_trans ?_ hE
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hjk) (fun i _ _ => ?_)
      have : (0 : ℝ) ≤ (ell : ℝ) - 1 := by linarith
      have := hδ0 i
      positivity
    obtain ⟨h1, h2⟩ := level_data ell k hell hdvd hP U δ hδ0 hT hjk E hEj gf
    set NF := NsZ (ell ^ j) (LamF G j) (Qcomposite (fun _ => trivialU L) ell j gf) with hNF
    set q := NsZ (ell ^ j) (LamF G j) (Qcomposite (bgTower G U) ell j gf) with hq
    set ρ := NsZ 1 (Rj G ell j) gf with hρ
    have hρsq : ρ ^ 2 = ∑ x ∈ Rj G ell j, ‖gf x‖ ^ 2 := by
      rw [hρ, NsZ_sq]; simp
    have hNF0 : 0 ≤ NF := NsZ_nonneg _ _ _
    have hq0 : 0 ≤ q := NsZ_nonneg _ _ _
    have hρ0 : 0 ≤ ρ := NsZ_nonneg _ _ _
    have h3 : NF ^ 2 ≤ 2 * q ^ 2 + 2 * (E ^ 2 * ρ ^ 2) := by
      have := pow_le_pow_left₀ hNF0 h2 2
      nlinarith [sq_nonneg (q - E * ρ)]
    rw [← hρsq]
    rw [hρsq] at h3
    rw [hρsq]
    nlinarith [h1, h3]
  -- sum the level inequalities
  have hsum := Finset.sum_le_sum hlev
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [← hpart] at hsum
  -- energy aggregation
  have hSj : ∀ j ∈ Finset.range (k + 1), 3 * ((ell : ℝ) ^ j) ^ 2 * ∑ y ∈ LamF G j, ∑ b ∈ inBlockBonds y (ell ^ j),
      ‖gf (periodicLatticeShift b.1 b.2) - gf b.1‖ ^ 2
      ≤ 3 * n ^ 2 * ∑ y ∈ LamF G j, ∑ b ∈ inBlockBonds y (ell ^ j),
      ‖gf (periodicLatticeShift b.1 b.2) - gf b.1‖ ^ 2 := by
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hnj : (ell : ℝ) ^ j ≤ n := pow_le_pow_right₀ (by linarith) hjk
    have hS : 0 ≤ ∑ y ∈ LamF G j, ∑ b ∈ inBlockBonds y (ell ^ j), ‖gf (periodicLatticeShift b.1 b.2) - gf b.1‖ ^ 2 :=
      Finset.sum_nonneg (fun y _ => Finset.sum_nonneg (fun b _ => sq_nonneg _))
    have : ((ell : ℝ) ^ j) ^ 2 ≤ n ^ 2 := pow_le_pow_left₀ (by positivity) hnj 2
    nlinarith
  have hagg := sum_blockbonds_le hP (fun b => ‖gf (periodicLatticeShift b.1 b.2) - gf b.1‖ ^ 2)
    (fun b => sq_nonneg _)
  have hflat := sum_flat_eq g
  have hD1 : ∑ j ∈ Finset.range (k + 1), 3 * ((ell : ℝ) ^ j) ^ 2 * ∑ y ∈ LamF G j, ∑ b ∈ inBlockBonds y (ell ^ j),
      ‖gf (periodicLatticeShift b.1 b.2) - gf b.1‖ ^ 2 ≤ 3 * n ^ 2 * ‖gradL2 (trivialU L) g‖ ^ 2 := by
    refine le_trans (Finset.sum_le_sum hSj) ?_
    rw [← Finset.mul_sum]
    have : ∑ j ∈ Finset.range (k + 1), ∑ y ∈ LamF G j, ∑ b ∈ inBlockBonds y (ell ^ j),
        ‖gf (periodicLatticeShift b.1 b.2) - gf b.1‖ ^ 2 ≤ ‖gradL2 (trivialU L) g‖ ^ 2 := by
      rw [← hflat]; exact hagg
    nlinarith
  -- gradient drift (local)
  have hdr := gradL2_drift_local U G.Om0 (δ0 := α / n) (div_nonneg hα hnpos.le) hU g hg
  have hDtri : ‖gradL2 (trivialU L) g‖ ^ 2 ≤ 2 * ‖gradL2 U g‖ ^ 2 + 2 * (12 * (α / n) ^ 2 * ‖g‖ ^ 2) := by
    have h1 : ‖gradL2 (trivialU L) g‖ ≤ ‖gradL2 U g‖ + ‖gradL2 U g - gradL2 (trivialU L) g‖ := by
      have := norm_sub_le (gradL2 U g) (gradL2 U g - gradL2 (trivialU L) g)
      simpa using this
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖gradL2 U g‖ - ‖gradL2 U g - gradL2 (trivialU L) g‖)]
  have hcancel : n ^ 2 * (12 * (α / n) ^ 2 * ‖g‖ ^ 2) = 12 * α ^ 2 * ‖g‖ ^ 2 := by
    field_simp
  -- mass
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
  have hmass_lb : ∀ j ∈ Finset.range (k + 1),
      4 * NsZ (ell ^ j) (LamF G j) (Qcomposite (bgTower G U) ell j gf) ^ 2
        ≤ (16 / (3 * a)) * n ^ 2 * (ajSeq a ell j * (ell : ℝ) ^ j *
            ∑ y ∈ LamF G j, ‖Qcomposite (bgTower G U) ell j gf y‖ ^ 2) := by
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hnj : (ell : ℝ) ^ j ≤ n := pow_le_pow_right₀ (by linarith) hjk
    have hSn : 0 ≤ ∑ y ∈ LamF G j, ‖Qcomposite (bgTower G U) ell j gf y‖ ^ 2 :=
      Finset.sum_nonneg (fun y _ => sq_nonneg _)
    have hak := ajSeq_ge ell j hell ha
    have hN := NsZ_sq (ell ^ j) (LamF G j) (Qcomposite (bgTower G U) ell j gf)
    have hnc : (((ell ^ j : ℕ)) : ℝ) = (ell : ℝ) ^ j := by push_cast; rfl
    rw [hN, hnc]
    set S := ∑ y ∈ LamF G j, ‖Qcomposite (bgTower G U) ell j gf y‖ ^ 2 with hS
    have hnjpos : 0 < (ell : ℝ) ^ j := by positivity
    have h1 : (16 / (3 * a)) * ((3 / 4 : ℝ) * a) = 4 := by field_simp; norm_num
    have h2 : (16 / (3 * a)) * n ^ 2 * (ajSeq a ell j * (ell : ℝ) ^ j * S)
        ≥ (16 / (3 * a)) * n ^ 2 * (((3 / 4 : ℝ) * a) * (ell : ℝ) ^ j * S) := by
      gcongr
    have h3 : (16 / (3 * a)) * n ^ 2 * (((3 / 4 : ℝ) * a) * (ell : ℝ) ^ j * S)
        = 4 * (n ^ 2 * ((ell : ℝ) ^ j * S)) := by
      have : (16 / (3 * a)) * n ^ 2 * (((3 / 4 : ℝ) * a) * (ell : ℝ) ^ j * S)
          = ((16 / (3 * a)) * ((3 / 4 : ℝ) * a)) * (n ^ 2 * ((ell : ℝ) ^ j * S)) := by ring
      rw [this, h1]
    have h4 : ((ell : ℝ) ^ j) ^ 3 * S ≤ n ^ 2 * ((ell : ℝ) ^ j * S) := by
      have : ((ell : ℝ) ^ j) ^ 2 ≤ n ^ 2 := pow_le_pow_left₀ hnjpos.le hnj 2
      have hh : 0 ≤ (ell : ℝ) ^ j * S := by positivity
      nlinarith [mul_le_mul_of_nonneg_right this hh]
    nlinarith
  have hmass_sum : 4 * ∑ j ∈ Finset.range (k + 1), NsZ (ell ^ j) (LamF G j) (Qcomposite (bgTower G U) ell j gf) ^ 2
      ≤ (16 / (3 * a)) * n ^ 2 * ⟪g, Qpa G U a g⟫ := by
    rw [hmassid, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum hmass_lb
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
  have hDU : 0 ≤ n ^ 2 * ‖gradL2 U g‖ ^ 2 := mul_nonneg (sq_nonneg n) (sq_nonneg _)
  have hMn : 0 ≤ n ^ 2 * ⟪g, Qpa G U a g⟫ := mul_nonneg (sq_nonneg n) hM0
  have h3D : 3 * n ^ 2 * ‖gradL2 (trivialU L) g‖ ^ 2 ≤ 6 * (n ^ 2 * ‖gradL2 U g‖ ^ 2) + 72 * α ^ 2 * ‖g‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_left hDtri (mul_nonneg (by norm_num) (sq_nonneg n) : (0 : ℝ) ≤ 3 * n ^ 2)
    nlinarith [this, hcancel]
  have hmain : (1 - 72 * α ^ 2 - 4 * E ^ 2) * ‖g‖ ^ 2
      ≤ 6 * (n ^ 2 * ‖gradL2 U g‖ ^ 2) + (16 / (3 * a)) * n ^ 2 * ⟪g, Qpa G U a g⟫ := by
    linarith [hsum, hD1, h3D, hmass_sum]
  have h6 := mul_le_mul_of_nonneg_right hm1 hDU
  have h16 := mul_le_mul_of_nonneg_right hm2 hMn
  linarith [hmain, h6, h16]
