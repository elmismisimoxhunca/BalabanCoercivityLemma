import PSiteC6
import PSiteC2
import PSiteC1
import SectBGraph
import AdalyFormal.Balaban.GeneralUHodgeDrift

/-!
# SC7 -- NESTED site coercivity: the genuine R2 `DelpA` at the FULL k-level tower (ratio `ell`, `Λ_k` = all stride-`ell^k` centres).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
namespace AdalyFormal.SiteCoercivity

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf stepAverage Qcomposite)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap gradValueCovariant)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond frobNorm_le_frobSupBond)

variable {L : PeriodicLatticeExtent}

/-- the full `k`-level tower on the whole torus: `Ω₀ = univ`, `Λ_j = ∅` for `j < k`, `Λ_k` = stride-`ell^k` centres. -/
noncomputable def fullGeom (L : PeriodicLatticeExtent) (ell k : ℕ) : TowerGeom L where
  ell := ell
  k := k
  Om0 := Set.univ
  Lam := fun j => if j = k then ((CoarseLattice L (ell ^ k) : Finset _) : Set _) else ∅

theorem fullGeom_Lam_lt (ell k : ℕ) {j : ℕ} (hj : j ≠ k) : (fullGeom L ell k).Lam j = ∅ := by
  simp [fullGeom, hj]

theorem fullGeom_Lam_k (ell k : ℕ) :
    (fullGeom L ell k).Lam k = ((CoarseLattice L (ell ^ k) : Finset _) : Set _) := by
  simp [fullGeom]

theorem inner_DelpA_full (ell k : ℕ) (U : Cfg L) (a : ℝ) (f : SiteL2 L) :
    ⟪f, DelpA (fullGeom L ell k) U a f⟫
      = ‖gradL2 U f‖ ^ 2 + ajSeq a ell k * (ell : ℝ) ^ k *
          ∑ y ∈ CoarseLattice L (ell ^ k),
            ‖Qcomposite (bgTower (fullGeom L ell k) U) ell k (WithLp.ofLp f) y‖ ^ 2 := by
  rw [DelpA_univ _ rfl, inner_add_right, inner_lapFull, inner_Qpa]
  have hk : (fullGeom L ell k).k = k := rfl
  have he : (fullGeom L ell k).ell = ell := rfl
  rw [hk, he]
  rw [Finset.sum_eq_single k]
  · rw [fullGeom_Lam_k]
    simp only [Finset.mem_coe]
    rw [Finset.sum_ite_mem Finset.univ (CoarseLattice L (ell ^ k)), Finset.univ_inter, Finset.mul_sum]
    congr 1
  · intro j _ hj
    rw [fullGeom_Lam_lt ell k hj]
    simp
  · intro hk'
    exfalso; exact hk' (Finset.mem_range.mpr (Nat.lt_succ_self k))


open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.GeneralUHodgeDrift (siteEnergy)

theorem norm_sq_gradL2' (U : Cfg L) (f : SiteL2 L) :
    ‖gradL2 U f‖ ^ 2 = ∑ b, ‖gradValueCovariant U (WithLp.ofLp f) b‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

theorem norm_sq_site (f : SiteL2 L) : ‖f‖ ^ 2 = ∑ x, ‖f x‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]

theorem sum_flat_eq (f : SiteL2 L) :
    ∑ b : Bond L, ‖f (periodicLatticeShift b.1 b.2) - f b.1‖ ^ 2 = ‖gradL2 (trivialU L) f‖ ^ 2 := by
  rw [norm_sq_gradL2']
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp [gradValueCovariant, trivialU, AdalyFormal.Balaban.CovariantOperators.RMap_one]

theorem gradL2_drift (U : Cfg L) {δ0 : ℝ} (h : frobSupBond U ≤ δ0) (f : SiteL2 L) :
    ‖gradL2 U f - gradL2 (trivialU L) f‖ ^ 2 ≤ 12 * δ0 ^ 2 * ‖f‖ ^ 2 := by
  have hδ0 : 0 ≤ δ0 := by
    obtain ⟨b⟩ := (inferInstance : Nonempty (Bond L))
    exact le_trans (AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _)
      ((frobNorm_le_frobSupBond U b).trans h)
  have hp : ∀ b : Bond L, ‖(gradL2 U f - gradL2 (trivialU L) f) b‖ ^ 2
      ≤ 4 * δ0 ^ 2 * ‖f (periodicLatticeShift b.1 b.2)‖ ^ 2 := by
    intro b
    have e : (gradL2 U f - gradL2 (trivialU L) f) b
        = RMap (U b) (f (periodicLatticeShift b.1 b.2)) - f (periodicLatticeShift b.1 b.2) := by
      show gradValueCovariant U (WithLp.ofLp f) b - gradValueCovariant (trivialU L) (WithLp.ofLp f) b = _
      simp [gradValueCovariant, trivialU, AdalyFormal.Balaban.CovariantOperators.RMap_one]
    rw [e]
    have h1 := AdalyFormal.Balaban.RMapLipschitz.norm_RMap_sub_self_le (U b) (f (periodicLatticeShift b.1 b.2))
    have h2 : AdalyFormal.Balaban.RMapLipschitz.frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ δ0 :=
      (frobNorm_le_frobSupBond U b).trans h
    have h3 : ‖RMap (U b) (f (periodicLatticeShift b.1 b.2)) - f (periodicLatticeShift b.1 b.2)‖
        ≤ 2 * δ0 * ‖f (periodicLatticeShift b.1 b.2)‖ := by
      refine h1.trans ?_
      gcongr
    have h4 := pow_le_pow_left₀ (norm_nonneg _) h3 2
    nlinarith [h4]
  rw [PiLp.norm_sq_eq_of_L2]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun b _ => hp b)
  rw [← Finset.mul_sum] at hs
  have hh := AdalyFormal.Balaban.DeltaPrimeBound.sum_lam_head_sq_eq (fun x : PeriodicLatticeSite L => f x)
  rw [hh] at hs
  unfold siteEnergy at hs
  rw [norm_sq_site]
  nlinarith [hs]


theorem Ns_one (f : PeriodicLatticeSite L → SuTwo) : Ns 1 f ^ 2 = ∑ x, ‖f x‖ ^ 2 := by
  rw [Ns_sq]
  have : CoarseLattice L 1 = Finset.univ := by
    ext x; simp [CoarseLattice, Nat.mod_one]
  rw [this]
  simp

theorem ajSeq_ge (ell k : ℕ) (hell : 2 ≤ ell) {a : ℝ} (ha : 0 < a) : (3 / 4 : ℝ) * a ≤ ajSeq a ell k := by
  have hℓ : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hd0 : 0 < a / ((ell : ℝ) * ell) := by positivity
  have hdl : a / ((ell : ℝ) * ell) ≤ a / 4 := by
    apply div_le_div_of_nonneg_left ha.le (by norm_num)
    nlinarith
  by_cases hk : k = 0
  · subst hk
    simp [ajSeq]
    linarith
  · have h := (AdalyFormal.Balaban.ConstantA.aSeqAux_invariant a (a / ((ell : ℝ) * ell)) ha hd0
      (by linarith)) (k - 1)
    have : ajSeq a ell k = AdalyFormal.Balaban.ConstantA.aSeq a (ell : ℝ) (k - 1) := by
      simp [ajSeq, hk]
    rw [this]
    unfold AdalyFormal.Balaban.ConstantA.aSeq
    linarith [h.1]


/-- **NESTED SITE COERCIVITY (genuine R2 object, full `k`-level tower, whole torus).**
Hypotheses: `ell ≥ 2`, the stride-`ell^k` blocks tile the torus, `frobSupBond U ≤ α/ell^k`, and a bound
`frobSupBond (Ū^i) ≤ δ_i` for the background tower on levels `i < k`, `Σ_{i<k} 6(ell-1)δ_i ≤ E`.
Conclusion (scaled form, `n = ell^k`):
`(1 − 72α² − 4E²)‖f‖² ≤ max(6, 16/(3a)) · n² · ⟨f, Δ'_a(U) f⟩`. -/
theorem site_coercive_nested (ell k : ℕ) (hell : 2 ≤ ell) (hdvd : ∀ μ, ell ^ k ∣ L μ + 1) (U : Cfg L)
    (a : ℝ) (ha : 0 < a) (α E : ℝ) (hU : frobSupBond U ≤ α / (ell : ℝ) ^ k) (δ : ℕ → ℝ)
    (hδ : ∀ i, i < k → frobSupBond (bgTower (fullGeom L ell k) U i) ≤ δ i)
    (hE : ∑ i ∈ Finset.range k, 6 * ((ell : ℝ) - 1) * δ i ≤ E) (f : SiteL2 L) :
    (1 - 72 * α ^ 2 - 4 * E ^ 2) * ‖f‖ ^ 2
      ≤ max 6 (16 / (3 * a)) * ((ell : ℝ) ^ k) ^ 2 * ⟪f, DelpA (fullGeom L ell k) U a f⟫ := by
  have hell0 : 0 < ell := by omega
  have hellR : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  set n : ℝ := (ell : ℝ) ^ k with hn
  have hnpos : 0 < n := by positivity
  have hnat : 0 < ell ^ k := pow_pos hell0 k
  have hncast : (((ell ^ k : ℕ)) : ℝ) = n := by rw [hn]; push_cast; rfl
  set g : PeriodicLatticeSite L → SuTwo := WithLp.ofLp f with hg
  set G := fullGeom L ell k with hG
  set Q : PeriodicLatticeSite L → SuTwo := Qcomposite (bgTower G U) ell k g with hQ
  set F : PeriodicLatticeSite L → SuTwo := Qcomposite (fun _ => trivialU L) ell k g with hF
  have hr : Ns 1 g = ‖f‖ := by
    have h := Ns_one g
    rw [← norm_sq_site f] at h
    exact (pow_left_inj₀ (Ns_nonneg 1 g) (norm_nonneg f) two_ne_zero).mp h
  -- telescoping
  have tel := Ns_telescope ell hell0 (bgTower G U) δ k hδ g k le_rfl
  rw [hr] at tel
  have hEnn : 0 ≤ E := by
    refine le_trans ?_ hE
    refine Finset.sum_nonneg (fun i hi => ?_)
    have hδi : 0 ≤ δ i := le_trans (by
        unfold frobSupBond
        exact (Finset.le_sup'_iff _).mpr ⟨(0, 0), Finset.mem_univ _, AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _⟩)
      (hδ i (Finset.mem_range.mp hi))
    have : (0 : ℝ) ≤ (ell : ℝ) - 1 := by linarith
    positivity
  have hQF : Ns (ell ^ k) (Q - F) ≤ E * ‖f‖ :=
    le_trans tel (mul_le_mul_of_nonneg_right hE (norm_nonneg f))
  have hFQ : Ns (ell ^ k) F ≤ Ns (ell ^ k) Q + E * ‖f‖ := by
    have h1 : F = Q - (Q - F) := by abel
    calc Ns (ell ^ k) F = Ns (ell ^ k) (Q - (Q - F)) := by rw [← h1]
      _ ≤ Ns (ell ^ k) Q + Ns (ell ^ k) (Q - F) := Ns_sub_le _ _ _
      _ ≤ _ := by linarith
  -- flat Poincare
  have vgb := HConstruction.SectBAstra.vector_graph_bound (L := L) (ell ^ k) hnat hdvd (fun x => f x)
  rw [hncast] at vgb
  have hflat : ∑ y ∈ CoarseLattice L (ell ^ k), ‖(1 / n ^ 3) • ∑ x ∈ blockOf y (ell ^ k), f x‖ ^ 2
      = ∑ y ∈ CoarseLattice L (ell ^ k), ‖F y‖ ^ 2 := by
    refine Finset.sum_congr rfl (fun y hy => ?_)
    have := Qflat_eq_blockMean ell hell0 g k y hy
    rw [hF, this, hncast]
  rw [hflat, sum_flat_eq, ← norm_sq_site f] at vgb
  have hFsq : n ^ 3 * ∑ y ∈ CoarseLattice L (ell ^ k), ‖F y‖ ^ 2 = Ns (ell ^ k) F ^ 2 := by
    rw [Ns_sq, hncast]
  -- drift of the gradient
  have hD := gradL2_drift U hU f
  have hDtri : ‖gradL2 (trivialU L) f‖ ^ 2 ≤ 2 * ‖gradL2 U f‖ ^ 2 + 2 * (12 * (α / n) ^ 2 * ‖f‖ ^ 2) := by
    have h1 : ‖gradL2 (trivialU L) f‖ ≤ ‖gradL2 U f‖ + ‖gradL2 U f - gradL2 (trivialU L) f‖ := by
      have := norm_sub_le (gradL2 U f) (gradL2 U f - gradL2 (trivialU L) f)
      simpa using this
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖gradL2 U f‖ - ‖gradL2 U f - gradL2 (trivialU L) f‖)]
  -- mass identity
  have hid := inner_DelpA_full ell k U a f
  have hq : ∑ y ∈ CoarseLattice L (ell ^ k), ‖Q y‖ ^ 2 * n ^ 3 = Ns (ell ^ k) Q ^ 2 := by
    rw [Ns_sq, hncast, ← Finset.sum_mul]; ring
  have hak := ajSeq_ge ell k hell ha
  -- assemble
  have hNF : 0 ≤ Ns (ell ^ k) F := Ns_nonneg _ _
  have hNQ : 0 ≤ Ns (ell ^ k) Q := Ns_nonneg _ _
  have hFsq2 : Ns (ell ^ k) F ^ 2 ≤ 2 * Ns (ell ^ k) Q ^ 2 + 2 * (E ^ 2 * ‖f‖ ^ 2) := by
    have h := pow_le_pow_left₀ hNF hFQ 2
    nlinarith [sq_nonneg (Ns (ell ^ k) Q - E * ‖f‖)]
  have hcancel : n ^ 2 * (12 * (α / n) ^ 2 * ‖f‖ ^ 2) = 12 * α ^ 2 * ‖f‖ ^ 2 := by
    field_simp
  have h3 : ‖f‖ ^ 2 ≤ 6 * (n ^ 2 * ‖gradL2 U f‖ ^ 2) + 72 * α ^ 2 * ‖f‖ ^ 2
      + 4 * Ns (ell ^ k) Q ^ 2 + 4 * (E ^ 2 * ‖f‖ ^ 2) := by
    have e1 : 3 * (n : ℝ) ^ 2 * ‖gradL2 (trivialU L) f‖ ^ 2
        ≤ 3 * n ^ 2 * (2 * ‖gradL2 U f‖ ^ 2 + 2 * (12 * (α / n) ^ 2 * ‖f‖ ^ 2)) := by
      gcongr
    have e2 : 3 * (n : ℝ) ^ 2 * (2 * ‖gradL2 U f‖ ^ 2 + 2 * (12 * (α / n) ^ 2 * ‖f‖ ^ 2))
        = 6 * (n ^ 2 * ‖gradL2 U f‖ ^ 2) + 6 * (n ^ 2 * (12 * (α / n) ^ 2 * ‖f‖ ^ 2)) := by ring
    rw [hcancel] at e2
    nlinarith [vgb, hFsq, hFsq2, e1, e2]
  have hmass : n ^ 2 * ⟪f, DelpA G U a f⟫
      = n ^ 2 * ‖gradL2 U f‖ ^ 2 + ajSeq a ell k * Ns (ell ^ k) Q ^ 2 := by
    have hid' : ⟪f, DelpA G U a f⟫
        = ‖gradL2 U f‖ ^ 2 + ajSeq a ell k * n * ∑ y ∈ CoarseLattice L (ell ^ k), ‖Q y‖ ^ 2 := hid
    have hNsQ : Ns (ell ^ k) Q ^ 2 = n ^ 3 * ∑ y ∈ CoarseLattice L (ell ^ k), ‖Q y‖ ^ 2 := by
      rw [Ns_sq, hncast]
    rw [hid', hNsQ]
    ring
  have hm1 : (6 : ℝ) ≤ max 6 (16 / (3 * a)) := le_max_left _ _
  have hm2 : 16 / (3 * a) ≤ max 6 (16 / (3 * a)) := le_max_right _ _
  have h4 : 4 ≤ max 6 (16 / (3 * a)) * ajSeq a ell k := by
    have : 4 ≤ (16 / (3 * a)) * ((3 / 4 : ℝ) * a) := by
      field_simp; norm_num
    calc (4 : ℝ) ≤ (16 / (3 * a)) * ((3 / 4 : ℝ) * a) := this
      _ ≤ max 6 (16 / (3 * a)) * ajSeq a ell k := by
          apply mul_le_mul hm2 hak (by positivity) (by linarith)
  have hDU : 0 ≤ n ^ 2 * ‖gradL2 U f‖ ^ 2 := by positivity
  have hNQ2 : 0 ≤ Ns (ell ^ k) Q ^ 2 := sq_nonneg _
  rw [mul_assoc, hmass]
  nlinarith [mul_le_mul_of_nonneg_left hm1 hDU, mul_le_mul_of_nonneg_right h4 hNQ2]

end AdalyFormal.SiteCoercivity
