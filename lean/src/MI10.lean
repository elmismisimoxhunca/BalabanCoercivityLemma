import MI9

/-!
# MI10 -- the partition oscillates by `O(1/(κM))` across a constraint block; the commutator of `Q'` (M1 lane E)

* `hvec`, `hvec_dist_sq`, `hvec_path` : the partition as a point of `ℓ²(p)` and telescoping along a path;
  `gammaPath_length_le` : the staircase of a block has `≤ 3(n − 1)` steps;  `hfam`;
* `osc_block` : for a constraint row `q = (j, y)` and `x` in its block, `Σ_p (h_p y − h_p x)² ≤ 9 KG`;
* `ypMul` (`ypMul_apply`) : multiplication of padded rows by `h(rowSite ·)`;
* `cQ_row`, `cQ_pad`, `cQ_sum` : `Σ_p ‖ℓ^{strat} (h_p Q' f − Q' (h_p f))‖² ≤ 9 a KG ‖f‖²`
  (the `Q'*` commutator `cQs_sum` is in MI11).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.M1IMS

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer
open AdalyFormal.M1Site
open AdalyFormal.StatementLane (Tower Admissible bigSide)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap BondFnL2)
open AdalyFormal.Balaban.TowerLawCov (coarsePathEndpoint coarseGammaPath coarseStraightSegment coarseCoordSteps)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)

variable {L : PeriodicLatticeExtent}

/-! ## 0. distance in `ℓ²(p)` along paths -/

section path
variable {ι : Type*} [Fintype ι]

/-- the partition as a point of `ℓ²(ι)`. -/
noncomputable def hvec (h : ι → PeriodicLatticeSite L → ℝ) (x : PeriodicLatticeSite L) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => h i x)

theorem hvec_dist_sq (h : ι → PeriodicLatticeSite L → ℝ) (x y : PeriodicLatticeSite L) :
    dist (hvec h x) (hvec h y) ^ 2 = ∑ i, (h i x - h i y) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Real.dist_eq, sq_abs]; rfl

/-- telescoping along a path whose steps stay in `B`. -/
theorem hvec_path (h : ι → PeriodicLatticeSite L → ℝ) (B : Set (PeriodicLatticeSite L)) (s0 : ℝ)
    (hstep : ∀ z ∈ B, ∀ μ : Fin 3, periodicLatticeShift z μ ∈ B →
      dist (hvec h z) (hvec h (periodicLatticeShift z μ)) ≤ s0) :
    ∀ (p : List (Fin 3)) (y : PeriodicLatticeSite L), PathIn2 B B 1 y p →
      dist (hvec h y) (hvec h (coarsePathEndpoint 1 y p)) ≤ p.length * s0 := by
  intro p
  induction p with
  | nil => intro y _; simp [coarsePathEndpoint]
  | cons μ rest ih =>
    intro y hp
    obtain ⟨hyB, hsB, hrest⟩ := hp
    have e : coarsePathEndpoint 1 y (μ :: rest) = coarsePathEndpoint 1 (coarseShift y 1 μ) rest := rfl
    rw [e]
    have h1 := hstep y hyB μ hsB
    have h2 := ih (coarseShift y 1 μ) hrest
    have h3 := dist_triangle (hvec h y) (hvec h (coarseShift y 1 μ)) (hvec h (coarsePathEndpoint 1 (coarseShift y 1 μ) rest))
    rw [List.length_cons, Nat.cast_add, Nat.cast_one]
    have : coarseShift y 1 μ = periodicLatticeShift y μ := rfl
    rw [this] at h2 h3 ⊢
    linarith

end path

/-- the staircase from `y` to `x` in a block of side `n` has at most `3(n−1)` unit steps. -/
theorem gammaPath_length_le {y x : PeriodicLatticeSite L} {n : ℕ} (hx : x ∈ blockOf y n) :
    (coarseGammaPath 1 y x).length ≤ 3 * (n - 1) := by
  rw [mem_blockOf] at hx
  have hb : ∀ μ : Fin 3, ((x μ) - (y μ)).val ≤ n - 1 := by
    intro μ
    rw [Fin.sub_val_of_le (Fin.le_def.mpr (hx μ).1)]
    have := (hx μ).2; omega
  unfold coarseGammaPath coarseStraightSegment coarseCoordSteps
  simp only [List.length_append, List.length_replicate, Nat.div_one]
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have e1 : (Function.update y 2 (x 2)) 1 = y 1 := Function.update_of_ne h21.symm _ _
  have e0 : (Function.update (Function.update y 2 (x 2)) 1 (x 1)) 0 = y 0 := by
    rw [Function.update_of_ne h10.symm, Function.update_of_ne h20.symm]
  rw [e1, e0]
  have := hb 0; have := hb 1; have := hb 2
  omega

/-- the partition family as a function of the index. -/
noncomputable def hfam {Lf : PeriodicLatticeExtent} (ell M k κ c : ℕ) (S : Tower Lf) :
    Fin (k + 1) × PeriodicLatticeSite Lf → PeriodicLatticeSite Lf → ℝ :=
  fun p => AdalyFormal.M1.hpart ell M k κ c S p

/-! ## 1. oscillation of the partition across a constraint block -/

section osc
variable {Lf : PeriodicLatticeExtent} {ell M R k κ c : ℕ} {S : Tower Lf}
  (hS : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M) (hell : 2 ≤ ell) (hR1 : 1 ≤ R)
  (hR : (c + 3) * κ * ell ≤ R) (hc : 5 ≤ c)
include hS hκ hM hell hR1 hR hc

theorem osc_block (q : QIdx (geomOf ell k S)) {x : PeriodicLatticeSite Lf}
    (hx : x ∈ blockOf (yq q) (ell ^ jq q)) :
    ∑ p, (AdalyFormal.M1.hpart ell M k κ c S p (yq q) - AdalyFormal.M1.hpart ell M k κ c S p x) ^ 2
      ≤ 9 * KG ell M κ c := by
  have hell0 : 0 < ell := by omega
  have hP := properTower_geomOf hell0 hS
  have hdvd := hdvd_of_admissible hS
  have hj : jq q ≤ k := by have := jq_le q; exact this
  have hy : yq q ∈ (geomOf ell k S).Lam (jq q) := yq_mem q
  have hlr : (0 : ℝ) < (ell : ℝ) ^ jq q := by have : (0 : ℝ) < ell := (by exact_mod_cast hell0); positivity
  -- step bound inside the block
  have hstep : ∀ z ∈ (↑(blockOf (yq q) (ell ^ jq q)) : Set (PeriodicLatticeSite Lf)), ∀ μ : Fin 3,
      periodicLatticeShift z μ ∈ (↑(blockOf (yq q) (ell ^ jq q)) : Set (PeriodicLatticeSite Lf)) →
      dist (hvec (hfam ell M k κ c S) z) (hvec (hfam ell M k κ c S) (periodicLatticeShift z μ))
        ≤ Real.sqrt (KG ell M κ c) / (ell : ℝ) ^ jq q := by
    intro z hz μ hz'
    have hz0 : z ∈ S.Om 0 := block_Om0 hP q (Finset.mem_coe.mp hz)
    have hz0' : periodicLatticeShift z μ ∈ S.Om 0 := block_Om0 hP q (Finset.mem_coe.mp hz')
    have hs := hpart_step_w hS hκ hM hell hR1 hR hc hz0 μ hz0'
    rw [stratG_eq hP hj hy (Finset.mem_coe.mp hz)] at hs
    have hsq := hvec_dist_sq (hfam ell M k κ c S) z (periodicLatticeShift z μ)
    have hd0 := dist_nonneg (x := hvec (hfam ell M k κ c S) z) (y := hvec (hfam ell M k κ c S) (periodicLatticeShift z μ))
    rw [le_div_iff₀ hlr]
    have h1 : (dist (hvec (hfam ell M k κ c S) z) (hvec (hfam ell M k κ c S) (periodicLatticeShift z μ))
        * (ell : ℝ) ^ jq q) ^ 2 ≤ KG ell M κ c := by
      rw [mul_pow, hsq, mul_comm]; exact hs
    calc dist (hvec (hfam ell M k κ c S) z) (hvec (hfam ell M k κ c S) (periodicLatticeShift z μ)) * (ell : ℝ) ^ jq q
        = Real.sqrt ((dist (hvec (hfam ell M k κ c S) z) (hvec (hfam ell M k κ c S) (periodicLatticeShift z μ))
            * (ell : ℝ) ^ jq q) ^ 2) := by rw [Real.sqrt_sq (by positivity)]
      _ ≤ Real.sqrt (KG ell M κ c) := Real.sqrt_le_sqrt h1
  -- the staircase
  have hfit : ∀ μ, (yq q μ).val + 1 * ell ^ jq q ≤ Lf μ + 1 := by
    intro μ; rw [one_mul]; exact fit_q hP hdvd hell0 q μ
  have hxs : x ∈ AdalyFormal.Balaban.QjComposite.stepBlockOf (yq q) 1 (ell ^ jq q) := by
    rw [AdalyFormal.Balaban.QjComposite.stepBlockOf_one]; exact hx
  have hpath := gammaPath_PathIn (show 0 < 1 by omega) hfit hxs
  rw [one_mul] at hpath
  have hend : coarsePathEndpoint 1 (yq q) (coarseGammaPath 1 (yq q) x) = x := by
    have hxm := AdalyFormal.Balaban.QjComposite.mem_stepBlockOf.mp hxs
    exact AdalyFormal.Balaban.QjComposite.coarsePathEndpoint_coarseGammaPath (fun μ => ⟨(hxm μ).1, (hxm μ).2.2⟩)
  have hpath2 := PathIn2_of_PathIn (↑(blockOf (yq q) (ell ^ jq q)) : Set (PeriodicLatticeSite Lf))
    (↑(blockOf (yq q) (ell ^ jq q))) 1 (le_refl _) (coarseGammaPath 1 (yq q) x) (yq q) hpath
    (by rw [hend]; exact Finset.mem_coe.mpr hx)
  have hd := hvec_path (hfam ell M k κ c S) _ _ hstep _ (yq q) hpath2
  rw [hend] at hd
  have hlen := gammaPath_length_le hx
  have hlenr : ((coarseGammaPath 1 (yq q) x).length : ℝ) ≤ 3 * (ell : ℝ) ^ jq q := by
    have : ((coarseGammaPath 1 (yq q) x).length : ℝ) ≤ ((3 * (ell ^ jq q - 1) : ℕ) : ℝ) := by exact_mod_cast hlen
    refine this.trans ?_
    have h1 : 1 ≤ ell ^ jq q := Nat.one_le_pow _ _ hell0
    rw [Nat.cast_mul, Nat.cast_sub h1]; push_cast
    linarith
  have hK0 := KG_nonneg ell M κ c
  have hdist : dist (hvec (hfam ell M k κ c S) (yq q)) (hvec (hfam ell M k κ c S) x) ≤ 3 * Real.sqrt (KG ell M κ c) := by
    refine hd.trans ?_
    calc ((coarseGammaPath 1 (yq q) x).length : ℝ) * (Real.sqrt (KG ell M κ c) / (ell : ℝ) ^ jq q)
        ≤ (3 * (ell : ℝ) ^ jq q) * (Real.sqrt (KG ell M κ c) / (ell : ℝ) ^ jq q) :=
          mul_le_mul_of_nonneg_right hlenr (by positivity)
      _ = 3 * Real.sqrt (KG ell M κ c) := by field_simp
  have hsq := hvec_dist_sq (hfam ell M k κ c S) (yq q) x
  have hd0 := dist_nonneg (x := hvec (hfam ell M k κ c S) (yq q)) (y := hvec (hfam ell M k κ c S) x)
  have hfin : ∑ p, (hfam ell M k κ c S p (yq q) - hfam ell M k κ c S p x) ^ 2 ≤ 9 * KG ell M κ c := by
    rw [← hsq]
    calc dist (hvec (hfam ell M k κ c S) (yq q)) (hvec (hfam ell M k κ c S) x) ^ 2
        ≤ (3 * Real.sqrt (KG ell M κ c)) ^ 2 := pow_le_pow_left₀ hd0 hdist 2
      _ = 9 * KG ell M κ c := by rw [mul_pow, Real.sq_sqrt hK0]; ring
  exact hfin

end osc

/-! ## 2. row multiplication and the `Q'` commutator -/

/-- multiplication of padded rows by `h` at the row's base site. -/
noncomputable def ypMul (G : TowerGeom L) (h : PeriodicLatticeSite L → ℝ) : YP G →L[ℝ] YP G :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (fun p => h (rowSite p) • v p)
      map_add' := fun v w => by refine PiLp.ext (fun p => ?_); simp [smul_add]
      map_smul' := fun c v => by
        refine PiLp.ext (fun p => ?_)
        simp only [PiLp.smul_apply, RingHom.id_apply]
        exact smul_comm _ _ _ }

theorem ypMul_apply (G : TowerGeom L) (h : PeriodicLatticeSite L → ℝ) (v : YP G) (p : PIdx G) :
    ypMul G h v p = h (rowSite p) • v p := rfl

section comm
variable {Lf : PeriodicLatticeExtent} {ell M R k κ c : ℕ} {S : Tower Lf}
  (hS : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M) (hell : 2 ≤ ell) (hR1 : 1 ≤ R)
  (hR : (c + 3) * κ * ell ≤ R) (hc : 5 ≤ c)
include hS hκ hM hell hR1 hR hc

/-- row form of the `Q'` commutator. -/
theorem cQ_row (U : Cfg Lf) (a : ℝ) (h : PeriodicLatticeSite Lf → ℝ) (f : SiteL2 Lf) (q : QIdx (geomOf ell k S)) :
    (ypMul (geomOf ell k S) h (QpP (geomOf ell k S) U a f) - QpP (geomOf ell k S) U a (siteMul h f)) (Sum.inl q)
      = Real.sqrt (wq (geomOf ell k S) a (jq q)) •
          Qlev (geomOf ell k S) U (jq q) (yq q) (siteMul (fun x => h (yq q) - h x) (siteMask (geomOf ell k S).Om0 f)) := by
  rw [PiLp.sub_apply, ypMul_apply, QpP_inl, QpP_inl, siteMask_siteMul, smul_smul, mul_comm, ← smul_smul, ← smul_sub,
    ← map_smul, ← map_sub]
  congr 2
  refine PiLp.ext (fun x => ?_)
  rw [PiLp.sub_apply, PiLp.smul_apply, siteMul_apply, siteMul_apply, sub_smul]
  rfl

theorem cQ_pad (U : Cfg Lf) (a : ℝ) (h : PeriodicLatticeSite Lf → ℝ) (f : SiteL2 Lf) (x : OffIdx (geomOf ell k S)) :
    (ypMul (geomOf ell k S) h (QpP (geomOf ell k S) U a f) - QpP (geomOf ell k S) U a (siteMul h f)) (Sum.inr x) = 0 := by
  rw [PiLp.sub_apply, ypMul_apply, QpP_inr, QpP_inr, siteMul_apply]
  show h x.1 • f x.1 - h x.1 • f x.1 = 0
  exact sub_self _

/-- **(L3) the `Q'` commutator**: `Σ_p ‖ℓ^{strat}(h_p Q' f − Q'(h_p f))‖² ≤ 9 a KG ‖f‖²`. -/
theorem cQ_sum (U : Cfg Lf) (a : ℝ) (ha : 0 < a) (f : SiteL2 Lf) :
    ∑ p, ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S))
        (ypMul (geomOf ell k S) (AdalyFormal.M1.hpart ell M k κ c S p) (QpP (geomOf ell k S) U a f)
          - QpP (geomOf ell k S) U a (siteMul (AdalyFormal.M1.hpart ell M k κ c S p) f))‖ ^ 2
      ≤ 9 * a * KG ell M κ c * ‖f‖ ^ 2 := by
  classical
  set G := geomOf ell k S
  have hell0 : 0 < ell := by omega
  have hP := properTower_geomOf hell0 hS
  have hellG : 0 < G.ell := hell0
  simp only [PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type]
  rw [Finset.sum_add_distrib]
  have hpad : ∀ p, ∑ x : OffIdx G, ‖(ypWt G (sigG G) (ypMul G (AdalyFormal.M1.hpart ell M k κ c S p) (QpP G U a f) - QpP G U a (siteMul (AdalyFormal.M1.hpart ell M k κ c S p) f)))
      (Sum.inr x)‖ ^ 2 = 0 := by
    intro p
    refine Finset.sum_eq_zero (fun x _ => ?_)
    rw [ypWt_apply, cQ_pad hS hκ hM hell hR1 hR hc, smul_zero, norm_zero]; simp
  simp only [hpad, Finset.sum_const_zero, add_zero]
  rw [Finset.sum_comm]
  have hrow : ∀ q : QIdx G, ∑ p, ‖(ypWt G (sigG G) (ypMul G (AdalyFormal.M1.hpart ell M k κ c S p) (QpP G U a f) - QpP G U a (siteMul (AdalyFormal.M1.hpart ell M k κ c S p) f)))
      (Sum.inl q)‖ ^ 2 ≤ 9 * a * KG ell M κ c * ∑ x ∈ blockOf (yq q) (ell ^ jq q), ‖f x‖ ^ 2 := by
    intro q
    have hj : (jq q) ≤ k := by have := jq_le q; exact this
    have hy : (yq q) ∈ G.Lam (jq q) := yq_mem q
    have hw0 : 0 ≤ wq G a (jq q) := (wq_pos hell hP a (jq q) ha).le
    have hwq : wq G a (jq q) ≤ a * (ell : ℝ) ^ (jq q) := by
      unfold wq
      have := ajSeq_le ell (jq q) hell ha
      have h0 : (0 : ℝ) ≤ (ell : ℝ) ^ (jq q) := by positivity
      show ajSeq a ell (jq q) * (ell : ℝ) ^ (jq q) ≤ _
      nlinarith
    have e : ∀ p, ‖(ypWt G (sigG G) (ypMul G (AdalyFormal.M1.hpart ell M k κ c S p) (QpP G U a f) - QpP G U a (siteMul (AdalyFormal.M1.hpart ell M k κ c S p) f))) (Sum.inl q)‖ ^ 2
        = ((ell : ℝ) ^ (jq q)) ^ 2 * wq G a (jq q) *
          ‖Qlev G U (jq q) (yq q) (siteMul (fun x => AdalyFormal.M1.hpart ell M k κ c S p (yq q) - AdalyFormal.M1.hpart ell M k κ c S p x) (siteMask G.Om0 f))‖ ^ 2 := by
      intro p
      rw [ypWt_apply, cQ_row hS hκ hM hell hR1 hR hc, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, mul_pow, Real.sq_sqrt hw0]
      show (Real.exp (sigG G (yq q))) ^ 2 * _ = _
      rw [exp_sig G hellG]
      have hsy : stratG G (yq q) = (jq q) := by
        refine stratG_eq hP hj hy ?_
        rw [mem_blockOf]; intro μ; exact ⟨le_rfl, by have := Nat.one_le_pow (jq q) ell hell0; omega⟩
      rw [hsy, show ((G.ell : ℕ) : ℝ) = (ell : ℝ) from rfl]; ring
    simp only [e]
    have hQ : ∀ p, ‖Qlev G U (jq q) (yq q) (siteMul (fun x => AdalyFormal.M1.hpart ell M k κ c S p (yq q) - AdalyFormal.M1.hpart ell M k κ c S p x) (siteMask G.Om0 f))‖ ^ 2
        ≤ ((1 / (ell : ℝ) ^ 3) ^ (jq q)) * ∑ x ∈ blockOf (yq q) (ell ^ (jq q)), (AdalyFormal.M1.hpart ell M k κ c S p (yq q) - AdalyFormal.M1.hpart ell M k κ c S p x) ^ 2 * ‖f x‖ ^ 2 := by
      intro p
      rw [Qlev_apply]
      have h1 := Qcomposite_sq_le (bgTower G U) G.ell hellG (jq q)
        (WithLp.ofLp (siteMul (fun x => AdalyFormal.M1.hpart ell M k κ c S p (yq q) - AdalyFormal.M1.hpart ell M k κ c S p x) (siteMask G.Om0 f))) (yq q)
      refine h1.trans (le_of_eq ?_)
      show ((1 / (ell : ℝ) ^ 3) ^ (jq q)) * ∑ x ∈ boxF (yq q) (ell ^ (jq q)), _ = _
      rw [boxF_eq_blockOf]
      congr 1
      refine Finset.sum_congr rfl (fun x hx => ?_)
      have hx0 : x ∈ G.Om0 := block_Om0 hP q hx
      show ‖siteMul (fun x => AdalyFormal.M1.hpart ell M k κ c S p (yq q) - AdalyFormal.M1.hpart ell M k κ c S p x) (siteMask G.Om0 f) x‖ ^ 2 = _
      rw [siteMul_apply, siteMask_on _ _ _ hx0, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have hosc : ∀ x ∈ blockOf (yq q) (ell ^ (jq q)), ∑ p, (AdalyFormal.M1.hpart ell M k κ c S p (yq q) - AdalyFormal.M1.hpart ell M k κ c S p x) ^ 2 ≤ 9 * KG ell M κ c :=
      fun x hx => osc_block hS hκ hM hell hR1 hR hc q hx
    have hK0 := KG_nonneg ell M κ c
    have hpow : ((ell : ℝ) ^ (jq q)) ^ 2 * (a * (ell : ℝ) ^ (jq q)) * ((1 / (ell : ℝ) ^ 3) ^ (jq q)) = a := by
      have : (0 : ℝ) < (ell : ℝ) ^ (jq q) := by have : (0:ℝ) < ell := (by exact_mod_cast hell0); positivity
      rw [one_div, inv_pow, ← pow_mul]
      field_simp; ring
    calc ∑ p, ((ell : ℝ) ^ (jq q)) ^ 2 * wq G a (jq q) * ‖Qlev G U (jq q) (yq q) (siteMul (fun x => AdalyFormal.M1.hpart ell M k κ c S p (yq q) - AdalyFormal.M1.hpart ell M k κ c S p x) (siteMask G.Om0 f))‖ ^ 2
        ≤ ∑ p, ((ell : ℝ) ^ (jq q)) ^ 2 * (a * (ell : ℝ) ^ (jq q)) *
            (((1 / (ell : ℝ) ^ 3) ^ (jq q)) * ∑ x ∈ blockOf (yq q) (ell ^ (jq q)), (AdalyFormal.M1.hpart ell M k κ c S p (yq q) - AdalyFormal.M1.hpart ell M k κ c S p x) ^ 2 * ‖f x‖ ^ 2) := by
          refine Finset.sum_le_sum (fun p _ => ?_)
          exact mul_le_mul (mul_le_mul_of_nonneg_left hwq (by positivity)) (hQ p) (sq_nonneg _) (by positivity)
      _ = a * ∑ x ∈ blockOf (yq q) (ell ^ (jq q)), (∑ p, (AdalyFormal.M1.hpart ell M k κ c S p (yq q) - AdalyFormal.M1.hpart ell M k κ c S p x) ^ 2) * ‖f x‖ ^ 2 := by
          have hcoef : ∀ T : ℝ, ((ell : ℝ) ^ (jq q)) ^ 2 * (a * (ell : ℝ) ^ (jq q)) * (((1 / (ell : ℝ) ^ 3) ^ (jq q)) * T)
              = a * T := fun T => by
            calc ((ell : ℝ) ^ (jq q)) ^ 2 * (a * (ell : ℝ) ^ (jq q)) * (((1 / (ell : ℝ) ^ 3) ^ (jq q)) * T)
                = (((ell : ℝ) ^ (jq q)) ^ 2 * (a * (ell : ℝ) ^ (jq q)) * ((1 / (ell : ℝ) ^ 3) ^ (jq q))) * T := by ring
              _ = a * T := by rw [hpow]
          simp only [hcoef]
          rw [← Finset.mul_sum, Finset.sum_comm]
          congr 1
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [Finset.sum_mul]
      _ ≤ a * ∑ x ∈ blockOf (yq q) (ell ^ (jq q)), 9 * KG ell M κ c * ‖f x‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x hx => ?_)) ha.le
          exact mul_le_mul_of_nonneg_right (hosc x hx) (sq_nonneg _)
      _ = 9 * a * KG ell M κ c * ∑ x ∈ blockOf (yq q) (ell ^ (jq q)), ‖f x‖ ^ 2 := by
          rw [← Finset.mul_sum]; ring
  calc ∑ q : QIdx G, ∑ p, ‖(ypWt G (sigG G) (ypMul G (AdalyFormal.M1.hpart ell M k κ c S p) (QpP G U a f) - QpP G U a (siteMul (AdalyFormal.M1.hpart ell M k κ c S p) f))) (Sum.inl q)‖ ^ 2
      ≤ ∑ q : QIdx G, 9 * a * KG ell M κ c * ∑ x ∈ blockOf (yq q) (ell ^ jq q), ‖f x‖ ^ 2 :=
        Finset.sum_le_sum (fun q _ => hrow q)
    _ = 9 * a * KG ell M κ c * ∑ q : QIdx G, ∑ x ∈ blockOf (yq q) (ell ^ jq q), ‖f x‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 9 * a * KG ell M κ c * ‖f‖ ^ 2 := by
        have := KG_nonneg ell M κ c
        exact mul_le_mul_of_nonneg_left (sum_blocks_le hP f) (by positivity)
    _ = 9 * a * KG ell M κ c * ∑ x, ‖f x‖ ^ 2 := by rw [PiLp.norm_sq_eq_of_L2]

end comm

end AdalyFormal.M1IMS

#print axioms AdalyFormal.M1IMS.hvec_dist_sq
#print axioms AdalyFormal.M1IMS.hvec_path
#print axioms AdalyFormal.M1IMS.gammaPath_length_le
#print axioms AdalyFormal.M1IMS.osc_block
#print axioms AdalyFormal.M1IMS.ypMul_apply
#print axioms AdalyFormal.M1IMS.cQ_row
#print axioms AdalyFormal.M1IMS.cQ_pad
#print axioms AdalyFormal.M1IMS.cQ_sum
#print axioms AdalyFormal.M1IMS.hvec
#print axioms AdalyFormal.M1IMS.hfam
#print axioms AdalyFormal.M1IMS.ypMul
