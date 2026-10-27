import MS13
import M1A

/-!
# MI6 -- the RESCALED (hatted) stratified site chain as an instance of the abstract DL10 `SiteHyp` (M1 lane E, 2026-10-13)

`σ(x) = stratG(x) · ln ℓ`, so `e^{σ} = ℓ^{strat}` (= `Ξ⁻¹`).  Hatted operators on the plain spaces:
`D̂ = Dm ∘ e^{σ}`, `Q̂ = QpP ∘ e^{σ}`, `L̂ = D̂*D̂ + Q̂*Q̂ = e^{σ} LP e^{σ}`, `L̂⁻¹ = e^{−σ} LinvP e^{−σ}`.
* `strat_eq_stratG` (GLUE, lane B ↔ lane C): `strat S k x = stratG (geomOf ell k S) x` for every site (Admissible).
* `exp_sig` : `e^{σ x} = ℓ^{stratG x}`;  `stratG_off` : `stratG = 0` off `Ω₀`.
* `Lh_eq` : `L̂ = e^{σ} ∘ LP ∘ e^{σ}`;  `hatCoer` : S1 (`cs · wNormSq f ≤ ⟪f, Δ'_a f⟫`, `cs ≤ 1`) ⇒ `cs ‖f‖² ≤ ⟪f, L̂ f⟫`
  (k-free: the stratified weight is absorbed into the rescaling).
* `ypWt φ`, `ypWP φ` : `e^{φ}` on padded rows (row `(j,y)` at its base point `y`, padding row `x` at `x`).
* `hatD_comm` : `‖(e^{φ} D̂ e^{−φ} − D̂) f‖ ≤ √3 (e^θ − 1) ‖f‖` if `|φ(b₋) − φ(b₊)| ≤ θ/ℓ^{strat b₊}` on bonds with head in `Ω₀`;
* `hatQ_comm` : `‖(e^{φ} Q̂ e^{−φ} − Q̂) f‖ ≤ √a (e^{δ₀} − 1) ‖f‖` if `|φ(y) − φ(x)| ≤ δ₀` on every constraint block.
* `hatSiteHyp` : the DL10 `SiteHyp (SiteL2) (BondFnL2) (YP G)` with `m = 1`, weights `e^{±φ}`.
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

/-! ## 0. glue: lane B's `strat` is lane C's `stratG` -/

section glue
variable {Lf : PeriodicLatticeExtent}

open Classical in
theorem findGreatest_eq_sSup (P : ℕ → Prop) [DecidablePred P] (k : ℕ) :
    Nat.findGreatest P k = sSup {j | j ≤ k ∧ P j} := by
  have hbdd : BddAbove {j | j ≤ k ∧ P j} := ⟨k, fun j hj => hj.1⟩
  apply le_antisymm
  · rcases Nat.eq_zero_or_pos (Nat.findGreatest P k) with h0 | hpos
    · rw [h0]; exact Nat.zero_le _
    · exact le_csSup hbdd ⟨Nat.findGreatest_le k, Nat.findGreatest_of_ne_zero rfl hpos.ne'⟩
  · rcases Set.eq_empty_or_nonempty {j | j ≤ k ∧ P j} with he | hne
    · rw [he, csSup_empty]; exact bot_le
    · have hm := Nat.sSup_mem hne hbdd
      exact Nat.le_findGreatest hm.1 hm.2

/-- **glue**: `AdalyFormal.M1.strat S k x = stratG (geomOf ell k S) x` (every site, admissible tower). -/
theorem strat_eq_stratG {ell M R k : ℕ} (hell : 0 < ell) {S : Tower Lf} (hS : Admissible ell M R k S)
    (x : PeriodicLatticeSite Lf) : AdalyFormal.M1.strat S k x = stratG (geomOf ell k S) x := by
  classical
  rw [stratG_geomOf hell hS x]
  unfold AdalyFormal.M1.strat
  exact findGreatest_eq_sSup _ k

end glue

variable {L : PeriodicLatticeExtent}

/-! ## 1. the stratum weight -/

/-- `σ = stratG · ln ℓ` -/
noncomputable def sigG (G : TowerGeom L) (x : PeriodicLatticeSite L) : ℝ := (stratG G x : ℝ) * Real.log G.ell

theorem exp_sig (G : TowerGeom L) (hell : 0 < G.ell) (x : PeriodicLatticeSite L) :
    Real.exp (sigG G x) = (G.ell : ℝ) ^ stratG G x := by
  unfold sigG
  rw [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast hell)]

theorem stratG_off {G : TowerGeom L} {ell k : ℕ} (hP : ProperTower G ell k) {x : PeriodicLatticeSite L}
    (hx : x ∉ G.Om0) : stratG G x = 0 := by
  unfold stratG
  have he : {j | j ≤ G.k ∧ OmGe G j x} = ∅ := by
    ext j
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    rintro - ⟨i, -, hik, y, hy, hxy⟩
    apply hx
    rw [hP.cover x]
    refine ⟨i, by rw [← hP.k_eq]; exact hik, y, hy, ?_⟩
    rw [mem_blockOf, ← hP.ell_eq]; exact hxy
  rw [he, csSup_empty]; rfl

theorem siteWt_comm (φ χ : PeriodicLatticeSite L → ℝ) (f : SiteL2 L) :
    siteWt φ (siteWt χ f) = siteWt χ (siteWt φ f) := by
  refine PiLp.ext (fun x => ?_)
  rw [siteWt_apply, siteWt_apply, siteWt_apply, siteWt_apply, smul_smul, smul_smul, mul_comm]

theorem siteWt_adjoint (φ : PeriodicLatticeSite L → ℝ) :
    ContinuousLinearMap.adjoint (siteWt φ) = siteWt φ := by
  ext1 f
  refine ext_inner_left ℝ (fun g => ?_)
  rw [ContinuousLinearMap.adjoint_inner_right, siteWt_symm]

/-! ## 2. hatted operators -/

/-- `D̂ = Dm ∘ e^{σ}` -/
noncomputable def Dh (G : TowerGeom L) (U : Cfg L) : SiteL2 L →L[ℝ] BondFnL2 L := Dm G U ∘L siteWt (sigG G)

/-- `Q̂ = QpP ∘ e^{σ}` -/
noncomputable def Qh (G : TowerGeom L) (U : Cfg L) (a : ℝ) : SiteL2 L →L[ℝ] YP G := QpP G U a ∘L siteWt (sigG G)

/-- `L̂⁻¹ = e^{−σ} LinvP e^{−σ}` -/
noncomputable def Linvh (G : TowerGeom L) (U : Cfg L) (a : ℝ) : SiteL2 L →L[ℝ] SiteL2 L :=
  siteWt (-sigG G) ∘L LinvP G U a ∘L siteWt (-sigG G)

theorem Lh_eq (G : TowerGeom L) (U : Cfg L) (a : ℝ) (hw : ∀ j, 0 ≤ wq G a j) :
    ContinuousLinearMap.adjoint (Dh G U) ∘L Dh G U + (1 : ℝ) • (ContinuousLinearMap.adjoint (Qh G U a) ∘L Qh G U a)
      = siteWt (sigG G) ∘L LP G U a ∘L siteWt (sigG G) := by
  ext1 f
  rw [LP_eq_L G U a hw]
  simp only [Dh, Qh, ContinuousLinearMap.adjoint_comp, siteWt_adjoint, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, one_smul, map_add]

theorem Lh_Linvh (G : TowerGeom L) (U : Cfg L) (a : ℝ) (hw : ∀ j, 0 ≤ wq G a j) (hu : IsUnit (LP G U a))
    (x : SiteL2 L) :
    (ContinuousLinearMap.adjoint (Dh G U) ∘L Dh G U + (1 : ℝ) • (ContinuousLinearMap.adjoint (Qh G U a) ∘L Qh G U a))
      (Linvh G U a x) = x := by
  rw [Lh_eq G U a hw]
  simp only [Linvh, ContinuousLinearMap.comp_apply]
  rw [siteWt_neg_cancel, LP_LinvP G U a hu]
  have := siteWt_neg_cancel (sigG G) x
  exact this

theorem Linvh_Lh (G : TowerGeom L) (U : Cfg L) (a : ℝ) (hw : ∀ j, 0 ≤ wq G a j) (hu : IsUnit (LP G U a))
    (x : SiteL2 L) :
    Linvh G U a ((ContinuousLinearMap.adjoint (Dh G U) ∘L Dh G U
      + (1 : ℝ) • (ContinuousLinearMap.adjoint (Qh G U a) ∘L Qh G U a)) x) = x := by
  rw [Lh_eq G U a hw]
  simp only [Linvh, ContinuousLinearMap.comp_apply]
  rw [siteWt_cancel_neg, LinvP_LP G U a hu, siteWt_cancel_neg]

/-- **hatted coercivity from S1**: `cs · wNormSq ≤ ⟪·, Δ'_a ·⟫` with `cs ≤ 1` gives `cs ‖f‖² ≤ ⟪e^σ f, LP e^σ f⟫`. -/
theorem hatCoer {G : TowerGeom L} {ell k : ℕ} (hP : ProperTower G ell k) (hell : 0 < ell) (U : Cfg L) (a cs : ℝ)
    (hcs1 : cs ≤ 1) (hS1 : ∀ f, cs * wNormSq G f ≤ ⟪f, DelpA G U a f⟫) (f : SiteL2 L) :
    cs * ‖f‖ ^ 2 ≤ ⟪siteWt (sigG G) f, LP G U a (siteWt (sigG G) f)⟫ := by
  classical
  have hellG : 0 < G.ell := by rw [hP.ell_eq]; exact hell
  set g := siteWt (sigG G) f with hg
  have hLP : ⟪g, LP G U a g⟫ = ⟪g, DelpA G U a g⟫ + ∑ x : OffIdx G, ⟪g x.1, g x.1⟫ := by
    rw [LP, ContinuousLinearMap.add_apply, inner_add_right, inner_one_sub_mask]
  have hw : wNormSq G g = ∑ x, (if x ∈ G.Om0 then ‖f x‖ ^ 2 else 0) := by
    unfold wNormSq
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hx : x ∈ G.Om0
    · rw [if_pos hx, siteMask_on _ _ _ hx, hg, siteWt_apply, norm_smul, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), exp_sig G hellG]
      have : (0 : ℝ) < (G.ell : ℝ) ^ stratG G x := by
        have : (0 : ℝ) < G.ell := by exact_mod_cast hellG
        positivity
      field_simp
    · rw [if_neg hx, siteMask_off _ _ _ hx]; simp
  have hoff : ∑ x : OffIdx G, ⟪g x.1, g x.1⟫ = ∑ x, (if x ∈ G.Om0 then 0 else ‖f x‖ ^ 2) := by
    have e : ∀ x : OffIdx G, ⟪g x.1, g x.1⟫ = ‖f x.1‖ ^ 2 := by
      intro x
      rw [real_inner_self_eq_norm_sq, hg, siteWt_apply]
      unfold sigG
      rw [stratG_off hP x.2]
      simp
    rw [Finset.sum_congr rfl (fun x _ => e x)]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => x ∈ G.Om0)]
    rw [Finset.sum_ite_of_true (fun x hx => (Finset.mem_filter.mp hx).2),
      Finset.sum_ite_of_false (fun x hx => (Finset.mem_filter.mp hx).2)]
    rw [Finset.sum_const_zero, zero_add]
    exact (Finset.sum_subtype (p := fun x => x ∉ G.Om0) _ (fun x => by simp) (fun x => ‖f x‖ ^ 2)).symm
  have h1 := hS1 g
  rw [hw] at h1
  rw [hLP, hoff]
  have hsplit : ‖f‖ ^ 2 = ∑ x, (if x ∈ G.Om0 then ‖f x‖ ^ 2 else 0) + ∑ x, (if x ∈ G.Om0 then 0 else ‖f x‖ ^ 2) := by
    rw [← Finset.sum_add_distrib, PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    split_ifs <;> simp
  rw [hsplit, mul_add]
  have h2 : cs * ∑ x, (if x ∈ G.Om0 then 0 else ‖f x‖ ^ 2) ≤ ∑ x, (if x ∈ G.Om0 then 0 else ‖f x‖ ^ 2) := by
    have h0 : 0 ≤ ∑ x, (if x ∈ G.Om0 then (0 : ℝ) else ‖f x‖ ^ 2) :=
      Finset.sum_nonneg (fun x _ => by split_ifs <;> positivity)
    by_cases hc : 0 ≤ cs
    · nlinarith
    · push Not at hc; nlinarith
  linarith

/-! ## 3. weights on the padded rows -/

/-- base site of a padded row -/
def rowSite {G : TowerGeom L} : PIdx G → PeriodicLatticeSite L := Sum.elim (fun q => q.1.2) (fun x => x.1)

/-- `e^{φ}` on padded rows -/
noncomputable def ypWt (G : TowerGeom L) (φ : PeriodicLatticeSite L → ℝ) : YP G →L[ℝ] YP G :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (fun p => Real.exp (φ (rowSite p)) • v p)
      map_add' := fun v w => by refine PiLp.ext (fun p => ?_); simp [smul_add]
      map_smul' := fun c v => by
        refine PiLp.ext (fun p => ?_)
        simp only [PiLp.smul_apply, RingHom.id_apply, PiLp.toLp_apply]
        exact smul_comm _ _ _ }

theorem ypWt_apply (G : TowerGeom L) (φ : PeriodicLatticeSite L → ℝ) (v : YP G) (p : PIdx G) :
    ypWt G φ v p = Real.exp (φ (rowSite p)) • v p := rfl

theorem ypWt_neg_cancel (G : TowerGeom L) (φ : PeriodicLatticeSite L → ℝ) (v : YP G) :
    ypWt G φ (ypWt G (-φ) v) = v := by
  refine PiLp.ext (fun p => ?_)
  rw [ypWt_apply, ypWt_apply, smul_smul, ← Real.exp_add]; simp

theorem ypWt_cancel_neg (G : TowerGeom L) (φ : PeriodicLatticeSite L → ℝ) (v : YP G) :
    ypWt G (-φ) (ypWt G φ v) = v := by
  refine PiLp.ext (fun p => ?_)
  rw [ypWt_apply, ypWt_apply, smul_smul, ← Real.exp_add]; simp

theorem ypWt_symm (G : TowerGeom L) (φ : PeriodicLatticeSite L → ℝ) (v w : YP G) :
    ⟪ypWt G φ v, w⟫ = ⟪v, ypWt G φ w⟫ := by
  simp only [PiLp.inner_apply, ypWt_apply, real_inner_smul_left, real_inner_smul_right]

noncomputable def ypWP (G : TowerGeom L) (φ : PeriodicLatticeSite L → ℝ) : WPair (YP G) where
  w := ypWt G φ
  wi := ypWt G (-φ)
  w_wi := ypWt_neg_cancel G φ
  wi_w := ypWt_cancel_neg G φ
  w_sym := ypWt_symm G φ
  wi_sym := ypWt_symm G (-φ)

/-! ## 4. the commutators of the hatted operators -/

/-- **gradient commutator of `D̂`** (stratified Lipschitz weight, head-indexed). -/
theorem hatD_comm {G : TowerGeom L} {ell k : ℕ} (hP : ProperTower G ell k) (hell : 0 < ell) (U : Cfg L)
    (φ : PeriodicLatticeSite L → ℝ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hφ : ∀ b : Bond L, periodicLatticeShift b.1 b.2 ∈ G.Om0 →
      |φ b.1 - φ (periodicLatticeShift b.1 b.2)| ≤ θ / (ell : ℝ) ^ stratG G (periodicLatticeShift b.1 b.2))
    (f : SiteL2 L) :
    ‖(cjp (siteWP φ) (bondWP φ) (Dh G U) - Dh G U) f‖ ≤ Real.sqrt 3 * (Real.exp θ - 1) * ‖f‖ := by
  classical
  have hellG : 0 < G.ell := by rw [hP.ell_eq]; exact hell
  set g := siteMask G.Om0 (siteWt (sigG G) f) with hg
  have he : (cjp (siteWP φ) (bondWP φ) (Dh G U) - Dh G U) f
      = bondWt φ (gradL2 U (siteWt (-φ) g)) - gradL2 U g := by
    rw [ContinuousLinearMap.sub_apply, cjp_apply]
    simp only [Dh, Dm, ContinuousLinearMap.comp_apply]
    show bondWt φ (gradL2 U (siteMask G.Om0 (siteWt (sigG G) (siteWt (-φ) f)))) - _ = _
    rw [siteWt_comm (sigG G) (-φ), ← siteWt_mask]
  rw [he]
  have hpt : ∀ b : Bond L, ‖(bondWt φ (gradL2 U (siteWt (-φ) g)) - gradL2 U g) b‖
      ≤ (Real.exp θ - 1) * ‖f (periodicLatticeShift b.1 b.2)‖ := by
    intro b
    rw [grad_conj_sub, norm_smul, Real.norm_eq_abs, AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap]
    set h := periodicLatticeShift b.1 b.2
    by_cases hh : h ∈ G.Om0
    · rw [hg, siteMask_on _ _ _ hh, siteWt_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        exp_sig G hellG, hP.ell_eq]
      set s := stratG G h
      have hs : (1 : ℝ) ≤ (ell : ℝ) ^ s := one_le_pow₀ (by exact_mod_cast hell)
      have hs0 : (0 : ℝ) < (ell : ℝ) ^ s := by linarith
      have h1 : |Real.exp (φ b.1 - φ h) - 1| ≤ Real.exp (θ / (ell : ℝ) ^ s) - 1 :=
        abs_exp_sub_one_le_of _ _ (hφ b hh)
      have h2 : Real.exp (θ / (ell : ℝ) ^ s) - 1 ≤ (Real.exp θ - 1) / (ell : ℝ) ^ s := by
        have := exp_div_sub_one_le θ hθ (ell ^ s) (Nat.one_le_pow _ _ hell)
        push_cast at this; exact this
      have h3 : |Real.exp (φ b.1 - φ h) - 1| * (ell : ℝ) ^ s ≤ Real.exp θ - 1 := by
        have := mul_le_mul_of_nonneg_right (h1.trans h2) hs0.le
        rwa [div_mul_cancel₀ _ hs0.ne'] at this
      calc |Real.exp (φ b.1 - φ h) - 1| * ((ell : ℝ) ^ s * ‖f h‖)
          = (|Real.exp (φ b.1 - φ h) - 1| * (ell : ℝ) ^ s) * ‖f h‖ := by ring
        _ ≤ (Real.exp θ - 1) * ‖f h‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
    · rw [hg, siteMask_off _ _ _ hh, norm_zero, mul_zero]
      have : 0 ≤ Real.exp θ - 1 := by linarith [Real.add_one_le_exp θ]
      positivity
  have hθ1 : 0 ≤ Real.exp θ - 1 := by linarith [Real.add_one_le_exp θ]
  have hsq : ‖bondWt φ (gradL2 U (siteWt (-φ) g)) - gradL2 U g‖ ^ 2 ≤ (3 * (Real.exp θ - 1) ^ 2) * ‖f‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc ∑ b, ‖(bondWt φ (gradL2 U (siteWt (-φ) g)) - gradL2 U g) b‖ ^ 2
        ≤ ∑ b : Bond L, (Real.exp θ - 1) ^ 2 * ‖f (periodicLatticeShift b.1 b.2)‖ ^ 2 := by
          refine Finset.sum_le_sum (fun b _ => ?_)
          rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hpt b) 2
      _ = (Real.exp θ - 1) ^ 2 * (3 * ‖f‖ ^ 2) := by rw [← Finset.mul_sum, sum_shift_sq]
      _ = _ := by ring
  have e3 : (3 * (Real.exp θ - 1) ^ 2) * ‖f‖ ^ 2 = (Real.sqrt 3 * (Real.exp θ - 1) * ‖f‖) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]
  rw [e3] at hsq
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- disjoint constraint blocks: `Σ_q Σ_{x∈B_q} ‖f x‖² ≤ ‖f‖²`. -/
theorem sum_blocks_le {G : TowerGeom L} {ell k : ℕ} (hP : ProperTower G ell k) (f : SiteL2 L) :
    ∑ q : QIdx G, ∑ x ∈ blockOf (yq q) (ell ^ jq q), ‖f x‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  classical
  rw [PiLp.norm_sq_eq_of_L2]
  rw [← Finset.sum_biUnion (s := (Finset.univ : Finset (QIdx G))) (t := fun q => blockOf (yq q) (ell ^ jq q))]
  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => sq_nonneg _)
  · intro q _ q' _ hne
    exact disj_q hP hne

/-- **row commutator of `Q̂`** (block oscillation `δ₀`). -/
theorem hatQ_comm {G : TowerGeom L} {ell k : ℕ} (hP : ProperTower G ell k) (hell : 2 ≤ ell) (U : Cfg L)
    (a : ℝ) (ha : 0 < a) (φ : PeriodicLatticeSite L → ℝ) (δ0 : ℝ) (hδ0 : 0 ≤ δ0)
    (hφ : ∀ q : QIdx G, ∀ x ∈ blockOf (yq q) (ell ^ jq q), |φ (yq q) - φ x| ≤ δ0)
    (f : SiteL2 L) :
    ‖(cjp (siteWP φ) (ypWP G φ) (Qh G U a) - Qh G U a) f‖ ≤ Real.sqrt a * (Real.exp δ0 - 1) * ‖f‖ := by
  classical
  have hell0 : 0 < ell := by omega
  have hellG : 0 < G.ell := by rw [hP.ell_eq]; exact hell0
  have hellG2 : 2 ≤ G.ell := by rw [hP.ell_eq]; exact hell
  set g := siteWt (sigG G) f with hg
  have hδ1 : 0 ≤ Real.exp δ0 - 1 := by linarith [Real.add_one_le_exp δ0]
  -- pointwise rows
  have hrow : ∀ q : QIdx G, ‖((cjp (siteWP φ) (ypWP G φ) (Qh G U a) - Qh G U a) f) (Sum.inl q)‖ ^ 2
      ≤ a * (Real.exp δ0 - 1) ^ 2 * ∑ x ∈ blockOf (yq q) (ell ^ jq q), ‖f x‖ ^ 2 := by
    intro q
    set j := jq q; set y := yq q
    have hj : j ≤ k := by rw [← hP.k_eq]; exact jq_le q
    have hy : y ∈ G.Lam j := yq_mem q
    have e1 : ((cjp (siteWP φ) (ypWP G φ) (Qh G U a) - Qh G U a) f) (Sum.inl q)
        = Real.sqrt (wq G a j) • (Qlev G U j y (siteWt (fun x => φ y - φ x) (siteMask G.Om0 g))
            - Qlev G U j y (siteMask G.Om0 g)) := by
      rw [ContinuousLinearMap.sub_apply, PiLp.sub_apply, cjp_apply]
      show ypWt G φ (QpP G U a (siteWt (sigG G) (siteWt (-φ) f))) (Sum.inl q) - QpP G U a (siteWt (sigG G) f) (Sum.inl q) = _
      rw [ypWt_apply, QpP_inl, QpP_inl, siteWt_comm (sigG G) (-φ), ← siteWt_mask,
        Qlev_siteWt_shift G U _ _ (-φ) (-φ (yq q)) (siteMask G.Om0 (siteWt (sigG G) f))]
      have e2 : (fun x => (-φ) x - -φ (yq q)) = (fun x => φ (yq q) - φ x) := by
        funext x; simp only [Pi.neg_apply]; ring
      rw [e2, smul_smul, smul_smul]
      have hs : Real.exp (φ (rowSite (Sum.inl q : PIdx G))) * Real.sqrt (wq G a q.1.1.val) * Real.exp (-φ (yq q))
          = Real.sqrt (wq G a q.1.1.val) := by
        have e3 : φ (rowSite (Sum.inl q : PIdx G)) + -φ (yq q) = 0 := by
          show φ (yq q) + -φ (yq q) = 0; ring
        rw [mul_comm (Real.exp _) (Real.sqrt _), mul_assoc, ← Real.exp_add, e3, Real.exp_zero, mul_one]
      rw [hs, ← smul_sub]
      rfl
    rw [e1, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (wq_pos hell hP a j ha).le]
    have hbox : ∀ x ∈ boxF y (G.ell ^ j), |(fun x => φ y - φ x) x| ≤ δ0 := by
      intro x hx
      rw [hP.ell_eq, boxF_eq_blockOf] at hx
      exact hφ q x hx
    have herr := Qlev_err_sq G U hellG j y (fun x => φ y - φ x) δ0 hbox (siteMask G.Om0 g)
    have hsum : ∑ x ∈ boxF y (G.ell ^ j), ‖siteMask G.Om0 g x‖ ^ 2
        = ((ell : ℝ) ^ j) ^ 2 * ∑ x ∈ blockOf y (ell ^ j), ‖f x‖ ^ 2 := by
      rw [hP.ell_eq, boxF_eq_blockOf, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x hx => ?_)
      have hx0 : x ∈ G.Om0 := block_Om0 hP q hx
      rw [siteMask_on _ _ _ hx0, hg, siteWt_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        exp_sig G hellG, stratG_eq hP hj hy hx, hP.ell_eq]
      ring
    rw [hsum] at herr
    have hwq : wq G a j ≤ a * (ell : ℝ) ^ j := by
      unfold wq
      rw [hP.ell_eq]
      have := ajSeq_le ell j hell ha
      have h0 : (0 : ℝ) ≤ (ell : ℝ) ^ j := by positivity
      nlinarith
    have hpow : ((1 / (G.ell : ℝ) ^ 3) ^ j) * ((ell : ℝ) ^ j) ^ 2 * (ell : ℝ) ^ j = 1 := by
      rw [hP.ell_eq]
      have : (0 : ℝ) < (ell : ℝ) ^ j := by positivity
      rw [one_div, inv_pow, ← pow_mul]
      field_simp
      ring
    have hS0 : 0 ≤ ∑ x ∈ blockOf y (ell ^ j), ‖f x‖ ^ 2 := Finset.sum_nonneg (fun x _ => sq_nonneg _)
    set Sb := ∑ x ∈ blockOf y (ell ^ j), ‖f x‖ ^ 2
    have hw0 : 0 ≤ wq G a j := (wq_pos hell hP a j ha).le
    calc wq G a j * ‖Qlev G U j y (siteWt (fun x => φ y - φ x) (siteMask G.Om0 g)) - Qlev G U j y (siteMask G.Om0 g)‖ ^ 2
        ≤ (a * (ell : ℝ) ^ j) * (((1 / (G.ell : ℝ) ^ 3) ^ j) * (Real.exp δ0 - 1) ^ 2 * (((ell : ℝ) ^ j) ^ 2 * Sb)) :=
          mul_le_mul hwq herr (sq_nonneg _) (by positivity)
      _ = a * (Real.exp δ0 - 1) ^ 2 * Sb * (((1 / (G.ell : ℝ) ^ 3) ^ j) * ((ell : ℝ) ^ j) ^ 2 * (ell : ℝ) ^ j) := by ring
      _ = a * (Real.exp δ0 - 1) ^ 2 * Sb := by rw [hpow, mul_one]
  have hoff : ∀ x : OffIdx G, ((cjp (siteWP φ) (ypWP G φ) (Qh G U a) - Qh G U a) f) (Sum.inr x) = 0 := by
    intro x
    rw [ContinuousLinearMap.sub_apply, PiLp.sub_apply, cjp_apply]
    show ypWt G φ (QpP G U a (siteWt (sigG G) (siteWt (-φ) f))) (Sum.inr x) - QpP G U a (siteWt (sigG G) f) (Sum.inr x) = 0
    rw [ypWt_apply, QpP_inr, QpP_inr, siteWt_apply, siteWt_apply, siteWt_apply, smul_smul, smul_smul]
    simp only [rowSite, Sum.elim_inr, Pi.neg_apply]
    rw [sub_eq_zero]
    congr 1
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hsq : ‖(cjp (siteWP φ) (ypWP G φ) (Qh G U a) - Qh G U a) f‖ ^ 2 ≤ (a * (Real.exp δ0 - 1) ^ 2) * ‖f‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type]
    simp only [hoff, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero,
      add_zero]
    calc ∑ q : QIdx G, ‖((cjp (siteWP φ) (ypWP G φ) (Qh G U a) - Qh G U a) f) (Sum.inl q)‖ ^ 2
        ≤ ∑ q : QIdx G, a * (Real.exp δ0 - 1) ^ 2 * ∑ x ∈ blockOf (yq q) (ell ^ jq q), ‖f x‖ ^ 2 :=
          Finset.sum_le_sum (fun q _ => hrow q)
      _ = a * (Real.exp δ0 - 1) ^ 2 * ∑ q : QIdx G, ∑ x ∈ blockOf (yq q) (ell ^ jq q), ‖f x‖ ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ a * (Real.exp δ0 - 1) ^ 2 * ‖f‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (sum_blocks_le hP f) (by positivity)
  have e3 : (a * (Real.exp δ0 - 1) ^ 2) * ‖f‖ ^ 2 = (Real.sqrt a * (Real.exp δ0 - 1) * ‖f‖) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt ha.le]
  rw [e3] at hsq
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-! ## 5. the hatted `SiteHyp` -/

/-- **the rescaled stratified site chain as a DL10 `SiteHyp`.** -/
noncomputable def hatSiteHyp (G : TowerGeom L) (U : Cfg L) (a : ℝ) (hw : ∀ j, 0 ≤ wq G a j) (hu : IsUnit (LP G U a))
    (φ : PeriodicLatticeSite L → ℝ) (c δD δQ : ℝ) (hc : 0 < c) (hδD : 0 ≤ δD) (hδQ : 0 ≤ δQ)
    (hcoer : ∀ f, c * ‖f‖ ^ 2 ≤ ⟪siteWt (sigG G) f, LP G U a (siteWt (sigG G) f)⟫)
    (hDp : ‖cjp (siteWP φ) (bondWP φ) (Dh G U) - Dh G U‖ ≤ δD)
    (hDm : ‖cjm (siteWP φ) (bondWP φ) (Dh G U) - Dh G U‖ ≤ δD)
    (hQp : ‖cjp (siteWP φ) (ypWP G φ) (Qh G U a) - Qh G U a‖ ≤ δQ)
    (hQm : ‖cjm (siteWP φ) (ypWP G φ) (Qh G U a) - Qh G U a‖ ≤ δQ)
    (hsmall : 24 * (δD ^ 2 + 1 * δQ ^ 2) ≤ c) (hsmallD : 4 * δD ^ 2 ≤ c) :
    SiteHyp (SiteL2 L) (BondFnL2 L) (YP G) where
  D := Dh G U
  Qp := Qh G U a
  m := 1
  Linv := Linvh G U a
  ωS := siteWP φ
  ωE := bondWP φ
  ωY := ypWP G φ
  c := c
  δD := δD
  δQ := δQ
  hm := zero_le_one
  hc := hc
  hδD := hδD
  hδQ := hδQ
  hL1 := Lh_Linvh G U a hw hu
  hL2 := Linvh_Lh G U a hw hu
  hcoer := fun f => by
    rw [Lh_eq G U a hw]
    simp only [ContinuousLinearMap.comp_apply]
    rw [← siteWt_symm]
    exact hcoer f
  hDp := hDp
  hDm := hDm
  hQp := hQp
  hQm := hQm
  hsmall := hsmall
  hsmallD := hsmallD

end AdalyFormal.M1IMS

#print axioms AdalyFormal.M1IMS.findGreatest_eq_sSup
#print axioms AdalyFormal.M1IMS.strat_eq_stratG
#print axioms AdalyFormal.M1IMS.exp_sig
#print axioms AdalyFormal.M1IMS.stratG_off
#print axioms AdalyFormal.M1IMS.siteWt_comm
#print axioms AdalyFormal.M1IMS.siteWt_adjoint
#print axioms AdalyFormal.M1IMS.Lh_eq
#print axioms AdalyFormal.M1IMS.Lh_Linvh
#print axioms AdalyFormal.M1IMS.Linvh_Lh
#print axioms AdalyFormal.M1IMS.hatCoer
#print axioms AdalyFormal.M1IMS.ypWt_neg_cancel
#print axioms AdalyFormal.M1IMS.ypWt_cancel_neg
#print axioms AdalyFormal.M1IMS.ypWt_symm
#print axioms AdalyFormal.M1IMS.hatD_comm
#print axioms AdalyFormal.M1IMS.sum_blocks_le
#print axioms AdalyFormal.M1IMS.hatQ_comm
#print axioms AdalyFormal.M1IMS.sigG
#print axioms AdalyFormal.M1IMS.Dh
#print axioms AdalyFormal.M1IMS.Qh
#print axioms AdalyFormal.M1IMS.Linvh
#print axioms AdalyFormal.M1IMS.rowSite
#print axioms AdalyFormal.M1IMS.ypWt
#print axioms AdalyFormal.M1IMS.ypWt_apply
#print axioms AdalyFormal.M1IMS.ypWP
#print axioms AdalyFormal.M1IMS.hatSiteHyp
