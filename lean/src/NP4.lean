import NP3
import DF

/-!
# NP4 -- the constraint rows of the two-stratum patch at a GENERAL configuration, and the decay estimate there
(m1_patch_nonflat, 2026-10-14)

Patch geometry `G = geomOf ell (i+1) (patchTower i Rg)` (`Rg` block-closed at `ell^{i+1}`, `ell^{i+1} ∣ L μ + 1`), its
constraint classes `patchClasses` (DF).  For the class of `x` the row is `ℓ_x = Q'_{lev x}(U)(cc x)` (`lev x = i+1` in `Rg`,
`i` outside).  At ANY `U`:
* `row_norm`  : `‖ℓ_x f‖ ≤ nn⁻³ Σ_{cls x} ‖f‖`  (BondComposite `norm_Qcomposite_le`);  `row_local` (reads only the class);
* `row_drift` : `‖ℓ_x f − nn⁻³ Σ_{cls x} f‖ ≤ D nn⁻³ Σ ‖f‖` from background bounds (BondComposite `Qcomposite_drift_pointwise`);
* `row_hit`   : a row whose block meets `cls x` IS `ℓ_x`;   `nk_of_class` : `f` supported in `cls x ⊆ K` with `ℓ_x f = 0` lies
  in `N_K(U)`;
* `rep_of_perp` : if `k ⟂ N_K(U)` then on every class inside `K`, `⟪k, f⟫ = ⟪c, ℓ_x f⟫` for one `c` (finite-dimensional
  `(ker T)ᗮ = range T†`);  `perp_class` : `Σ_{cls x} ⟪k, μ⟫ = 0` for `μ ∈ N(Q'(U))`;
The decay estimate assembled from these rows is NP5 `harmDecay_nf`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M1NonFlat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (pdist BlockClosed)
open AdalyFormal.StatementLaneR8 (Ball pdist_comm pdist_triangle pdist_shift_le)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)
open AdalyFormal.Balaban.QjComposite (Qcomposite)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobNorm_nonneg)
open AdalyFormal.M1Patch (corner corner_dvd patchTower mem_lam_j mem_lam_succ om0_univ lam_lt lam_gt)
open AdalyFormal.LemIFlat (cc corner_mem_Rg mem_blockOf_iff_corner corner_idem mem_Rg_of_block mem_Rg_of_small_block)
open AdalyFormal.M1Decay (Classes patchClasses patchClasses_anc patchClasses_nn pnn cc_mem_Rg lapDir_patch rD rD_pos
  rD_room smoothCut sc_nonneg sc_lip sc_lapR sc_one sc_zero)
open AdalyFormal.M1W2 (HK VK NK suppIn gradOn)

variable {L : PeriodicLatticeExtent}

open Classical in
/-- the level of the constraint row of `x`. -/
noncomputable def lev (ell i : ℕ) (Rg : Set (PeriodicLatticeSite L)) (x : PeriodicLatticeSite L) : ℕ :=
  if x ∈ Rg then i + 1 else i

section patch
variable {ell i : ℕ} (hell : 0 < ell) {Rg : Set (PeriodicLatticeSite L)} (hRg : BlockClosed (ell ^ (i + 1)) Rg)
  (hdvd : ∀ μ : Fin 3, ell ^ (i + 1) ∣ L μ + 1)

theorem lev_le (x : PeriodicLatticeSite L) : lev ell i Rg x ≤ i + 1 := by
  classical
  unfold lev; split_ifs <;> omega

theorem pnn_eq_pow (x : PeriodicLatticeSite L) : pnn ell i Rg x = ell ^ lev ell i Rg x := by
  classical
  unfold pnn lev; split_ifs <;> rfl

theorem cc_eq_corner (x : PeriodicLatticeSite L) : cc ell i Rg x = corner (ell ^ lev ell i Rg x) x := by
  classical
  unfold cc lev; split_ifs <;> rfl

include hell hRg in
theorem cc_lam (x : PeriodicLatticeSite L) :
    cc ell i Rg x ∈ (geomOf ell (i + 1) (patchTower i Rg)).Lam (lev ell i Rg x) := by
  classical
  unfold lev
  by_cases hx : x ∈ Rg
  · rw [if_pos hx]
    unfold cc; rw [if_pos hx]
    exact (mem_lam_succ ell i Rg _).mpr ⟨corner_dvd _ x,
      (corner_mem_Rg hell hRg (pow_pos hell _) (dvd_refl _) x).mpr hx⟩
  · rw [if_neg hx]
    unfold cc; rw [if_neg hx]
    exact (mem_lam_j ell i Rg _).mpr ⟨corner_dvd _ x, fun h => hx ((corner_mem_Rg hell hRg (pow_pos hell _)
      (pow_dvd_pow ell (Nat.le_succ i)) x).mp h)⟩

theorem cc_coarse (x : PeriodicLatticeSite L) :
    cc ell i Rg x ∈ CoarseLattice L (ell ^ lev ell i Rg x) := by
  rw [mem_CoarseLattice, cc_eq_corner]
  intro μ
  exact Nat.mod_eq_zero_of_dvd (corner_dvd _ x μ)

theorem inv_pow_eq (x : PeriodicLatticeSite L) :
    (1 / (ell : ℝ) ^ 3) ^ lev ell i Rg x = (((pnn ell i Rg x : ℕ) : ℝ) ^ 3)⁻¹ := by
  rw [pnn_eq_pow]; push_cast
  rw [one_div_pow, ← pow_mul, ← pow_mul, mul_comm, one_div]

include hell hRg hdvd in
theorem cls_eq (x : PeriodicLatticeSite L) :
    (patchClasses hell hRg hdvd).cls x = blockOf (cc ell i Rg x) (ell ^ lev ell i Rg x) := by
  rw [Classes.cls_eq_block, patchClasses_anc, patchClasses_nn, pnn_eq_pow]

/-- the row of `x`. -/
noncomputable abbrev rowx (U : Cfg L) (x : PeriodicLatticeSite L) : SiteL2 L →L[ℝ] SuTwo :=
  Qlev (geomOf ell (i + 1) (patchTower i Rg)) U (lev ell i Rg x) (cc ell i Rg x)

include hell hRg hdvd in
theorem row_norm (U : Cfg L) (x : PeriodicLatticeSite L) (f : SiteL2 L) :
    ‖rowx (ell := ell) (i := i) (Rg := Rg) U x f‖
      ≤ (((pnn ell i Rg x : ℕ) : ℝ) ^ 3)⁻¹ * ∑ z ∈ (patchClasses hell hRg hdvd).cls x, ‖f z‖ := by
  rw [Qlev_apply, cls_eq hell hRg hdvd, ← inv_pow_eq]
  exact AdalyFormal.BondComposite.norm_Qcomposite_le _ ell hell (WithLp.ofLp f) _ _

include hell hRg hdvd in
theorem row_local (U : Cfg L) (x : PeriodicLatticeSite L) (f g : SiteL2 L)
    (hfg : ∀ z ∈ (patchClasses hell hRg hdvd).cls x, f z = g z) :
    rowx (ell := ell) (i := i) (Rg := Rg) U x f = rowx (ell := ell) (i := i) (Rg := Rg) U x g := by
  have h := row_norm hell hRg hdvd U x (f - g)
  rw [Finset.sum_eq_zero (fun z hz => by
    show ‖(f - g) z‖ = 0
    rw [PiLp.sub_apply, hfg z hz, sub_self, norm_zero]), mul_zero] at h
  have := norm_le_zero_iff.mp h
  rw [map_sub] at this
  exact sub_eq_zero.mp this

include hell hRg hdvd in
theorem row_drift (U : Cfg L) (a : ℕ → ℝ) (D : ℝ)
    (hbg : ∀ j, j < i + 1 → ∀ y ∈ CoarseLattice L (ell ^ j), ∀ μ : Fin 3,
      frobNorm (((bgTower (geomOf ell (i + 1) (patchTower i Rg)) U j (y, μ) : _) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ a j)
    (hD : ∀ j, j ≤ i + 1 → AdalyFormal.BondComposite.dsum ell a j ≤ D)
    (x : PeriodicLatticeSite L) (f : SiteL2 L) :
    ‖rowx (ell := ell) (i := i) (Rg := Rg) U x f
        - (((pnn ell i Rg x : ℕ) : ℝ) ^ 3)⁻¹ • ∑ z ∈ (patchClasses hell hRg hdvd).cls x, f z‖
      ≤ D * ((((pnn ell i Rg x : ℕ) : ℝ) ^ 3)⁻¹ * ∑ z ∈ (patchClasses hell hRg hdvd).cls x, ‖f z‖) := by
  rw [Qlev_apply, cls_eq hell hRg hdvd, ← inv_pow_eq]
  have hdvdK : ∀ j, j ≤ i + 1 → ∀ μ : Fin 3, ell ^ j ∣ (L μ + 1) :=
    fun j hj μ => (pow_dvd_pow ell hj).trans (hdvd μ)
  have h := AdalyFormal.BondComposite.Qcomposite_drift_pointwise (bgTower (geomOf ell (i + 1) (patchTower i Rg)) U)
    ell hell a (i + 1) hdvdK hbg (WithLp.ofLp f) (lev ell i Rg x) (lev_le x) (cc ell i Rg x) (cc_coarse x)
  refine h.trans (mul_le_mul_of_nonneg_right (hD _ (lev_le x)) ?_)
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))

include hell hRg hdvd in
/-- a constraint row whose block meets the class of `x` is the row of `x`. -/
theorem row_hit (x : PeriodicLatticeSite L) (j : ℕ) (y : PeriodicLatticeSite L)
    (hy : y ∈ (geomOf ell (i + 1) (patchTower i Rg)).Lam j) (z : PeriodicLatticeSite L)
    (hzB : z ∈ blockOf y (ell ^ j)) (hzC : z ∈ (patchClasses hell hRg hdvd).cls x) :
    j = lev ell i Rg x ∧ y = cc ell i Rg x := by
  classical
  have hzx : cc ell i Rg z = cc ell i Rg x := (Classes.mem_cls _ x z).mp hzC
  rcases Nat.lt_or_ge j i with hlt | hge
  · rw [lam_lt ell i Rg hlt] at hy; exact False.elim hy
  rcases Nat.lt_or_ge (i + 1) j with hgt | hle
  · rw [lam_gt ell i Rg hgt] at hy; exact False.elim hy
  rcases Nat.lt_or_ge j (i + 1) with hj | hj
  · have hji : j = i := by omega
    subst hji
    obtain ⟨hal, hyR⟩ := (mem_lam_j ell j Rg y).mp hy
    have hzR : z ∉ Rg := fun h => hyR ((mem_Rg_of_small_block hell hRg hal hzB).mp h)
    have hxR : x ∉ Rg := by
      intro hx
      have : cc ell j Rg x ∈ Rg := (cc_mem_Rg hell hRg x).mpr hx
      rw [← hzx] at this
      exact hzR ((cc_mem_Rg hell hRg z).mp this)
    have hcz : corner (ell ^ j) z = y := (mem_blockOf_iff_corner (pow_pos hell _) y z hal).mp hzB
    refine ⟨by unfold lev; rw [if_neg hxR], ?_⟩
    rw [← hzx]; unfold cc; rw [if_neg hzR, hcz]
  · have hji : j = i + 1 := by omega
    subst hji
    obtain ⟨hal, hyR⟩ := (mem_lam_succ ell i Rg y).mp hy
    have hzR : z ∈ Rg := (mem_Rg_of_block hell hRg hal hzB).mpr hyR
    have hxR : x ∈ Rg := by
      have : cc ell i Rg z ∈ Rg := (cc_mem_Rg hell hRg z).mpr hzR
      rw [hzx] at this
      exact (cc_mem_Rg hell hRg x).mp this
    have hcz : corner (ell ^ (i + 1)) z = y := (mem_blockOf_iff_corner (pow_pos hell _) y z hal).mp hzB
    refine ⟨by unfold lev; rw [if_pos hxR], ?_⟩
    rw [← hzx]; unfold cc; rw [if_pos hzR, hcz]

include hell hRg hdvd in
/-- `f` supported in a class inside `K` with zero row lies in `N_K(U)`. -/
theorem nk_of_class (U : Cfg L) (K : Set (PeriodicLatticeSite L)) (x : PeriodicLatticeSite L)
    (hK : ∀ z ∈ (patchClasses hell hRg hdvd).cls x, z ∈ K) (f : SiteL2 L)
    (hf : ∀ z, z ∉ (patchClasses hell hRg hdvd).cls x → f z = 0)
    (h0 : rowx (ell := ell) (i := i) (Rg := Rg) U x f = 0) :
    f ∈ NK (geomOf ell (i + 1) (patchTower i Rg)) U K := by
  classical
  refine ⟨⟨fun z hz => absurd (by
      show z ∈ (patchTower i Rg).Om 0
      rw [show (patchTower i Rg).Om 0 = Set.univ from om0_univ i Rg ell]; trivial) hz, fun j _ y hy => ?_⟩,
    fun z hz => hf z (fun hzC => hz (hK z hzC))⟩
  by_cases hmeet : ∃ z ∈ blockOf y (ell ^ j), z ∈ (patchClasses hell hRg hdvd).cls x
  · obtain ⟨z, hzB, hzC⟩ := hmeet
    obtain ⟨rfl, rfl⟩ := row_hit hell hRg hdvd x j y hy z hzB hzC
    exact h0
  · push Not at hmeet
    rw [Qlev_apply]
    have h := AdalyFormal.BondComposite.norm_Qcomposite_le
      (bgTower (geomOf ell (i + 1) (patchTower i Rg)) U) ell hell (WithLp.ofLp f) j y
    rw [Finset.sum_eq_zero (fun z hz => by
      show ‖f z‖ = 0
      rw [hf z (hmeet z hz), norm_zero]), mul_zero] at h
    exact norm_le_zero_iff.mp h

include hell hRg hdvd in
/-- **the row representation** of a field orthogonal to `N_K(U)` on a class inside `K`. -/
theorem rep_of_perp (U : Cfg L) (K : Set (PeriodicLatticeSite L)) (k : SiteL2 L)
    (hk : ∀ f ∈ NK (geomOf ell (i + 1) (patchTower i Rg)) U K, ⟪k, f⟫ = 0)
    (x : PeriodicLatticeSite L) (hK : ∀ z ∈ (patchClasses hell hRg hdvd).cls x, z ∈ K) :
    ∃ c : SuTwo, ∀ f : SiteL2 L, (∀ z, z ∉ (patchClasses hell hRg hdvd).cls x → f z = 0) →
      ⟪k, f⟫ = ⟪c, rowx (ell := ell) (i := i) (Rg := Rg) U x f⟫ := by
  classical
  set C : Set (PeriodicLatticeSite L) := ↑((patchClasses hell hRg hdvd).cls x) with hCdef
  set M := siteMask C with hM
  set T : SiteL2 L →L[ℝ] SuTwo := (rowx (ell := ell) (i := i) (Rg := Rg) U x).comp M with hT
  have hMsupp : ∀ f : SiteL2 L, ∀ z, z ∉ (patchClasses hell hRg hdvd).cls x → M f z = 0 := by
    intro f z hz; rw [hM, siteMask_apply, if_neg (by simpa [hCdef] using hz)]
  have hMid : ∀ f : SiteL2 L, (∀ z, z ∉ (patchClasses hell hRg hdvd).cls x → f z = 0) → M f = f := by
    intro f hf
    ext1 z
    rw [hM, siteMask_apply]
    split_ifs with hz
    · rfl
    · exact (hf z (by simpa [hCdef] using hz)).symm
  have hkC : M k ∈ T.kerᗮ := by
    rw [Submodule.mem_orthogonal]
    intro f hf0
    have hf : T f = 0 := hf0
    rw [real_inner_comm, hM, siteMask_symm]
    exact hk _ (nk_of_class hell hRg hdvd U K x hK (M f) (hMsupp f) hf)
  have hker : T.kerᗮ = (ContinuousLinearMap.adjoint T).range := by
    have h1 := ContinuousLinearMap.orthogonal_ker T
    rw [h1]
    exact (Submodule.closed_of_finiteDimensional _).submodule_topologicalClosure_eq
  rw [hker] at hkC
  obtain ⟨c, hc⟩ := hkC
  refine ⟨c, fun f hf => ?_⟩
  have e1 : ⟪k, f⟫ = ⟪M k, f⟫ := by rw [hM, siteMask_symm, ← hM, hMid f hf]
  have e2 : ⟪M k, f⟫ = ⟪(ContinuousLinearMap.adjoint T) c, f⟫ := by rw [← hc]; rfl
  rw [e1, e2, ContinuousLinearMap.adjoint_inner_left, hT, ContinuousLinearMap.comp_apply, hMid f hf]

include hell hRg hdvd in
theorem perp_class (U : Cfg L) (K : Set (PeriodicLatticeSite L)) (k : SiteL2 L)
    (hk : ∀ f ∈ NK (geomOf ell (i + 1) (patchTower i Rg)) U K, ⟪k, f⟫ = 0)
    (μ : SiteL2 L) (hμ : μ ∈ NQp (geomOf ell (i + 1) (patchTower i Rg)) U)
    (x : PeriodicLatticeSite L) (hK : ∀ z ∈ (patchClasses hell hRg hdvd).cls x, z ∈ K) :
    ∑ z ∈ (patchClasses hell hRg hdvd).cls x, ⟪k z, μ z⟫ = 0 := by
  classical
  obtain ⟨c, hc⟩ := rep_of_perp hell hRg hdvd U K k hk x hK
  set μC : SiteL2 L := WithLp.toLp 2 (fun z => if z ∈ (patchClasses hell hRg hdvd).cls x then μ z else 0) with hμC
  have hsupp : ∀ z, z ∉ (patchClasses hell hRg hdvd).cls x → μC z = 0 := fun z hz => by
    show (if z ∈ (patchClasses hell hRg hdvd).cls x then μ z else 0) = 0; rw [if_neg hz]
  have e1 : ∑ z ∈ (patchClasses hell hRg hdvd).cls x, ⟪k z, μ z⟫ = ⟪k, μC⟫ := by
    rw [PiLp.inner_apply, ← Finset.sum_subset (Finset.subset_univ ((patchClasses hell hRg hdvd).cls x))]
    · refine Finset.sum_congr rfl (fun z hz => ?_)
      show _ = ⟪k z, (if z ∈ (patchClasses hell hRg hdvd).cls x then μ z else 0)⟫
      rw [if_pos hz]
    · intro z _ hz
      show ⟪k z, (if z ∈ (patchClasses hell hRg hdvd).cls x then μ z else 0)⟫ = 0
      rw [if_neg hz, inner_zero_right]
  have e2 : rowx (ell := ell) (i := i) (Rg := Rg) U x μC = rowx (ell := ell) (i := i) (Rg := Rg) U x μ :=
    row_local hell hRg hdvd U x μC μ (fun z hz => by
      show (if z ∈ (patchClasses hell hRg hdvd).cls x then μ z else 0) = μ z; rw [if_pos hz])
  have e3 : rowx (ell := ell) (i := i) (Rg := Rg) U x μ = 0 :=
    hμ.2 _ (lev_le x) _ (cc_lam hell hRg x)
  rw [e1, hc μC hsupp, e2, e3, inner_zero_right]

end patch

end AdalyFormal.M1NonFlat

#print axioms AdalyFormal.M1NonFlat.cc_lam
#print axioms AdalyFormal.M1NonFlat.row_norm
#print axioms AdalyFormal.M1NonFlat.row_local
#print axioms AdalyFormal.M1NonFlat.row_drift
#print axioms AdalyFormal.M1NonFlat.row_hit
#print axioms AdalyFormal.M1NonFlat.nk_of_class
#print axioms AdalyFormal.M1NonFlat.rep_of_perp
#print axioms AdalyFormal.M1NonFlat.perp_class
