import LF5b

/-!
# LF5c -- the cell-edge energy of a block-constant field is controlled by the patch mass (M1)

`G = geomOf ell (j+1) (patchTower j Rg)`, `n = ell^j`, `N = ell^{j+1}`, flat `U`.  For `v ⟂ N(Q')`:
`epsN n v ≤ (1 + 165 ell⁴) (n/a) · mass(D v)`  (`epsN_le_mass`).
Ingredients: the flat row formula (LF3), the case analysis of a cell edge (inside the bottom stratum / inside one top
block / crossing into `Rg`), the crossing lemma, and the cube Poincaré inequality inside the virtual big blocks.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace AdalyFormal.LemIFlat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.M1Patch (patchTower corner corner_dvd mem_lam_j mem_lam_succ lam_lt lam_gt onLat_back)
open AdalyFormal.StatementLane (BlockClosed)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf inBlock)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_val_eq coarseShift_apply_ne)
open AdalyFormal.Balaban.QjComposite (Qcomposite stepBlockOf mem_stepBlockOf)
open AdalyFormal.SliceCoerc (OnLat onLat_shift)

variable {L : PeriodicLatticeExtent}

/-- the patch geometry. -/
abbrev GQ (ell j : ℕ) (Rg : Set (PeriodicLatticeSite L)) : TowerGeom L := geomOf ell (j + 1) (patchTower j Rg)

/-- the level-`i` composite average at flat `U`. -/
noncomputable def Qa (ell j : ℕ) (Rg : Set (PeriodicLatticeSite L)) (i : ℕ) (f : PeriodicLatticeSite L → SuTwo)
    (z : PeriodicLatticeSite L) : SuTwo :=
  Qcomposite (bgTower (GQ ell j Rg) (flatCfg : Cfg L)) ell i f z

theorem Qa_flat (ell j : ℕ) (hell : 0 < ell) (Rg : Set (PeriodicLatticeSite L)) (i : ℕ)
    (f : PeriodicLatticeSite L → SuTwo) (z : PeriodicLatticeSite L) :
    Qa ell j Rg i f z = ((1 / (ell : ℝ) ^ 3) ^ i) • ∑ x ∈ blockOf z (ell ^ i), f x :=
  Qcomp_flat (GQ ell j Rg) hell i z f

/-- the level-`i` row energy of a bond (no membership condition). -/
noncomputable def rowE (ell j : ℕ) (Rg : Set (PeriodicLatticeSite L)) (a : ℝ) (i : ℕ)
    (f : PeriodicLatticeSite L → SuTwo) (b : Bond L) : ℝ :=
  a / (ell : ℝ) ^ i * ‖Qa ell j Rg i f (coarseShift b.1 (ell ^ i) b.2) - Qa ell j Rg i f b.1‖ ^ 2

open Classical in
noncomputable def rowF (ell j : ℕ) (Rg : Set (PeriodicLatticeSite L)) (a : ℝ) (i : ℕ)
    (f : PeriodicLatticeSite L → SuTwo) (b : Bond L) : ℝ :=
  if b ∈ bondsLam (GQ ell j Rg) i then rowE ell j Rg a i f b else 0

noncomputable def rowS (ell j : ℕ) (Rg : Set (PeriodicLatticeSite L)) (a : ℝ) (i : ℕ)
    (f : PeriodicLatticeSite L → SuTwo) : ℝ :=
  ∑ b : Bond L, rowF ell j Rg a i f b

theorem rowE_nonneg (ell j : ℕ) (Rg : Set (PeriodicLatticeSite L)) (a : ℝ) (ha : 0 ≤ a) (i : ℕ)
    (f : PeriodicLatticeSite L → SuTwo) (b : Bond L) : 0 ≤ rowE ell j Rg a i f b := by
  unfold rowE; positivity

theorem rowF_nonneg (ell j : ℕ) (Rg : Set (PeriodicLatticeSite L)) (a : ℝ) (ha : 0 ≤ a) (i : ℕ)
    (f : PeriodicLatticeSite L → SuTwo) (b : Bond L) : 0 ≤ rowF ell j Rg a i f b := by
  unfold rowF; split_ifs
  · exact rowE_nonneg ell j Rg a ha i f b
  · exact le_refl 0

theorem norm_add3_sq_le {E : Type*} [NormedAddCommGroup E] (x y z : E) :
    ‖x + y + z‖ ^ 2 ≤ 3 * (‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2) := by
  have h := norm_add₃_le (a := x) (b := y) (c := z)
  have h0 : 0 ≤ ‖x + y + z‖ := norm_nonneg _
  have hsq : ‖x + y + z‖ ^ 2 ≤ (‖x‖ + ‖y‖ + ‖z‖) ^ 2 := pow_le_pow_left₀ h0 h 2
  nlinarith [sq_nonneg (‖x‖ - ‖y‖), sq_nonneg (‖y‖ - ‖z‖), sq_nonneg (‖x‖ - ‖z‖)]

theorem sum_subtype_ite {α : Type*} [Fintype α] (S : Set α) [DecidablePred (· ∈ S)] {F : Fintype {x // x ∈ S}}
    (g : α → ℝ) : ∑ x : {x // x ∈ S}, g x.1 = ∑ x, if x ∈ S then g x else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter (· ∈ S)) (by simp) g).symm

section patch
variable {ell j : ℕ} (hell : 0 < ell) {Rg : Set (PeriodicLatticeSite L)} (hRg : BlockClosed (ell ^ (j + 1)) Rg)
  (hdvd : ∀ μ : Fin 3, ell ^ (j + 1) ∣ L μ + 1)
include hell hRg hdvd

/-! ### the mass dominates the two row sums -/

theorem row_lat (i : ℕ) (hi : i ≤ j + 1) (b : Bond L) (hb : b ∈ bondsLam (GQ ell j Rg) i) :
    OnLat (ell ^ i) b.1 ∧ OnLat (ell ^ i) (coarseShift b.1 (ell ^ i) b.2) := by
  have hm : ∀ μ : Fin 3, ell ^ i ∣ L μ + 1 := fun μ => (pow_dvd_pow ell hi).trans (hdvd μ)
  rcases hb.1 with h | h
  · have h0 : OnLat (ell ^ i) b.1 := h.1
    exact ⟨h0, onLat_shift _ hm _ h0 _⟩
  · have h1 : OnLat (ell ^ i) (coarseShift b.1 (ell ^ i) b.2) := h.1
    exact ⟨onLat_back _ hm _ _ h1, h1⟩

theorem mass_term (v : SiteL2 L) (a : ℝ) (p : BIdx (GQ ell j Rg)) :
    a * ((GQ ell j Rg).ell : ℝ) ^ (p.1 : ℕ) * ‖(QfullOf (GQ ell j Rg) (flatCfg : Cfg L) (gradL2 (flatCfg : Cfg L) v)).ofLp p‖ ^ 2
      = rowE ell j Rg a p.1 v.ofLp p.2.1 := by
  have hi : (p.1 : ℕ) ≤ j + 1 := Nat.lt_succ_iff.mp p.1.isLt
  obtain ⟨h0, h1⟩ := row_lat hell hRg hdvd p.1 hi p.2.1 p.2.2
  have hdivG : ∀ μ : Fin 3, (GQ ell j Rg).ell ^ (GQ ell j Rg).k ∣ L μ + 1 := hdvd
  rw [QfullOf_grad_flat (GQ ell j Rg) hell hdivG v p h0 h1, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  unfold rowE Qa
  have hpos : (0 : ℝ) < (ell : ℝ) ^ (p.1 : ℕ) := by positivity
  show a * (ell : ℝ) ^ (p.1 : ℕ) * (((ell : ℝ) ^ (p.1 : ℕ))⁻¹ ^ 2 * _) = a / (ell : ℝ) ^ (p.1 : ℕ) * _
  field_simp
  rfl

theorem mass_ge (v : SiteL2 L) (a : ℝ) (ha : 0 ≤ a) :
    rowS ell j Rg a j v.ofLp + rowS ell j Rg a (j + 1) v.ofLp
      ≤ massP (GQ ell j Rg) a (gradL2 (flatCfg : Cfg L) v) := by
  classical
  rw [massP_eq]
  simp_rw [mass_term hell hRg hdvd v a]
  rw [Fintype.sum_sigma]
  have hrow : ∀ i : Fin ((GQ ell j Rg).k + 1),
      ∑ b : {b // b ∈ bondsLam (GQ ell j Rg) i}, rowE ell j Rg a i v.ofLp b.1 = rowS ell j Rg a i v.ofLp := by
    intro i
    rw [sum_subtype_ite]
    unfold rowS rowF
    rfl
  simp_rw [hrow]
  have hk : (GQ ell j Rg).k = j + 1 := rfl
  set ij : Fin ((GQ ell j Rg).k + 1) := ⟨j, by rw [hk]; omega⟩
  set ij1 : Fin ((GQ ell j Rg).k + 1) := ⟨j + 1, by rw [hk]; omega⟩
  have hne : ij ≠ ij1 := by intro h; have := congrArg Fin.val h; simp [ij, ij1] at this
  have hsub : ({ij, ij1} : Finset (Fin ((GQ ell j Rg).k + 1))) ⊆ Finset.univ := Finset.subset_univ _
  have h := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun i _ _ => Finset.sum_nonneg (fun b _ => rowF_nonneg ell j Rg a ha i v.ofLp b))
    (f := fun i : Fin ((GQ ell j Rg).k + 1) => rowS ell j Rg a i v.ofLp)
  rw [Finset.sum_pair hne] at h
  exact h

/-! ### values of the composite averages on block-constant fields -/

theorem Qa_cell (v : SiteL2 L) (hv : v ∈ (NQp (GQ ell j Rg) (flatCfg : Cfg L))ᗮ) (c : PeriodicLatticeSite L)
    (hc : ∀ μ : Fin 3, ell ^ j ∣ (c μ).val) : Qa ell j Rg j v.ofLp c = v.ofLp c := by
  rw [Qa_flat ell j hell Rg j v.ofLp c]
  have hw : ∀ x, v.ofLp x = v.ofLp (corner (ell ^ j) x) := orth_cell hell hRg v hv
  rw [cell_sum hell hRg hdvd v.ofLp hw c hc, smul_smul]
  have : (1 / (ell : ℝ) ^ 3) ^ j * ((ell ^ j : ℕ) : ℝ) ^ 3 = 1 := by
    have hpos : (0 : ℝ) < ell := by exact_mod_cast hell
    push_cast; rw [div_pow, one_pow, ← pow_mul, ← pow_mul]; field_simp; ring_nf
  rw [this, one_smul]

theorem Qa_Rg (v : SiteL2 L) (hv : v ∈ (NQp (GQ ell j Rg) (flatCfg : Cfg L))ᗮ) (Z : PeriodicLatticeSite L)
    (hZ : ∀ μ : Fin 3, ell ^ (j + 1) ∣ (Z μ).val) (hZR : Z ∈ Rg) : Qa ell j Rg (j + 1) v.ofLp Z = v.ofLp Z := by
  rw [Qa_flat ell j hell Rg (j + 1) v.ofLp Z]
  have hconst : ∀ x ∈ blockOf Z (ell ^ (j + 1)), v.ofLp x = v.ofLp Z := by
    intro x hx
    have hxR : x ∈ Rg := (mem_Rg_of_block hell hRg hZ hx).mpr hZR
    rw [orth_big hell hRg v hv x hxR, (mem_blockOf_iff_corner (pow_pos hell _) Z x hZ).mp hx]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const,
    AdalyFormal.M1Site.card_blockOf Z _ (fit_big ell j hell hdvd Z hZ), ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have : (1 / (ell : ℝ) ^ 3) ^ (j + 1) * (((ell ^ (j + 1)) ^ 3 : ℕ) : ℝ) = 1 := by
    have hpos : (0 : ℝ) < ell := by exact_mod_cast hell
    push_cast; rw [div_pow, one_pow, ← pow_mul, ← pow_mul]; field_simp; ring_nf
  rw [this, one_smul]

/-- the virtual average is the cube average of the cell values. -/
theorem Qa_big (v : SiteL2 L) (hv : v ∈ (NQp (GQ ell j Rg) (flatCfg : Cfg L))ᗮ) (Y : PeriodicLatticeSite L)
    (hY : ∀ μ : Fin 3, ell ^ (j + 1) ∣ (Y μ).val) :
    Qa ell j Rg (j + 1) v.ofLp Y = ((1 : ℝ) / (ell : ℝ) ^ 3) • ∑ i ∈ cube ell, v.ofLp (iota (ell ^ j) Y i) := by
  rw [Qa_flat ell j hell Rg (j + 1) v.ofLp Y]
  have hn : 0 < ell ^ j := pow_pos hell j
  have hsplit := AdalyFormal.FlatExt.sum_stepBlock_blockOf (ell ^ j) ell hn Y (fun x => v.ofLp x)
  rw [← pow_succ] at hsplit
  rw [← hsplit]
  have hw : ∀ x, v.ofLp x = v.ofLp (corner (ell ^ j) x) := orth_cell hell hRg v hv
  have hcell : ∀ x ∈ stepBlockOf Y (ell ^ j) ell, ∑ x' ∈ blockOf x (ell ^ j), v.ofLp x'
      = ((ell ^ j : ℕ) : ℝ) ^ 3 • v.ofLp x := by
    intro x hx
    apply cell_sum hell hRg hdvd v.ofLp hw x
    intro μ
    have h := (mem_stepBlockOf.mp hx) μ
    obtain ⟨h1, _, ⟨p, hp⟩⟩ := h
    have hz' : ell ^ j ∣ (Y μ).val := (pow_dvd_pow ell (Nat.le_succ j)).trans (hY μ)
    obtain ⟨q, hq⟩ := hz'
    exact ⟨p + q, by rw [Nat.mul_add]; omega⟩
  rw [Finset.sum_congr rfl hcell, ← Finset.smul_sum, sum_stepBlock_cube ell j hell hdvd Y hY, smul_smul]
  congr 1
  have hpos : (0 : ℝ) < ell := by exact_mod_cast hell
  push_cast; rw [div_pow, one_pow, ← pow_mul, ← pow_mul]; field_simp; ring_nf

/-- `OmGe` at the top level is membership in `Rg`. -/
theorem omGe_Rg (z : PeriodicLatticeSite L) (h : OmGe (GQ ell j Rg) (j + 1) z) : z ∈ Rg := by
  obtain ⟨i, hi1, hi2, y, hy, hz⟩ := h
  have hk : (GQ ell j Rg).k = j + 1 := rfl
  have hij : i = j + 1 := by rw [hk] at hi2; omega
  subst hij
  rw [mem_lam_succ] at hy
  have hzb : z ∈ blockOf y (ell ^ (j + 1)) := by
    rw [mem_blockOf]; intro μ; exact hz μ
  exact (mem_Rg_of_block hell hRg hy.1 hzb).mpr hy.2

/-! ### the crossing lemma -/

theorem crossing (y : PeriodicLatticeSite L) (hy : ∀ μ : Fin 3, ell ^ j ∣ (y μ).val) (μ : Fin 3)
    (hne : corner (ell ^ (j + 1)) (coarseShift y (ell ^ j) μ) ≠ corner (ell ^ (j + 1)) y) :
    corner (ell ^ (j + 1)) (coarseShift y (ell ^ j) μ) = coarseShift (corner (ell ^ (j + 1)) y) (ell ^ (j + 1)) μ := by
  have hn : 0 < ell ^ j := pow_pos hell j
  have hN : 0 < ell ^ (j + 1) := pow_pos hell (j + 1)
  have hnN : ell ^ j ∣ ell ^ (j + 1) := pow_dvd_pow ell (Nat.le_succ j)
  obtain ⟨c, hc⟩ : ∃ c, (y μ).val / ell ^ (j + 1) * ell ^ (j + 1) = c := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, (y μ).val % ell ^ (j + 1) = t := ⟨_, rfl⟩
  have hyct : (y μ).val = c + t := by
    rw [← hc, ← ht, Nat.mul_comm]; exact (Nat.div_add_mod _ _).symm
  have htN : t < ell ^ (j + 1) := ht ▸ Nat.mod_lt _ hN
  have htn : ell ^ j ∣ t := ht ▸ (Nat.dvd_mod_iff hnN).mpr (hy μ)
  have hcN : ell ^ (j + 1) ∣ c := hc ▸ Dvd.intro_left _ rfl
  obtain ⟨a', ha'⟩ := hcN
  have hylt := (y μ).isLt
  obtain ⟨b', hb'⟩ := hdvd μ
  have hfit : c + ell ^ (j + 1) ≤ L μ + 1 := by
    have hlt : ell ^ (j + 1) * a' < ell ^ (j + 1) * b' := by rw [← ha', ← hb']; omega
    have hab : a' + 1 ≤ b' := Nat.lt_of_mul_lt_mul_left hlt
    have h2 := Nat.mul_le_mul_left (ell ^ (j + 1)) hab
    rw [Nat.mul_succ] at h2
    rw [ha', hb']; omega
  have hstep : t + ell ^ j ≤ ell ^ (j + 1) := by
    obtain ⟨a'', ha''⟩ := htn
    have hNn : ell ^ (j + 1) = ell ^ j * ell := pow_succ ell j
    rw [ha'', hNn] at htN ⊢
    have h1 : a'' < ell := Nat.lt_of_mul_lt_mul_left htN
    have h2 := Nat.mul_le_mul_left (ell ^ j) (Nat.succ_le_of_lt h1)
    rw [Nat.mul_succ] at h2; omega
  have hdivc : ∀ s : ℕ, s < ell ^ (j + 1) → (c + s) / ell ^ (j + 1) * ell ^ (j + 1) = c := by
    intro s hs
    rw [ha', show ell ^ (j + 1) * a' + s = s + ell ^ (j + 1) * a' by ring, Nat.add_mul_div_left _ _ hN,
      Nat.div_eq_of_lt hs, zero_add, Nat.mul_comm]
  rcases Nat.lt_or_ge (t + ell ^ j) (ell ^ (j + 1)) with hlt | hge
  · -- no crossing: contradiction
    exfalso; apply hne
    funext ν
    apply Fin.ext
    by_cases hν : ν = μ
    · subst hν
      rw [corner_val, corner_val, coarseShift_val_eq, hyct, Nat.mod_eq_of_lt (by omega),
        show c + t + ell ^ j = c + (t + ell ^ j) by ring, hdivc _ hlt, hdivc _ htN]
    · rw [corner_val, corner_val, coarseShift_apply_ne _ _ _ _ hν]
  · have htt : t + ell ^ j = ell ^ (j + 1) := le_antisymm hstep hge
    funext ν
    apply Fin.ext
    by_cases hν : ν = μ
    · subst hν
      rw [corner_val, coarseShift_val_eq, coarseShift_val_eq, corner_val, hyct,
        show c + t + ell ^ j = c + ell ^ (j + 1) by omega, hdivc _ htN]
      have hdv : ell ^ (j + 1) ∣ (c + ell ^ (j + 1)) % (L ν + 1) := by
        rw [hb']
        exact (Nat.dvd_mod_iff (Dvd.intro _ rfl)).mpr (Nat.dvd_add ⟨a', ha'⟩ (dvd_refl _))
      rw [Nat.div_mul_cancel hdv]
    · rw [corner_val, coarseShift_apply_ne _ _ _ _ hν, coarseShift_apply_ne _ _ _ _ hν, corner_val]

end patch

#print axioms rowE_nonneg
#print axioms rowF_nonneg
#print axioms norm_add3_sq_le
#print axioms Qa_flat
#print axioms sum_subtype_ite
#print axioms row_lat
#print axioms mass_term
#print axioms mass_ge
#print axioms Qa_cell
#print axioms Qa_Rg
#print axioms Qa_big
#print axioms omGe_Rg
#print axioms crossing

end AdalyFormal.LemIFlat
