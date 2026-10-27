import WN3

/-!
# WN4 (renamed from NF4: module-name collision with deps/base/NF4) -- FlatExt for the two-stratum patch: a right inverse of the FLAT all-rows map `Qrow G 1`

Patch `G = geomOf ℓ (j+1) (patchTower j Rg)` on the fine torus `scaleUp ℓ j Lu'` (rows: level `j` outside `Rg`, level `j+1`
inside `Rg`, `Rg` a union of `ℓ^{j+1}`-blocks).  `E1 = flatE_j ∘ lift`:
* `lift w` : the height-`j` full-tower row vector whose value at an `ℓ^j`-aligned site `z` is `w` at the patch row containing
  `z` (`(j, z)` if `z ∉ Rg`, `(j+1, corner z)` if `z ∈ Rg`);
* `flatE ℓ j Lu'` : M0's smooth right inverse of the flat top-level map at height `j` (FE3).
Facts: `Qrow G 1 (E1 w) = w` (`flat_rightInv_patch`), `‖E1 w‖ ≤ √(729 (ℓ^j)³) √(ℓ³) ‖w‖`,
`‖D_1 E1 w‖ ≤ √(78732 ℓ^j) √(ℓ³) ‖w‖` (each patch row is hit by at most `ℓ³` aligned sites: `card_stepBlockOf_le`).
`flatExt_patch_gen` transports the statement to any torus `L` equal to `scaleUp ℓ j Lu'`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.W3NF

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.QjComposite (Qcomposite stepBlockOf mem_stepBlockOf)
open AdalyFormal.M1Site (QIdx jq yq jq_le yq_mem card_blockOf)
open AdalyFormal.M1Patch (patchTower corner corner_dvd mem_lam_j mem_lam_succ lam_lt lam_gt div_eq_of_aligned)
open AdalyFormal.StatementLane (BlockClosed scaleUp)
open AdalyFormal.SliceCoerc (coarseC GF Qtop)
open AdalyFormal.FlatExt (flatE)

theorem corner_div {L : PeriodicLatticeExtent} {m : ℕ} (hm : 0 < m) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    (corner m x μ).val / m = (x μ).val / m := by
  show (x μ).val / m * m / m = _
  exact Nat.mul_div_cancel _ hm

theorem corner_mem_iff {L : PeriodicLatticeExtent} {m : ℕ} (hm : 0 < m) {Rg : Set (PeriodicLatticeSite L)}
    (hRg : BlockClosed m Rg) (x : PeriodicLatticeSite L) : corner m x ∈ Rg ↔ x ∈ Rg :=
  ⟨fun h => hRg _ h x (fun μ => (corner_div hm x μ).symm), fun h => hRg x h _ (fun μ => corner_div hm x μ)⟩

section patch
variable (ell j : ℕ) (Lu' : PeriodicLatticeExtent) (Rg : Set (PeriodicLatticeSite (scaleUp ell j Lu')))

/-- the patch geometry on `scaleUp ℓ j Lu'` -/
abbrev GQ : TowerGeom (scaleUp ell j Lu') := geomOf ell (j + 1) (patchTower j Rg)

/-- the height-`j` full-tower rows -/
abbrev ZJ : Type := {y // y ∈ (GF ell j Lu').Lam (GF ell j Lu').k}

variable {ell j Lu' Rg}

theorem zj_dvd (z : ZJ ell j Lu') (μ : Fin 3) : ell ^ j ∣ (z.1 μ).val :=
  (fullTower_lam_k ell j Lu' z.1).mp z.2 μ

variable (hell : 0 < ell) (hRg : BlockClosed (ell ^ (j + 1)) Rg)
include hell hRg

/-- the patch row containing an aligned site -/
noncomputable def rowOf (z : ZJ ell j Lu') : QIdx (GQ ell j Lu' Rg) := by
  classical
  exact if h : z.1 ∈ Rg then
    ⟨(⟨j + 1, by show j + 1 < j + 1 + 1; omega⟩, corner (ell ^ (j + 1)) z.1),
      (mem_lam_succ ell j Rg _).mpr ⟨corner_dvd _ _, (corner_mem_iff (pow_pos hell _) hRg _).mpr h⟩⟩
  else
    ⟨(⟨j, by show j < j + 1 + 1; omega⟩, z.1), (mem_lam_j ell j Rg _).mpr ⟨zj_dvd z, h⟩⟩

theorem rowOf_in (z : ZJ ell j Lu') (hz : z.1 ∈ Rg) :
    jq (rowOf hell hRg z) = j + 1 ∧ yq (rowOf hell hRg z) = corner (ell ^ (j + 1)) z.1 := by
  unfold rowOf; rw [dif_pos hz]; exact ⟨rfl, rfl⟩

theorem rowOf_out (z : ZJ ell j Lu') (hz : z.1 ∉ Rg) :
    jq (rowOf hell hRg z) = j ∧ yq (rowOf hell hRg z) = z.1 := by
  unfold rowOf; rw [dif_neg hz]; exact ⟨rfl, rfl⟩

/-- the lift `CRow G → coarseC (GF ℓ j Lu')` -/
noncomputable def liftL : CRow (GQ ell j Lu' Rg) →L[ℝ] coarseC (GF ell j Lu') :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => WithLp.toLp 2 (fun z : ZJ ell j Lu' => w (rowOf hell hRg z))
      map_add' := fun f g => by refine PiLp.ext (fun z => ?_); simp
      map_smul' := fun c f => by refine PiLp.ext (fun z => ?_); simp }

theorem liftL_apply (w : CRow (GQ ell j Lu' Rg)) (z : ZJ ell j Lu') :
    liftL hell hRg w z = w (rowOf hell hRg z) := rfl

/-- every aligned site lies in the step block of its row's base point -/
theorem mem_stepBlock_rowOf (z : ZJ ell j Lu') :
    z.1 ∈ stepBlockOf (yq (rowOf hell hRg z)) (ell ^ j) ell := by
  classical
  rw [mem_stepBlockOf]
  intro μ
  by_cases hz : z.1 ∈ Rg
  · rw [(rowOf_in hell hRg z hz).2]
    show (z.1 μ).val / ell ^ (j + 1) * ell ^ (j + 1) ≤ (z.1 μ).val ∧
      (z.1 μ).val < (z.1 μ).val / ell ^ (j + 1) * ell ^ (j + 1) + ell ^ j * ell ∧
      ell ^ j ∣ (z.1 μ).val - (z.1 μ).val / ell ^ (j + 1) * ell ^ (j + 1)
    have hp : 0 < ell ^ (j + 1) := pow_pos hell _
    refine ⟨Nat.div_mul_le_self _ _, ?_, ?_⟩
    · rw [← pow_succ]
      have := Nat.lt_div_mul_add (a := (z.1 μ).val) hp
      linarith
    · refine Nat.dvd_sub (zj_dvd z μ) ?_
      exact Dvd.dvd.mul_left (pow_dvd_pow ell (Nat.le_succ j)) _
  · rw [(rowOf_out hell hRg z hz).2]
    refine ⟨le_rfl, ?_, by simp⟩
    have : 0 < ell ^ j * ell := Nat.mul_pos (pow_pos hell _) hell
    omega

/-- **`‖lift w‖² ≤ ℓ³ ‖w‖²`** -/
theorem liftL_norm_sq (w : CRow (GQ ell j Lu' Rg)) :
    ‖liftL hell hRg w‖ ^ 2 ≤ (ell : ℝ) ^ 3 * ‖w‖ ^ 2 := by
  classical
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  simp only [liftL_apply]
  rw [← Finset.sum_fiberwise Finset.univ (rowOf hell hRg) (fun z => ‖w (rowOf hell hRg z)‖ ^ 2), Finset.mul_sum]
  refine Finset.sum_le_sum (fun q _ => ?_)
  have hcongr : ∑ z ∈ Finset.univ with rowOf hell hRg z = q, ‖w (rowOf hell hRg z)‖ ^ 2
      = ∑ z ∈ Finset.univ with rowOf hell hRg z = q, ‖w q‖ ^ 2 :=
    Finset.sum_congr rfl (fun z hz => by rw [(Finset.mem_filter.mp hz).2])
  rw [hcongr, Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  have hcard : (Finset.univ.filter (fun z => rowOf hell hRg z = q)).card ≤ ell ^ 3 := by
    refine le_trans ?_ (AdalyFormal.Balaban.ClassPropagationUbar.card_stepBlockOf_le (yq q) (s := ell ^ j)
      (ell := ell) (pow_pos hell j))
    refine Finset.card_le_card_of_injOn (fun z => z.1) ?_ ?_
    · intro z hz
      have hq := (Finset.mem_filter.mp hz).2
      have := mem_stepBlock_rowOf hell hRg z
      rw [hq] at this
      exact this
    · intro z _ z' _ h
      exact Subtype.ext h
  exact_mod_cast hcard

variable (hdvd1 : ∀ μ, ell ^ (j + 1) ∣ scaleUp ell j Lu' μ + 1)
include hdvd1

omit hRg hdvd1 in
/-- the flat block sums of `flatE v` -/
theorem flatE_block (v : coarseC (GF ell j Lu')) (z : ZJ ell j Lu') :
    (1 / (ell : ℝ) ^ 3) ^ j • ∑ x ∈ blockOf z.1 (ell ^ j), (flatE ell j Lu' v) x = v z := by
  have h := congrArg (fun g : coarseC (GF ell j Lu') => g z) (AdalyFormal.FlatExt.flatE_rightInv ell j Lu' hell v)
  simp only at h
  rw [AdalyFormal.FlatExt.Qtop_flat ell j Lu' hell] at h
  exact h

/-- **`Q'(1)` of the patch is right-inverted by `flatE_j ∘ lift`.** -/
theorem flat_rightInv_patch (w : CRow (GQ ell j Lu' Rg)) :
    Qrow (GQ ell j Lu' Rg) (trivialU _) (flatE ell j Lu' (liftL hell hRg w)) = w := by
  classical
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  set f := flatE ell j Lu' (liftL hell hRg w) with hf
  have hbg1 : bgTower (GQ ell j Lu' Rg) (trivialU (scaleUp ell j Lu')) = fun _ => trivialU _ :=
    funext (fun i => AdalyFormal.PortSlice.bgTower_trivialU _ i)
  have hdj : ∀ μ, ell ^ j ∣ scaleUp ell j Lu' μ + 1 := fun μ =>
    Dvd.dvd.trans (pow_dvd_pow ell (Nat.le_succ j)) (hdvd1 μ)
  -- block sums of f on aligned sites
  have hsum : ∀ z : ZJ ell j Lu', ∑ x ∈ blockOf z.1 (ell ^ j), (WithLp.ofLp f) x
      = ((ell : ℝ) ^ j) ^ 3 • w (rowOf hell hRg z) := by
    intro z
    have h := flatE_block hell (liftL hell hRg w) z
    rw [liftL_apply] at h
    rw [← h, smul_smul]
    have : ((ell : ℝ) ^ j) ^ 3 * (1 / (ell : ℝ) ^ 3) ^ j = 1 := by
      rw [one_div_pow, ← pow_mul, ← pow_mul, mul_comm 3 j]; field_simp
    rw [this, one_smul]
  refine PiLp.ext (fun q => ?_)
  rw [Qrow_apply, Qlev_apply, hbg1]
  show Qcomposite (fun _ => trivialU _) ell (jq q) (WithLp.ofLp f) (yq q) = w q
  rw [AdalyFormal.FlatExt.Qcomposite_flat ell hell]
  have hjq : jq q ≤ j + 1 := jq_le q
  have hyq := yq_mem q
  rcases Nat.lt_or_ge (jq q) j with hlt | hge
  · exfalso
    have : (GQ ell j Lu' Rg).Lam (jq q) = ∅ := lam_lt ell j Rg hlt
    rw [this] at hyq; exact hyq
  rcases Nat.eq_or_lt_of_le hge with heq | hgt
  · -- bottom row
    have hj' : jq q = j := heq.symm
    have hy : yq q ∈ (GQ ell j Lu' Rg).Lam j := by have := hyq; rwa [hj'] at this
    obtain ⟨hal, hout⟩ := (mem_lam_j ell j Rg _).mp hy
    set z : ZJ ell j Lu' := ⟨yq q, (fullTower_lam_k ell j Lu' _).mpr hal⟩ with hz
    have hrow : rowOf hell hRg z = q := by
      obtain ⟨h1, h2⟩ := rowOf_out hell hRg z hout
      apply Subtype.ext; apply Prod.ext
      · exact Fin.ext (h1.trans hj'.symm)
      · exact h2
    rw [hj', hsum z, hrow, smul_smul]
    have : (1 / (ell : ℝ) ^ 3) ^ j * ((ell : ℝ) ^ j) ^ 3 = 1 := by
      rw [one_div_pow, ← pow_mul, ← pow_mul, mul_comm 3 j]; field_simp
    rw [this, one_smul]
  · -- top row
    have hj' : jq q = j + 1 := by omega
    have hy : yq q ∈ (GQ ell j Lu' Rg).Lam (j + 1) := by have := hyq; rwa [hj'] at this
    obtain ⟨hal, hin⟩ := (mem_lam_succ ell j Rg _).mp hy
    set y := yq q with hydef
    set SB := stepBlockOf y (ell ^ j) ell with hSB
    have hs : 0 < ell ^ j := pow_pos hell j
    -- every point of the step block is aligned, in `Rg`, with corner `y`
    have hpt : ∀ x ∈ SB, ∃ hx : x ∈ (GF ell j Lu').Lam (GF ell j Lu').k, rowOf hell hRg ⟨x, hx⟩ = q := by
      intro x hxSB
      have hxs := mem_stepBlockOf.mp hxSB
      have hxal : ∀ μ, ell ^ j ∣ (x μ).val := by
        intro μ
        have h1 := (hxs μ).2.2
        have h2 : ell ^ j ∣ (y μ).val := (pow_dvd_pow ell (Nat.le_succ j)).trans (hal μ)
        have h3 := (hxs μ).1
        have : (x μ).val = (x μ).val - (y μ).val + (y μ).val := by omega
        rw [this]; exact Nat.dvd_add h1 h2
      have hdiv : ∀ μ, (y μ).val / ell ^ (j + 1) = (x μ).val / ell ^ (j + 1) := by
        intro μ
        have h1 := (hxs μ).1
        have h2 := (hxs μ).2.1
        rw [← pow_succ] at h2
        have := div_eq_of_aligned (ell := 1) (pow_pos hell (j + 1)) (hal μ) h1 h2
        simpa using this
      have hxR : x ∈ Rg := hRg y hin x (fun μ => (hdiv μ).symm)
      refine ⟨(fullTower_lam_k ell j Lu' x).mpr hxal, ?_⟩
      obtain ⟨h1, h2⟩ := rowOf_in hell hRg ⟨x, (fullTower_lam_k ell j Lu' x).mpr hxal⟩ hxR
      apply Subtype.ext; apply Prod.ext
      · exact Fin.ext (h1.trans hj'.symm)
      · refine h2.trans ?_
        funext μ
        apply Fin.ext
        show (x μ).val / ell ^ (j + 1) * ell ^ (j + 1) = (y μ).val
        rw [← hdiv μ]
        exact Nat.div_mul_cancel (hal μ)
    have hblk : ∑ x ∈ blockOf y (ell ^ (j + 1)), (WithLp.ofLp f) x
        = ∑ x ∈ SB, ((ell : ℝ) ^ j) ^ 3 • w q := by
      rw [pow_succ, ← AdalyFormal.FlatExt.sum_stepBlock_blockOf (ell ^ j) ell hs y (fun x => (WithLp.ofLp f) x)]
      refine Finset.sum_congr rfl (fun x hx => ?_)
      obtain ⟨hxL, hrow⟩ := hpt x hx
      have := hsum ⟨x, hxL⟩
      rw [hrow] at this
      exact this
    -- count: |SB| ℓ^{3j} = ℓ^{3(j+1)}
    have hfitj : ∀ x ∈ SB, ∀ μ, (x μ).val + ell ^ j ≤ scaleUp ell j Lu' μ + 1 := by
      intro x hx
      obtain ⟨hxL, -⟩ := hpt x hx
      have hc : x ∈ CoarseLattice (scaleUp ell j Lu') (ell ^ j) := by
        rw [mem_CoarseLattice]; intro μ
        exact Nat.mod_eq_zero_of_dvd ((fullTower_lam_k ell j Lu' x).mp hxL μ)
      exact AdalyFormal.Balaban.PoincareBridge.coarseLattice_fits hdj hc
    have hyc : y ∈ CoarseLattice (scaleUp ell j Lu') (ell ^ (j + 1)) := by
      rw [mem_CoarseLattice]; intro μ; exact Nat.mod_eq_zero_of_dvd (hal μ)
    have hfity := AdalyFormal.Balaban.PoincareBridge.coarseLattice_fits hdvd1 hyc
    have hcount : (SB.card : ℝ) * ((ell : ℝ) ^ j) ^ 3 = ((ell : ℝ) ^ (j + 1)) ^ 3 := by
      have h1 := AdalyFormal.FlatExt.sum_stepBlock_blockOf (L := scaleUp ell j Lu') (M := ℝ) (ell ^ j) ell hs y
        (fun _ => (1 : ℝ))
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h1
      rw [← pow_succ, card_blockOf y _ hfity] at h1
      rw [Finset.sum_congr rfl (fun x hx => by rw [card_blockOf x _ (hfitj x hx)])] at h1
      rw [Finset.sum_const, nsmul_eq_mul] at h1
      rw [← hSB] at h1
      push_cast at h1
      linarith
    have : (1 / (ell : ℝ) ^ 3) ^ (j + 1) * ((SB.card : ℝ) * ((ell : ℝ) ^ j) ^ 3) = 1 := by
      rw [hcount, one_div_pow, ← pow_mul, ← pow_mul, mul_comm 3 (j + 1)]; field_simp
    rw [hj', hblk, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, smul_smul, mul_assoc, this, one_smul]

end patch

/-- the FlatExt constants -/
noncomputable def aEP (ell j : ℕ) : ℝ := Real.sqrt (729 * ((ell : ℝ) ^ j) ^ 3) * Real.sqrt ((ell : ℝ) ^ 3)
noncomputable def bEP (ell j : ℕ) : ℝ := Real.sqrt (78732 * (ell : ℝ) ^ j) * Real.sqrt ((ell : ℝ) ^ 3)

theorem aEP_nonneg (ell j : ℕ) : 0 ≤ aEP ell j := by unfold aEP; positivity
theorem bEP_nonneg (ell j : ℕ) : 0 ≤ bEP ell j := by unfold bEP; positivity

/-- **FlatExt on the patch** (torus `scaleUp ℓ j Lu'`). -/
theorem flatExt_patch (ell j : ℕ) (hell : 0 < ell) (Lu' : PeriodicLatticeExtent)
    (Rg : Set (PeriodicLatticeSite (scaleUp ell j Lu'))) (hRg : BlockClosed (ell ^ (j + 1)) Rg)
    (hdvd1 : ∀ μ, ell ^ (j + 1) ∣ scaleUp ell j Lu' μ + 1) :
    ∃ E1 : CRow (GQ ell j Lu' Rg) →L[ℝ] SiteL2 (scaleUp ell j Lu'),
      (∀ w, Qrow (GQ ell j Lu' Rg) (trivialU _) (E1 w) = w) ∧ (∀ w, ‖E1 w‖ ≤ aEP ell j * ‖w‖) ∧
      (∀ w, ‖gradL2 (trivialU _) (E1 w)‖ ≤ bEP ell j * ‖w‖) := by
  refine ⟨(flatE ell j Lu').comp (liftL hell hRg), fun w => flat_rightInv_patch hell hRg hdvd1 w, fun w => ?_,
    fun w => ?_⟩
  · have h1 := AdalyFormal.FlatExt.flatE_norm_le ell j Lu' hell (liftL hell hRg w)
    have h2 : ‖liftL hell hRg w‖ ≤ Real.sqrt ((ell : ℝ) ^ 3) * ‖w‖ :=
      AdalyFormal.FlatExt.norm_le_of_sq _ (by positivity) (norm_nonneg _) (norm_nonneg _) (liftL_norm_sq hell hRg w)
    show ‖flatE ell j Lu' (liftL hell hRg w)‖ ≤ _
    unfold aEP
    calc _ ≤ _ := h1
      _ ≤ Real.sqrt (729 * ((ell : ℝ) ^ j) ^ 3) * (Real.sqrt ((ell : ℝ) ^ 3) * ‖w‖) :=
          mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
      _ = _ := by ring
  · have h1 := AdalyFormal.FlatExt.flatE_grad_norm_le ell j Lu' hell (liftL hell hRg w)
    have h2 : ‖liftL hell hRg w‖ ≤ Real.sqrt ((ell : ℝ) ^ 3) * ‖w‖ :=
      AdalyFormal.FlatExt.norm_le_of_sq _ (by positivity) (norm_nonneg _) (norm_nonneg _) (liftL_norm_sq hell hRg w)
    show ‖gradL2 (trivialU _) (flatE ell j Lu' (liftL hell hRg w))‖ ≤ _
    unfold bEP
    calc _ ≤ _ := h1
      _ ≤ Real.sqrt (78732 * (ell : ℝ) ^ j) * (Real.sqrt ((ell : ℝ) ^ 3) * ‖w‖) :=
          mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
      _ = _ := by ring

/-- **FlatExt on the patch, any torus equal to `scaleUp ℓ j Lu'`** (transport by `subst`). -/
theorem flatExt_patch_gen (ell j : ℕ) (hell : 0 < ell) (Lu' : PeriodicLatticeExtent) :
    ∀ (L : PeriodicLatticeExtent), scaleUp ell j Lu' = L → ∀ (Rg : Set (PeriodicLatticeSite L)),
      BlockClosed (ell ^ (j + 1)) Rg → (∀ μ, ell ^ (j + 1) ∣ L μ + 1) →
      ∃ E1 : CRow (geomOf ell (j + 1) (patchTower j Rg)) →L[ℝ] SiteL2 L,
        (∀ w, Qrow (geomOf ell (j + 1) (patchTower j Rg)) (trivialU L) (E1 w) = w) ∧
        (∀ w, ‖E1 w‖ ≤ aEP ell j * ‖w‖) ∧ (∀ w, ‖gradL2 (trivialU L) (E1 w)‖ ≤ bEP ell j * ‖w‖) := by
  intro L hL
  subst hL
  intro Rg hRg hdvd1
  exact flatExt_patch ell j hell Lu' Rg hRg hdvd1

/-- the torus identity `scaleUp ℓ j (scaleUp ℓ 1 Lu) = scaleUp ℓ (j+1) Lu`. -/
theorem scaleUp_split (ell j : ℕ) (hell : 0 < ell) (Lu : PeriodicLatticeExtent) :
    scaleUp ell j (scaleUp ell 1 Lu) = scaleUp ell (j + 1) Lu := by
  funext μ
  show ((Lu μ + 1) * ell ^ 1 - 1 + 1) * ell ^ j - 1 = (Lu μ + 1) * ell ^ (j + 1) - 1
  have h1 : 1 ≤ (Lu μ + 1) * ell ^ 1 := by rw [pow_one]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  rw [Nat.sub_add_cancel h1, pow_one, pow_succ, mul_assoc, mul_comm ell (ell ^ j)]

#print axioms corner_div
#print axioms corner_mem_iff
#print axioms rowOf_in
#print axioms rowOf_out
#print axioms mem_stepBlock_rowOf
#print axioms liftL_norm_sq
#print axioms flatE_block
#print axioms flat_rightInv_patch
#print axioms aEP_nonneg
#print axioms bEP_nonneg
#print axioms flatExt_patch
#print axioms flatExt_patch_gen
#print axioms scaleUp_split

end AdalyFormal.W3NF
