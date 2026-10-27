import DLR70
import NJE7

/-!
# DL71 -- **the one-step linear jet at a CURVED background in `ℓ¹`**: `A_s ≤ ell⁻² + 1536·ell·κ`

`Lq` the stride-`s` sublattice (`L μ + 1 = s (Lq μ + 1)`, `ell ∣ Lq μ + 1`), `V0` regular with the links of `resV V0`
within `ε0` of `1` (`rhoOf ell ε0 < π/2`), `κ = e2Majorant (rhoOf ell ε0)`:
  **`Qlin_l1`** : `Σ_{c (s·ell)-aligned} ‖suOf (QlinStepX s ell V0 w c)‖ ≤ (ell⁻² + 1536·ell·κ) Σ_{e s-aligned} ‖suOf (w e)‖`.
Pieces: row locality (DL28 `QlinStepX_row_local`) to restrict `w` to `VisStep c`; the CURVED derivative formula
(NJE5 `fderiv_qStepX_stride_apply`: `D qStep(0)w (embE c) = ell · q124Principal(...)`); `q124 = T1 + Δ` with
`‖Δ‖ ≤ 8κ·sup` (NJ9dQ124 `q124_sub_T1_le`) applied to the RESTRICTED field (sup ≤ the visible ℓ¹ mass);
`T1` in `ℓ¹` (DL70, isometric conjugations: background-free `ell⁻³`); visible multiplicity 192 (DL68).
At `κ = 0` this is the flat value `ell⁻²` (one step of `ℓ¹` contraction `ell⁻²` against the `ell` of `L^j Q_j`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.DLayer

open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.RMapLipschitz (frobSq frobNorm frobSq_nonneg frobNorm_nonneg frobNorm_sq norm_sq_eq_half_frobSq)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2NegOne)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (loopVar)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.TowerLawCov (unitToCoarseCov)
open AdalyFormal.Balaban.StridedAveraging (mem_coarseLattice_one)
open AdalyFormal.IngredientFamilyR2 (QlinStepX RegBg XS toM2 toM2_mem fromM2 toM2_fromM2)
open AdalyFormal.NonflatJet (suOf embE embS embS_val embS_injective resV resA fA l1 rhoOf guard_of_small
  q124_sub_T1_le fderiv_qStepX_stride_apply)
open AdalyFormal.BondComposite (sum_embE embS_surj)
open EstimatesLayer.E1E3 (e2Majorant)

variable {L Lq : PeriodicLatticeExtent} {s : ℕ}

open Classical in
/-- edges of the sublattice torus ↔ `s`-aligned bonds of `L` -/
theorem sum_embE_edge' (hs : ∀ μ, L μ + 1 = s * (Lq μ + 1)) (g : PeriodicLatticeEdge L → ℝ) :
    ∑ e : PeriodicLatticeEdge Lq, g (embE hs e) = ∑ c : CoarseBond L s, g (c.1.1, c.2) := by
  have hs0 : 0 < s := AdalyFormal.NonflatJet.s_pos_of hs
  refine Fintype.sum_bijective (fun e : PeriodicLatticeEdge Lq => ((⟨embS hs e.1, mem_CoarseLattice.mpr (fun μ => by
      rw [embS_val]; exact Nat.mul_mod_right _ _)⟩, e.2) : CoarseBond L s)) ⟨?_, ?_⟩ _ _ (fun e => rfl)
  · intro e e' h
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
    exact Prod.ext (embS_injective hs h.1) h.2
  · intro c
    obtain ⟨y, hy⟩ := embS_surj hs c.1.1 (fun μ => Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp c.1.2 μ))
    exact ⟨(y, c.2), Prod.ext (Subtype.ext hy) rfl⟩

/-- `CoarseBond Lq ell ≃ CoarseBond Lq (1 * ell)` for summands reading only `(c₋, μ)` -/
theorem sum_one_mul (ell : ℕ) (F : PeriodicLatticeSite Lq → Fin 3 → ℝ) :
    ∑ c : CoarseBond Lq ell, F c.1.1 c.2 = ∑ c : CoarseBond Lq (1 * ell), F c.1.1 c.2 := by
  refine Fintype.sum_bijective (fun c : CoarseBond Lq ell =>
      ((⟨c.1.1, by rw [one_mul]; exact c.1.2⟩, c.2) : CoarseBond Lq (1 * ell))) ⟨?_, ?_⟩ _ _ (fun c => rfl)
  · intro c c' h
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
    exact Prod.ext (Subtype.ext h.1) h.2
  · rintro ⟨⟨y, hy⟩, μ⟩
    have hy' : y ∈ CoarseLattice Lq ell := by rwa [one_mul] at hy
    exact ⟨(⟨y, hy'⟩, μ), rfl⟩

theorem sum_lin {ι : Type*} (S : Finset ι) (f g : ι → ℝ) (a b : ℝ) :
    ∑ i ∈ S, a * (f i + b * g i) = a * ∑ i ∈ S, f i + a * b * ∑ i ∈ S, g i := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem suOf_fromM2 (X : SuTwo) : suOf (fromM2 (X : M2)) = X := by
  apply Subtype.ext
  exact toM2_fromM2 X.2

open Classical in
theorem Qlin_l1 (hs : ∀ μ, L μ + 1 = s * (Lq μ + 1)) (ell : ℕ) (hell : 0 < ell)
    (hdvdq : ∀ μ, ell ∣ Lq μ + 1) (V0 : PeriodicLinkConfiguration SU2 L) (hreg : RegBg s ell V0)
    (ε0 : ℝ) (hε0 : 0 ≤ ε0) (hV : ∀ e, frobNorm (((resV hs V0 e : SU2) : M2) - 1) ≤ ε0)
    (hsmall : rhoOf ell ε0 < Real.pi / 2) (w : XS L) :
    ∑ c : CoarseBond L (s * ell), ‖suOf (QlinStepX s ell V0 w (c.1.1, c.2))‖
      ≤ (1 / (ell : ℝ) ^ 2 + 1536 * ell * e2Majorant (rhoOf ell ε0)) * ∑ e : CoarseBond L s, ‖suOf (w (e.1.1, e.2))‖ := by
  have hs0 : 0 < s := AdalyFormal.NonflatJet.s_pos_of hs
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hn : ∀ ν, s * ell ∣ L ν + 1 := fun ν => by rw [hs ν]; exact Nat.mul_dvd_mul_left s (hdvdq ν)
  set κ := e2Majorant (rhoOf ell ε0) with hκ
  have hκ0 : 0 ≤ κ := by
    have : 0 ≤ rhoOf ell ε0 := by unfold rhoOf; positivity
    exact EstimatesLayer.E1E3.e2Majorant_nonneg this
  -- the unrestricted unit field on Lq
  set A : CoarseBond Lq 1 → SuTwo := fun b => suOf (resA hs w (b.1.1, b.2)) with hAdef
  -- per-c' bound
  set Vis : PeriodicLatticeEdge L → Finset (PeriodicLatticeEdge L) :=
    fun C => Finset.univ.filter (fun e => VisStep s ell C e) with hVis
  have hrow : ∀ c' : CoarseBond Lq ell,
      ‖suOf (QlinStepX s ell V0 w (embE hs (c'.1.1, c'.2)))‖
        ≤ (ell : ℝ) * ((1 / (ell : ℝ) ^ 4) * ∑ u ∈ AdalyFormal.Balaban.ThirdLevelArrows.unitSitesOf 1 (1 * ell) c'.1.1,
              ∑ i ∈ Finset.range ell, fA A (AdalyFormal.Balaban.QOne.pathSite u.1 c'.2 (i * 1), c'.2)
            + 8 * κ * ∑ e ∈ Vis (embE hs (c'.1.1, c'.2)), ‖suOf (w e)‖) := by
    intro c'
    set C := embE hs (c'.1.1, c'.2) with hC
    set w' : XS L := restrX (VisStep s ell C) w with hw'
    -- row locality
    have hloc : QlinStepX s ell V0 w C = QlinStepX s ell V0 w' C := by
      have h0 := QlinStepX_row_local s ell V0 hreg C (w - w') (fun e he => by
        rw [Pi.sub_apply, hw', restrX_eq_on _ _ _ he, sub_self])
      rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
      exact h0
    -- the curved derivative formula
    have hcell : c'.1.1 ∈ CoarseLattice Lq ell := c'.1.2
    have hnc2 : ∀ x ∈ stepBlockOf (c'.1.1, c'.2).1 1 ell, loopVar 1 ell (resV hs V0) (c'.1.1, c'.2) x ≠ su2NegOne :=
      fun x hx => guard_of_small (resV hs V0) ε0 hε0 hV hsmall c' x hx
    have hjet := fderiv_qStepX_stride_apply hs V0 ell hreg (c'.1.1, c'.2) hcell hell hdvdq hnc2 w'
    set A' : CoarseBond Lq 1 → SuTwo := fun b => suOf (resA hs w' (b.1.1, b.2)) with hA'def
    have hA' : fineDirToUnitBond (fun e => toM2 (resA hs w' e))
        (fun e => (toM2_mem (resA hs w' e)).1) (fun e => (toM2_mem (resA hs w' e)).2) = A' := rfl
    rw [hA'] at hjet
    set c'' : CoarseBond Lq (1 * ell) := (⟨⟨c'.1.1, by rw [one_mul]; exact hcell⟩, c'.2⟩ : CoarseBond Lq (1 * ell))
    have hX : suOf (QlinStepX s ell V0 w C) = (ell : ℝ) • AdalyFormal.DeltaKR85.q124Principal 1 ell (resV hs V0) A' c'' := by
      rw [hloc]
      apply Subtype.ext
      show toM2 (QlinStepX s ell V0 w' C) = _
      have e1 : QlinStepX s ell V0 w' C = fderiv ℝ (AdalyFormal.IngredientFamilyR2.qStepX s ell V0) 0 w' C := rfl
      rw [e1, hC, hjet, map_smul, toM2_fromM2 (AdalyFormal.DeltaKR85.q124Principal 1 ell (resV hs V0) A' c'').2]
      rfl
    rw [hX, norm_smul, Real.norm_of_nonneg hellR.le]
    refine mul_le_mul_of_nonneg_left ?_ hellR.le
    -- split q124 = T1 + Δ
    set M := ∑ e ∈ Vis C, ‖suOf (w e)‖ with hM
    have hM0 : 0 ≤ M := Finset.sum_nonneg (fun e _ => norm_nonneg _)
    have hA'b : ∀ b, ‖A' b‖ ≤ M := by
      intro b
      by_cases hv : VisStep s ell C (embE hs (b.1.1, b.2))
      · have e2 : A' b = suOf (w (embE hs (b.1.1, b.2))) := by
          simp only [hA'def, AdalyFormal.NonflatJet.resA, hw', restrX_eq_on _ _ _ hv]
        rw [e2]
        exact Finset.single_le_sum (f := fun e => ‖suOf (w e)‖) (fun e _ => norm_nonneg _)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩)
      · have e2 : A' b = 0 := by
          simp only [hA'def, AdalyFormal.NonflatJet.resA, hw']
          rw [restrX_apply, if_neg hv]
          apply Subtype.ext
          show toM2 0 = 0
          exact map_zero _
        rw [e2, norm_zero]; exact hM0
    have hd := q124_sub_T1_le hell hdvdq (resV hs V0) ε0 hε0 hV hsmall A' M hM0 hA'b c''
    have hT := T1_pointwise_l1 (resV hs V0) A' c''
    have hdom : ∀ e : PeriodicLatticeEdge Lq, fA A' e ≤ fA A e := by
      intro e
      show ‖A' (⟨e.1, mem_coarseLattice_one e.1⟩, e.2)‖ ≤ ‖A (⟨e.1, mem_coarseLattice_one e.1⟩, e.2)‖
      by_cases hv : VisStep s ell C (embE hs (e.1, e.2))
      · have e2 : A' (⟨e.1, mem_coarseLattice_one e.1⟩, e.2) = A (⟨e.1, mem_coarseLattice_one e.1⟩, e.2) := by
          simp only [hA'def, hAdef, AdalyFormal.NonflatJet.resA, hw', restrX_eq_on _ _ _ hv]
        rw [e2]
      · have e2 : A' (⟨e.1, mem_coarseLattice_one e.1⟩, e.2) = 0 := by
          simp only [hA'def, AdalyFormal.NonflatJet.resA, hw']
          rw [restrX_apply, if_neg hv]
          apply Subtype.ext
          show toM2 0 = 0
          exact map_zero _
        rw [e2, norm_zero]; exact norm_nonneg _
    have hT' : ‖unitToCoarseCov 1 ell (resV hs V0) A' c''‖
        ≤ (1 / (ell : ℝ) ^ 4) * ∑ u ∈ AdalyFormal.Balaban.ThirdLevelArrows.unitSitesOf 1 (1 * ell) c'.1.1,
            ∑ i ∈ Finset.range ell, fA A (AdalyFormal.Balaban.QOne.pathSite u.1 c'.2 (i * 1), c'.2) := by
      refine hT.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun i _ =>
        hdom _) (by positivity))
    have htri : ‖AdalyFormal.DeltaKR85.q124Principal 1 ell (resV hs V0) A' c''‖
        ≤ ‖unitToCoarseCov 1 ell (resV hs V0) A' c''‖
          + ‖AdalyFormal.DeltaKR85.q124Principal 1 ell (resV hs V0) A' c'' - unitToCoarseCov 1 ell (resV hs V0) A' c''‖ := by
      have := norm_add_le (unitToCoarseCov 1 ell (resV hs V0) A' c'')
        (AdalyFormal.DeltaKR85.q124Principal 1 ell (resV hs V0) A' c'' - unitToCoarseCov 1 ell (resV hs V0) A' c'')
      rwa [add_sub_cancel] at this
    linarith
  -- sum over c'
  have hsumE := sum_embE hs ell (fun e => ‖suOf (QlinStepX s ell V0 w e)‖)
  rw [← hsumE]
  refine (Finset.sum_le_sum fun c' _ => hrow c').trans ?_
  rw [sum_lin]
  -- T1 counting
  have hT1 := T1_count hell A
  have hl1 : l1 (fA A) = ∑ e : CoarseBond L s, ‖suOf (w (e.1.1, e.2))‖ := by
    unfold l1
    rw [← sum_embE_edge' hs (fun e => ‖suOf (w e)‖)]
    rfl
  rw [hl1] at hT1
  -- visible counting
  have hV2 : ∑ c' : CoarseBond Lq ell, ∑ e ∈ Vis (embE hs (c'.1.1, c'.2)), ‖suOf (w e)‖
      ≤ 192 * ∑ e : CoarseBond L s, ‖suOf (w (e.1.1, e.2))‖ := by
    have h1 := sum_embE hs ell (fun e => ∑ e' ∈ Vis e, ‖suOf (w e')‖)
    rw [h1]
    exact sum_vis_le s ell hs0 hell hn (fun e => ‖suOf (w e)‖) (fun e => norm_nonneg _)
  set S1 := ∑ e : CoarseBond L s, ‖suOf (w (e.1.1, e.2))‖ with hS1
  have hS10 : 0 ≤ S1 := Finset.sum_nonneg (fun e _ => norm_nonneg _)
  have hT1' : ∑ c' : CoarseBond Lq ell, (1 / (ell : ℝ) ^ 4) *
      ∑ u ∈ AdalyFormal.Balaban.ThirdLevelArrows.unitSitesOf 1 (1 * ell) c'.1.1,
        ∑ i ∈ Finset.range ell, fA A (AdalyFormal.Balaban.QOne.pathSite u.1 c'.2 (i * 1), c'.2)
      ≤ (1 / (ell : ℝ) ^ 3) * S1 := by
    have hbij := sum_one_mul (Lq := Lq) ell (fun y μ => (1 / (ell : ℝ) ^ 4) *
      ∑ u ∈ AdalyFormal.Balaban.ThirdLevelArrows.unitSitesOf 1 (1 * ell) y,
        ∑ i ∈ Finset.range ell, fA A (AdalyFormal.Balaban.QOne.pathSite u.1 μ (i * 1), μ))
    rw [hbij]; exact hT1
  have hfin : (ell : ℝ) * ((1 / (ell : ℝ) ^ 3) * S1 + 8 * κ * (192 * S1))
      = (1 / (ell : ℝ) ^ 2 + 1536 * ell * κ) * S1 := by
    field_simp; ring
  rw [← hfin, mul_add, ← mul_assoc]
  refine add_le_add (mul_le_mul_of_nonneg_left hT1' hellR.le) ?_
  have h9 := mul_le_mul_of_nonneg_left hV2 (by positivity : (0 : ℝ) ≤ (ell : ℝ) * 8 * κ)
  have h10 : (ell : ℝ) * 8 * κ * (192 * S1) = (ell : ℝ) * (8 * κ * (192 * S1)) := by ring
  linarith

#print axioms sum_embE_edge'
#print axioms Qlin_l1

end AdalyFormal.DLayer
