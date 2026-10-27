import DLR67
import DLR68
import BC3

/-!
# DL69 -- the per-step second jet in `ℓ¹ ← ℓ²` on the aligned sublattices

**`C2Step_l1`** : for `n = s·ell` with `n ∣ L ν + 1`, a regular background with loops within `1/16` of `1` at every
`n`-aligned bond, and any coordinate field `Y`,
  `Σ_{c n-aligned} ‖suOf (C2StepX s ell V0 Y c)‖ ≤ K2s ell · Σ_{e s-aligned} ‖suOf (Y e)‖²`,
  `K2s ell = 2·192·√3·3613500·(3 ell)²`  (k-, s-, volume-free).
Pieces: `C2StepX_row_le` (DL67) with `β_c² = Σ_{e∈Vis(c)} ‖toM2 (Y e)‖_F²`, `sum_vis_le` (DL68),
`‖suOf v‖² = ½‖toM2 v‖_F²` and `‖suOf v‖ ≤ √3 ‖v‖_∞`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.DLayer

open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.RMapLipschitz (frobSq frobNorm frobSq_nonneg frobNorm_nonneg frobNorm_sq norm_sq_eq_half_frobSq)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (loopVar)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.IngredientFamilyR2 (C2StepX RegBg XS toM2 toM2_mem)
open AdalyFormal.NonflatJet (suOf)

local notation "Mt" => Matrix (Fin 2) (Fin 2) ℂ

variable {L : PeriodicLatticeExtent}

theorem norm_suOf_sq (v : Fin 3 → ℝ) : ‖suOf v‖ ^ 2 = frobNorm (toM2 v) ^ 2 / 2 := by
  rw [norm_sq_eq_half_frobSq, frobNorm_sq]
  show (1 / 2 : ℝ) * frobSq (toM2 v) = frobSq (toM2 v) / 2
  ring

theorem frobSq_toM2 (v : Fin 3 → ℝ) : frobSq (toM2 v) = 2 * (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) := by
  unfold frobSq
  simp [toM2, Fin.sum_univ_two, Complex.normSq_apply]
  ring

theorem norm_suOf_le (v : Fin 3 → ℝ) : ‖suOf v‖ ≤ Real.sqrt 3 * ‖v‖ := by
  have h1 : ‖suOf v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
    rw [norm_suOf_sq, frobNorm_sq, frobSq_toM2]; ring
  have hv : ∀ i, |v i| ≤ ‖v‖ := fun i => by
    have := norm_le_pi_norm v i; rwa [Real.norm_eq_abs] at this
  have h2 : ‖suOf v‖ ^ 2 ≤ (Real.sqrt 3 * ‖v‖) ^ 2 := by
    rw [h1, mul_pow, Real.sq_sqrt (by norm_num)]
    have a0 := sq_le_sq' (neg_le_of_abs_le (hv 0)) (le_of_abs_le (hv 0))
    have a1 := sq_le_sq' (neg_le_of_abs_le (hv 1)) (le_of_abs_le (hv 1))
    have a2 := sq_le_sq' (neg_le_of_abs_le (hv 2)) (le_of_abs_le (hv 2))
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

noncomputable def K2s (ell : ℕ) : ℝ := 2 * 192 * Real.sqrt 3 * 3613500 * (3 * (ell : ℝ)) ^ 2

open Classical in
theorem C2Step_l1 (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell) (hn : ∀ ν, s * ell ∣ L ν + 1)
    (V0 : PeriodicLinkConfiguration SU2 L) (hreg : RegBg s ell V0)
    (hW : ∀ c : CoarseBond L (s * ell), ∀ x ∈ stepBlockOf c.1.1 s ell,
      frobNorm (((loopVar s ell V0 (c.1.1, c.2) x : SU2) : Mt) - 1) ≤ 1 / 16)
    (Y : XS L) :
    ∑ c : CoarseBond L (s * ell), ‖suOf (C2StepX s ell V0 Y (c.1.1, c.2))‖
      ≤ K2s ell * ∑ e : CoarseBond L s, ‖suOf (Y (e.1.1, e.2))‖ ^ 2 := by
  set K : ℝ := 3613500 * (3 * (ell : ℝ)) ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  set g : PeriodicLatticeEdge L → ℝ := fun e => frobNorm (toM2 (Y e)) ^ 2 with hg
  have hg0 : ∀ e, 0 ≤ g e := fun e => sq_nonneg _
  have hrow : ∀ c : CoarseBond L (s * ell), ‖suOf (C2StepX s ell V0 Y (c.1.1, c.2))‖
      ≤ Real.sqrt 3 * K * ∑ e ∈ Finset.univ.filter (fun e => VisStep s ell (c.1.1, c.2) e), g e := by
    intro c
    set S := ∑ e ∈ Finset.univ.filter (fun e => VisStep s ell (c.1.1, c.2) e), g e with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg (fun e _ => hg0 e)
    have hβ : ∀ e, VisStep s ell (c.1.1, c.2) e → frobNorm (toM2 (Y e)) ≤ Real.sqrt S := by
      intro e he
      have h1 : g e ≤ S := Finset.single_le_sum (fun e _ => hg0 e)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
      rw [← Real.sqrt_sq (frobNorm_nonneg (toM2 (Y e)))]
      exact Real.sqrt_le_sqrt h1
    have hr := C2StepX_row_le s ell hs hell V0 hreg (c.1.1, c.2) (hW c) Y (Real.sqrt S) (Real.sqrt_nonneg _) hβ
    rw [Real.sq_sqrt hS0] at hr
    refine (norm_suOf_le _).trans ?_
    have := mul_le_mul_of_nonneg_left hr (Real.sqrt_nonneg 3)
    rw [hK]; linarith
  refine (Finset.sum_le_sum (fun c _ => hrow c)).trans ?_
  rw [← Finset.mul_sum]
  have hsum := sum_vis_le s ell hs hell hn g hg0
  have hconv : ∑ e : CoarseBond L s, g (e.1.1, e.2) = 2 * ∑ e : CoarseBond L s, ‖suOf (Y (e.1.1, e.2))‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [hg, norm_suOf_sq]; ring
  rw [hconv] at hsum
  have h3 : 0 ≤ Real.sqrt 3 * K := by positivity
  have := mul_le_mul_of_nonneg_left hsum h3
  unfold K2s; rw [hK] at this ⊢
  linarith

#print axioms norm_suOf_le
#print axioms C2Step_l1

end AdalyFormal.DLayer
