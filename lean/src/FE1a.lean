import AdalyFormal.Balaban.FourierFaithfulU1

/-!
# FE1a -- LOCAL block Cauchy-Schwarz (scalar): the localisation of `FourierFaithfulU1.sum_sq_coarseCurl_le`.
For a set `Y` of coarse centres whose `ell^2`-windows (shifts `i e_mu + j e_nu` of block sites) all lie in a fine site
set `Pd`:   ell * sum_{y in Y} (coarse curl of the faithful Q_ell A)(y,d)^2  <=  sum_{z in Pd} (curl A)(z,d)^2.
Same proof as the upstream (pointwise Cauchy-Schwarz over the ell^5 terms, then exact reindexing), the only change is that the
total over centres is bounded by the sum over the image of the (disjoint) union of blocks of `Y`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.FlatEllGeneral

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators
open AdalyFormal.Balaban.CoarseCurl
open AdalyFormal.Balaban.CoarseShiftCovariance
open AdalyFormal.Balaban.LineIntegralAveraging
open AdalyFormal.Balaban.FourierFaithfulU1

variable {L : PeriodicLatticeExtent}

theorem local_sum_sq_coarseCurl_le {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (A : Bond L → ℝ) (d : PeriodicPlaquetteDirections)
    (Y : Finset {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}) (Pd : Finset (PeriodicLatticeSite L))
    (hY : ∀ y ∈ Y, ∀ x ∈ blockOf y.1 ell, ∀ i ∈ Finset.range ell, ∀ j ∈ Finset.range ell,
      coarseShift (coarseShift x j d.1.2) i d.1.1 ∈ Pd) :
    (ell : ℝ) * ∑ y ∈ Y, (coarseCurlValue hdvd (lineCoarseRestrict ell A) (y, d)) ^ 2
      ≤ ∑ z ∈ Pd, (curlValue A (z, d)) ^ 2 := by
  classical
  have hellR : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  set f : PeriodicLatticeSite L → ℝ := fun z => (curlValue A (z, d)) ^ 2 with hf
  set T : PeriodicLatticeSite L → ℝ := fun y =>
    ∑ x ∈ blockOf y ell, ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
      (curlValue A (coarseShift (coarseShift x j d.1.2) i d.1.1, d)) ^ 2 with hT
  -- pointwise Cauchy-Schwarz (as upstream)
  have hpointwise : ∀ y : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell},
      (coarseCurlValue hdvd (lineCoarseRestrict ell A) (y, d)) ^ 2
        ≤ (1 / (ell : ℝ) ^ 3) * T y.1 := by
    intro y
    set s : Finset (PeriodicLatticeSite L × (ℕ × ℕ)) :=
      (blockOf y.1 ell) ×ˢ (Finset.range ell ×ˢ Finset.range ell) with hs
    set F : PeriodicLatticeSite L × (ℕ × ℕ) → ℝ := fun t =>
      curlValue A (coarseShift (coarseShift t.1 t.2.2 d.1.2) t.2.1 d.1.1, d) with hF
    have hsum : (∑ t ∈ s, F t) = ∑ x ∈ blockOf y.1 ell, ∑ i ∈ Finset.range ell,
        ∑ j ∈ Finset.range ell,
          curlValue A (coarseShift (coarseShift x j d.1.2) i d.1.1, d) := by
      rw [hs, Finset.sum_product]
      exact Finset.sum_congr rfl fun x _ => by rw [Finset.sum_product]
    have hsumsq : (∑ t ∈ s, (F t) ^ 2) = ∑ x ∈ blockOf y.1 ell, ∑ i ∈ Finset.range ell,
        ∑ j ∈ Finset.range ell,
          (curlValue A (coarseShift (coarseShift x j d.1.2) i d.1.1, d)) ^ 2 := by
      rw [hs, Finset.sum_product]
      exact Finset.sum_congr rfl fun x _ => by rw [Finset.sum_product]
    have hcard : (s.card : ℝ) = (ell : ℝ) ^ 5 := by
      simp only [hs, Finset.card_product, Finset.card_range,
        card_blockOf_of_coarse hdvd y.2]
      push_cast
      ring
    have hCS : (∑ t ∈ s, F t) ^ 2 ≤ (ell : ℝ) ^ 5 * ∑ t ∈ s, (F t) ^ 2 := by
      have h := sq_sum_le_card_mul_sum_sq (s := s) (f := F)
      rw [hcard] at h
      exact h
    have hTy : T y.1 = ∑ t ∈ s, (F t) ^ 2 := by
      rw [hT]
      exact hsumsq.symm
    rw [coarseCurl_lineCoarseRestrict_eq_blockSum hell hdvd A y d, ← hsum, hTy]
    calc ((1 / (ell : ℝ) ^ 4) * ∑ t ∈ s, F t) ^ 2
        = (1 / (ell : ℝ) ^ 8) * (∑ t ∈ s, F t) ^ 2 := by ring
      _ ≤ (1 / (ell : ℝ) ^ 8) * ((ell : ℝ) ^ 5 * ∑ t ∈ s, (F t) ^ 2) :=
          mul_le_mul_of_nonneg_left hCS (by positivity)
      _ = (1 / (ell : ℝ) ^ 3) * ∑ t ∈ s, (F t) ^ 2 := by
          have hne : (ell : ℝ) ≠ 0 := ne_of_gt hellR
          field_simp
  have hsumbound : (∑ y ∈ Y, (coarseCurlValue hdvd (lineCoarseRestrict ell A) (y, d)) ^ 2)
      ≤ (1 / (ell : ℝ) ^ 3) * ∑ y ∈ Y, T y.1 := by
    calc (∑ y ∈ Y, (coarseCurlValue hdvd (lineCoarseRestrict ell A) (y, d)) ^ 2)
        ≤ ∑ y ∈ Y, (1 / (ell : ℝ) ^ 3) * T y.1 := Finset.sum_le_sum fun y _ => hpointwise y
      _ = (1 / (ell : ℝ) ^ 3) * ∑ y ∈ Y, T y.1 := by rw [Finset.mul_sum]
  -- local total: sum over Y of T <= ell^2 * sum over Pd of f
  set Ys : Finset (PeriodicLatticeSite L) := Y.map ⟨Subtype.val, Subtype.val_injective⟩ with hYs
  set X : Finset (PeriodicLatticeSite L) := Ys.biUnion (fun y => blockOf y ell) with hX
  have hdisj : (↑Ys : Set (PeriodicLatticeSite L)).PairwiseDisjoint (fun y => blockOf y ell) := by
    intro y hy y' hy' hne
    refine Finset.disjoint_left.mpr fun x hx hx' => hne ?_
    have hyY : y ∈ Ys := Finset.mem_coe.mp hy
    have hyY' : y' ∈ Ys := Finset.mem_coe.mp hy'
    obtain ⟨u, -, rfl⟩ := Finset.mem_map.mp hyY
    obtain ⟨u', -, rfl⟩ := Finset.mem_map.mp hyY'
    exact coarseLattice_unique ell u.2 u'.2 hx hx'
  have hTsum : (∑ y ∈ Y, T y.1) = ∑ y ∈ Ys, T y := by
    rw [hYs, Finset.sum_map]; rfl
  have hTX : (∑ y ∈ Ys, T y) = ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
      ∑ x ∈ X, f (coarseShift (coarseShift x j d.1.2) i d.1.1) := by
    have h1 : (∑ y ∈ Ys, T y) = ∑ y ∈ Ys, ∑ x ∈ blockOf y ell, ∑ i ∈ Finset.range ell,
        ∑ j ∈ Finset.range ell, f (coarseShift (coarseShift x j d.1.2) i d.1.1) := rfl
    rw [h1]
    have h2 : (∑ y ∈ Ys, ∑ x ∈ blockOf y ell, ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
        f (coarseShift (coarseShift x j d.1.2) i d.1.1))
        = ∑ x ∈ X, ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
            f (coarseShift (coarseShift x j d.1.2) i d.1.1) := by
      rw [hX, Finset.sum_biUnion hdisj]
    rw [h2, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_comm]
  have hbij : ∀ i j : ℕ, Function.Injective (fun x : PeriodicLatticeSite L =>
      coarseShift (coarseShift x j d.1.2) i d.1.1) := fun i j =>
    ((coarseShift_bijective i d.1.1).comp (coarseShift_bijective j d.1.2)).1
  have hXP : ∀ i ∈ Finset.range ell, ∀ j ∈ Finset.range ell,
      (∑ x ∈ X, f (coarseShift (coarseShift x j d.1.2) i d.1.1)) ≤ ∑ z ∈ Pd, f z := by
    intro i hi j hj
    have h1 : (∑ x ∈ X, f (coarseShift (coarseShift x j d.1.2) i d.1.1))
        = ∑ z ∈ X.image (fun x => coarseShift (coarseShift x j d.1.2) i d.1.1), f z := by
      rw [Finset.sum_image (fun a _ b _ h => hbij i j h)]
    rw [h1]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun z _ _ => sq_nonneg _)
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y, hy, hxy⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hy
    exact hY u hu x hxy i hi j hj
  have hloc : (∑ y ∈ Y, T y.1) ≤ (ell : ℝ) ^ 2 * ∑ z ∈ Pd, f z := by
    rw [hTsum, hTX]
    calc (∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
          ∑ x ∈ X, f (coarseShift (coarseShift x j d.1.2) i d.1.1))
        ≤ ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell, ∑ z ∈ Pd, f z :=
          Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hXP i hi j hj))
      _ = (ell : ℝ) ^ 2 * ∑ z ∈ Pd, f z := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast; ring
  calc (ell : ℝ) * ∑ y ∈ Y, (coarseCurlValue hdvd (lineCoarseRestrict ell A) (y, d)) ^ 2
      ≤ (ell : ℝ) * ((1 / (ell : ℝ) ^ 3) * ∑ y ∈ Y, T y.1) :=
        mul_le_mul_of_nonneg_left hsumbound (le_of_lt hellR)
    _ ≤ (ell : ℝ) * ((1 / (ell : ℝ) ^ 3) * ((ell : ℝ) ^ 2 * ∑ z ∈ Pd, f z)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hloc (by positivity)) hellR.le
    _ = ∑ z ∈ Pd, f z := by
        field_simp

#print axioms local_sum_sq_coarseCurl_le

end AdalyFormal.FlatEllGeneral
