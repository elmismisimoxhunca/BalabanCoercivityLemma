import UA9
import FE1b

/-!
# UB1 -- flat Stokes, ONE coarse plaquette at a time, and the window counting (lane m2_unit_20261014)

Coarse scale `n` on a torus `L` (`n ∣ L_μ + 1`).  Window sum of a plaquette function `f` over the coarse plaquette `p = (y, d)`:
  `winSum n f p = Σ_{x∈B(y)} Σ_{i<n} Σ_{j<n} f(x + j e_ν + i e_μ, d)`.
* `stokes_pt` : `n ‖coarse curl (q₁ A) p‖² ≤ n⁻² winSum n ‖flatCurl A‖² p`  (one plaquette; FE1a's pointwise Cauchy–Schwarz,
  su(2) by coordinates).  Lets each coarse plaquette use ITS OWN gauge for the field `A`.
* `winSum_count` : for `f ≥ 0`, `Σ_{p∈Y} winSum n f p ≤ n² Σ_{q∈Pq} f q` when every window plaquette of `Y` is in `Pq`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace AdalyFormal.M2Unit

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators (curlValue)
open AdalyFormal.Balaban.CoarseCurl
open AdalyFormal.Balaban.CoarseShiftCovariance
open AdalyFormal.Balaban.LineIntegralAveraging (lineCoarseRestrict)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoGeomU1
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue)
open AdalyFormal.Balaban.ThirdLevelStokes (coarseCurlSuTwo)
open AdalyFormal.Balaban.RegularUGamma0 (suCoordLM_coarseCurlSuTwo)

variable {L : PeriodicLatticeExtent}

/-- the window plaquette of `(x, i, j)` for the coarse plaquette with directions `d`. -/
def winPl (d : PeriodicPlaquetteDirections) (x : PeriodicLatticeSite L) (i j : ℕ) : PeriodicLatticePlaquette L :=
  (coarseShift (coarseShift x j d.1.2) i d.1.1, d)

/-- the window sum. -/
noncomputable def winSum (n : ℕ) (f : PeriodicLatticePlaquette L → ℝ) (p : CoarsePlaquette L n) : ℝ :=
  ∑ x ∈ blockOf p.1.1 n, ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, f (winPl p.2 x i j)

theorem winSum_nonneg (n : ℕ) (f : PeriodicLatticePlaquette L → ℝ) (hf : ∀ q, 0 ≤ f q) (p : CoarsePlaquette L n) :
    0 ≤ winSum n f p :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => hf _)))

theorem winSum_mono (n : ℕ) {f g : PeriodicLatticePlaquette L → ℝ} (hfg : ∀ q, f q ≤ g q) (p : CoarsePlaquette L n) :
    winSum n f p ≤ winSum n g p :=
  Finset.sum_le_sum (fun _ _ => Finset.sum_le_sum (fun _ _ => Finset.sum_le_sum (fun _ _ => hfg _)))

/-- scalar pointwise Cauchy–Schwarz (FE1a, one coarse plaquette). -/
theorem stokes_pt_scalar {n : ℕ} (hn : 0 < n) (hdvd : ∀ μ : Fin 3, n ∣ (L μ + 1)) (A : Bond L → ℝ)
    (p : CoarsePlaquette L n) :
    (coarseCurlValue hdvd (lineCoarseRestrict n A) p) ^ 2
      ≤ (1 / (n : ℝ) ^ 3) * winSum n (fun z => (curlValue A z) ^ 2) p := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set s : Finset (PeriodicLatticeSite L × (ℕ × ℕ)) :=
    (blockOf p.1.1 n) ×ˢ (Finset.range n ×ˢ Finset.range n) with hs
  set F : PeriodicLatticeSite L × (ℕ × ℕ) → ℝ := fun t => curlValue A (winPl p.2 t.1 t.2.1 t.2.2) with hF
  have hsum : (∑ t ∈ s, F t) = ∑ x ∈ blockOf p.1.1 n, ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      curlValue A (coarseShift (coarseShift x j p.2.1.2) i p.2.1.1, p.2) := by
    rw [hs, Finset.sum_product]
    exact Finset.sum_congr rfl fun x _ => by rw [Finset.sum_product]; rfl
  have hsumsq : (∑ t ∈ s, (F t) ^ 2) = winSum n (fun z => (curlValue A z) ^ 2) p := by
    rw [hs, Finset.sum_product]
    exact Finset.sum_congr rfl fun x _ => by rw [Finset.sum_product]
  have hcard : (s.card : ℝ) = (n : ℝ) ^ 5 := by
    simp only [hs, Finset.card_product, Finset.card_range, card_blockOf_of_coarse hdvd p.1.2]
    push_cast; ring
  have hCS : (∑ t ∈ s, F t) ^ 2 ≤ (n : ℝ) ^ 5 * ∑ t ∈ s, (F t) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := s) (f := F)
    rw [hcard] at h; exact h
  have hid := AdalyFormal.Balaban.FourierFaithfulU1.coarseCurl_lineCoarseRestrict_eq_blockSum hn hdvd A p.1 p.2
  have hp : p = (p.1, p.2) := rfl
  rw [hp, hid, ← hsum, ← hsumsq]
  calc ((1 / (n : ℝ) ^ 4) * ∑ t ∈ s, F t) ^ 2
      = (1 / (n : ℝ) ^ 8) * (∑ t ∈ s, F t) ^ 2 := by ring
    _ ≤ (1 / (n : ℝ) ^ 8) * ((n : ℝ) ^ 5 * ∑ t ∈ s, (F t) ^ 2) :=
        mul_le_mul_of_nonneg_left hCS (by positivity)
    _ = (1 / (n : ℝ) ^ 3) * ∑ t ∈ s, (F t) ^ 2 := by field_simp

/-- **flat Stokes at ONE coarse plaquette, su(2)**. -/
theorem stokes_pt {n : ℕ} (hn : 0 < n) (hdvd : ∀ μ : Fin 3, n ∣ (L μ + 1)) (A : Bond L → SuTwo)
    (p : CoarsePlaquette L n) :
    (n : ℝ) * ‖coarseCurlSuTwo hdvd (lineCoarseRestrictSuTwo n A) p‖ ^ 2
      ≤ (1 / (n : ℝ) ^ 2) * winSum n (fun z => ‖flatCurlValue A z‖ ^ 2) p := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : ‖coarseCurlSuTwo hdvd (lineCoarseRestrictSuTwo n A) p‖ ^ 2
      = ∑ i : Fin 3, (coarseCurlValue hdvd (lineCoarseRestrict n (suComp i A)) p) ^ 2 := by
    rw [AdalyFormal.FlatEllGeneral.norm_sq_suTwo_eq_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [suCoordLM_coarseCurlSuTwo]
    congr 2
    funext c
    exact suCoordLM_lineCoarseRestrictSuTwo i n A c
  have hR : winSum n (fun z => ‖flatCurlValue A z‖ ^ 2) p
      = ∑ i : Fin 3, winSum n (fun z => (curlValue (suComp i A) z) ^ 2) p := by
    unfold winSum
    simp only [AdalyFormal.FlatEllGeneral.norm_sq_suTwo_eq_sum, suCoordLM_flatCurlValue]
    set F : Fin 3 → PeriodicLatticeSite L → ℕ → ℕ → ℝ := fun c x a b => (curlValue (suComp c A) (winPl p.2 x a b)) ^ 2
      with hF
    show ∑ x ∈ blockOf p.1.1 n, ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, ∑ c : Fin 3, F c x a b
      = ∑ c : Fin 3, ∑ x ∈ blockOf p.1.1 n, ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, F c x a b
    calc ∑ x ∈ blockOf p.1.1 n, ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, ∑ c : Fin 3, F c x a b
        = ∑ x ∈ blockOf p.1.1 n, ∑ a ∈ Finset.range n, ∑ c : Fin 3, ∑ b ∈ Finset.range n, F c x a b :=
          Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun a _ => Finset.sum_comm))
      _ = ∑ x ∈ blockOf p.1.1 n, ∑ c : Fin 3, ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, F c x a b :=
          Finset.sum_congr rfl (fun x _ => Finset.sum_comm)
      _ = ∑ c : Fin 3, ∑ x ∈ blockOf p.1.1 n, ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, F c x a b :=
          Finset.sum_comm
  rw [hL, hR, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have h := stokes_pt_scalar hn hdvd (suComp i A) p
  have e : (n : ℝ) * ((1 / (n : ℝ) ^ 3) * winSum n (fun z => (curlValue (suComp i A) z) ^ 2) p)
      = (1 / (n : ℝ) ^ 2) * winSum n (fun z => (curlValue (suComp i A) z) ^ 2) p := by
    field_simp
  rw [← e]
  exact mul_le_mul_of_nonneg_left h hnR.le

open Classical in
/-- **window counting**: each translation `(i, j)` is injective, so a plane's windows count every plaquette `n²` times. -/
theorem winSum_count {n : ℕ} (hn : 0 < n) (f : PeriodicLatticePlaquette L → ℝ) (hf : ∀ q, 0 ≤ f q)
    (Y : Finset (CoarsePlaquette L n)) (Pq : Finset (PeriodicLatticePlaquette L))
    (hY : ∀ p ∈ Y, ∀ x ∈ blockOf p.1.1 n, ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n, winPl p.2 x i j ∈ Pq) :
    ∑ p ∈ Y, winSum n f p ≤ (n : ℝ) ^ 2 * ∑ q ∈ Pq, f q := by
  rw [AdalyFormal.FlatEllGeneral.sum_by_second Y, AdalyFormal.FlatEllGeneral.sum_by_second Pq, Finset.mul_sum]
  refine Finset.sum_le_sum (fun d _ => ?_)
  set Yd := (Finset.univ : Finset {y : PeriodicLatticeSite L // y ∈ CoarseLattice L n}).filter (fun y => (y, d) ∈ Y)
    with hYd
  set Pd := (Finset.univ : Finset (PeriodicLatticeSite L)).filter (fun z => (z, d) ∈ Pq) with hPd
  set g : PeriodicLatticeSite L → ℝ := fun z => f (z, d) with hg
  set Ys : Finset (PeriodicLatticeSite L) := Yd.map ⟨Subtype.val, Subtype.val_injective⟩ with hYs
  set X : Finset (PeriodicLatticeSite L) := Ys.biUnion (fun y => blockOf y n) with hX
  have hdisj : (↑Ys : Set (PeriodicLatticeSite L)).PairwiseDisjoint (fun y => blockOf y n) := by
    intro y hy y' hy' hne
    refine Finset.disjoint_left.mpr fun x hx hx' => hne ?_
    obtain ⟨u, -, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hy)
    obtain ⟨u', -, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hy')
    exact coarseLattice_unique n u.2 u'.2 hx hx'
  have hT : ∑ y ∈ Yd, winSum n f (y, d)
      = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, ∑ x ∈ X, g (coarseShift (coarseShift x j d.1.2) i d.1.1) := by
    have h1 : ∑ y ∈ Yd, winSum n f (y, d) = ∑ y ∈ Ys, ∑ x ∈ blockOf y n, ∑ i ∈ Finset.range n,
        ∑ j ∈ Finset.range n, g (coarseShift (coarseShift x j d.1.2) i d.1.1) := by
      rw [hYs, Finset.sum_map]; rfl
    have h2 : (∑ y ∈ Ys, ∑ x ∈ blockOf y n, ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        g (coarseShift (coarseShift x j d.1.2) i d.1.1))
        = ∑ x ∈ X, ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
            g (coarseShift (coarseShift x j d.1.2) i d.1.1) := by
      rw [hX, Finset.sum_biUnion hdisj]
    rw [h1, h2, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_comm]
  have hbij : ∀ i j : ℕ, Function.Injective (fun x : PeriodicLatticeSite L =>
      coarseShift (coarseShift x j d.1.2) i d.1.1) := fun i j =>
    ((coarseShift_bijective i d.1.1).comp (coarseShift_bijective j d.1.2)).1
  have hXP : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      (∑ x ∈ X, g (coarseShift (coarseShift x j d.1.2) i d.1.1)) ≤ ∑ z ∈ Pd, g z := by
    intro i hi j hj
    have h1 : (∑ x ∈ X, g (coarseShift (coarseShift x j d.1.2) i d.1.1))
        = ∑ z ∈ X.image (fun x => coarseShift (coarseShift x j d.1.2) i d.1.1), g z := by
      rw [Finset.sum_image (fun a _ b _ h => hbij i j h)]
    rw [h1]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun z _ _ => hf _)
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y, hy, hxy⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hy
    have huY : (u, d) ∈ Y := (Finset.mem_filter.mp hu).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hY (u, d) huY x hxy i hi j hj⟩
  rw [hT]
  calc (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, ∑ x ∈ X, g (coarseShift (coarseShift x j d.1.2) i d.1.1))
      ≤ ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, ∑ z ∈ Pd, g z :=
        Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hXP i hi j hj))
    _ = (n : ℝ) ^ 2 * ∑ z ∈ Pd, g z := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast; ring

end AdalyFormal.M2Unit

#print axioms AdalyFormal.M2Unit.stokes_pt_scalar
#print axioms AdalyFormal.M2Unit.stokes_pt
#print axioms AdalyFormal.M2Unit.winSum_count
