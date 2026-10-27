import NsCvOS13
import NsCvOS9

/-!
# CvOS14 -- the composite `Q'_j` on a point mass, and triviality of the cokernel of the constraints (lane omega/near2/struct)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3

namespace AdalyFormal.CoverOmega.Struct

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_one)
open AdalyFormal.Balaban.QjComposite (stepBlockOf stepAverage Qcomposite mem_stepBlockOf)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath coarseGammaPath_self)

variable {L : PeriodicLatticeExtent}

theorem block_aligned_eq (ell j : ℕ) (hell : 0 < ell) {x y : PeriodicLatticeSite L}
    (hx : ∀ μ, ell ^ (j + 1) ∣ (x μ).val) (hy : ∀ μ, ell ^ (j + 1) ∣ (y μ).val)
    (hmem : y ∈ stepBlockOf x (ell ^ j) ell) : y = x := by
  funext μ
  apply Fin.ext
  obtain ⟨hle, hlt, -⟩ := mem_stepBlockOf.1 hmem μ
  obtain ⟨a, ha⟩ := hx μ
  obtain ⟨b, hb⟩ := hy μ
  have hM : 0 < ell ^ (j + 1) := pow_pos hell _
  have hpow : ell ^ (j + 1) = ell ^ j * ell := pow_succ ell j
  rw [ha, hb] at hle hlt
  rw [← hpow] at hlt
  have h1 : a ≤ b := Nat.le_of_mul_le_mul_left hle hM
  have h2 : b < a + 1 := by
    apply Nat.lt_of_mul_lt_mul_left (a := ell ^ (j + 1))
    rw [mul_add, mul_one]; exact hlt
  have : b = a := by omega
  rw [hb, ha, this]

theorem Qcomp_delta (bg : ℕ → Cfg L) (ell : ℕ) (hell : 0 < ell) (v : SuTwo) (y : PeriodicLatticeSite L) :
    ∀ j : ℕ, (∀ μ, ell ^ j ∣ (y μ).val) → ∀ x : PeriodicLatticeSite L, (∀ μ, ell ^ j ∣ (x μ).val) →
      Qcomposite bg ell j (fun z => if z = y then v else 0) x
        = if x = y then (((1 : ℝ) / (ell : ℝ) ^ 3) ^ j) • v else 0 := by
  classical
  intro j
  induction j with
  | zero =>
      intro hy x hx
      show (fun z => if z = y then v else 0) x = _
      simp
  | succ j ih =>
      intro hy x hx
      have hy' : ∀ μ, ell ^ j ∣ (y μ).val := fun μ => dvd_trans (pow_dvd_pow ell (Nat.le_succ j)) (hy μ)
      have hx' : ∀ μ, ell ^ j ∣ (x μ).val := fun μ => dvd_trans (pow_dvd_pow ell (Nat.le_succ j)) (hx μ)
      show stepAverage (ell ^ j) (bg j) ell (Qcomposite bg ell j (fun z => if z = y then v else 0)) x = _
      unfold stepAverage
      have hsum : ∑ z ∈ stepBlockOf x (ell ^ j) ell,
          RMap (coarsePathHolonomy (ell ^ j) (bg j) x (coarseGammaPath (ell ^ j) x z))
            (Qcomposite bg ell j (fun z => if z = y then v else 0) z)
          = if y ∈ stepBlockOf x (ell ^ j) ell then
              RMap (coarsePathHolonomy (ell ^ j) (bg j) x (coarseGammaPath (ell ^ j) x y))
                ((((1 : ℝ) / (ell : ℝ) ^ 3) ^ j) • v) else 0 := by
        rw [← Finset.sum_ite_eq' (stepBlockOf x (ell ^ j) ell) y
          (fun z => RMap (coarsePathHolonomy (ell ^ j) (bg j) x (coarseGammaPath (ell ^ j) x z))
            ((((1 : ℝ) / (ell : ℝ) ^ 3) ^ j) • v))]
        refine Finset.sum_congr rfl (fun z hz => ?_)
        have hza : ∀ μ, ell ^ j ∣ (z μ).val := by
          intro μ
          obtain ⟨hle, -, hdv⟩ := mem_stepBlockOf.1 hz μ
          have : (z μ).val = ((z μ).val - (x μ).val) + (x μ).val := by omega
          rw [this]; exact Nat.dvd_add hdv (hx' μ)
        rw [ih hy' z hza]
        by_cases h : z = y
        · simp [h]
        · simp [h]
      rw [hsum]
      by_cases hxy : x = y
      · subst hxy
        have hmem : x ∈ stepBlockOf x (ell ^ j) ell := by
          rw [mem_stepBlockOf]
          intro μ
          refine ⟨le_rfl, ?_, by simp⟩
          have : 0 < ell ^ j * ell := Nat.mul_pos (pow_pos hell _) hell
          omega
        rw [if_pos hmem, coarseGammaPath_self]
        simp [coarsePathHolonomy, RMap_one, smul_smul, pow_succ, mul_comm]
      · have hnm : y ∉ stepBlockOf x (ell ^ j) ell := fun hm => hxy (block_aligned_eq ell j hell hx hy hm).symm
        rw [if_neg hnm, if_neg hxy, smul_zero]

/-- **the cokernel of the `Q'` constraints on `Om0`-supported fields is trivial** (for every link configuration). -/
theorem Bq_cokernel_trivial (G : TowerGeom L) (U : Cfg L) (hell : 0 < G.ell)
    (hal : ∀ j, ∀ y ∈ G.Lam j, ∀ μ, G.ell ^ j ∣ (y μ).val)
    (h0 : ∀ j, j ≤ G.k → ∀ y ∈ G.Lam j, y ∈ G.Om0)
    (hdisj : ∀ j j', j' < j → ∀ y, y ∈ G.Lam j → y ∈ G.Lam j' → False)
    (w : WQ G) (hw : ∀ f : SiteL2 L, siteMask G.Om0 f = f → ⟪Bq G U f, w⟫ = 0) : w = 0 := by
  classical
  by_contra hne
  have hex : ∃ p0 : RowIdx G, w p0 ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hne (PiLp.ext (fun p => by simpa using hall p))
  obtain ⟨p0, hp0⟩ := hex
  obtain ⟨p, hpmem, hmax⟩ := Finset.exists_max_image (Finset.univ.filter (fun q : RowIdx G => w q ≠ 0))
    (fun q : RowIdx G => ((q.1.1 : Fin (G.k + 1)) : ℕ)) ⟨p0, by simp [hp0]⟩
  have hwp : w p ≠ 0 := (Finset.mem_filter.1 hpmem).2
  set j : ℕ := ((p.1.1 : Fin (G.k + 1)) : ℕ) with hj
  set y : PeriodicLatticeSite L := p.1.2 with hy
  have hyL : y ∈ G.Lam j := p.2
  have hyOm : y ∈ G.Om0 := h0 j (by have := p.1.1.2; omega) y hyL
  let lam : PeriodicLatticeSite L → SuTwo := fun z => if z = y then w p else 0
  let f : SiteL2 L := WithLp.toLp 2 lam
  have hmf : siteMask G.Om0 f = f := by
    ext z
    rw [siteMask_apply]
    by_cases hz : z ∈ G.Om0
    · rw [if_pos hz]
    · rw [if_neg hz]
      have : z ≠ y := fun h => hz (h ▸ hyOm)
      simp [f, lam, this]
  have hsum := hw f hmf
  rw [PiLp.inner_apply] at hsum
  have hterm : ∀ q : RowIdx G, q ≠ p → ⟪(Bq G U f) q, w q⟫ = 0 := by
    intro q hq
    by_cases hwq : w q = 0
    · rw [hwq, inner_zero_right]
    · have hqmem : q ∈ Finset.univ.filter (fun q : RowIdx G => w q ≠ 0) := by simp [hwq]
      have hle : ((q.1.1 : Fin (G.k + 1)) : ℕ) ≤ j := hmax q hqmem
      set j' : ℕ := ((q.1.1 : Fin (G.k + 1)) : ℕ) with hj'
      set y' : PeriodicLatticeSite L := q.1.2 with hy'
      have hy'L : y' ∈ G.Lam j' := q.2
      have hyal : ∀ μ, G.ell ^ j' ∣ (y μ).val := fun μ =>
        dvd_trans (pow_dvd_pow G.ell hle) (hal j y hyL μ)
      have hBq : (Bq G U f) q = Qcomposite (bgTower G U) G.ell j' lam y' := rfl
      rw [hBq, Qcomp_delta (bgTower G U) G.ell hell (w p) y j' hyal y' (hal j' y' hy'L)]
      by_cases hyy : y' = y
      · exfalso
        rcases Nat.lt_or_ge j' j with hlt | hge
        · exact hdisj j j' hlt y hyL (hyy ▸ hy'L)
        · have hjj : j' = j := le_antisymm hle hge
          apply hq
          apply Subtype.ext
          apply Prod.ext
          · exact Fin.ext hjj
          · exact hyy
      · rw [if_neg hyy, inner_zero_left]
  rw [Finset.sum_eq_single p (fun q _ hq => hterm q hq) (fun h => absurd (Finset.mem_univ p) h)] at hsum
  have hBp : (Bq G U f) p = Qcomposite (bgTower G U) G.ell j lam y := rfl
  rw [hBp, Qcomp_delta (bgTower G U) G.ell hell (w p) y j (hal j y hyL) y (hal j y hyL), if_pos rfl,
    real_inner_smul_left, real_inner_self_eq_norm_sq] at hsum
  have hpos : 0 < ((1 : ℝ) / (G.ell : ℝ) ^ 3) ^ j := by
    have : (0 : ℝ) < G.ell := by exact_mod_cast hell
    positivity
  have hnorm : 0 < ‖w p‖ ^ 2 := by positivity
  nlinarith

#print axioms Bq_cokernel_trivial

end AdalyFormal.CoverOmega.Struct
