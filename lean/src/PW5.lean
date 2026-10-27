import PW4
import PW3
import PGFC18

/-!
# PW5 -- flat mass comparison: the full height-`(j+1)` tower's mass is dominated by the patch mass

`massF G a A = ⟨A, Q*aQ A⟩` at `U = 1` (r8 `MassFull` with `bondSectorOf G 1`).
`massF_univ_le` (proved in PW6 from the lemmas here) : for `Rg` a union of `ell^{j+1}` blocks on a torus with `ell^{j+1} ∣ L+1`,
`massF (geomOf ell (j+1) (patchTower j univ)) a A ≤ massF (geomOf ell (j+1) (patchTower j Rg)) a A`, `a ≥ 0`.
(`patchTower j univ = fullTower ell (j+1) Lu`, PW1.)  Mechanism: a level-`(j+1)` row that does not touch `Rg` is an
average of `ell^4` level-`j` line averages (tower law), all of which are level-`j` rows of the patch; Cauchy–Schwarz and the
count (each level-`j` row is used `ell` times) give the factor `ell^{-2} ≤ 1`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.M1Patch

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower BlockClosed scaleUp)
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp SU2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice Bond coarseLattice_mem_fits)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf card_stepBlockOf)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.ThirdLevelArrows (pathSite_mul_coarse)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.SliceCoerc (OnLat onLat_shift)
open AdalyFormal.Balaban.UbarTowerCov (UbarTower)

variable {L : PeriodicLatticeExtent}

/-- the flat mass form of a geometry. -/
noncomputable def massF (G : TowerGeom L) (a : ℝ) (A : BondFnL2 L) : ℝ :=
  ⟪A, MassFull G a (bondSectorOf G (flatCfg : PeriodicLinkConfiguration SU2 L)) A⟫

/-- row value at level `i`, bond `b` (depends on the geometry only through `ell`). -/
noncomputable def rv (ell : ℕ) (A : BondFnL2 L) (i : ℕ) (b : Bond L) : SuTwo :=
  (((ell : ℝ) ^ i)⁻¹) • (WithLp.ofLp (suCoordInv (QlinCompL ell
    (UbarTower su2LogExp ell (flatCfg : PeriodicLinkConfiguration SU2 L)) i (suCoord A)))) b

open Classical in
theorem sum_BIdx (G : TowerGeom L) (F : ℕ → Bond L → ℝ) :
    ∑ p : BIdx G, F (p.1 : ℕ) p.2.1
      = ∑ i : Fin (G.k + 1), ∑ b ∈ Finset.univ.filter (fun b => b ∈ bondsLam G i), F i b := by
  classical
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_subtype (Finset.univ.filter (fun b => b ∈ bondsLam G i)) (p := fun b => b ∈ bondsLam G i)
    (fun b => by simp)]

open Classical in
theorem massF_eq (ell k : ℕ) {S : Tower L} (a : ℝ) (A : BondFnL2 L) :
    massF (geomOf ell k S) a A = ∑ i : Fin (k + 1), ∑ b ∈ Finset.univ.filter (fun b => b ∈ bondsLam (geomOf ell k S) i),
      a * (ell : ℝ) ^ (i : ℕ) * ‖rv ell A i b‖ ^ 2 := by
  unfold massF
  rw [inner_MassFull]
  exact sum_BIdx (geomOf ell k S) (fun i b => a * (ell : ℝ) ^ i * ‖rv ell A i b‖ ^ 2)

/-- flat closed form of `rv`. -/
theorem rv_flat {ell J : ℕ} (hell : 0 < ell) (hdvd : ∀ μ, ell ^ J ∣ L μ + 1) (A : BondFnL2 L) {i : ℕ} (hi : i ≤ J)
    (b : Bond L) (hc : b.1 ∈ CoarseLattice L (ell ^ i)) :
    rv ell A i b = lineCoarseRestrictSuTwo (ell ^ i) (WithLp.ofLp A) (⟨b.1, hc⟩, b.2) := by
  have hbg : ∀ j, UbarTower su2LogExp ell (flatCfg : PeriodicLinkConfiguration SU2 L) j = flatCfg := fun j => Ubar_flat ell j
  have hreg : RegTower ell (UbarTower su2LogExp ell (flatCfg : PeriodicLinkConfiguration SU2 L)) J :=
    fun j _ => by rw [hbg j]; exact RegBg_flat _ _
  have hcl := AdalyFormal.GenuineU1.Qcomp_closed ell hell _ hbg J hdvd (suCoord A) i hi (ell ^ i) rfl (⟨b.1, hc⟩, b.2)
  rw [suCoordFInv_suCoord] at hcl
  unfold rv
  rw [QlinCompL_eq_QlinCompX ell _ J hreg i hi]
  have h2 : (WithLp.ofLp (suCoordInv (QlinCompX ell (UbarTower su2LogExp ell (flatCfg : PeriodicLinkConfiguration SU2 L)) i
      (suCoord A)))) b = suCoordFInv (QlinCompX ell (UbarTower su2LogExp ell flatCfg) i (suCoord A)) (b.1, b.2) := rfl
  rw [h2, hcl, smul_smul]
  have hne : ((ell : ℝ) ^ i) ≠ 0 := by
    have : (0 : ℝ) < ell := by exact_mod_cast hell
    positivity
  push_cast
  rw [inv_mul_cancel₀ hne, one_smul]

/-! ## counting -/

theorem coarse_of_coarse_mul {n m : ℕ} {x : PeriodicLatticeSite L} (h : x ∈ CoarseLattice L (n * m)) :
    x ∈ CoarseLattice L n := by
  rw [mem_CoarseLattice] at h ⊢
  intro μ
  exact Nat.mod_eq_zero_of_dvd (dvd_trans (dvd_mul_right n m) (Nat.dvd_of_mod_eq_zero (h μ)))

/-- partition of the `n`-coarse sites into `n ell`-blocks. -/
theorem sum_partition {n ell : ℕ} (hn : 0 < n) (hell : 0 < ell) (hdvd : ∀ μ, n * ell ∣ L μ + 1)
    (h : PeriodicLatticeSite L → ℝ) :
    ∑ y ∈ CoarseLattice L (n * ell), ∑ x ∈ stepBlockOf y n ell, h x = ∑ x ∈ CoarseLattice L n, h x := by
  classical
  have hN : 0 < n * ell := Nat.mul_pos hn hell
  have step1 : ∀ y ∈ CoarseLattice L (n * ell), ∑ x ∈ stepBlockOf y n ell, h x
      = ∑ x ∈ CoarseLattice L n, if x ∈ blockOf y (n * ell) then h x else 0 := by
    intro y hy
    rw [AdalyFormal.GenuineU1.stepBlock_eq_filter (coarse_of_coarse_mul hy), ← Finset.sum_filter]
    congr 1
    ext x; simp only [Finset.mem_filter]; tauto
  rw [Finset.sum_congr rfl step1, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_eq_single (corner (n * ell) x)]
  · rw [if_pos (mem_block_corner hN x)]
  · intro y hy hne
    rw [if_neg]
    intro hxy
    apply hne
    funext μ; apply Fin.ext
    have hyd : n * ell ∣ (y μ).val := Nat.dvd_of_mod_eq_zero ((mem_CoarseLattice.mp hy) μ)
    have h1 := (mem_blockOf.mp hxy) μ
    rw [AdalyFormal.M1Site.aligned_eq (n * ell) _ _ hN hyd h1.1 h1.2]
    show n * ell * ((x μ).val / (n * ell)) = (x μ).val / (n * ell) * (n * ell)
    ring
  · intro hc
    exfalso; apply hc
    rw [mem_CoarseLattice]; intro μ
    exact Nat.mod_eq_zero_of_dvd (corner_dvd _ x μ)

theorem pathSite_inj (μ : Fin 3) (k : ℕ) {x y : PeriodicLatticeSite L} (h : pathSite x μ k = pathSite y μ k) : x = y := by
  rw [AdalyFormal.FlatCoercivity.pathSite_eq, AdalyFormal.FlatCoercivity.pathSite_eq] at h
  exact add_right_cancel h

/-- a translate-sum over the `n`-coarse sites is at most the plain sum (nonnegative summand). -/
theorem sum_shift_le {n : ℕ} (hdvd : ∀ μ, n ∣ L μ + 1) (μ : Fin 3) (i : ℕ) (g : PeriodicLatticeSite L → ℝ)
    (hg : ∀ x, 0 ≤ g x) :
    ∑ x ∈ CoarseLattice L n, g (pathSite x μ (i * n)) ≤ ∑ x ∈ CoarseLattice L n, g x := by
  classical
  rw [← Finset.sum_image (f := g) (s := CoarseLattice L n) (g := fun x => pathSite x μ (i * n))
    (fun x _ y _ h => pathSite_inj μ (i * n) h)]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ => hg x)
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
  exact pathSite_mul_coarse n hdvd hx μ i


/-! ## geometry of the rows -/

section rows
variable {ell j : ℕ} (hell : 0 < ell) {Rg : Set (PeriodicLatticeSite L)} (hRg : BlockClosed (ell ^ (j + 1)) Rg)
  (hdvd : ∀ μ : Fin 3, ell ^ (j + 1) ∣ L μ + 1)

include hell hRg in
theorem not_omGe_of_not_mem (z : PeriodicLatticeSite L) (hz : z ∉ Rg) :
    ¬ OmGe (geomOf ell (j + 1) (patchTower j Rg)) (j + 1) z := by
  rintro ⟨i, hi1, hi2, y, hy, hzy⟩
  have hij : i = j + 1 := le_antisymm hi2 hi1
  subst hij
  rw [mem_lam_succ] at hy
  have hb : z ∈ blockOf y (ell ^ (j + 1)) := mem_blockOf.mpr hzy
  exact hz (hRg y hy.2 z (fun μ => (same_block_div (pow_pos hell _) hy.1 hb μ).symm))

theorem not_row_lt_univ {i : ℕ} (hi : i ≤ j) (b : Bond L) :
    b ∉ bondsLam (geomOf ell (j + 1) (patchTower j (Set.univ : Set (PeriodicLatticeSite L)))) i := by
  rintro ⟨h1, -⟩
  rcases Nat.lt_or_ge i j with hlt | hge
  · rw [lam_lt ell j _ hlt] at h1; rcases h1 with h | h <;> exact h
  · have hij : i = j := le_antisymm hi hge
    subst hij
    rcases h1 with h | h
    · exact ((mem_lam_j ell i _ _).mp h).2 (Set.mem_univ _)
    · exact ((mem_lam_j ell i _ _).mp h).2 (Set.mem_univ _)

include hdvd in
theorem row_univ_coarse (b : Bond L)
    (hb : b ∈ bondsLam (geomOf ell (j + 1) (patchTower j (Set.univ : Set (PeriodicLatticeSite L)))) (j + 1)) :
    OnLat (ell ^ (j + 1)) b.1 := by
  rcases hb.1 with h | h
  · exact ((mem_lam_succ ell j _ _).mp h).1
  · exact AdalyFormal.M1Patch.onLat_back _ hdvd _ _ ((mem_lam_succ ell j _ _).mp h).1

include hell hRg hdvd in
theorem row_diff_out (b : Bond L)
    (hb : b ∈ bondsLam (geomOf ell (j + 1) (patchTower j (Set.univ : Set (PeriodicLatticeSite L)))) (j + 1))
    (hnb : b ∉ bondsLam (geomOf ell (j + 1) (patchTower j Rg)) (j + 1)) :
    b.1 ∉ Rg ∧ coarseShift b.1 (ell ^ (j + 1)) b.2 ∉ Rg := by
  have hc0 := row_univ_coarse hdvd b hb
  have hc1 : OnLat (ell ^ (j + 1)) (coarseShift b.1 (ell ^ (j + 1)) b.2) := onLat_shift _ hdvd _ hc0 _
  have hno : ¬ (OmGe (geomOf ell (j + 1) (patchTower j Rg)) (j + 1 + 1) b.1 ∨
      OmGe (geomOf ell (j + 1) (patchTower j Rg)) (j + 1 + 1) (coarseShift b.1 (ell ^ (j + 1)) b.2)) := by
    rintro (h | h) <;> exact not_OmGe_of_lt (G := geomOf ell (j + 1) (patchTower j Rg)) (by show j + 1 < j + 1 + 1; omega) _ h
  constructor
  · intro hR; exact hnb ⟨Or.inl ((mem_lam_succ ell j Rg _).mpr ⟨hc0, hR⟩), hno⟩
  · intro hR; exact hnb ⟨Or.inr ((mem_lam_succ ell j Rg _).mpr ⟨hc1, hR⟩), hno⟩

include hell hRg in
theorem row_j_of_out (x : PeriodicLatticeSite L) (hx : OnLat (ell ^ j) x) (μ : Fin 3) (h0 : x ∉ Rg)
    (h1 : coarseShift x (ell ^ j) μ ∉ Rg) :
    ((x, μ) : Bond L) ∈ bondsLam (geomOf ell (j + 1) (patchTower j Rg)) j := by
  refine ⟨Or.inl ((mem_lam_j ell j Rg x).mpr ⟨hx, h0⟩), ?_⟩
  rintro (h | h)
  · exact not_omGe_of_not_mem hell hRg x h0 h
  · exact not_omGe_of_not_mem hell hRg _ h1 h

theorem div_window {N t z : ℕ} (hN : 0 < N) (h1 : N * t ≤ z) (h2 : z < N * t + N) : z / N = t :=
  Nat.div_eq_of_lt_le (by linarith) (by nlinarith)

theorem div_same {N t a b : ℕ} (hN : 0 < N) (ha : a = N * t) (h1 : N * t ≤ b) (h2 : b < N * t + N) : a / N = b / N := by
  rw [ha, Nat.mul_div_cancel_left t hN, div_window hN h1 h2]

include hell hRg hdvd in
/-- a site within two consecutive `ell^{j+1}`-blocks (along `μ`) of two outside blocks is outside. -/
theorem shift_out (c : PeriodicLatticeSite L) (hc : OnLat (ell ^ (j + 1)) c) (μ : Fin 3) (hc0 : c ∉ Rg)
    (hc1 : coarseShift c (ell ^ (j + 1)) μ ∉ Rg) (x : PeriodicLatticeSite L) (hx : x ∈ blockOf c (ell ^ (j + 1)))
    (k : ℕ) (hk : (x μ).val + k < (c μ).val + 2 * ell ^ (j + 1)) :
    coarseShift x k μ ∉ Rg := by
  have hN : 0 < ell ^ (j + 1) := pow_pos hell _
  have hxb := mem_blockOf.mp hx
  obtain ⟨tc, htc⟩ := hc μ
  obtain ⟨s, hs⟩ := hdvd μ
  have hlt := (c μ).isLt
  have hts : tc < s := by
    rw [htc, hs] at hlt
    exact Nat.lt_of_mul_lt_mul_left hlt
  have hfit : (c μ).val + ell ^ (j + 1) ≤ L μ + 1 := by
    have : ell ^ (j + 1) * (tc + 1) ≤ ell ^ (j + 1) * s := Nat.mul_le_mul_left _ hts
    rw [htc, hs]; nlinarith
  have hzν : ∀ ν, ν ≠ μ → coarseShift x k μ ν = x ν :=
    fun ν hν => AdalyFormal.Balaban.CoarseCurl.coarseShift_apply_ne _ _ _ _ hν
  have hzμ : ((coarseShift x k μ) μ).val = ((x μ).val + k) % (L μ + 1) :=
    AdalyFormal.Balaban.CoarseCurl.coarseShift_val_eq _ _ _
  have htrans : ∀ ν, ν ≠ μ → (c ν).val / ell ^ (j + 1) = ((coarseShift x k μ) ν).val / ell ^ (j + 1) := by
    intro ν hν
    rw [hzν ν hν]
    obtain ⟨t, ht⟩ := hc ν
    have h := hxb ν
    exact div_same hN ht (by rw [← ht]; exact h.1) (by rw [← ht]; exact h.2)
  have hx1 := (hxb μ).1
  have hx2 := (hxb μ).2
  by_cases hcase : (x μ).val + k < (c μ).val + ell ^ (j + 1)
  · intro hzR
    apply hc0
    refine hRg _ hzR c (fun ν => ?_)
    by_cases hν : ν = μ
    · subst hν
      have hl : (x ν).val + k < L ν + 1 := lt_of_lt_of_le hcase hfit
      rw [hzμ, Nat.mod_eq_of_lt hl]
      exact div_same hN htc (by rw [← htc]; omega) (by rw [← htc]; omega)
    · exact htrans ν hν
  · intro hzR
    apply hc1
    refine hRg _ hzR _ (fun ν => ?_)
    by_cases hν : ν = μ
    · subst hν
      rw [AdalyFormal.Balaban.CoarseCurl.coarseShift_val_eq, hzμ]
      rcases Nat.lt_or_ge ((c ν).val + ell ^ (j + 1)) (L ν + 1) with hl | hl
      · have hts2 : tc + 1 < s := by
          have : ell ^ (j + 1) * (tc + 1) < ell ^ (j + 1) * s := by rw [← hs]; nlinarith
          exact Nat.lt_of_mul_lt_mul_left this
        have hfit2 : (c ν).val + 2 * ell ^ (j + 1) ≤ L ν + 1 := by
          have : ell ^ (j + 1) * (tc + 2) ≤ ell ^ (j + 1) * s := Nat.mul_le_mul_left _ hts2
          rw [htc, hs]; nlinarith
        rw [Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt (by omega)]
        have e1 : (c ν).val + ell ^ (j + 1) = ell ^ (j + 1) * (tc + 1) := by rw [htc]; ring
        exact div_same hN e1 (by rw [← e1]; omega) (by rw [← e1]; omega)
      · have heq : (c ν).val + ell ^ (j + 1) = L ν + 1 := le_antisymm hfit hl
        have h1 : ((c ν).val + ell ^ (j + 1)) % (L ν + 1) = 0 := by rw [heq, Nat.mod_self]
        have hge : L ν + 1 ≤ (x ν).val + k := by omega
        have hlt2 : (x ν).val + k - (L ν + 1) < L ν + 1 := by omega
        have h2 : ((x ν).val + k) % (L ν + 1) = (x ν).val + k - (L ν + 1) := by
          rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt2]
        rw [h1, h2]
        exact div_same hN (t := 0) (by ring) (by omega) (by omega)
    · rw [AdalyFormal.Balaban.CoarseCurl.coarseShift_apply_ne _ _ _ _ hν]
      exact htrans ν hν

end rows

end AdalyFormal.M1Patch
