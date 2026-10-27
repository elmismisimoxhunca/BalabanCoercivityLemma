import PW8
import LF4

/-!
# LF3 -- flat identities on the two-stratum patch

At `U = flatCfg` (= `trivialU`) on `G = geomOf ell (j+1) (patchTower j Rg)` (`n = ell^j`, `N = ell^{j+1}`):
* `Qlev_flat`: the constraint map is the plain block average.
* `QfullOf_grad_flat`: `(Q (D ν))_p = ell^{-i} (Q'_i ν(z') - Q'_i ν(z))` for every row `p` of level `i` with lattice ends.
* `cc` (constraint corner): `corner N x` in `Rg`, `corner n x` outside; `orth_cc`: every `v ⟂ N(Q')` is constant on
  constraint blocks, `v x = v (cc x)`; hence `orth_cell` (`v x = v (corner n x)`) and `orth_big` (`v x = v (corner N x)` on `Rg`).
* `ext3_sub_mem`: for every cell-constant `w`, `ext3 w - w ∈ N(Q')` (exact block averages at both levels).
* `massP`, `massP_add_NQp` (mass invariant along `D N(Q')`), `PhiP_grad` (`Φ(Dφ) = mass(Dφ)`).
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace AdalyFormal.LemIFlat

open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.M1Patch
open AdalyFormal.StatementLane (Tower BlockClosed scaleUp)
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp M2 SU2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf inBlock)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_val_eq coarseShift_apply_ne)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.QjComposite (Qcomposite stepBlockOf mem_stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (UbarTower UbarTower_zero)
open AdalyFormal.SliceCoerc (OnLat dG dG_eq_Qcomposite QlinCompX_pureGauge suCoord_grad)

variable {L : PeriodicLatticeExtent}

theorem flatCfg_eq : (flatCfg : Cfg L) = trivialU L := rfl

theorem bg_flat_triv (G : TowerGeom L) : bgTower G (flatCfg : Cfg L) = fun _ => trivialU L :=
  funext (fun j => bg_flat G j)

/-- the flat constraint map is the block average. -/
theorem Qlev_flat (G : TowerGeom L) (hell : 0 < G.ell) (i : ℕ) (z : PeriodicLatticeSite L) (f : SiteL2 L) :
    Qlev G (flatCfg : Cfg L) i z f = ((1 / (G.ell : ℝ) ^ 3) ^ i) • ∑ x ∈ blockOf z (G.ell ^ i), f.ofLp x := by
  rw [Qlev_apply, bg_flat_triv]
  exact AdalyFormal.FlatExt.Qcomposite_flat G.ell hell i _ z

theorem Qcomp_flat (G : TowerGeom L) (hell : 0 < G.ell) (i : ℕ) (z : PeriodicLatticeSite L)
    (f : PeriodicLatticeSite L → SuTwo) :
    Qcomposite (bgTower G (flatCfg : Cfg L)) G.ell i f z = ((1 / (G.ell : ℝ) ^ 3) ^ i) • ∑ x ∈ blockOf z (G.ell ^ i), f x := by
  rw [bg_flat_triv]
  exact AdalyFormal.FlatExt.Qcomposite_flat G.ell hell i _ z

theorem regTower_flat (G : TowerGeom L) (J : ℕ) : RegTower G.ell (bgTower G (flatCfg : Cfg L)) J :=
  fun i _ => by rw [bg_flat]; exact RegBg_flat _ _

/-- **the flat row formula**: `(Q D ν)_p = ell^{-i} (Q'_i ν(z') - Q'_i ν(z))`. -/
theorem QfullOf_grad_flat (G : TowerGeom L) (hell : 0 < G.ell) (hdiv : ∀ μ : Fin 3, G.ell ^ G.k ∣ L μ + 1)
    (ν : SiteL2 L) (p : BIdx G)
    (hlat0 : OnLat (G.ell ^ (p.1 : ℕ)) p.2.1.1)
    (hlat1 : OnLat (G.ell ^ (p.1 : ℕ)) (coarseShift p.2.1.1 (G.ell ^ (p.1 : ℕ)) p.2.1.2)) :
    (QfullOf G (flatCfg : Cfg L) (gradL2 (flatCfg : Cfg L) ν)).ofLp p
      = (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) •
        (Qcomposite (bgTower G (flatCfg : Cfg L)) G.ell p.1 (WithLp.ofLp ν) (coarseShift p.2.1.1 (G.ell ^ (p.1 : ℕ)) p.2.1.2)
          - Qcomposite (bgTower G (flatCfg : Cfg L)) G.ell p.1 (WithLp.ofLp ν) p.2.1.1) := by
  have hj : (p.1 : ℕ) ≤ G.k := Nat.lt_succ_iff.mp p.1.isLt
  have hreg := regTower_flat G G.k
  have hjet := QlinCompX_pureGauge G.ell (flatCfg : Cfg L) (WithLp.ofLp ν) G.k hreg p.1 hj
  have hbg : bgTower G (flatCfg : Cfg L) = UbarTower su2LogExp G.ell (flatCfg : Cfg L) := rfl
  have hd0 := dG_eq_Qcomposite G.ell hell (UbarTower su2LogExp G.ell (flatCfg : Cfg L)) (WithLp.ofLp ν) G.k hdiv p.1 hj _ hlat0
  have hd1 := dG_eq_Qcomposite G.ell hell (UbarTower su2LogExp G.ell (flatCfg : Cfg L)) (WithLp.ofLp ν) G.k hdiv p.1 hj _ hlat1
  have hU : ∀ i c, ((UbarTower su2LogExp G.ell (flatCfg : Cfg L) i c : SU2) : M2) = 1 := by
    intro i c
    rw [← hbg, bg_flat]; rfl
  have hcoord : suCoord (gradL2 (flatCfg : Cfg L) ν) = -(fun c : PeriodicLatticeEdge L =>
      fromM2 (dG G.ell (UbarTower su2LogExp G.ell (flatCfg : Cfg L)) (WithLp.ofLp ν) 0 c.1
        - ((UbarTower su2LogExp G.ell (flatCfg : Cfg L) 0 c : SU2) : M2)
          * dG G.ell (UbarTower su2LogExp G.ell (flatCfg : Cfg L)) (WithLp.ofLp ν) 0 (coarseShift c.1 (G.ell ^ 0) c.2)
          * ((UbarTower su2LogExp G.ell (flatCfg : Cfg L) 0 c : SU2) : M2)ᴴ)) := by
    rw [suCoord_grad, pow_zero, UbarTower_zero]; rfl
  set a1 := Qcomposite (bgTower G (flatCfg : Cfg L)) G.ell p.1 (WithLp.ofLp ν)
    (coarseShift p.2.1.1 (G.ell ^ (p.1 : ℕ)) p.2.1.2) with ha1
  set a0 := Qcomposite (bgTower G (flatCfg : Cfg L)) G.ell p.1 (WithLp.ofLp ν) p.2.1.1 with ha0
  have hval : QlinCompX G.ell (bgTower G (flatCfg : Cfg L)) p.1 (suCoord (gradL2 (flatCfg : Cfg L) ν)) p.2.1
      = fromM2 (((a1 - a0 : SuTwo)) : M2) := by
    rw [hcoord, map_neg, hbg, hjet]
    simp only [Pi.neg_apply, hU, one_mul, mul_one, Matrix.conjTranspose_one]
    rw [hd0, hd1, ← hbg, ← map_neg]
    congr 1
    simp only [Submodule.coe_sub]
    abel
  have hq : QlinB G (flatCfg : Cfg L) p.1 (gradL2 (flatCfg : Cfg L) ν)
      = suCoordInv (QlinCompX G.ell (bgTower G (flatCfg : Cfg L)) p.1 (suCoord (gradL2 (flatCfg : Cfg L) ν))) :=
    QlinB_eq_r7 G (flatCfg : Cfg L) G.k hreg p.1 hj _
  show WithLp.ofLp (QfullOf G (flatCfg : Cfg L) (gradL2 (flatCfg : Cfg L) ν)) p = _
  simp only [QfullOf, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]
  congr 1
  rw [hq]
  apply Subtype.ext
  show toM2 ((QlinCompX G.ell (bgTower G (flatCfg : Cfg L)) p.1 (suCoord (gradL2 (flatCfg : Cfg L) ν))) p.2.1) = _
  rw [hval, toM2_fromM2 (a1 - a0).2]

/-! ## the patch: corners and constraint blocks -/

theorem corner_val (m : ℕ) (x : PeriodicLatticeSite L) (μ : Fin 3) : (corner m x μ).val = (x μ).val / m * m := rfl


theorem mem_blockOf_iff_corner {m : ℕ} (hm : 0 < m) (z x : PeriodicLatticeSite L) (hz : ∀ μ : Fin 3, m ∣ (z μ).val) :
    x ∈ blockOf z m ↔ corner m x = z := by
  rw [mem_blockOf]
  constructor
  · intro h
    funext μ; apply Fin.ext
    rw [corner_val]
    obtain ⟨c, hc⟩ := hz μ
    have h1 := (h μ).1; have h2 := (h μ).2
    rw [hc] at h1 h2 ⊢
    have hlo : c * m ≤ (x μ).val := by rw [Nat.mul_comm]; exact h1
    have hhi : (x μ).val < (c + 1) * m := by rw [Nat.add_mul, one_mul, Nat.mul_comm]; exact h2
    rw [Nat.div_eq_of_lt_le hlo hhi, Nat.mul_comm]
  · rintro rfl μ
    rw [corner_val]
    exact ⟨Nat.div_mul_le_self _ _, by have := Nat.lt_div_mul_add (a := (x μ).val) hm; linarith⟩



theorem corner_div {m M : ℕ} (hm : 0 < m) (hmM : m ∣ M) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    (corner m x μ).val / M = (x μ).val / M := by
  rw [corner_val]
  obtain ⟨r, rfl⟩ := hmM
  rw [← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ hm, Nat.div_div_eq_div_mul]

theorem corner_corner {m m' : ℕ} (hm : 0 < m) (hmm : m ∣ m') (x : PeriodicLatticeSite L) :
    corner m' (corner m x) = corner m' x := by
  funext μ; apply Fin.ext
  rw [corner_val m' (corner m x) μ, corner_val m' x μ, corner_div hm hmm x μ]

theorem corner_idem {m : ℕ} (hm : 0 < m) (x : PeriodicLatticeSite L) : corner m (corner m x) = corner m x :=
  corner_corner hm (dvd_refl m) x


/-- the mass functional. -/
noncomputable def massP (G : TowerGeom L) (a : ℝ) (y : BondFnL2 L) : ℝ :=
  ⟪y, MassFull G a (bondSectorOf G (flatCfg : Cfg L)) y⟫

theorem massP_eq (G : TowerGeom L) (a : ℝ) (y : BondFnL2 L) :
    massP G a y = ∑ p : BIdx G, a * (G.ell : ℝ) ^ (p.1 : ℕ) * ‖(QfullOf G (flatCfg : Cfg L) y).ofLp p‖ ^ 2 :=
  inner_MassFull G a _ y

theorem massP_nonneg (G : TowerGeom L) (a : ℝ) (ha : 0 ≤ a) (y : BondFnL2 L) : 0 ≤ massP G a y := by
  rw [massP_eq]; exact Finset.sum_nonneg (fun p _ => by positivity)

theorem PhiP_grad (G : TowerGeom L) (a : ℝ) (φ : SiteL2 L) :
    PhiP G (flatCfg : Cfg L) a (gradL2 (flatCfg : Cfg L) φ) = massP G a (gradL2 (flatCfg : Cfg L) φ) := by
  unfold PhiP massP
  rw [AdalyFormal.StatementLaneG.inner_DpiFull_flat, AdalyFormal.StatementLane3.curl_gradL2_flat, map_zero, norm_zero]
  ring

section patch
variable {ell j : ℕ} (hell : 0 < ell) {Rg : Set (PeriodicLatticeSite L)} (hRg : BlockClosed (ell ^ (j + 1)) Rg)
include hell hRg

theorem corner_mem_Rg {m : ℕ} (hm : 0 < m) (hmN : m ∣ ell ^ (j + 1)) (x : PeriodicLatticeSite L) :
    corner m x ∈ Rg ↔ x ∈ Rg := by
  constructor
  · intro h; exact hRg _ h x (fun μ => (corner_div hm hmN x μ).symm)
  · intro h; exact hRg x h _ (fun μ => corner_div hm hmN x μ)

theorem mem_Rg_of_block {z y : PeriodicLatticeSite L} (hz : ∀ μ : Fin 3, ell ^ (j + 1) ∣ (z μ).val)
    (hy : y ∈ blockOf z (ell ^ (j + 1))) : y ∈ Rg ↔ z ∈ Rg := by
  have h := same_block_div (pow_pos hell _) hz hy
  constructor
  · intro hyR; exact hRg y hyR z (fun μ => (h μ))
  · intro hzR; exact hRg z hzR y (fun μ => (h μ).symm)

theorem mem_Rg_of_small_block {z y : PeriodicLatticeSite L} (hz : ∀ μ : Fin 3, ell ^ j ∣ (z μ).val)
    (hy : y ∈ blockOf z (ell ^ j)) : y ∈ Rg ↔ z ∈ Rg := by
  have h := same_big_block hell hz hy
  constructor
  · intro hyR; exact hRg y hyR z (fun μ => (h μ))
  · intro hzR; exact hRg z hzR y (fun μ => (h μ).symm)

open Classical in
/-- the corner of the constraint block of `x`. -/
noncomputable def cc (ell j : ℕ) (Rg : Set (PeriodicLatticeSite L)) (x : PeriodicLatticeSite L) : PeriodicLatticeSite L :=
  if x ∈ Rg then corner (ell ^ (j + 1)) x else corner (ell ^ j) x

/-- `x` and `cc x` lie in exactly the same constraint blocks. -/
theorem block_iff_cc (i : ℕ) (hi : i ≤ j + 1) (z : PeriodicLatticeSite L)
    (hz : z ∈ (geomOf ell (j + 1) (patchTower j Rg)).Lam i) (x : PeriodicLatticeSite L) :
    x ∈ blockOf z (ell ^ i) ↔ cc ell j Rg x ∈ blockOf z (ell ^ i) := by
  classical
  have hn : 0 < ell ^ j := pow_pos hell j
  have hN : 0 < ell ^ (j + 1) := pow_pos hell (j + 1)
  have hnN : ell ^ j ∣ ell ^ (j + 1) := pow_dvd_pow ell (Nat.le_succ j)
  rcases Nat.lt_or_ge i j with hlt | hge
  · rw [lam_lt ell j Rg hlt] at hz; exact False.elim hz
  rcases Nat.lt_or_ge i (j + 1) with hlt2 | hge2
  · have hij : i = j := by omega
    rw [hij] at hz ⊢
    rw [mem_lam_j] at hz
    obtain ⟨hzd, hzR⟩ := hz
    unfold cc
    by_cases hx : x ∈ Rg
    · rw [if_pos hx]
      have h1 : x ∉ blockOf z (ell ^ j) := fun hb => hzR ((mem_Rg_of_small_block hell hRg hzd hb).mp hx)
      have h2 : corner (ell ^ (j + 1)) x ∉ blockOf z (ell ^ j) := fun hb =>
        hzR ((mem_Rg_of_small_block hell hRg hzd hb).mp ((corner_mem_Rg hell hRg hN (dvd_refl _) x).mpr hx))
      exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
    · rw [if_neg hx, mem_blockOf_iff_corner hn z x hzd,
        mem_blockOf_iff_corner hn z _ hzd, corner_idem hn]
  · have hij : i = j + 1 := by omega
    rw [hij] at hz ⊢
    rw [mem_lam_succ] at hz
    obtain ⟨hzd, hzR⟩ := hz
    unfold cc
    by_cases hx : x ∈ Rg
    · rw [if_pos hx, mem_blockOf_iff_corner hN z x hzd,
        mem_blockOf_iff_corner hN z _ hzd, corner_idem hN]
    · rw [if_neg hx]
      have h1 : x ∉ blockOf z (ell ^ (j + 1)) := fun hb => hx ((mem_Rg_of_block hell hRg hzd hb).mpr hzR)
      have h2 : corner (ell ^ j) x ∉ blockOf z (ell ^ (j + 1)) := fun hb =>
        hx ((corner_mem_Rg hell hRg hn hnN x).mp ((mem_Rg_of_block hell hRg hzd hb).mpr hzR))
      exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩

/-- `δ_x s - δ_{cc x} s ∈ N(Q')`. -/
theorem single_diff_mem (x : PeriodicLatticeSite L) (s : SuTwo) :
    (WithLp.toLp 2 (Pi.single x s - Pi.single (cc ell j Rg x) s) : SiteL2 L)
      ∈ NQp (geomOf ell (j + 1) (patchTower j Rg)) (flatCfg : Cfg L) := by
  classical
  refine ⟨fun y hy => absurd (by rw [om0_univ]; trivial) hy, fun i hi z hz => ?_⟩
  rw [Qlev_flat (geomOf ell (j + 1) (patchTower j Rg)) hell]
  have hB := block_iff_cc hell hRg i hi z hz x
  show _ • ∑ y ∈ blockOf z (ell ^ i), (Pi.single x s - Pi.single (cc ell j Rg x) s : PeriodicLatticeSite L → SuTwo) y = 0
  simp only [Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_pi_single']
  by_cases h : x ∈ blockOf z (ell ^ i)
  · rw [if_pos h, if_pos (hB.mp h), sub_self, smul_zero]
  · rw [if_neg h, if_neg (fun h' => h (hB.mpr h')), sub_self, smul_zero]

/-- **every `v ⟂ N(Q')` is constant on constraint blocks**. -/
theorem orth_cc (v : SiteL2 L) (hv : v ∈ (NQp (geomOf ell (j + 1) (patchTower j Rg)) (flatCfg : Cfg L))ᗮ)
    (x : PeriodicLatticeSite L) : v.ofLp x = v.ofLp (cc ell j Rg x) := by
  classical
  set s : SuTwo := v.ofLp x - v.ofLp (cc ell j Rg x) with hs
  have h0 := (Submodule.mem_orthogonal _ v).mp hv _ (single_diff_mem hell hRg x s)
  rw [PiLp.inner_apply] at h0
  simp only [WithLp.ofLp_toLp, Pi.sub_apply, inner_sub_left] at h0
  rw [Finset.sum_sub_distrib] at h0
  have e1 : ∑ y, ⟪(Pi.single x s : PeriodicLatticeSite L → SuTwo) y, v.ofLp y⟫ = ⟪s, v.ofLp x⟫ := by
    rw [Finset.sum_eq_single x (fun y _ hy => by rw [Pi.single_eq_of_ne hy, inner_zero_left])
      (fun h => absurd (Finset.mem_univ x) h), Pi.single_eq_same]
  have e2 : ∑ y, ⟪(Pi.single (cc ell j Rg x) s : PeriodicLatticeSite L → SuTwo) y, v.ofLp y⟫
      = ⟪s, v.ofLp (cc ell j Rg x)⟫ := by
    rw [Finset.sum_eq_single (cc ell j Rg x) (fun y _ hy => by rw [Pi.single_eq_of_ne hy, inner_zero_left])
      (fun h => absurd (Finset.mem_univ _) h), Pi.single_eq_same]
  rw [e1, e2, ← inner_sub_right, ← hs, real_inner_self_eq_norm_sq] at h0
  have : s = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0
    exact norm_eq_zero.mp this
  exact sub_eq_zero.mp this

theorem orth_cell (v : SiteL2 L) (hv : v ∈ (NQp (geomOf ell (j + 1) (patchTower j Rg)) (flatCfg : Cfg L))ᗮ)
    (x : PeriodicLatticeSite L) : v.ofLp x = v.ofLp (corner (ell ^ j) x) := by
  classical
  have hn : 0 < ell ^ j := pow_pos hell j
  have hN : 0 < ell ^ (j + 1) := pow_pos hell (j + 1)
  have hnN : ell ^ j ∣ ell ^ (j + 1) := pow_dvd_pow ell (Nat.le_succ j)
  rw [orth_cc hell hRg v hv x, orth_cc hell hRg v hv (corner (ell ^ j) x)]
  unfold cc
  by_cases hx : x ∈ Rg
  · rw [if_pos hx, if_pos ((corner_mem_Rg hell hRg hn hnN x).mpr hx), corner_corner hn hnN]
  · rw [if_neg hx, if_neg (fun h => hx ((corner_mem_Rg hell hRg hn hnN x).mp h)), corner_idem hn]

theorem orth_big (v : SiteL2 L) (hv : v ∈ (NQp (geomOf ell (j + 1) (patchTower j Rg)) (flatCfg : Cfg L))ᗮ)
    (x : PeriodicLatticeSite L) (hx : x ∈ Rg) : v.ofLp x = v.ofLp (corner (ell ^ (j + 1)) x) := by
  classical
  rw [orth_cc hell hRg v hv x]; unfold cc; rw [if_pos hx]

/-- block sums of a cell-constant function. -/
theorem cell_sum (hdvd : ∀ μ : Fin 3, ell ^ (j + 1) ∣ L μ + 1) (w : PeriodicLatticeSite L → SuTwo)
    (hw : ∀ x, w x = w (corner (ell ^ j) x)) (c : PeriodicLatticeSite L) (hc : ∀ μ : Fin 3, ell ^ j ∣ (c μ).val) :
    ∑ x ∈ blockOf c (ell ^ j), w x = ((ell ^ j : ℕ) : ℝ) ^ 3 • w c := by
  have hn : 0 < ell ^ j := pow_pos hell j
  have hnL : ∀ μ : Fin 3, ell ^ j ∣ L μ + 1 := fun μ => (pow_dvd_pow ell (Nat.le_succ j)).trans (hdvd μ)
  have hfit : ∀ μ : Fin 3, (c μ).val + ell ^ j ≤ L μ + 1 := by
    intro μ
    obtain ⟨a, ha⟩ := hc μ
    obtain ⟨b, hb⟩ := hnL μ
    have hlt : ell ^ j * a < ell ^ j * b := by rw [← ha, ← hb]; exact (c μ).isLt
    have hab : a + 1 ≤ b := Nat.lt_of_mul_lt_mul_left hlt
    have h2 := Nat.mul_le_mul_left (ell ^ j) hab
    rw [Nat.mul_succ] at h2
    rw [ha, hb]; omega
  have hconst : ∀ x ∈ blockOf c (ell ^ j), w x = w c := by
    intro x hx
    rw [hw x, (mem_blockOf_iff_corner hn c x hc).mp hx]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, AdalyFormal.M1Site.card_blockOf c _ hfit, ← Nat.cast_smul_eq_nsmul ℝ]
  congr 1; push_cast; ring

/-- **exact block averages**: for cell-constant `w`, `ext3 w - w ∈ N(Q')`. -/
theorem ext3_sub_mem (hdvd : ∀ μ : Fin 3, ell ^ (j + 1) ∣ L μ + 1) (Nu : Fin 3 → ℕ)
    (hNu : ∀ μ : Fin 3, L μ + 1 = Nu μ * ell ^ j) (w : PeriodicLatticeSite L → SuTwo)
    (hw : ∀ x, w x = w (corner (ell ^ j) x)) :
    ext3 (ell ^ j) Nu w - WithLp.toLp 2 w ∈ NQp (geomOf ell (j + 1) (patchTower j Rg)) (flatCfg : Cfg L) := by
  classical
  have hn : 0 < ell ^ j := pow_pos hell j
  have hcell : ∀ c : PeriodicLatticeSite L, (∀ μ : Fin 3, ell ^ j ∣ (c μ).val) →
      ∑ x ∈ blockOf c (ell ^ j), (ext3 (ell ^ j) Nu w - WithLp.toLp 2 w).ofLp x = 0 := by
    intro c hc
    simp only [WithLp.ofLp_sub, Pi.sub_apply, Finset.sum_sub_distrib, WithLp.ofLp_toLp]
    rw [ext3_block_sum (ell ^ j) Nu hn hNu w c hc, cell_sum hell hRg hdvd w hw c hc, sub_self]
  refine ⟨fun y hy => absurd (by rw [om0_univ]; trivial) hy, fun i hi z hz => ?_⟩
  rw [Qlev_flat (geomOf ell (j + 1) (patchTower j Rg)) hell]
  show _ • ∑ x ∈ blockOf z (ell ^ i), _ = 0
  have hk : (geomOf ell (j + 1) (patchTower j Rg)).k = j + 1 := rfl
  rw [hk] at hi
  rcases Nat.lt_or_ge i j with hlt | hge
  · rw [lam_lt ell j Rg hlt] at hz; exact False.elim hz
  rcases Nat.lt_or_ge i (j + 1) with hlt2 | hge2
  · have hij : i = j := by omega
    rw [hij] at hz ⊢
    rw [mem_lam_j] at hz
    rw [hcell z hz.1, smul_zero]
  · have hij : i = j + 1 := by omega
    rw [hij] at hz ⊢
    rw [mem_lam_succ] at hz
    have hsplit := AdalyFormal.FlatExt.sum_stepBlock_blockOf (ell ^ j) ell hn z
      (fun x => (ext3 (ell ^ j) Nu w - WithLp.toLp 2 w).ofLp x)
    rw [← pow_succ] at hsplit
    rw [← hsplit, Finset.sum_eq_zero, smul_zero]
    intro x hx
    apply hcell x
    intro μ
    have h := (mem_stepBlockOf.mp hx) μ
    obtain ⟨h1, _, ⟨p, hp⟩⟩ := h
    have hz' : ell ^ j ∣ (z μ).val := (pow_dvd_pow ell (Nat.le_succ j)).trans (hz.1 μ)
    obtain ⟨q, hq⟩ := hz'
    exact ⟨p + q, by rw [Nat.mul_add]; omega⟩

theorem massP_add_NQp (hdvd : ∀ μ : Fin 3, ell ^ (j + 1) ∣ L μ + 1) (a : ℝ) (y : BondFnL2 L) (ν : SiteL2 L)
    (hν : ν ∈ NQp (geomOf ell (j + 1) (patchTower j Rg)) (flatCfg : Cfg L)) :
    massP (geomOf ell (j + 1) (patchTower j Rg)) a (y + gradL2 (flatCfg : Cfg L) ν)
      = massP (geomOf ell (j + 1) (patchTower j Rg)) a y := by
  have hB0 := patch_B0 hell hRg hdvd (flatCfg : Cfg L) (regTower_flat (geomOf ell (j + 1) (patchTower j Rg)) (j + 1)) ν hν
  rw [massP_eq, massP_eq, map_add, hB0, add_zero]

end patch

#print axioms flatCfg_eq
#print axioms Qlev_flat
#print axioms QfullOf_grad_flat
#print axioms mem_blockOf_iff_corner
#print axioms block_iff_cc
#print axioms single_diff_mem
#print axioms orth_cc
#print axioms orth_cell
#print axioms orth_big
#print axioms cell_sum
#print axioms ext3_sub_mem
#print axioms PhiP_grad
#print axioms massP_add_NQp

#print axioms bg_flat_triv
#print axioms Qcomp_flat
#print axioms regTower_flat
#print axioms corner_val
#print axioms corner_div
#print axioms corner_corner
#print axioms corner_idem
#print axioms massP_eq
#print axioms massP_nonneg
#print axioms corner_mem_Rg
#print axioms mem_Rg_of_block
#print axioms mem_Rg_of_small_block

end AdalyFormal.LemIFlat
