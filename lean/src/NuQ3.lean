import NuQ2
import NtCvO48

/-!
# NuQ3 -- the row pairing `<Q w, zrow ρ> = <w, zfield (CoverOmega.Wt ρ)>`, `Q*(zrow)`, `Mass` on Z-fields for the direction-0 staggered tower (lane ncwdh_ell2_20261018)

Analogue of `NtCvO39`, `NtCvO41`, `NtCvO42`, `NtCvO44`, `NtCvO47` with `Z0Setup` in place of `StagSetup`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.NcwdhTwo

open scoped Matrix RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverOmega
open AdalyFormal.CoverNested (cartan cartan_coe)
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.GaugeCov
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.UbarTowerCov (UbarTower)

section
variable [CfData]

/-- geometry hypotheses of the Z-reduction for the direction-0 staggered tower. -/
structure Z0Setup (L : PeriodicLatticeExtent) (ell xs : ℕ) (t : ℝ) (G : TowerGeom L) (isRow : ℕ → ℕ → Prop) : Prop where
  z : Z0Hyp L ell xs t
  hG : G.ell = ell
  hk : G.k = 2
  hcrs : ∀ p : BIdx G, Crs (ell ^ (p.1 : ℕ)) p.2.1.1
  hrow : ∀ j, j ≤ 2 → ∀ y : PeriodicLatticeSite L, (y, (1 : Fin 3)) ∈ bondsLam G j ↔ (Crs (ell ^ j) y ∧ isRow j (y 0).val)

variable {L : PeriodicLatticeExtent} {ell xs : ℕ} {t : ℝ}

/-- `QlinB` on an arbitrary sigma_3-valued field (levels `0,1,2`). -/
theorem QlinB_sig0 (Z : Z0Hyp L ell xs t) (G : TowerGeom L) (hG : G.ell = ell) (j : ℕ) (hj : j ≤ 2)
    (A : BondFnL2 L) (hA : SigB (WithLp.ofLp A)) :
    QlinB G (stag0Cfg (L := L) xs t) j A = suCoordInv (aF (thetaSeq ell j (thetaOf (WithLp.ofLp A)))) := by
  have hreg := Z.regTower
  have e : bgTower G (stag0Cfg (L := L) xs t : Cfg L) = UbarTower su2LogExp ell (stag0Cfg (L := L) xs t : PeriodicLinkConfiguration SU2 L) := by
    unfold bgTower; rw [hG]
  obtain ⟨q1, q2, -, -⟩ := stag0_levels_sigma3 Z.hN Z.hE Z.hell t Z.ht Z.hc1 Z.hc2 (thetaOf (WithLp.ofLp A))
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with h0 | h1 | h2
  · subst h0
    rw [QlinB_zero]
    exact (suCoordInv_thetaOf A hA).symm
  · subst h1
    rw [QlinB_apply, e, hG, QlinCompL_eq_QlinCompX2 ell _ 2 hreg 1 (by norm_num), suCoord_sig A hA, q1]
  · subst h2
    rw [QlinB_apply, e, hG, QlinCompL_eq_QlinCompX2 ell _ 2 hreg 2 le_rfl, suCoord_sig A hA, q2]

open Classical in
theorem pair_levels0 {G : TowerGeom L} {isRow : ℕ → ℕ → Prop} (S : Z0Setup L ell xs t G isRow)
    (w : BondFnL2 L) (hw : SigB (WithLp.ofLp w)) (ρ : ℕ → ℕ → ℝ) :
    (inner ℝ (QfullOf G (stag0Cfg (L := L) xs t) w) (zrow G ρ) : ℝ) =
      ∑ j ∈ Finset.range 3, (((ell : ℝ) ^ j)⁻¹) * c0 *
        ∑ y : PeriodicLatticeSite L, (if Crs (ell ^ j) y then Hrow isRow ρ j (y 0).val * thetaSeq ell j (thetaOf (WithLp.ofLp w)) (y, 1) else 0) := by
  rw [PiLp.inner_apply]
  have hterm : ∀ p : BIdx G, (inner ℝ ((QfullOf G (stag0Cfg (L := L) xs t) w) p) ((zrow G ρ) p) : ℝ) =
      (fun (j : Fin (G.k + 1)) (b : Bond L) => if b.2 = 1 then (((ell : ℝ) ^ (j : ℕ))⁻¹) * (thetaSeq ell j (thetaOf (WithLp.ofLp w)) b * ρ j (b.1 0).val * c0) else 0)
        p.1 p.2.1 := by
    intro p
    have hj : (p.1 : ℕ) ≤ 2 := by have := p.1.2; have := S.hk; omega
    show hsInner ((((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (QlinB G (stag0Cfg (L := L) xs t) p.1 w)) p.2.1)
      (if p.2.1.2 = 1 then dgS (ρ (p.1 : ℕ) (p.2.1.1 0).val) else 0) = _
    rw [QlinB_sig0 S.z G S.hG p.1 hj w hw, S.hG, suCoordInv_aF]
    by_cases hb : p.2.1.2 = 1
    · simp only [if_pos hb]
      rw [AdalyFormal.Balaban.SuTwoInner.hsInner_smul_left, hsInner_dgS_dgS]
      rfl
    · simp only [if_neg hb]
      exact AdalyFormal.Balaban.DeltaKU.hsInner_zero_right _
  have hsum := Finset.sum_congr (rfl : (Finset.univ : Finset (BIdx G)) = Finset.univ) (fun p _ => hterm p)
  rw [hsum, sum_BIdx G (fun (j : Fin (G.k + 1)) (b : Bond L) => if b.2 = 1 then (((ell : ℝ) ^ (j : ℕ))⁻¹) * (thetaSeq ell j (thetaOf (WithLp.ofLp w)) b * ρ j (b.1 0).val * c0) else 0)]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => ∑ b : Bond L, (if b ∈ bondsLam G j then (if b.2 = 1 then (((ell : ℝ) ^ j)⁻¹) * (thetaSeq ell j (thetaOf (WithLp.ofLp w)) b * ρ j (b.1 0).val * c0) else 0) else 0)) (G.k + 1)]
  rw [S.hk]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj2 : j ≤ 2 := by have := Finset.mem_range.mp hj; omega
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Fin.sum_univ_three]
  have h0 : (0 : Fin 3) ≠ 1 := by decide
  have h2 : (2 : Fin 3) ≠ 1 := by decide
  simp only [h0, h2, if_false, ite_self, add_zero, zero_add, if_true]
  by_cases hy : Crs (ell ^ j) y
  · by_cases hr : isRow j (y 0).val
    · have hm : (y, (1 : Fin 3)) ∈ bondsLam G j := (S.hrow j hj2 y).mpr ⟨hy, hr⟩
      simp only [if_pos hm, if_pos hy, Hrow, if_pos hr]
      ring
    · have hm : (y, (1 : Fin 3)) ∉ bondsLam G j := fun h => hr ((S.hrow j hj2 y).mp h).2
      simp only [if_neg hm, if_pos hy, Hrow, if_neg hr]
      ring
  · have hm : (y, (1 : Fin 3)) ∉ bondsLam G j := fun h => hy ((S.hrow j hj2 y).mp h).1
    simp only [if_neg hm, if_neg hy]
    ring

open Classical in
theorem pair_Q_zrow0 {G : TowerGeom L} {isRow : ℕ → ℕ → Prop} (S : Z0Setup L ell xs t G isRow)
    (w : BondFnL2 L) (hw : SigB (WithLp.ofLp w)) (ρ : ℕ → ℕ → ℝ) :
    (inner ℝ (QfullOf G (stag0Cfg (L := L) xs t) w) (zrow G ρ) : ℝ) =
      c0 * ∑ x : PeriodicLatticeSite L, thetaOf (WithLp.ofLp w) (x, 1) * CoverOmega.Wt ell isRow ρ (x 0).val := by
  rw [pair_levels0 S w hw ρ]
  obtain ⟨l0, l1, l2⟩ := lev_sums S.z.hell S.z.hdiv (thetaOf (WithLp.ofLp w)) (Hrow isRow ρ)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [l0, l1, l2]
  have hW : ∀ x : PeriodicLatticeSite L, thetaOf (WithLp.ofLp w) (x, 1) * CoverOmega.Wt ell isRow ρ (x 0).val =
      (((ell : ℝ) ^ 0)⁻¹ * ((((ell : ℝ) ^ 2)⁻¹) ^ 0) * (Hrow isRow ρ 0 (ell ^ 0 * ((x 0).val / ell ^ 0)) * thetaOf (WithLp.ofLp w) (x, 1))) +
      (((ell : ℝ) ^ 1)⁻¹ * ((((ell : ℝ) ^ 2)⁻¹) ^ 1) * (Hrow isRow ρ 1 (ell ^ 1 * ((x 0).val / ell ^ 1)) * thetaOf (WithLp.ofLp w) (x, 1))) +
      (((ell : ℝ) ^ 2)⁻¹ * ((((ell : ℝ) ^ 2)⁻¹) ^ 2) * (Hrow isRow ρ 2 (ell ^ 2 * ((x 0).val / ell ^ 2)) * thetaOf (WithLp.ofLp w) (x, 1))) := by
    intro x
    simp only [CoverOmega.Wt, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Hrow]
    ring
  rw [Finset.sum_congr rfl (fun x _ => hW x), Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem Qfull_adBL0 (G : TowerGeom L) (w : BondFnL2 L) :
    QfullOf G (stag0Cfg (L := L) xs t) (adBL (hGauge L) w) = adFL (hGauge L) G (QfullOf G (stag0Cfg (L := L) xs t) w) := by
  have := QfullOf_gauge G (stag0Cfg (L := L) xs t : Cfg L) (hGauge L) w
  rwa [gaugeTransform_hGauge (stag0Cfg_cartan xs t)] at this

/-- **`<Q w, zrow ρ> = <w, zfield (CoverOmega.Wt ρ)>` for every `w`**. -/
theorem inner_Q_zrow0 {G : TowerGeom L} {isRow : ℕ → ℕ → Prop} (S : Z0Setup L ell xs t G isRow)
    (w : BondFnL2 L) (ρ : ℕ → ℕ → ℝ) :
    (inner ℝ (QfullOf G (stag0Cfg (L := L) xs t) w) (zrow G ρ) : ℝ) = inner ℝ w (zfield (CoverOmega.Wt ell isRow ρ)) := by
  set A := adBL (hGauge L) with hA
  set AF := adFL (hGauge L) G with hAF
  set u := w + A w with hu
  have hAu : A u = u := by
    rw [hu, map_add, hA, adBL_hGauge_sq]; abel
  have hus : SigB (WithLp.ofLp u) := (adBL_hGauge_fixed_iff u).mp hAu
  have hl : (inner ℝ (QfullOf G (stag0Cfg (L := L) xs t) u) (zrow G ρ) : ℝ) = 2 * inner ℝ (QfullOf G (stag0Cfg (L := L) xs t) w) (zrow G ρ) := by
    rw [hu, map_add, Qfull_adBL0, inner_add_left]
    have : (inner ℝ (AF (QfullOf G (stag0Cfg (L := L) xs t) w)) (zrow G ρ) : ℝ) = inner ℝ (QfullOf G (stag0Cfg (L := L) xs t) w) (zrow G ρ) := by
      conv_lhs => rw [← adFL_zrow G ρ]
      exact (adFL (hGauge L) G).inner_map_map _ _
    rw [this]; ring
  have hr : (inner ℝ u (zfield (CoverOmega.Wt ell isRow ρ)) : ℝ) = 2 * inner ℝ w (zfield (CoverOmega.Wt ell isRow ρ)) := by
    rw [hu, inner_add_left]
    have : (inner ℝ (A w) (zfield (CoverOmega.Wt ell isRow ρ)) : ℝ) = inner ℝ w (zfield (CoverOmega.Wt ell isRow ρ)) := by
      conv_lhs => rw [← adBL_zfield (L := L) (CoverOmega.Wt ell isRow ρ)]
      exact (adBL (hGauge L)).inner_map_map _ _
    rw [this]; ring
  have key := pair_Q_zrow0 S u hus ρ
  rw [inner_sig_zfield u hus] at hr
  linarith

theorem Qfull_zfield_eq_zrow0 {G : TowerGeom L} {isRow : ℕ → ℕ → Prop} (S : Z0Setup L ell xs t G isRow)
    (f : ℕ → ℝ) : QfullOf G (stag0Cfg (L := L) xs t) (zfield f) = zrow G (fun j v => ((ell : ℝ) ^ j)⁻¹ * fSum ell j f v) := by
  refine PiLp.ext (fun p => ?_)
  rw [Qfull_zfield0 S.z f G S.hG S.hk S.hcrs p]
  show _ = (if p.2.1.2 = 1 then dgS (((ell : ℝ) ^ (p.1 : ℕ))⁻¹ * fSum ell (p.1 : ℕ) f (p.2.1.1 0).val) else 0)
  split_ifs
  · rw [dgS_smul]
  · simp

theorem Qstar_zrow0 {G : TowerGeom L} {isRow : ℕ → ℕ → Prop} (S : Z0Setup L ell xs t G isRow)
    (ρ : ℕ → ℕ → ℝ) : ContinuousLinearMap.adjoint (QfullOf G (stag0Cfg (L := L) xs t)) (zrow G ρ) = zfield (CoverOmega.Wt ell isRow ρ) := by
  apply ext_inner_left ℝ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact inner_Q_zrow0 S w ρ

/-- **`Mass` on a Z-field**. -/
theorem MassFull_zfield0 {G : TowerGeom L} {isRow : ℕ → ℕ → Prop} (S : Z0Setup L ell xs t G isRow)
    (a : ℝ) (f : ℕ → ℝ) :
    MassFull G a (bondSectorOf G (stag0Cfg (L := L) xs t)) (zfield f) =
      zfield (CoverOmega.Wt ell isRow (fun j v => a * fSum ell j f v)) := by
  show ContinuousLinearMap.adjoint (QfullOf G (stag0Cfg (L := L) xs t)) (diagW G (massW G a) (QfullOf G (stag0Cfg (L := L) xs t) (zfield f))) = _
  rw [Qfull_zfield_eq_zrow0 S f, diagW_massW_zrow G ell S.hG, Qstar_zrow0 S]
  have hne : ∀ j : ℕ, (ell : ℝ) ^ j ≠ 0 := fun j => pow_ne_zero _ (by exact_mod_cast S.z.hell.ne')
  have : (fun (j v : ℕ) => a * (ell : ℝ) ^ j * (((ell : ℝ) ^ j)⁻¹ * fSum ell j f v)) = (fun (j v : ℕ) => a * fSum ell j f v) := by
    funext j v
    field_simp [hne j]
  rw [this]

end

end AdalyFormal.NcwdhTwo
