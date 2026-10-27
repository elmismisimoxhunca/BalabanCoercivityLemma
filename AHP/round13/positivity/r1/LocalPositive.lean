import DrEquiv
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

namespace AdalyFormal.Round2.Guarded.Pin

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

/-! Verbatim operative declarations from D1Lit.lean:29-101. -/
abbrev PlaqSel : Type := ∀ (L : PeriodicLatticeExtent), TowerGeom L → Set (PeriodicLatticePlaquette L)

def selIn : PlaqSel := fun _ G => plaqIn G.Om0

def selAll : PlaqSel := fun _ _ => Set.univ

section Selectors
variable (sD sJ : PlaqSel)

noncomputable def DeltaS {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L) : BondFnL2 L →L[ℝ] BondFnL2 L :=
  AdalyFormal.StatementLaneR6.deltaKLocCLM U (sD L G)

noncomputable def DpiFullS {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L) (a : ℝ) : BondFnL2 L →L[ℝ] BondFnL2 L :=
  (ContinuousLinearMap.adjoint (Wop G U a)).comp ((DeltaS sD G U).comp (Wop G U a))

theorem DpiFullS_symm {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L) (a : ℝ) (x y : BondFnL2 L) :
    ⟪DpiFullS sD G U a x, y⟫ = ⟪x, DpiFullS sD G U a y⟫ := by
  simp only [DpiFullS, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]
  exact AdalyFormal.StatementLaneR6.deltaKLocCLM_symm U _ _ _

section Ops
variable (P : IngrBParams)

noncomputable def JfS : BondFnL2 (scaleUp P.ell P.k P.Lu) :=
  WithLp.toLp 2 (fun b => -(AdalyFormal.IngredientFamily.JSU2Loc 1 (sJ _ P.G) P.U b))

noncomputable def dataS : BaseDataS ↥(bondSupp P.G) (SiteL2 (scaleUp P.ell P.k P.Lu)) (FSp P.G) :=
  { baseData P.G P.U P.a P.sector (JfS sJ P) with
    Dpi := (pE P.G).comp ((DpiFullS sD P.G P.U P.a).comp (iE P.G)) }

theorem dataS_laws : (dataS sD sJ P).Laws := by
  refine ⟨fun x y => ?_, P.data_laws.C2_quad⟩
  show ⟪((pE P.G).comp ((DpiFullS sD P.G P.U P.a).comp (iE P.G))) x, y⟫ = ⟪x, ((pE P.G).comp ((DpiFullS sD P.G P.U P.a).comp (iE P.G))) y⟫
  simp only [ContinuousLinearMap.comp_apply]
  rw [pE_inner_left, pE_inner_right]
  exact DpiFullS_symm sD P.G P.U P.a _ _



end Ops
end Selectors
end AdalyFormal.Round2.Guarded.Pin


noncomputable section
namespace AdalyFormal.Round4.Guarded.RefuteR1
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round2.Guarded.Pin

open Classical

def dilLu (q R : ℕ) : PeriodicLatticeExtent :=
  fun μ => if μ = 0 then 6 * (R * q) + 8 * q - 1 else 4 * q - 1

def dilTower (q R : ℕ) : Tower (scaleUp 2 1 (dilLu q R)) where
  Om j := if j = 0 then {x | 4 * q ≤ (x 0).val ∧ (x 0).val < 12 * (R * q) + 12 * q}
    else if j = 1 then {x | 2 * (R * q) + 4 * q ≤ (x 0).val ∧ (x 0).val < 10 * (R * q) + 12 * q}
    else ∅

def dilLam (q R : ℕ) : Set (PeriodicLatticeSite (dilLu q R)) :=
  {x | 3 * (R * q) + 4 * q ≤ (x 0).val ∧ (x 0).val < 3 * (R * q) + 6 * q}

theorem dil_unit_size {q : ℕ} (hq : 0 < q) (R : ℕ) (μ : Fin 3) :
    dilLu q R μ + 1 = if μ = 0 then 6 * (R * q) + 8 * q else 4 * q := by
  by_cases h : μ = 0 <;> simp [dilLu, h] <;> omega

theorem dil_fine_size {q : ℕ} (hq : 0 < q) (R : ℕ) (μ : Fin 3) :
    scaleUp 2 1 (dilLu q R) μ + 1 = if μ = 0 then 12 * (R * q) + 16 * q else 8 * q := by
  simp only [scaleUp, dil_unit_size hq]
  by_cases h : μ = 0 <;> simp [h] <;> omega

def dilPattern (q R : ℕ) (e : Bond (scaleUp 2 1 (dilLu q R))) : Prop :=
  (e.1 0).val = 2*(R*q)+4*q ∧ (e.1 1).val % 2 = 0 ∧ (e.1 2).val % 2 = 0 ∧ e.2 = 1

noncomputable def dilU (q R : ℕ) (ε : ℝ) (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  fun e => if e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) then V e
    else Ug (if dilPattern q R e then ε else 0)

end AdalyFormal.Round4.Guarded.RefuteR1


namespace AdalyFormal.Round3.Guarded.RefuteR2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
theorem zero_coord_le_pdist {L : PeriodicLatticeExtent} (x y : PeriodicLatticeSite L) :
    pcd (L 0 + 1) (x 0).val (y 0).val ≤ pdist x y :=
  Finset.single_le_sum (f := fun μ : Fin 3 => pcd (L μ + 1) (x μ).val (y μ).val)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)


end AdalyFormal.Round3.Guarded.RefuteR2

namespace AdalyFormal.Round4.Guarded.RefuteR1
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round3.Guarded.RefuteR2 (zero_coord_le_pdist)
open AdalyFormal.NonVac (iv_block pcd_clamp pcd_near pcd_self')
theorem dil_fine_bound {q : ℕ} (hq : 0 < q) (R : ℕ)
    (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) :
    (x 0).val < 12 * (R * q) + 16 * q := by
  have h := (x 0).isLt
  simpa only [dil_fine_size hq, ↓reduceIte] using h

theorem dil_admissible {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) :
    Admissible 2 (2*q) R 1 (dilTower q R) := by
  have hp : 4*q ∣ 2*(R*q)+4*q := by
    obtain ⟨t, rfl⟩ := hR; exact ⟨t+1, by ring⟩
  have hq' : 4*q ∣ 10*(R*q)+12*q := by
    obtain ⟨t, rfl⟩ := hR; exact ⟨5*t+3, by ring⟩
  have hlo : 2*q ∣ 4*q := ⟨2, by ring⟩
  have hhi : 2*q ∣ 12*(R*q)+12*q := ⟨6*R+6, by ring⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j x hx
    by_cases h0 : j = 0
    · subst j
      change (2*(R*q)+4*q ≤ (x 0).val ∧ (x 0).val < 10*(R*q)+12*q) at hx
      change 4*q ≤ (x 0).val ∧ (x 0).val < 12*(R*q)+12*q
      omega
    · simp [dilTower, h0] at hx
  · intro j hj
    simp [dilTower, show j ≠ 0 by omega, show j ≠ 1 by omega]
  · intro j hj μ
    rw [dil_fine_size hq]
    interval_cases j <;> by_cases hμ : μ = 0 <;> simp only [bigSide, pow_zero, pow_one, mul_one, hμ, ↓reduceIte]
    · exact ⟨6*R+8, by ring⟩
    · exact ⟨4, by ring⟩
    · exact ⟨3*R+4, by ring⟩
    · exact ⟨2, by ring⟩
  · intro j hj x hx y hy
    interval_cases j
    · change (4*q ≤ (x 0).val ∧ (x 0).val < 12*(R*q)+12*q) at hx
      change 4*q ≤ (y 0).val ∧ (y 0).val < 12*(R*q)+12*q
      apply iv_block (by omega : 0 < 2*q) hlo hhi _ hx
      simpa [bigSide] using hy 0
    · change (2*(R*q)+4*q ≤ (x 0).val ∧ (x 0).val < 10*(R*q)+12*q) at hx
      change 2*(R*q)+4*q ≤ (y 0).val ∧ (y 0).val < 10*(R*q)+12*q
      apply iv_block (by omega : 0 < 4*q) hp hq' _ hx
      simpa [bigSide, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hy 0
  · intro j hj x hx y hy
    interval_cases j
    · change ¬ (4*q ≤ (x 0).val ∧ (x 0).val < 12*(R*q)+12*q) at hx
      change (2*(R*q)+4*q ≤ (y 0).val ∧ (y 0).val < 10*(R*q)+12*q) at hy
      have hxb := dil_fine_bound hq R x
      have hpd := zero_coord_le_pdist x y
      simp only [dil_fine_size hq, ↓reduceIte] at hpd
      have hcoord : 2*(R*q) < pcd (12*(R*q)+16*q) (x 0).val (y 0).val := by
        unfold pcd; split_ifs <;> omega
      have heq : R * bigSide (2*q) 2 0 = 2*(R*q) := by simp [bigSide]; ring
      rw [heq]; exact lt_of_lt_of_le hcoord hpd
    · simp [dilTower] at hy
  · intro x
    change (4*q ≤ (x 0).val ∧ (x 0).val < 12*(R*q)+12*q) ↔ _
    have hrm : R*(2*q) = 2*(R*q) := by ring
    constructor
    · intro hx
      let v := if (x 0).val < 2*(R*q)+4*q then 2*(R*q)+4*q
        else if (x 0).val < 10*(R*q)+12*q then (x 0).val else 10*(R*q)+12*q-1
      have hv : v < scaleUp 2 1 (dilLu q R) 0 + 1 := by
        rw [dil_fine_size hq, if_pos rfl]
        dsimp [v]; split_ifs <;> omega
      refine ⟨Function.update x 0 ⟨v, hv⟩, ?_, x, fun μ => rfl, ?_⟩
      · change 2*(R*q)+4*q ≤ v ∧ v < 10*(R*q)+12*q
        dsimp [v]; split_ifs <;> omega
      · unfold pdist
        rw [Finset.sum_eq_single (0 : Fin 3)]
        · simp only [Function.update_self, dil_fine_size hq, ↓reduceIte, hrm]
          have hc := pcd_clamp (N := 12*(R*q)+16*q) (a := (x 0).val)
            (lo := 2*(R*q)+4*q) (hi := 10*(R*q)+12*q) (D := 2*(R*q))
            (by omega) (by omega) (dil_fine_bound hq R x) (by omega)
          simpa [v] using hc
        · intro μ _ hμ; rw [Function.update_of_ne hμ, pcd_self']
        · intro h; exact (h (Finset.mem_univ _)).elim
    · rintro ⟨y, hy, z, hz, hd⟩
      change (2*(R*q)+4*q ≤ (y 0).val ∧ (y 0).val < 10*(R*q)+12*q) at hy
      have hcoord := le_trans (zero_coord_le_pdist z y) hd
      simp only [dil_fine_size hq, ↓reduceIte, hrm] at hcoord
      have hn := pcd_near (dil_fine_bound hq R z) hy
        (show 2*(R*q) ≤ 2*(R*q)+4*q by omega)
        (show 10*(R*q)+12*q+2*(R*q) ≤ 12*(R*q)+16*q by omega) hcoord
      have hzmem : 4*q ≤ (z 0).val ∧ (z 0).val < 12*(R*q)+12*q := by omega
      exact iv_block (by omega : 0 < 2*q) hlo hhi (hz 0).symm hzmem


end AdalyFormal.Round4.Guarded.RefuteR1

namespace AdalyFormal.Round9.Guarded.AnalyticR2
open scoped RealInnerProductSpace Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.QjComposite (stepAverage)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
variable {L : PeriodicLatticeExtent}
theorem Qcomposite_one' (bg : ℕ → Cfg L) (ell : ℕ) (lam : PeriodicLatticeSite L → SuTwo) :
    AdalyFormal.Balaban.QjComposite.Qcomposite bg ell 1 lam = stepAverage (ell ^ 0) (bg 0) ell lam :=
  rfl

theorem bgTower_zero' (G : TowerGeom L) (U : Cfg L) : bgTower G U 0 = U := rfl

theorem QfullOf_apply (G : TowerGeom L) (U : Cfg L) (A : BondFnL2 L) (p : BIdx G) :
    WithLp.ofLp (QfullOf G U A) p
      = (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (QlinB G U p.1 A)) p.2.1 := rfl

theorem dil_G_k (q R : ℕ) : (geomOf 2 1 (dilTower q R)).k = 1 := rfl
theorem dil_G_ell (q R : ℕ) : (geomOf 2 1 (dilTower q R)).ell = 2 := rfl

theorem delW_zero (ell k : ℕ) (hell : 0 < ell) : AdalyFormal.W6.delW ell k (fun _ => 0) = 0 := by
  unfold AdalyFormal.W6.delW AdalyFormal.W6.SS
  simp [AdalyFormal.BondComposite.thetaOf_zero ell hell]

theorem dil_Qs_inj {q R : ℕ} (hq : 0 < q) (hR16 : 16 ≤ R) (hS : Admissible 2 (2 * q) R 1 (dilTower q R)) :
    Function.Injective (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (trivialU (scaleUp 2 1 (dilLu q R))) 1 (dilLam q R)).data.Qs :=
  AdalyFormal.W6.qs_injective_strat (by norm_num) (le_refl 2) hS (by omega) (by omega)
    (trivialU _) 1 (dilLam q R) (fun _ => 0) (AdalyFormal.W6.regTower_triv (by norm_num))
    (AdalyFormal.W6.towerClass_triv (by norm_num)) (fun _ _ => le_rfl)
    (fun _ _ => AdalyFormal.W6.rhoOf_zero_lt 2) (by rw [delW_zero 2 1 (by norm_num)]; norm_num)


end AdalyFormal.Round9.Guarded.AnalyticR2
namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

/-! ## J. The flat localized carrier of the dilated tower is positive definite

At the trivial background `⟪x, B x⟫ = ‖χ curl x‖² + ‖T x‖² + Σ a ℓʲ ‖Q x‖²` (`B` the localized
carrier).  If it vanishes, `x` is curl-free on the plaquettes of `Ω₀`, vanishes on every bond not
touching `Ω₁` (level-0 rows of `Q`), and has vanishing level-1 rows.  Integrating `x` along the
longitudinal lines from the left boundary gives a site field `ξ` with `x = D ξ` on the bonds
before the right edge; the level-1 rows telescope along the longitudinal chain of blocks from the
left collar (where `ξ = 0`) to the right collar (where `ξ` is a transverse constant), so the
constant is `0`, `ξ ∈ N(Q')` and `x = D ξ` everywhere; then `T (D ξ) = 0` forces `D ξ = 0`
(the frozen `final_step` argument, copied). -/
section FlatKernel

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dil_fine_size)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_one curlValueCovariant
  gradValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QjComposite (stepBlockOf stepAverage)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open Fin.NatCast

/-! ### Frozen `NsPtD2.final_step` (outside the `DrEquiv` closure), copied verbatim. -/

theorem siteMask_eq_self_of_supp' {L : PeriodicLatticeExtent} (S : Set (PeriodicLatticeSite L))
    (ξ : SiteL2 L) (h : ∀ x, x ∉ S → ξ x = 0) : siteMask S ξ = ξ := by
  classical
  ext x
  rw [siteMask_apply]
  by_cases hx : x ∈ S
  · rw [if_pos hx]
  · rw [if_neg hx, h x hx]

theorem lapDir_eq_mask_lap' {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L) (ξ : SiteL2 L)
    (h : ∀ x, x ∉ G.Om0 → ξ x = 0) : lapDir G U ξ = siteMask G.Om0 (lapFull U ξ) := by
  unfold lapDir
  simp only [ContinuousLinearMap.comp_apply]
  rw [siteMask_eq_self_of_supp' _ _ h]

theorem final_step' {L : PeriodicLatticeExtent} (G : TowerGeom L) (ξ : SiteL2 L)
    (hξ : ξ ∈ NQp G (flatCfg : Cfg L))
    (hT : Tfull G (flatCfg : Cfg L) (gradL2 (flatCfg : Cfg L) ξ) = 0) :
    gradL2 (flatCfg : Cfg L) ξ = 0 := by
  have hsupp := hξ.1
  have hlap := lapDir_eq_mask_lap' G flatCfg ξ hsupp
  have hmem : lapDir G (flatCfg : Cfg L) ξ ∈ RImage G (flatCfg : Cfg L) :=
    Submodule.mem_map.mpr ⟨ξ, hξ, rfl⟩
  have hR : Rproj G (flatCfg : Cfg L) (lapFull (flatCfg : Cfg L) ξ) = 0 := by
    have : Tfull G (flatCfg : Cfg L) (gradL2 (flatCfg : Cfg L) ξ) =
        Rproj G (flatCfg : Cfg L) (lapFull (flatCfg : Cfg L) ξ) := rfl
    rw [← this]; exact hT
  have horth : lapFull (flatCfg : Cfg L) ξ ∈ (RImage G (flatCfg : Cfg L))ᗮ := by
    have := hR
    unfold Rproj at this
    exact (Submodule.starProjection_apply_eq_zero_iff _).mp this
  have h1 : ⟪lapDir G (flatCfg : Cfg L) ξ, lapFull (flatCfg : Cfg L) ξ⟫ = 0 :=
    (Submodule.mem_orthogonal _ _).mp horth _ hmem
  have h2 : ⟪lapDir G (flatCfg : Cfg L) ξ, lapFull (flatCfg : Cfg L) ξ⟫ =
      ‖lapDir G (flatCfg : Cfg L) ξ‖ ^ 2 := by
    have e : ⟪siteMask G.Om0 (lapFull (flatCfg : Cfg L) ξ), lapFull (flatCfg : Cfg L) ξ⟫
        = ⟪siteMask G.Om0 (lapFull (flatCfg : Cfg L) ξ),
            siteMask G.Om0 (lapFull (flatCfg : Cfg L) ξ)⟫ := by
      calc ⟪siteMask G.Om0 (lapFull (flatCfg : Cfg L) ξ), lapFull (flatCfg : Cfg L) ξ⟫
          = ⟪siteMask G.Om0 (siteMask G.Om0 (lapFull (flatCfg : Cfg L) ξ)),
              lapFull (flatCfg : Cfg L) ξ⟫ := by rw [siteMask_idem]
        _ = _ := siteMask_symm _ _ _
    rw [hlap, e, real_inner_self_eq_norm_sq]
  have h3 : lapDir G (flatCfg : Cfg L) ξ = 0 := by
    rw [h2] at h1
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h1)
  have h4 : ⟪ξ, lapFull (flatCfg : Cfg L) ξ⟫ = 0 := by
    have : ⟪ξ, lapFull (flatCfg : Cfg L) ξ⟫ = ⟪siteMask G.Om0 ξ, lapFull (flatCfg : Cfg L) ξ⟫ := by
      rw [siteMask_eq_self_of_supp' _ _ hsupp]
    rw [this, siteMask_symm, ← hlap, h3, inner_zero_right]
  have h5 : ⟪ξ, lapFull (flatCfg : Cfg L) ξ⟫ = ‖gradL2 (flatCfg : Cfg L) ξ‖ ^ 2 := by
    simp only [lapFull, ContinuousLinearMap.comp_apply, gradAdj, ContinuousLinearMap.adjoint_inner_right]
    rw [real_inner_self_eq_norm_sq]
  rw [h5] at h4
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h4)

/-! ### Coordinates of the dilated tower -/

variable {q R : ℕ}

theorem dsize0 (hq : 0 < q) : scaleUp 2 1 (dilLu q R) 0 + 1 = 12 * (R * q) + 16 * q := by
  have h := dil_fine_size hq R 0
  simpa using h

theorem dsizeT (hq : 0 < q) {μ : Fin 3} (hμ : μ ≠ 0) : scaleUp 2 1 (dilLu q R) μ + 1 = 8 * q := by
  rw [dil_fine_size hq R μ, if_neg hμ]

theorem x0_lt (hq : 0 < q) (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) :
    (x 0).val < 12 * (R * q) + 16 * q := by
  have h1 := (x 0).isLt
  have h2 := dsize0 (R := R) hq
  omega

theorem xT_lt (hq : 0 < q) (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {μ : Fin 3} (hμ : μ ≠ 0) :
    (x μ).val < 8 * q := by
  have h1 := (x μ).isLt
  have h2 := dsizeT (R := R) hq hμ
  omega

theorem mem_Om0 (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) :
    x ∈ (dilTower q R).Om 0 ↔ 4 * q ≤ (x 0).val ∧ (x 0).val < 12 * (R * q) + 12 * q := Iff.rfl

theorem mem_Om1 (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) :
    x ∈ (dilTower q R).Om 1 ↔
      2 * (R * q) + 4 * q ≤ (x 0).val ∧ (x 0).val < 10 * (R * q) + 12 * q := Iff.rfl

theorem not_mem_Om2 (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) :
    x ∉ (dilTower q R).Om 2 := by
  simp [dilTower]

theorem shift_coord_ne {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) {μ ν : Fin 3}
    (h : ν ≠ μ) : (periodicLatticeShift x μ) ν = x ν := by
  unfold periodicLatticeShift
  rw [Function.update_of_ne h]

theorem shift_self_coord {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) (μ : Fin 3) :
    (periodicLatticeShift x μ) μ = x μ + 1 := by
  unfold periodicLatticeShift
  rw [Function.update_self]

theorem shift0_val_lt {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L)
    (h : (x 0).val + 1 < L 0 + 1) : ((periodicLatticeShift x 0) 0).val = (x 0).val + 1 := by
  rw [shift_self_coord, Fin.val_add_one, if_neg]
  intro hc
  rw [hc, Fin.val_last] at h
  omega

theorem shift0_val_last {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L)
    (h : (x 0).val + 1 = L 0 + 1) : ((periodicLatticeShift x 0) 0).val = 0 := by
  rw [shift_self_coord, Fin.val_add_one, if_pos]
  ext
  rw [Fin.val_last]
  omega

/-! ### The kernel argument -/

section Kernel
variable (hq : 0 < q) (hR : 1 ≤ R) (A : BondFnL2 (scaleUp 2 1 (dilLu q R)))
  (hsupp : ∀ b, b ∉ bondsOm0 (geomOf 2 1 (dilTower q R)) → A b = 0)
  (hQ : QfullOf (geomOf 2 1 (dilTower q R)) flatCfg A = 0)

theorem OmGe1_mem {x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))}
    (h : OmGe (geomOf 2 1 (dilTower q R)) 1 x) : x ∈ (dilTower q R).Om 1 := by
  obtain ⟨i, hi1, hik, y, hy, hxy⟩ := h
  have hi : i = 1 := by
    have : i ≤ 1 := hik
    omega
  subst hi
  obtain ⟨hdiv, hyOm, -⟩ := hy
  rw [mem_Om1] at hyOm ⊢
  have h0 := hxy 0
  have hd := hdiv 0
  have hell : (geomOf 2 1 (dilTower q R)).ell = 2 := rfl
  simp only [pow_one, hell] at hd h0
  have hb : 2 ∣ 10 * (R * q) + 12 * q := ⟨5 * (R * q) + 6 * q, by ring⟩
  omega

include hsupp hQ in
theorem A_zero_off {b : Bond (scaleUp 2 1 (dilLu q R))} (h1 : b.1 ∉ (dilTower q R).Om 1)
    (h2 : periodicLatticeShift b.1 b.2 ∉ (dilTower q R).Om 1) : A b = 0 := by
  by_cases hb : b ∈ bondsOm0 (geomOf 2 1 (dilTower q R))
  · have hL : b ∈ bondsLam (geomOf 2 1 (dilTower q R)) 0 := by
      refine ⟨?_, ?_⟩
      · rcases hb with hb | hb
        · exact Or.inl ⟨fun μ => by simp, hb, h1⟩
        · exact Or.inr ⟨fun μ => by simp, hb, h2⟩
      · rintro (h | h)
        · exact h1 (OmGe1_mem h)
        · exact h2 (OmGe1_mem h)
    have h := congrArg (fun v : FSp (geomOf 2 1 (dilTower q R)) => WithLp.ofLp v ⟨0, ⟨b, hL⟩⟩) hQ
    have h' : WithLp.ofLp (QfullOf (geomOf 2 1 (dilTower q R)) flatCfg A) ⟨0, ⟨b, hL⟩⟩ = A b := by
      rw [QfullOf_apply]
      show (((geomOf 2 1 (dilTower q R)).ell : ℝ) ^ 0)⁻¹ •
        (WithLp.ofLp (QlinB (geomOf 2 1 (dilTower q R)) flatCfg 0 A)) b = A b
      rw [QlinB_zero, pow_zero, inv_one, one_smul]
    simp only at h
    rw [h'] at h
    exact h
  · exact hsupp b hb

/-- the site with longitudinal coordinate replaced by `u`. -/
def sitex (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u : ℕ) :
    PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) :=
  Function.update z 0 ((u : ℕ) : Fin (scaleUp 2 1 (dilLu q R) 0 + 1))

omit hq A in
theorem sitex_val (hq : 0 < q) (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {u : ℕ}
    (hu : u < 12 * (R * q) + 16 * q) : ((sitex z u) 0).val = u := by
  unfold sitex
  rw [Function.update_self, Fin.val_natCast, dsize0 hq]
  exact Nat.mod_eq_of_lt hu

omit A in
theorem sitex_coord (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u : ℕ) {ν : Fin 3}
    (hν : ν ≠ 0) : (sitex z u) ν = z ν := by
  unfold sitex
  rw [Function.update_of_ne hν]

omit A in
theorem sitex_self (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) : sitex z (z 0).val = z := by
  unfold sitex
  rw [Fin.cast_val_eq_self, Function.update_eq_self]

omit A in
theorem sitex_sitex (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u v : ℕ) :
    sitex (sitex z v) u = sitex z u := by
  unfold sitex
  rw [Function.update_idem]

omit A in
theorem shift_sitex0 (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u : ℕ) :
    periodicLatticeShift (sitex z u) 0 = sitex z (u + 1) := by
  unfold periodicLatticeShift sitex
  rw [Function.update_idem, Function.update_self, Nat.cast_succ]

omit A in
theorem shift_sitex (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u : ℕ) {μ : Fin 3}
    (hμ : μ ≠ 0) : periodicLatticeShift (sitex z u) μ = sitex (periodicLatticeShift z μ) u := by
  unfold periodicLatticeShift sitex
  rw [Function.update_of_ne hμ, Function.update_comm (Ne.symm hμ)]

omit A in
theorem sitex_of_shift0 (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u : ℕ) :
    sitex (periodicLatticeShift z 0) u = sitex z u := by
  unfold periodicLatticeShift sitex
  rw [Function.update_idem]

/-- the longitudinal potential. -/
noncomputable def xi (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) : SuTwo :=
  ∑ u ∈ Finset.range (z 0).val, A (sitex z u, 0)

include hq in
/-- longitudinal step. -/
theorem xi_shift0 (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)))
    (h : (z 0).val + 1 < 12 * (R * q) + 16 * q) :
    xi A (periodicLatticeShift z 0) = xi A z + A (z, 0) := by
  unfold xi
  have hz : ((periodicLatticeShift z 0) 0).val = (z 0).val + 1 :=
    shift0_val_lt z (by have h2 := dsize0 (R := R) hq; omega)
  rw [hz, Finset.sum_range_succ]
  simp only [sitex_of_shift0]
  rw [sitex_self]

include hq hR hsupp hQ in
/-- the plaquette identity in the `(0, μ)` plane, from curl-freeness or vanishing of all bonds. -/
theorem trans_step
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (w : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {μ : Fin 3} (hμ : μ ≠ 0)
    (hw : (w 0).val + 1 < 12 * (R * q) + 16 * q) :
    A (periodicLatticeShift w μ, 0) - A (w, 0) = A (periodicLatticeShift w 0, μ) - A (w, μ) := by
  classical
  have h0μ : (0 : Fin 3) < μ := by
    rcases Fin.pos_iff_ne_zero.mpr hμ with h
    exact h
  have hw0 : ((periodicLatticeShift w 0) 0).val = (w 0).val + 1 :=
    shift0_val_lt w (by have h2 := dsize0 (R := R) hq; omega)
  have hwμ : (periodicLatticeShift w μ) 0 = w 0 := shift_coord_ne w (Ne.symm hμ)
  have hw0μ : ((periodicLatticeShift (periodicLatticeShift w 0) μ) 0).val = (w 0).val + 1 := by
    rw [shift_coord_ne _ (Ne.symm hμ), hw0]
  have hwμ0 : ((periodicLatticeShift (periodicLatticeShift w μ) 0) 0).val = (w 0).val + 1 := by
    rw [shift0_val_lt _ (by have h2 := dsize0 (R := R) hq; rw [hwμ]; omega), hwμ]
  by_cases hin : 4 * q ≤ (w 0).val ∧ (w 0).val + 1 < 12 * (R * q) + 12 * q
  · let p : PeriodicLatticePlaquette (scaleUp 2 1 (dilLu q R)) := (w, ⟨(0, μ), h0μ⟩)
    have hp : p ∈ plaqIn ((dilTower q R).Om 0) := by
      intro e he
      simp only [periodicPlaquetteBoundaryEdges, Finset.mem_insert, Finset.mem_singleton, p] at he
      rcases he with rfl | rfl | rfl | rfl
      · refine ⟨(mem_Om0 _).mpr ⟨?_, ?_⟩, (mem_Om0 _).mpr ⟨?_, ?_⟩⟩ <;> dsimp only <;> omega
      · refine ⟨(mem_Om0 _).mpr ⟨?_, ?_⟩, (mem_Om0 _).mpr ⟨?_, ?_⟩⟩ <;> dsimp only <;> omega
      · refine ⟨(mem_Om0 _).mpr ⟨?_, ?_⟩, (mem_Om0 _).mpr ⟨?_, ?_⟩⟩ <;> dsimp only <;> omega
      · refine ⟨(mem_Om0 _).mpr ⟨?_, ?_⟩, (mem_Om0 _).mpr ⟨?_, ?_⟩⟩ <;> dsimp only <;> omega
    have hc := hcurl p hp
    simp only [curlValueCovariant, p, flatCfg, RMap_one, LinearMap.id_apply] at hc
    have e : A (periodicLatticeShift w μ, 0) - A (w, 0) - (A (periodicLatticeShift w 0, μ) - A (w, μ)) = 0 := by
      rw [← neg_eq_zero, ← hc]; abel
    exact sub_eq_zero.mp e
  · have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
    have hR1 : ∀ x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)),
        ((x 0).val = (w 0).val ∨ (x 0).val = (w 0).val + 1) → x ∉ (dilTower q R).Om 1 := by
      intro x hx hxm
      rw [mem_Om1] at hxm
      rcases hx with hx | hx <;> rw [hx] at hxm <;>
        (by_cases h4 : 4 * q ≤ (w 0).val
         · have h5 : ¬ ((w 0).val + 1 < 12 * (R * q) + 12 * q) := fun h => hin ⟨h4, h⟩
           omega
         · omega)
    have z1 := A_zero_off A hsupp hQ (b := (w, 0)) (hR1 w (Or.inl rfl)) (hR1 _ (Or.inr hw0))
    have z2 := A_zero_off A hsupp hQ (b := (periodicLatticeShift w 0, μ)) (hR1 _ (Or.inr hw0))
      (hR1 _ (Or.inr hw0μ))
    have z3 := A_zero_off A hsupp hQ (b := (periodicLatticeShift w μ, 0))
      (hR1 (periodicLatticeShift w μ) (Or.inl (by rw [hwμ]))) (hR1 _ (Or.inr hwμ0))
    have z4 := A_zero_off A hsupp hQ (b := (w, μ)) (hR1 w (Or.inl rfl))
      (hR1 (periodicLatticeShift w μ) (Or.inl (by rw [hwμ])))
    rw [z1, z2, z3, z4]

include hq hR hsupp hQ in
/-- transverse step. -/
theorem xi_shiftT
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {μ : Fin 3} (hμ : μ ≠ 0) :
    xi A (periodicLatticeShift z μ) = xi A z + (A (z, μ) - A (sitex z 0, μ)) := by
  unfold xi
  rw [shift_coord_ne z (Ne.symm hμ)]
  have hz := x0_lt hq z
  have e : ∀ u ∈ Finset.range (z 0).val, A (sitex (periodicLatticeShift z μ) u, 0)
      = A (sitex z u, 0) + (A (sitex z (u + 1), μ) - A (sitex z u, μ)) := by
    intro u hu
    rw [Finset.mem_range] at hu
    have hval : ((sitex z u) 0).val = u := sitex_val hq z (by omega)
    have ht := trans_step hq hR A hsupp hQ hcurl (sitex z u) hμ (by rw [hval]; omega)
    rw [shift_sitex z u hμ, shift_sitex0] at ht
    rw [← sub_eq_iff_eq_add', ht]
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_range_sub (fun u => A (sitex z u, μ)),
    sitex_self]

include hq hsupp hQ in
theorem xi_left (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)))
    (h : (z 0).val < 2 * (R * q) + 4 * q) : xi A z = 0 := by
  unfold xi
  refine Finset.sum_eq_zero (fun u hu => ?_)
  rw [Finset.mem_range] at hu
  have hz := x0_lt hq z
  have hv : ((sitex z u) 0).val = u := sitex_val hq z (by omega)
  refine A_zero_off A hsupp hQ ?_ ?_
  · rw [mem_Om1, hv]; omega
  · rw [mem_Om1, shift_sitex0, sitex_val hq z (by omega)]; omega

include hq hsupp hQ in
/-- beyond the right edge of `Ω₁` the potential equals its value at the right edge. -/
theorem xi_right (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)))
    (h : 10 * (R * q) + 12 * q ≤ (z 0).val) :
    xi A z = xi A (sitex z (10 * (R * q) + 12 * q)) := by
  have hz := x0_lt hq z
  have key : ∀ n, 10 * (R * q) + 12 * q + n < 12 * (R * q) + 16 * q →
      xi A (sitex z (10 * (R * q) + 12 * q + n)) = xi A (sitex z (10 * (R * q) + 12 * q)) := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      have hv : ((sitex z (10 * (R * q) + 12 * q + n)) 0).val = 10 * (R * q) + 12 * q + n :=
        sitex_val hq z (by omega)
      rw [← ih (by omega)]
      have e := xi_shift0 hq A (sitex z (10 * (R * q) + 12 * q + n)) (by rw [hv]; omega)
      rw [shift_sitex0] at e
      rw [show 10 * (R * q) + 12 * q + (n + 1) = 10 * (R * q) + 12 * q + n + 1 by ring, e]
      have h0 : A (sitex z (10 * (R * q) + 12 * q + n), 0) = 0 := by
        refine A_zero_off A hsupp hQ ?_ ?_
        · show sitex z _ ∉ _
          rw [mem_Om1, hv]; omega
        · show periodicLatticeShift (sitex z _) 0 ∉ _
          rw [mem_Om1, shift_sitex0, sitex_val hq z (by omega)]; omega
      rw [h0, add_zero]
  have hk := key ((z 0).val - (10 * (R * q) + 12 * q)) (by omega)
  rw [Nat.add_sub_cancel' h, sitex_self] at hk
  exact hk

/-- the right-edge value of the potential, a function of the transverse coordinates. -/
noncomputable def Iv (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) : SuTwo :=
  xi A (sitex z (10 * (R * q) + 12 * q))

include hq hR hsupp hQ in
theorem Iv_shiftT
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {μ : Fin 3} (hμ : μ ≠ 0) :
    Iv A (periodicLatticeShift z μ) = Iv A z := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  unfold Iv
  rw [← shift_sitex z _ hμ, xi_shiftT hq hR A hsupp hQ hcurl _ hμ]
  have hv : ((sitex z (10 * (R * q) + 12 * q)) 0).val = 10 * (R * q) + 12 * q :=
    sitex_val hq z (by omega)
  have e1 : A (sitex z (10 * (R * q) + 12 * q), μ) = 0 := by
    refine A_zero_off A hsupp hQ ?_ ?_
    · show sitex z _ ∉ _
      rw [mem_Om1, hv]; omega
    · show periodicLatticeShift (sitex z _) μ ∉ _
      rw [mem_Om1, shift_coord_ne _ (Ne.symm hμ), hv]; omega
  have e2 : A (sitex (sitex z (10 * (R * q) + 12 * q)) 0, μ) = 0 := by
    rw [sitex_sitex]
    have hv0 : ((sitex z 0) 0).val = 0 := sitex_val hq z (by omega)
    refine A_zero_off A hsupp hQ ?_ ?_
    · show sitex z 0 ∉ _
      rw [mem_Om1, hv0]; omega
    · show periodicLatticeShift (sitex z 0) μ ∉ _
      rw [mem_Om1, shift_coord_ne _ (Ne.symm hμ), hv0]; omega
  rw [e1, e2, sub_zero, add_zero]

omit hq hR A in
theorem update_shift_succ {L : PeriodicLatticeExtent} (w : PeriodicLatticeSite L) (μ : Fin 3) (n : ℕ) :
    Function.update w μ (w μ + ((n + 1 : ℕ) : Fin (L μ + 1))) =
      periodicLatticeShift (Function.update w μ (w μ + ((n : ℕ) : Fin (L μ + 1)))) μ := by
  unfold periodicLatticeShift
  rw [Function.update_idem, Function.update_self, Nat.cast_succ, add_assoc]

include hq hR hsupp hQ in
theorem Iv_update
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {μ : Fin 3} (hμ : μ ≠ 0)
    (v : Fin (scaleUp 2 1 (dilLu q R) μ + 1)) :
    Iv A (Function.update z μ v) = Iv A z := by
  have hn : ∀ n : ℕ, Iv A (Function.update z μ (z μ + ((n : ℕ) : Fin _))) = Iv A z := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [update_shift_succ, Iv_shiftT hq hR A hsupp hQ hcurl _ hμ, ih]
  have h := hn (v - z μ).val
  rw [Fin.cast_val_eq_self, add_sub_cancel] at h
  exact h

omit hq hR A in
theorem Iv_update0 (A : BondFnL2 (scaleUp 2 1 (dilLu q R))) (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)))
    (v : Fin (scaleUp 2 1 (dilLu q R) 0 + 1)) : Iv A (Function.update z 0 v) = Iv A z := by
  unfold Iv sitex
  rw [Function.update_idem]

include hq hR hsupp hQ in
theorem Iv_const
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) : Iv A z = Iv A (fun _ => 0) := by
  have e : (fun _ => (0 : Fin _) : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) =
      Function.update (Function.update (Function.update z 0 0) 1 0) 2 0 := by
    funext ν
    fin_cases ν <;> simp [Function.update] <;> rfl
  rw [e, Iv_update hq hR A hsupp hQ hcurl _ (by decide), Iv_update hq hR A hsupp hQ hcurl _ (by decide),
    Iv_update0]

omit hq hR A in
theorem coarseShift_sitex (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (t : ℕ) :
    coarseShift (sitex z t) 2 0 = sitex z (t + 2) := by
  show periodicLatticeShift (periodicLatticeShift (sitex z t) 0) 0 = _
  rw [shift_sitex0, shift_sitex0]

include hq hR hQ in
/-- one level-1 row along direction `0`: the block sums of the potential agree. -/
theorem row_step (y : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)))
    (hy1 : 2 ∣ (y 1).val) (hy2 : 2 ∣ (y 2).val) (hy0 : 2 ∣ (y 0).val)
    (hlo : 2 * (R * q) + 4 * q ≤ (y 0).val + 2) (hhi : (y 0).val + 2 ≤ 10 * (R * q) + 12 * q) :
    ∑ w ∈ stepBlockOf (coarseShift y 2 0) 1 2, xi A w = ∑ w ∈ stepBlockOf y 1 2, xi A w := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  have hN := dsize0 (R := R) hq
  have hy0' : ((periodicLatticeShift y 0) 0).val = (y 0).val + 1 := shift0_val_lt y (by omega)
  have hcs0 : ((coarseShift y 2 0) 0).val = (y 0).val + 2 := by
    show ((periodicLatticeShift (periodicLatticeShift y 0) 0) 0).val = _
    rw [shift0_val_lt _ (by rw [hy0']; omega), hy0']
  have hcsT : ∀ ν : Fin 3, ν ≠ 0 → (coarseShift y 2 0) ν = y ν := by
    intro ν hν
    show (periodicLatticeShift (periodicLatticeShift y 0) 0) ν = y ν
    rw [shift_coord_ne _ hν, shift_coord_ne _ hν]
  have hc : (y, (0 : Fin 3)) ∈ bondsLam (geomOf 2 1 (dilTower q R)) 1 := by
    refine ⟨?_, ?_⟩
    · by_cases hya : 2 * (R * q) + 4 * q ≤ (y 0).val
      · left
        show y ∈ (geomOf 2 1 (dilTower q R)).Lam 1
        refine ⟨fun μ => ?_, (mem_Om1 _).mpr ⟨hya, by omega⟩, not_mem_Om2 _⟩
        show 2 ^ 1 ∣ (y μ).val
        fin_cases μ
        · simpa using hy0
        · simpa using hy1
        · simpa using hy2
      · right
        have e1 : coarseShift (y, (0 : Fin 3)).1 ((geomOf 2 1 (dilTower q R)).ell ^ 1) (y, (0 : Fin 3)).2 =
            coarseShift y 2 0 := rfl
        rw [e1]
        show coarseShift y 2 0 ∈ (geomOf 2 1 (dilTower q R)).Lam 1
        refine ⟨fun μ => ?_, (mem_Om1 _).mpr ⟨by rw [hcs0]; omega, by rw [hcs0]; omega⟩, not_mem_Om2 _⟩
        show 2 ^ 1 ∣ ((coarseShift y 2 0) μ).val
        fin_cases μ
        · show 2 ^ 1 ∣ ((coarseShift y 2 0) 0).val
          rw [hcs0]; simpa using (Nat.dvd_add hy0 (dvd_refl 2))
        · show 2 ^ 1 ∣ ((coarseShift y 2 0) 1).val
          rw [hcsT 1 (by decide)]; simpa using hy1
        · show 2 ^ 1 ∣ ((coarseShift y 2 0) 2).val
          rw [hcsT 2 (by decide)]; simpa using hy2
    · rintro (h | h) <;>
        exact not_OmGe_of_lt (G := geomOf 2 1 (dilTower q R)) (lt_of_eq_of_lt (dil_G_k q R) (by norm_num)) _ h
  let p : BIdx (geomOf 2 1 (dilTower q R)) := ⟨1, ⟨(y, 0), hc⟩⟩
  have hrow : WithLp.ofLp (QfullOf (geomOf 2 1 (dilTower q R)) flatCfg A) p = 0 := by
    rw [hQ]; rfl
  have hQrow := AdalyFormal.W6.Qflat_row (ell := 2) (k := 1) (Lu := dilLu q R) (S := dilTower q R)
    (by norm_num) A p
  have hline : AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictSuTwo (2 ^ (p.1 : ℕ))
      (WithLp.ofLp A) (AdalyFormal.W6.rowCB (by norm_num) p) = 0 := by
    rw [← hQrow]; exact hrow
  have hline' : (1 / ((2 : ℕ) : ℝ) ^ 4) • ∑ x ∈ blockOf y 2, ∑ i ∈ Finset.range 2,
      A (pathSite x 0 i, 0) = 0 := hline
  have hsum : ∑ x ∈ blockOf y 2, ∑ i ∈ Finset.range 2, A (pathSite x 0 i, 0) = 0 := by
    rcases smul_eq_zero.mp hline' with h | h
    · norm_num at h
    · exact h
  have hpt : ∀ x ∈ blockOf y 2, ∑ i ∈ Finset.range 2, A (pathSite x 0 i, 0) =
      xi A (coarseShift x 2 0) - xi A x := by
    intro x hx
    have hxb := (mem_blockOf.mp hx) 0
    have hx0 : (x 0).val + 1 < 12 * (R * q) + 16 * q := by omega
    have hsx : ((periodicLatticeShift x 0) 0).val = (x 0).val + 1 := shift0_val_lt x (by omega)
    have e1 := xi_shift0 hq A x hx0
    have e2 := xi_shift0 hq A (periodicLatticeShift x 0) (by rw [hsx]; omega)
    show _ = xi A (periodicLatticeShift (periodicLatticeShift x 0) 0) - xi A x
    rw [e2, e1, Finset.sum_range_succ, Finset.sum_range_one]
    show A (x, 0) + A (periodicLatticeShift x 0, 0) = _
    abel
  have hfit : ∀ ν : Fin 3, (y ν).val + 1 * 2 ≤ scaleUp 2 1 (dilLu q R) ν + 1 := by
    intro ν
    by_cases hν : ν = 0
    · subst hν; omega
    · have := xT_lt hq y hν
      have h8 := dsizeT (R := R) hq hν
      have hev : 2 ∣ (y ν).val := by
        fin_cases ν
        · exact absurd rfl hν
        · exact hy1
        · exact hy2
      omega
  have hfit' : ∀ ν : Fin 3, ((coarseShift y 2 0) ν).val + 1 * 2 ≤ scaleUp 2 1 (dilLu q R) ν + 1 := by
    intro ν
    by_cases hν : ν = 0
    · subst hν; rw [hcs0]; omega
    · rw [hcsT ν hν]; exact hfit ν
  have hshift := AdalyFormal.CurvBlock.block_sum_shift 1 2 2 0 hfit hfit' (xi A)
  rw [← hshift]
  rw [AdalyFormal.Balaban.QjComposite.stepBlockOf_one] at *
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib] at hsum
  exact sub_eq_zero.mp hsum

include hq hR hsupp hQ in
/-- the block sums vanish along the whole longitudinal chain of blocks. -/
theorem chain_zero (y : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (hy1 : 2 ∣ (y 1).val) (hy2 : 2 ∣ (y 2).val) :
    ∀ m : ℕ, 2 * m ≤ 8 * (R * q) + 8 * q + 2 →
      ∑ w ∈ stepBlockOf (sitex y (2 * (R * q) + 4 * q - 2 + 2 * m)) 1 2, xi A w = 0 := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  have hN := dsize0 (R := R) hq
  intro m
  induction m with
  | zero =>
    intro _
    refine Finset.sum_eq_zero (fun w hw => ?_)
    have hb := ((AdalyFormal.Balaban.QjComposite.mem_stepBlockOf).mp hw) 0
    have hv : ((sitex y (2 * (R * q) + 4 * q - 2 + 2 * 0)) 0).val = 2 * (R * q) + 4 * q - 2 + 2 * 0 :=
      sitex_val hq y (by omega)
    rw [hv] at hb
    exact xi_left hq A hsupp hQ w (by omega)
  | succ m ih =>
    intro hm
    have hv : ((sitex y (2 * (R * q) + 4 * q - 2 + 2 * m)) 0).val = 2 * (R * q) + 4 * q - 2 + 2 * m :=
      sitex_val hq y (by omega)
    have e : sitex y (2 * (R * q) + 4 * q - 2 + 2 * (m + 1)) =
        coarseShift (sitex y (2 * (R * q) + 4 * q - 2 + 2 * m)) 2 0 := by
      rw [coarseShift_sitex]
      congr 1
    rw [e, row_step hq hR A hQ _ (by rw [sitex_coord _ _ (by decide)]; exact hy1)
      (by rw [sitex_coord _ _ (by decide)]; exact hy2) (by rw [hv]; omega) (by rw [hv]; omega)
      (by rw [hv]; omega)]
    exact ih (by omega)

include hq hR hsupp hQ in
theorem Iv_zero
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0) :
    Iv A (fun _ => 0) = 0 := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  have hN := dsize0 (R := R) hq
  let y0 : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) := fun _ => 0
  have hb := chain_zero hq hR A hsupp hQ y0 (by simp [y0]) (by simp [y0])
    (4 * (R * q) + 4 * q + 1) (by omega)
  have hv : ((sitex y0 (2 * (R * q) + 4 * q - 2 + 2 * (4 * (R * q) + 4 * q + 1))) 0).val =
      10 * (R * q) + 12 * q := by
    rw [sitex_val hq y0 (by omega)]; omega
  have e : ∀ w ∈ stepBlockOf (sitex y0 (2 * (R * q) + 4 * q - 2 + 2 * (4 * (R * q) + 4 * q + 1))) 1 2,
      xi A w = Iv A (fun _ => 0) := by
    intro w hw
    have hwb := ((AdalyFormal.Balaban.QjComposite.mem_stepBlockOf).mp hw) 0
    rw [hv] at hwb
    rw [xi_right hq A hsupp hQ w (by omega)]
    exact Iv_const hq hR A hsupp hQ hcurl w
  have hfit : ∀ ν : Fin 3, ((sitex y0 (2 * (R * q) + 4 * q - 2 + 2 * (4 * (R * q) + 4 * q + 1))) ν).val
      + 1 * 2 ≤ scaleUp 2 1 (dilLu q R) ν + 1 := by
    intro ν
    by_cases hν : ν = 0
    · subst hν; rw [hv]; omega
    · rw [sitex_coord _ _ hν]
      have h8 := dsizeT (R := R) hq hν
      show ((0 : Fin _) : ℕ) + 1 * 2 ≤ _
      simp only [Fin.val_zero]
      omega
  rw [Finset.sum_congr rfl e, Finset.sum_const,
    AdalyFormal.Balaban.QjComposite.card_stepBlockOf _ 1 2 one_pos hfit] at hb
  have h8 : (8 : ℝ) • Iv A (fun _ => 0) = 0 := by
    rw [show (8 : ℝ) = ((2 ^ 3 : ℕ) : ℝ) by norm_num, Nat.cast_smul_eq_nsmul]
    exact hb
  rcases smul_eq_zero.mp h8 with h | h
  · norm_num at h
  · exact h

include hq hR hsupp hQ in
theorem xi_mem_NQp
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0) :
    (WithLp.toLp 2 (xi A) : SiteL2 (scaleUp 2 1 (dilLu q R))) ∈
      NQp (geomOf 2 1 (dilTower q R)) flatCfg := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  have hN := dsize0 (R := R) hq
  have hzero : ∀ x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)),
      ¬ ((dilTower q R).Om 1 x) → xi A x = 0 := by
    intro x hx
    have hx' : ¬ (2 * (R * q) + 4 * q ≤ (x 0).val ∧ (x 0).val < 10 * (R * q) + 12 * q) := hx
    by_cases h : (x 0).val < 2 * (R * q) + 4 * q
    · exact xi_left hq A hsupp hQ x h
    · rw [xi_right hq A hsupp hQ x (by omega)]
      show Iv A x = 0
      rw [Iv_const hq hR A hsupp hQ hcurl x, Iv_zero hq hR A hsupp hQ hcurl]
  refine ⟨fun x hx => ?_, fun j hj y hy => ?_⟩
  · show xi A x = 0
    refine hzero x (fun h1 => hx ?_)
    have h1' : 2 * (R * q) + 4 * q ≤ (x 0).val ∧ (x 0).val < 10 * (R * q) + 12 * q := h1
    show 4 * q ≤ (x 0).val ∧ (x 0).val < 12 * (R * q) + 12 * q
    omega
  · have hj1 : j = 0 ∨ j = 1 := by
      have : j ≤ 1 := hj
      omega
    rcases hj1 with rfl | rfl
    · rw [Qlev_apply, AdalyFormal.Balaban.QjComposite.Qcomposite_zero]
      show xi A y = 0
      exact hzero y hy.2.2
    · rw [Qlev_apply, Qcomposite_one', bgTower_zero']
      show stepAverage (2 ^ 0) (trivialU _) 2 (xi A) y = 0
      rw [AdalyFormal.Balaban.QjComposite.stepAverage_trivialU, pow_zero]
      obtain ⟨hdiv, hy1, -⟩ := hy
      have hy1' : 2 * (R * q) + 4 * q ≤ (y 0).val ∧ (y 0).val < 10 * (R * q) + 12 * q := hy1
      have hd0 : 2 ∣ (y 0).val := by simpa using hdiv 0
      have hd1 : 2 ∣ (y 1).val := by simpa using hdiv 1
      have hd2 : 2 ∣ (y 2).val := by simpa using hdiv 2
      obtain ⟨m, hm⟩ : ∃ m, (y 0).val = 2 * (R * q) + 4 * q - 2 + 2 * m := by
        obtain ⟨t, ht⟩ := hd0
        refine ⟨t - (R * q) - 2 * q + 1, ?_⟩
        omega
      have hc := chain_zero hq hR A hsupp hQ y hd1 hd2 m (by omega)
      rw [← hm, sitex_self] at hc
      rw [hc, smul_zero]

include hq hR hsupp hQ in
theorem A_eq_grad
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0) :
    A = gradL2 flatCfg (WithLp.toLp 2 (xi A)) := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  have hN := dsize0 (R := R) hq
  refine PiLp.ext (fun e => ?_)
  obtain ⟨z, μ⟩ := e
  show A (z, μ) = gradValueCovariant flatCfg (xi A) (z, μ)
  simp only [gradValueCovariant, flatCfg, RMap_one, LinearMap.id_apply]
  have hz := x0_lt hq z
  by_cases hμ : μ = 0
  · subst hμ
    by_cases hz1 : (z 0).val + 1 < 12 * (R * q) + 16 * q
    · rw [xi_shift0 hq A z hz1]; abel
    · have hzl : (z 0).val + 1 = scaleUp 2 1 (dilLu q R) 0 + 1 := by omega
      have h0 : ((periodicLatticeShift z 0) 0).val = 0 := shift0_val_last z hzl
      have e1 : xi A (periodicLatticeShift z 0) = 0 := xi_left hq A hsupp hQ _ (by rw [h0]; omega)
      have e2 : xi A z = 0 := by
        rw [xi_right hq A hsupp hQ z (by omega)]
        show Iv A z = 0
        rw [Iv_const hq hR A hsupp hQ hcurl z, Iv_zero hq hR A hsupp hQ hcurl]
      have e3 : A (z, 0) = 0 := by
        refine A_zero_off A hsupp hQ ?_ ?_
        · show z ∉ _
          rw [mem_Om1]; omega
        · show periodicLatticeShift z 0 ∉ _
          rw [mem_Om1, h0]; omega
      rw [e1, e2, e3, sub_zero]
  · rw [xi_shiftT hq hR A hsupp hQ hcurl z hμ]
    have hv0 : ((sitex z 0) 0).val = 0 := sitex_val hq z (by omega)
    have e3 : A (sitex z 0, μ) = 0 := by
      refine A_zero_off A hsupp hQ ?_ ?_
      · show sitex z 0 ∉ _
        rw [mem_Om1, hv0]; omega
      · show periodicLatticeShift (sitex z 0) μ ∉ _
        rw [mem_Om1, shift_coord_ne _ (Ne.symm hμ), hv0]; omega
    rw [e3]; abel

include hq hR hsupp hQ in
/-- **The flat kernel of the dilated tower is trivial.** -/
theorem dil_flat_kernel
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (hT : Tfull (geomOf 2 1 (dilTower q R)) flatCfg A = 0) : A = 0 := by
  have hg := A_eq_grad hq hR A hsupp hQ hcurl
  have hmem := xi_mem_NQp hq hR A hsupp hQ hcurl
  rw [hg] at hT ⊢
  exact final_step' _ _ hmem hT

end Kernel

end FlatKernel

end AdalyFormal.Round9.Guarded.AnalyticR2


namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

/-! ## K. Assembly: the soft premise `InteriorSoft` of round 1 holds -/
section FlatCarrier

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dilU)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2 curlCovariantCLM_L2_toLp)
open AdalyFormal.StatementLaneR6 (plaqMask plaqMask_apply)

/-- The flat localized carrier form is a sum of three squares (frozen `NsPtD1.flat_ginv_form`,
outside the `DrEquiv` closure, restated for the pinned localized assembly). -/
theorem flat_ginv_form_in (P : IngrBParams) (hU : P.U = flatCfg) (x : ↥(bondSupp P.G)) :
    ⟪x, (dataS selIn selIn P).Ginv x⟫ =
      ‖plaqMask (plaqIn P.G.Om0) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x))‖ ^ 2
      + ‖Tfull P.G P.U (iE P.G x)‖ ^ 2
      + ∑ p : BIdx P.G, P.a * (P.ell : ℝ) ^ (p.1 : ℕ) * ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 := by
  rw [BaseDataS.inner_Ginv]
  have hD : ⟪x, (dataS selIn selIn P).Dpi x⟫ =
      ‖plaqMask (plaqIn P.G.Om0) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x))‖ ^ 2 := by
    have : ⟪x, (dataS selIn selIn P).Dpi x⟫ = ⟪iE P.G x, DpiFull P.G P.U P.a (iE P.G x)⟫ := by
      show ⟪x, (pE P.G) (DpiFull P.G P.U P.a (iE P.G x))⟫ = _
      rw [pE_inner_right]
    rw [this, hU]
    exact AdalyFormal.StatementLaneG.inner_DpiFull_flat P.G P.a (iE P.G x)
  have hM : ⟪x, (dataS selIn selIn P).Mass x⟫ =
      ∑ p : BIdx P.G, P.a * (P.ell : ℝ) ^ (p.1 : ℕ) * ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 := by
    have : ⟪x, (dataS selIn selIn P).Mass x⟫ = ⟪iE P.G x, MassFull P.G P.a P.sector (iE P.G x)⟫ := by
      show ⟪x, (pE P.G) (MassFull P.G P.a P.sector (iE P.G x))⟫ = _
      rw [pE_inner_right]
    rw [this, inner_MassFull]
    rfl
  rw [hD, hM]
  rfl

/-- The flat localized carrier of the dilated tower is positive definite. -/
theorem dil_flat_pos {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R)
    (x : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) (hx : x ≠ 0) :
    0 < ⟪x, (dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (fun _ => 1) 1 (dilLam q R))).Ginv x⟫ := by
  set P := gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (fun _ => 1) 1 (dilLam q R) with hP
  have hform := flat_ginv_form_in P rfl x
  have t1 := sq_nonneg ‖plaqMask (plaqIn P.G.Om0) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x))‖
  have t2 := sq_nonneg ‖Tfull P.G P.U (iE P.G x)‖
  have hell : (0 : ℝ) < P.ell := by show (0 : ℝ) < (2 : ℕ); norm_num
  have t3 : 0 ≤ ∑ p : BIdx P.G, P.a * (P.ell : ℝ) ^ (p.1 : ℕ) * ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 :=
    Finset.sum_nonneg (fun p _ => by
      have : (0 : ℝ) < P.a := by show (0 : ℝ) < 1; norm_num
      positivity)
  rcases (add_nonneg (add_nonneg t1 t2) t3).lt_or_eq with h | h
  · rw [hform]; exact h
  · exfalso
    apply hx
    have h1 : ‖plaqMask (plaqIn P.G.Om0) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x))‖ ^ 2 = 0 := by
      linarith
    have h2 : ‖Tfull P.G P.U (iE P.G x)‖ ^ 2 = 0 := by linarith
    have h3 : ∑ p : BIdx P.G, P.a * (P.ell : ℝ) ^ (p.1 : ℕ) * ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 = 0 := by
      linarith
    have hm : plaqMask (plaqIn P.G.Om0) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x)) = 0 :=
      norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h1)
    have hT : Tfull P.G P.U (iE P.G x) = 0 := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
    have hQ : QfullOf (geomOf 2 1 (dilTower q R)) flatCfg (iE P.G x) = 0 := by
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => by
        have : (0 : ℝ) < P.a := by show (0 : ℝ) < 1; norm_num
        positivity)).mp h3
      refine PiLp.ext (fun p => ?_)
      have h1 := hz p (Finset.mem_univ p)
      have hp : 0 < P.a * (P.ell : ℝ) ^ (p.1 : ℕ) := by
        have : (0 : ℝ) < P.a := by show (0 : ℝ) < 1; norm_num
        positivity
      have h2 : ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 = 0 := by
        rcases mul_eq_zero.mp h1 with h | h
        · exact absurd h hp.ne'
        · exact h
      have := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
      exact this
    have hsupp : ∀ b, b ∉ bondsOm0 (geomOf 2 1 (dilTower q R)) → (iE P.G x) b = 0 :=
      fun b hb => x.2 b hb
    have hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0),
        curlValueCovariant flatCfg (WithLp.ofLp (iE P.G x)) p = 0 := by
      intro p hp
      have h := congrArg (fun v : AdalyFormal.Balaban.CovariantHjMinimizer.PlaqFnL2 P.Lf => WithLp.ofLp v p) hm
      simp only [plaqMask_apply, PiLp.zero_apply] at h
      rw [if_pos (show p ∈ plaqIn P.G.Om0 from hp)] at h
      have e : curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x) =
          WithLp.toLp 2 (curlValueCovariant flatCfg (WithLp.ofLp (iE P.G x))) :=
        curlCovariantCLM_L2_toLp _ _
      rw [e] at h
      exact h
    have hA := dil_flat_kernel hq hR (iE P.G x) hsupp hQ hcurl hT
    exact Subtype.ext hA

theorem dil_flat_unit {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R) :
    IsUnit (dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (fun _ => 1) 1 (dilLam q R))).Ginv := by
  set M : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
    (dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (fun _ => 1) 1 (dilLam q R))).Ginv with hMdef
  have hinj : Function.Injective M := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hne
    have := dil_flat_pos hq hR x hne
    rw [hx, inner_zero_right] at this
    exact lt_irrefl _ this
  exact (ContinuousLinearMap.isUnit_iff_bijective).mpr
    ⟨hinj, (LinearMap.injective_iff_surjective (f := (M : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →ₗ[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))))).mp hinj⟩

end FlatCarrier

end AdalyFormal.Round9.Guarded.AnalyticR2

namespace AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Target.ClayStatement
open AdalyFormal.D1Literal (SU2m)
variable {L : PeriodicLatticeExtent}

def AnM (f : ℝ → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∀ (θ₀ : ℝ) (i j : Fin 2), AnalyticAt ℝ (fun θ => f θ i j) θ₀

def AnFam (U : ℝ → PeriodicLinkConfiguration SU2m L) : Prop :=
  ∀ e : PeriodicLatticeEdge L, AnM fun θ => ((U θ e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)

theorem analyticAt_exp_I (s : ℝ) (θ₀ : ℝ) :
    AnalyticAt ℝ (fun θ : ℝ => Complex.exp (s * θ * Complex.I)) θ₀ := by
  have hlin : AnalyticAt ℝ (fun θ : ℝ => (s : ℂ) * (θ : ℂ) * Complex.I) θ₀ := by
    have h1 : AnalyticAt ℝ (fun θ : ℝ => ((θ : ℂ))) θ₀ :=
      (Complex.ofRealCLM.analyticAt θ₀).congr (Filter.Eventually.of_forall (fun θ => rfl))
    exact (analyticAt_const.fun_mul h1).fun_mul analyticAt_const
  have hexp : AnalyticAt ℝ Complex.exp ((fun θ : ℝ => (s : ℂ) * (θ : ℂ) * Complex.I) θ₀) :=
    (analyticAt_cexp (z := (s : ℂ) * (θ₀ : ℂ) * Complex.I)).restrictScalars
  exact AnalyticAt.comp (f := fun θ : ℝ => (s : ℂ) * (θ : ℂ) * Complex.I) hexp hlin

theorem anM_uMat : AnM fun θ => AdalyFormal.D1Literal.uMat θ := by
  intro θ₀ i j
  fin_cases i <;> fin_cases j
  · refine (analyticAt_exp_I 1 θ₀).congr (Filter.Eventually.of_forall (fun θ => ?_))
    simp [AdalyFormal.D1Literal.uMat]
  · simp only [AdalyFormal.D1Literal.uMat]
    simp
    exact analyticAt_const
  · simp only [AdalyFormal.D1Literal.uMat]
    simp
    exact analyticAt_const
  · refine (analyticAt_exp_I (-1) θ₀).congr (Filter.Eventually.of_forall (fun θ => ?_))
    simp [AdalyFormal.D1Literal.uMat]

#print axioms AnM
#print axioms AnFam
#print axioms analyticAt_exp_I
#print axioms anM_uMat
end AdalyFormal.Round9.Guarded.QualitativeR2

namespace AdalyFormal.Round12.Noncancel.Path
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.CovariantHjMinimizer
  (periodicLatticeShiftBack periodicLatticeShift_shiftBack)
open AdalyFormal.D1Literal
open AdalyFormal.Round9.Guarded.QualitativeR2 (AnM AnFam anM_uMat)
variable {L : PeriodicLatticeExtent}

/-- The four transverse links incident to one site (when transverse side lengths exceed two). -/
def starLinks (x : PeriodicLatticeSite L) : Set (Bond L) :=
  {e | e.2 ≠ 0 ∧ (e.1 = x ∨ periodicLatticeShift e.1 e.2 = x)}

open Classical in
/-- Equal-sign exterior star; unlike the translation-invariant twist, the support is local. -/
def starPath (x : PeriodicLatticeSite L) (t : ℝ) : Cfg L :=
  fun e => if e ∈ starLinks x then uθ t else 1

theorem starPath_zero (x : PeriodicLatticeSite L) : starPath x 0 = fun _ => 1 := by
  funext e
  simp [starPath, uθ_zero]

theorem starPath_cont (x : PeriodicLatticeSite L) : ContFam (starPath x) := by
  intro e
  by_cases h : e ∈ starLinks x
  · simp only [starPath, h, if_true]
    change Continuous fun t => uMat t
    unfold uMat
    refine continuous_matrix (fun i j => ?_)
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · simp only [starPath, h, if_false]
    exact continuous_const

theorem starPath_an (x : PeriodicLatticeSite L) : AnFam (starPath x) := by
  intro e
  by_cases h : e ∈ starLinks x
  · simp only [starPath, h, if_true]
    show AnM fun t => uMat t
    exact anM_uMat
  · intro t i j
    simp only [starPath, h, if_false]
    exact analyticAt_const

theorem starLinks_exterior (Om : Set (PeriodicLatticeSite L))
    (x : PeriodicLatticeSite L) (hx : x ∉ Om)
    (htrans : ∀ z (ν : Fin 3), ν ≠ 0 → (periodicLatticeShift z ν ∈ Om ↔ z ∈ Om)) :
    starLinks x ⊆ Zb Om := by
  rintro ⟨z,ν⟩ ⟨hν,hz | hz⟩
  · change z = x at hz
    subst z
    exact ⟨hx, fun h => hx ((htrans x ν hν).mp h)⟩
  · exact ⟨fun h => hx (hz ▸ (htrans z ν hν).mpr h), fun h => hx (hz ▸ h)⟩

theorem starPath_off_exterior (Om : Set (PeriodicLatticeSite L))
    (x : PeriodicLatticeSite L) (hx : x ∉ Om)
    (htrans : ∀ z (ν : Fin 3), ν ≠ 0 → (periodicLatticeShift z ν ∈ Om ↔ z ∈ Om))
    (t : ℝ) (e : Bond L) (he : e ∉ Zb Om) : starPath x t e = 1 := by
  have hh : e ∉ starLinks x := fun h => he (starLinks_exterior Om x hx htrans h)
  simp [starPath, hh]

theorem starPath_interior (Om : Set (PeriodicLatticeSite L))
    (x : PeriodicLatticeSite L) (hx : x ∉ Om)
    (htrans : ∀ z (ν : Fin 3), ν ≠ 0 → (periodicLatticeShift z ν ∈ Om ↔ z ∈ Om))
    (t : ℝ) (e : Bond L) (he : e.1 ∈ Om) : starPath x t e = 1 := by
  have hh : e ∉ starLinks x := fun h => (starLinks_exterior Om x hx htrans h).1 he
  simp [starPath, hh]

theorem starPath_normal (x z : PeriodicLatticeSite L) (t : ℝ) :
    starPath x t (z,0) = 1 := by simp [starPath, starLinks]

/-- Use the exterior site immediately to the right of a frozen boundary point. -/
theorem star_holonomy1 {Om : Set (PeriodicLatticeSite L)} {x : PeriodicLatticeSite L}
    (hbd : BdPt Om x) (t : ℝ) (ν : {ν : Fin 3 // 0 < ν}) :
    holonomyElem (starPath (periodicLatticeShift x 0) t) (P1 x ν) = uθ t := by
  have hν : ν.1 ≠ 0 := ne_of_gt ν.2
  have h1 := starPath_normal (periodicLatticeShift x 0) x t
  have h2 : starPath (periodicLatticeShift x 0) t (periodicLatticeShift x 0,ν.1) = uθ t := by
    simp [starPath, starLinks, hν]
  have h3 := starPath_normal (periodicLatticeShift x 0) (periodicLatticeShift x ν.1) t
  have h4 := starPath_interior Om (periodicLatticeShift x 0) hbd.hx' hbd.trans t (x,ν.1) hbd.hx
  change periodicPlaquetteHolonomy _ _ = _
  unfold periodicPlaquetteHolonomy P1
  simp only
  rw [h1,h2,h3,h4]
  simp

theorem star_holonomy2 {Om : Set (PeriodicLatticeSite L)} {x : PeriodicLatticeSite L}
    (hbd : BdPt Om x) (t : ℝ) (ν : {ν : Fin 3 // 0 < ν}) :
    holonomyElem (starPath (periodicLatticeShift x 0) t) (P2 x ν) = uθ t := by
  have hν : ν.1 ≠ 0 := ne_of_gt ν.2
  have h1 := starPath_normal (periodicLatticeShift x 0) (periodicLatticeShiftBack x ν.1) t
  have h2 : starPath (periodicLatticeShift x 0) t
      (periodicLatticeShift (periodicLatticeShiftBack x ν.1) 0,ν.1) = uθ t := by
    have hs : periodicLatticeShift (periodicLatticeShift (periodicLatticeShiftBack x ν.1) 0) ν.1 =
        periodicLatticeShift x 0 := by
      rw [AdalyFormal.StatementLaneR8.shift_comm _ (Ne.symm hν), periodicLatticeShift_shiftBack]
    simp [starPath, starLinks, hν, hs]
  have h3 := starPath_normal (periodicLatticeShift x 0) x t
  have h4 := starPath_interior Om (periodicLatticeShift x 0) hbd.hx' hbd.trans t
    (periodicLatticeShiftBack x ν.1,ν.1) (hbd.shiftBack_mem ν)
  change periodicPlaquetteHolonomy _ _ = _
  unfold periodicPlaquetteHolonomy P2
  simp only
  rw [h1,h2,periodicLatticeShift_shiftBack,h3,h4]
  simp

/-- A genuine negative endpoint on the frozen all-plaquette carrier, for the local star.
This does not locate the first crossing below pi/2 or prove jet detection. -/
theorem star_negative_endpoint {ell M R k : ℕ} {Lu : PeriodicLatticeExtent}
    (hell0 : 0 < ell) (S : Tower (scaleUp ell k Lu))
    (Lam : Set (PeriodicLatticeSite Lu)) (a : ℝ)
    (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17*ell ≤ R*M)
    {x : PeriodicLatticeSite (scaleUp ell k Lu)} (hbd : BdPt (S.Om 0) x)
    (ha : 0 ≤ a) (ha4 : a < 4) (X : SuTwo) (hX : X ≠ 0) :
    ∃ v : ↥(bondSupp (geomOf ell k S)),
      ⟪v, (dataS selAll selAll (gparams ell k Lu hell0 S
        (starPath (periodicLatticeShift x 0) Real.pi) a Lam)).Ginv v⟫ < 0 := by
  let U := starPath (periodicLatticeShift x 0) Real.pi
  let P := gparams ell k Lu hell0 S U a Lam
  have hm := sing_mem_bondSupp (geomOf ell k S) hbd.hx X
  let v : ↥(bondSupp (geomOf ell k S)) := ⟨sing (x,0) X,hm⟩
  have hn : 0 < hsInner X X := by
    exact lt_of_le_of_ne (real_inner_self_nonneg (x := X))
      (fun h => hX (AdalyFormal.Balaban.SuTwoInner.hsInner_self_eq_zero h.symm))
  have hd : ⟪v, (dataS selAll selAll P).Dpi v⟫ = -4*hsInner X X := by
    have e := E0_Dpi_inner selAll (geomOf ell k S) U a v
    refine e.trans ?_
    have hw : Wop (geomOf ell k S) U a (iE (geomOf ell k S) v) = sing (x,0) X :=
      Wop_sing hS (by omega) hbd U a X
    rw [hw]
    apply delta_value U x X hbd.side
    · intro ν
      change ((holonomyElem (starPath _ Real.pi) (P1 x ν) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = -1
      rw [star_holonomy1 hbd, uθ_pi_coe]
    · intro ν
      change ((holonomyElem (starPath _ Real.pi) (P2 x ν) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = -1
      rw [star_holonomy2 hbd, uθ_pi_coe]
    · intro ν
      exact starPath_interior (S.Om 0) _ hbd.hx' hbd.trans _ _ (hbd.shiftBack_mem ν)
  have ht : (dataS selAll selAll P).T v = 0 :=
    Tfull_sing_zero hS (by omega) hbd U X
  have hmass : ⟪v, (dataS selAll selAll P).Mass v⟫ ≤ a*hsInner X X := by
    change ⟪v, ((pE (geomOf ell k S)).comp ((MassFull (geomOf ell k S) a
      (bondSectorOf (geomOf ell k S) U)).comp (iE (geomOf ell k S)))) v⟫ ≤ _
    simp only [ContinuousLinearMap.comp_apply]
    rw [pE_inner_right]
    exact Mass_sing_le hS hell (by omega) hbd U a ha X
  refine ⟨v,?_⟩
  change ⟪v, (dataS selAll selAll P).Ginv v⟫ < 0
  rw [BaseDataS.inner_Ginv,hd,ht]
  simp only [norm_zero]
  nlinarith

#print axioms starLinks
#print axioms starPath
#print axioms starPath_zero
#print axioms starPath_cont
#print axioms starPath_an
#print axioms starLinks_exterior
#print axioms starPath_off_exterior
#print axioms starPath_interior
#print axioms starPath_normal
#print axioms star_holonomy1
#print axioms star_holonomy2
#print axioms star_negative_endpoint
end AdalyFormal.Round12.Noncancel.Path

namespace AdalyFormal.Round4.Guarded.RefuteR1
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round3.Guarded.RefuteR2 (zero_coord_le_pdist)
open AdalyFormal.NonVac (iv_block pcd_clamp pcd_near pcd_self')
theorem dil_shift_zero {q : ℕ} (hq : 0 < q) (R : ℕ)
    (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (μ : Fin 3) :
    ((periodicLatticeShift x μ) 0).val =
      if μ = 0 then ((x 0).val+1) % (12*(R*q)+16*q) else (x 0).val := by
  by_cases h : μ = 0
  · subst μ
    simp only [periodicLatticeShift, Function.update_self, Fin.val_add, Fin.val_one',
      dil_fine_size hq, ↓reduceIte]
    rw [Nat.mod_eq_of_lt (by omega : 1 < 12*(R*q)+16*q)]
  · simp [periodicLatticeShift, Function.update_of_ne (Ne.symm h), h]


#print axioms dil_admissible
end AdalyFormal.Round4.Guarded.RefuteR1

namespace AdalyFormal.Round5.Guarded.IVTR2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.D1Literal (BdPt)
def rightSite {q : ℕ} (hq : 0 < q) (R : ℕ) :
    PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) :=
  fun μ => ⟨if μ = 0 then 12*(R*q)+12*q-1 else 0,
    by rw [dil_fine_size hq]; split_ifs <;> omega⟩

theorem rightSite_bd {q : ℕ} (hq : 0 < q) (R : ℕ) :
    BdPt ((dilTower q R).Om 0) (rightSite hq R) := by
  have hv : ((rightSite hq R) 0).val = 12*(R*q)+12*q-1 := by simp [rightSite]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change 4*q ≤ _ ∧ _ < 12*(R*q)+12*q
    rw [hv]; omega
  · change ¬ (4*q ≤ _ ∧ _ < 12*(R*q)+12*q)
    rw [dil_shift_zero hq R, if_pos rfl, hv, Nat.mod_eq_of_lt (by omega)]
    omega
  · intro z ν hν
    change (4*q ≤ _ ∧ _ < 12*(R*q)+12*q) ↔ (4*q ≤ _ ∧ _ < 12*(R*q)+12*q)
    rw [dil_shift_zero hq R, if_neg hν]
  · intro ν heq
    have hn : 1 < scaleUp 2 1 (dilLu q R) ν + 1 := by
      rw [dil_fine_size hq]; split_ifs <;> omega
    have hh := congrArg (fun y : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) => (y ν).val) heq
    simp only [periodicLatticeShift, Function.update_self, Fin.val_add, Fin.val_one'] at hh
    rw [Nat.mod_eq_of_lt hn] at hh
    have hw := ((rightSite hq R) ν).isLt
    rcases Nat.lt_or_ge (((rightSite hq R) ν).val+1) (scaleUp 2 1 (dilLu q R) ν+1) with h | h
    · rw [Nat.mod_eq_of_lt h] at hh; omega
    · have he : ((rightSite hq R) ν).val+1 = scaleUp 2 1 (dilLu q R) ν+1 := by omega
      rw [he, Nat.mod_self] at hh; omega


#print axioms rightSite_bd
end AdalyFormal.Round5.Guarded.IVTR2

namespace AdalyFormal.Round12.Noncancel.RightFamily
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.QualitativeR2 (AnFam)
open AdalyFormal.Round12.Noncancel.Path

/-- One consistently chosen family: the right exterior star, never reflected from a left computation. -/
def rightStar {q : ℕ} (hq : 0 < q) (R : ℕ) :
    ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  starPath (periodicLatticeShift (rightSite hq R) 0)


end AdalyFormal.Round12.Noncancel.RightFamily

namespace AdalyFormal.Round13.Positivity.Local
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round12.Noncancel.RightFamily
open AdalyFormal.Round12.Noncancel.Path
open AdalyFormal.Round2.Guarded.Pin

/-- The localized data are EXACTLY flat at every angle of this right star. -/
theorem rightStar_local_data_flat {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (a t : ℝ) :
    dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (rightStar hq R t) a (dilLam q R)) =
    dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (fun _ => 1) a (dilLam q R)) := by
  let P := gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
    (fun _ => 1) a (dilLam q R)
  have hroom : 17*2 ≤ R*(2*q) := by nlinarith
  have hbd := rightSite_bd hq R
  have hboth : ∀ e : Bond (scaleUp 2 1 (dilLu q R)),
      BothIn ((dilTower q R).Om 0) e → P.U e = rightStar hq R t e := by
    intro e he
    symm
    exact starPath_interior _ _ hbd.hx' hbd.trans t e he.1
  exact AdalyFormal.StatementLaneR8.data_congr P (dil_admissible hq hR)
    (by norm_num) hroom (rightStar hq R t) hboth

/-- Unconditional localized strict positivity for every q>0, even R>=18 and
EVERY real angle. This is the localized carrier, not the all-plaquette P2 claim. -/
theorem rightStar_local_positive {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (t : ℝ) (x : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) (hx : x ≠ 0) :
    0 < ⟪x, (dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (rightStar hq R t) 1 (dilLam q R))).Ginv x⟫ := by
  rw [rightStar_local_data_flat hq hR hR18]
  exact AdalyFormal.Round9.Guarded.AnalyticR2.dil_flat_pos hq (by omega) x hx

/-- Nested cofinal localized positivity, not a reversed forall/exists order. -/
theorem cofinal_rightStar_local_positive :
    ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
      R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
      ∀ t : ℝ, ∀ x : ↥(bondSupp (geomOf 2 1 (dilTower (2^j) R))), x ≠ 0 →
        0 < ⟪x, (dataS selIn selIn (gparams 2 1 (dilLu (2^j) R) (by norm_num)
          (dilTower (2^j) R) (rightStar (by positivity) R t) 1
          (dilLam (2^j) R))).Ginv x⟫ := by
  intro j₀
  refine ⟨j₀,le_rfl,?_⟩
  intro R₀
  let R := 2*(R₀+18)
  have hR : 2 ∣ R := ⟨R₀+18,rfl⟩
  have hR18 : 18 ≤ R := by dsimp [R]; omega
  refine ⟨R,by dsimp [R]; omega,hR,hR18,?_⟩
  intro t x hx
  exact rightStar_local_positive (by positivity) hR hR18 t x hx

set_option pp.fullNames true
#print axioms rightStar_local_data_flat
#print axioms rightStar_local_positive
#print axioms cofinal_rightStar_local_positive
end AdalyFormal.Round13.Positivity.Local
