import ZT5H
import ZLocLocal
import ZT5D2
import ZLocControls

/-!
# ZT6B -- r6 must-fire controls and the answer to the r5-Opus collapse (`statement_audit_r5_opus/VERDICT.md`)
The r5-Opus path `U_θ` moves `U` only on bonds with BOTH endpoints outside `Ω₀`.  After R1:
* `ZR2Ops2.Delta_congr_outside`: `Δ = Delta G U` depends on `U` only on the bonds with both endpoints in `Ω₀` (`BothIn Ω₀ = CubeBond Ω₀`);
* `ZXR2Wire2.Jf_congr_outside`: the same for `J`;
* `ZR2Ops2.Delta_outside_zero`: `Δ` annihilates every bond field supported OFF the both-in-`Ω₀` bonds (the single-bond test field `Xδ_{b₀}` of the
  r5 collapse is such a field: `⟨A,ΔA⟩ = 0` for every `U`, not `4cos θ‖X‖²`);
* below: `Delta_outside_single_bond_form` (the r5 collapse test field) and the class-locality `perCubeRegular2_congr`;
* `perCubeRegular2_congr`: membership in the regularity class depends on `U` only on `Ω₀`-both bonds (p.396: no constraint outside `Ω₀`).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.StatementLaneG

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLaneR6
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

theorem om_sub_om0 {L : PeriodicLatticeExtent} (S : Tower L) (hS : ∀ j, S.Om (j + 1) ⊆ S.Om j) :
    ∀ i, S.Om i ⊆ S.Om 0
  | 0 => le_rfl
  | (i + 1) => (hS i).trans (om_sub_om0 S hS i)

/-- every class cube lies inside `Ω₀` -/
theorem classCube_sub_om0 {L : PeriodicLatticeExtent} {ell M f k : ℕ} {S : Tower L}
    (hS : ∀ j, S.Om (j + 1) ⊆ S.Om j) {sites : Set (PeriodicLatticeSite L)} {j : ℕ}
    (h : IsClassCube ell M f k S sites j) : sites ⊆ S.Om 0 := by
  intro x hx
  rcases h.1.2.2.1 hx with h1 | h1
  · exact om_sub_om0 S hS j h1.1
  · exact om_sub_om0 S hS (j + 1) h1.1

/-- **The class depends on `U` only on the bonds with both endpoints in `Ω₀`.** -/
theorem perCubeRegular2_congr {L : PeriodicLatticeExtent} {ell M f k : ℕ} {S : Tower L}
    (hS : ∀ j, S.Om (j + 1) ⊆ S.Om j) {α₀ η : ℝ} {U U' : LinkCfg L}
    (hUU : ∀ e : Bond L, CubeBond (S.Om 0) e → U e = U' e)
    (h : PerCubeRegular2 ell M f k S α₀ η U) : PerCubeRegular2 ell M f k S α₀ η U' := by
  intro sites j hq
  have hsub := classCube_sub_om0 hS hq
  obtain ⟨g, A, hA, hD, hLap⟩ := h sites j hq
  refine ⟨g, A, ?_, hD, hLap⟩
  intro e he
  obtain ⟨h1, h2, h3⟩ := hA e he
  refine ⟨h1, ?_, h3⟩
  have hcb : CubeBond (S.Om 0) e := ⟨hsub he.1, hsub he.2⟩
  unfold periodicGaugeTransform at h2 ⊢
  rw [← hUU e hcb]
  exact h2

#print axioms perCubeRegular2_congr

/-- **The r5 collapse test field no longer sees `Δ`.**  For ANY tower geometry, any `U`, any bond `b₀` that is not an `Ω₀`-both bond and any `X`,
the single-bond field `X δ_{b₀}` has `⟨A, Δ A⟩ = 0` (r5: `4 cos θ ‖X‖²` along the r5-Opus path). -/
theorem Delta_outside_single_bond_form {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L)
    (b₀ : Bond L) (hb : ¬ BothIn G.Om0 b₀) (X : SuTwo) :
    (inner ℝ (WithLp.toLp 2 (Pi.single b₀ X : Bond L → SuTwo) : BondFnL2 L)
      (Delta G U (WithLp.toLp 2 (Pi.single b₀ X : Bond L → SuTwo))) : ℝ) = 0 := by
  have hz : Delta G U (WithLp.toLp 2 (Pi.single b₀ X : Bond L → SuTwo)) = 0 := by
    refine Delta_outside_zero G U _ (fun e he => ?_)
    have hne : e ≠ b₀ := fun h => hb (h ▸ he)
    show (Pi.single b₀ X : Bond L → SuTwo) e = 0
    simp [Pi.single_apply, hne]
  rw [hz, inner_zero_right]

/-- the r5-Opus boundary bond on the proper tower: `b₀ = (x, 0)` with `x₀ = 111 ∈ Ω₀`, `x₀ + 1 = 112 ∉ Ω₀`. -/
theorem proper_tower_boundary_bond_not_bothIn {Lf : PeriodicLatticeExtent} (hLf : ∀ μ, Lf μ + 1 = 120) :
    ∃ b₀ : Bond Lf, b₀.1 ∈ (TT Lf).Om 0 ∧ ¬ BothIn (geomOf 2 1 (TT Lf)).Om0 b₀ := by
  have h111 : 111 < Lf 0 + 1 := by have := hLf 0; omega
  let x : PeriodicLatticeSite Lf := Function.update (fun μ => ⟨0, by have := hLf μ; omega⟩) 0 ⟨111, h111⟩
  have hx0 : (x 0).val = 111 := by simp [x]
  refine ⟨(x, 0), ?_, ?_⟩
  · show x ∈ (TT Lf).Om 0
    simp only [TT, if_true, OmA, Set.mem_setOf_eq]; omega
  · intro hb
    have h := hb.2
    have hv : ((periodicLatticeShift x 0) 0).val = 112 := by
      rw [shift_val hLf, if_pos rfl, hx0]
    show False
    have h' : periodicLatticeShift x 0 ∈ (TT Lf).Om 0 := h
    simp only [TT, if_true, OmA, Set.mem_setOf_eq] at h'
    omega

/-- the r5 collapse test field on the proper tower: `⟨A, Δ A⟩ = 0` for every `U` and every `X`. -/
theorem proper_tower_collapse_field_form_zero {Lf : PeriodicLatticeExtent} (hLf : ∀ μ, Lf μ + 1 = 120)
    (U : Cfg Lf) (X : SuTwo) :
    ∃ b₀ : Bond Lf, (inner ℝ (WithLp.toLp 2 (Pi.single b₀ X : Bond Lf → SuTwo) : BondFnL2 Lf)
      (Delta (geomOf 2 1 (TT Lf)) U (WithLp.toLp 2 (Pi.single b₀ X : Bond Lf → SuTwo))) : ℝ) = 0 := by
  obtain ⟨b₀, -, hb⟩ := proper_tower_boundary_bond_not_bothIn hLf
  exact ⟨b₀, Delta_outside_single_bond_form _ U b₀ hb X⟩

#print axioms Delta_outside_single_bond_form
#print axioms proper_tower_boundary_bond_not_bothIn
#print axioms proper_tower_collapse_field_form_zero

/-! ### what "full tower" means after R1 -/

/-- the full tower has `Ω₀ = ` the whole torus (`Ω_j = univ` for `j ≤ k`, `k ≥ 0`), so `plaqIn Ω₀ = univ`. -/
theorem fullTower_Om0_univ (ell k : ℕ) (Lu : PeriodicLatticeExtent) :
    (geomOf ell k (fullTower ell k Lu)).Om0 = Set.univ := by
  simp [geomOf, fullTower]

/-- at the full tower the localised `Δ` IS the r5 (global) `Δ`. -/
theorem fullTower_Delta_global (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) :
    Delta (geomOf ell k (fullTower ell k Lu)) U = AdalyFormal.Balaban.DeltaPrimeOperator.deltaKCLMNormalized U :=
  Delta_Om0_univ _ (fullTower_Om0_univ ell k Lu) U

/-- at any parameters with `Ω₀ = univ` the localised `J` IS the r5 (global) `J`. -/
theorem Jf_Om0_univ (P : IngrBParams) (hP : P.G.Om0 = Set.univ) :
    P.Jf = WithLp.toLp 2 (fun b => -(AdalyFormal.IngredientFamily.JSU2 1 P.U b)) := by
  unfold IngrBParams.Jf
  have : plaqIn P.G.Om0 = Set.univ := by rw [hP]; ext p; simp [plaqIn]
  rw [this, AdalyFormal.IngredientFamily.JSU2Loc_univ]

#print axioms fullTower_Delta_global
#print axioms Jf_Om0_univ

end AdalyFormal.StatementLaneG
