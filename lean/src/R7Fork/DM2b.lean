import R7Fork.DM2a

/-!
# DM2b -- `Q_k` at the embedded unit bond for an ARBITRARY tower at flat `U`: the genuine level-`k` component is the
`ell^k`-block line average at the embedded coarse bond (generalises `GenuineU1.Qfull_top`, which is stated for the full tower via `eqv`).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000
namespace AdalyFormal.DirichletMono

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.GenuineU1
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)

theorem bgTower_flat (P : IngrBParams) (hU : P.U = flatCfg) (j : ℕ) :
    bgTower P.G P.U j = flatCfg := by
  unfold bgTower
  rw [hU]
  exact Ubar_flat _ j

theorem Qfull_top_gen (P : IngrBParams) (hU : P.U = flatCfg) (A : BondFnL2 (scaleUp P.ell P.k P.Lu))
    (e : Bond P.Lu) (h : unitBondEmb P.ell P.k P.Lu P.hell e ∈ bondsLam P.G P.k) :
    (P.sector.Qfull A) (pe P e h)
      = lineCoarseRestrictSuTwo (P.ell ^ P.k) (WithLp.ofLp A) (bondsE P.ell P.k P.Lu P.hell e) := by
  have hell' : (P.ell : ℝ) ≠ 0 := by exact_mod_cast P.hell.ne'
  have key := Qcomp_closed P.ell P.hell (bgTower P.G P.U) (bgTower_flat P hU) P.k
    (scaleUp_tiling P.ell P.k P.Lu P.hell)
    (suCoordF (WithLp.ofLp A)) P.k le_rfl (P.ell ^ P.k) rfl (bondsE P.ell P.k P.Lu P.hell e)
  rw [suCoordFInv_suCoordF] at key
  show (((P.G.ell : ℝ) ^ ((Fin.last P.k : Fin (P.k + 1)) : ℕ))⁻¹) •
    (WithLp.ofLp (QlinB P.G P.U ((Fin.last P.k : Fin (P.k + 1)) : ℕ) A))
      (unitBondEmb P.ell P.k P.Lu P.hell e) = _
  rw [Fin.val_last]
  have hQ : (WithLp.ofLp (QlinB P.G P.U P.k A))
      (unitBondEmb P.ell P.k P.Lu P.hell e) = suCoordFInv (QlinCompX P.ell
        (bgTower P.G P.U) P.k (suCoordF (WithLp.ofLp A)))
        ((bondsE P.ell P.k P.Lu P.hell e).1.1, (bondsE P.ell P.k P.Lu P.hell e).2) := rfl
  rw [hQ, key]
  show ((P.ell : ℝ) ^ P.k)⁻¹ • (((P.ell ^ P.k : ℕ) : ℝ) • _) = _
  rw [smul_smul]
  push_cast
  rw [inv_mul_cancel₀ (pow_ne_zero P.k hell'), one_smul]

#print axioms Qfull_top_gen

end AdalyFormal.DirichletMono
