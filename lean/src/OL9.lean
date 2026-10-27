import OL8

/-!
# OL9 -- `OpLayer` at ONE printed-class configuration (lane m2_oplayer_20261015)

* `qs_inj_of_hext` : an energy right inverse (`∀ v ∃ g, Q g = v ∧ …`) makes `Q` onto, hence `Q*` injective.
* **`opLayer_cfg`** : MZ5 `OpLayer` at one configuration from
  - a `CTBase B` (HatPack, `Gi`, row bound `γ`) at `U`, the holonomy regime, W4 (`cw`), `∀ p, RowQ` (OL5), an energy right inverse
    with constant `bN` (`hext`),
  - the printed class `ClassCoupled ℓ M 12 k S α₀ ℓ^{-k} U` (source split, MZ3), `4·12Mα₀ ≤ 1`, `18ℓ ≤ RM`, `ℓ³e^{−θRM} ≤ 1/2`,
  - the `C2` bound (constant `K2`), the `W` bound (`CW`), the `D̃⁽²⁾` bound (`KD`) — passed through,
  - the numeric-twin conditions of the two Schur instances (DN0/DN3 `rfl` twins).
  Output constants: `KH = CH √(aℓ)`, `KH1 = CH1 √(aℓ)`.
-/
set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 8000

namespace AdalyFormal.M2OpLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer (bondWt psiD)
open AdalyFormal.M1Site
open AdalyFormal.M1IMS
open AdalyFormal.StatementLane (Tower Admissible bigSide scaleUp)
open AdalyFormal.StatementLane2 (ClassCoupled)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.M1DStrat
open AdalyFormal.M2DLayer (Ageo)

/-- an energy right inverse makes `Q*` injective -/
theorem qs_inj_of_hext {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) (S : Tower (scaleUp ell k Lu))
    (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (bN : ℝ)
    (hext : ∀ v : FSp (geomOf ell k S), ∃ g : ↥(bondSupp (geomOf ell k S)),
      (gparams ell k Lu hell0 S U a Lam).data.Q g = v ∧
        ⟪g, (gparams ell k Lu hell0 S U a Lam).data.Ginv g⟫
          ≤ bN * ‖diagW (geomOf ell k S) (fun p => Real.sqrt (massW (geomOf ell k S) a p)) v‖ ^ 2) :
    Function.Injective (gparams ell k Lu hell0 S U a Lam).data.Qs := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨g, hg, -⟩ := hext y
  have h := (gparams ell k Lu hell0 S U a Lam).data.Q_adj g y
  rw [hg, hy, inner_zero_right] at h
  exact inner_self_eq_zero.mp h

section cfg
variable {ell M R k W : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}
  (B : CTBase ell M R k S W) (hell0 : 0 < ell) (Lam : Set (PeriodicLatticeSite Lu))
  (ρ : ℝ) (hρ : 0 ≤ ρ) (hreg : HolRegime S ell k B.U ρ)
  (hεγ : ∀ c, (B.toCT c).epsG * B.γ ≤ 1) (hcG : ∀ c, 0 < (B.toCT c).cG)
  (cw : ℝ) (hcw : 0 < cw)
  (hW4 : ∀ A : ↥(bondSupp (geomOf ell k S)),
    cw * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))
      ≤ ⟪A, (gparams ell k Lu hell0 S B.U B.a Lam).data.Ginv A⟫)
  (hR8 : 8 * ell ≤ R) (Sstar : ℝ) (Dr : ∀ p : BIdx (geomOf ell k S), AdalyFormal.M2F123.RowQ ell k Lu S B.U Sstar p)
  (bN : ℝ) (hbN : 0 < bN)
  (hext : ∀ v : FSp (geomOf ell k S), ∃ g : ↥(bondSupp (geomOf ell k S)),
    (gparams ell k Lu hell0 S B.U B.a Lam).data.Q g = v ∧
      ⟪g, (gparams ell k Lu hell0 S B.U B.a Lam).data.Ginv g⟫
        ≤ bN * ‖diagW (geomOf ell k S) (fun p => Real.sqrt (massW (geomOf ell k S) B.a p)) v‖ ^ 2)

include hρ hreg hεγ hcG hcw hW4 hR8 Dr hbN hext in
/-- the `hHL2` field at the configuration (centre `rowBase p`) -/
theorem hHL2_cfg (CH : ℝ) (hCH0 : 0 ≤ CH)
    (hκ : kapN ell B.a B.cs B.Θ B.Δ B.γ (3 * B.θ * (ell : ℝ) ^ 2) (3 * B.θ * ell) ρ cw Sstar < 1)
    (hcN : ENF (kapN ell B.a B.cs B.Θ B.Δ B.γ (3 * B.θ * (ell : ℝ) ^ 2) (3 * B.θ * ell) ρ cw Sstar)
        (CQN ell B.a B.cs B.Θ B.Δ B.γ ρ cw) (d3c ell B.a Sstar (3 * B.θ * ell)) cw < 1 / bN)
    (hCH : CHwF (kapN ell B.a B.cs B.Θ B.Δ B.γ (3 * B.θ * (ell : ℝ) ^ 2) (3 * B.θ * ell) ρ cw Sstar)
        (CQN ell B.a B.cs B.Θ B.Δ B.γ ρ cw) (d3c ell B.a Sstar (3 * B.θ * ell)) cw bN ≤ CH) :
    ∀ (p : BIdx (gparams ell k Lu hell0 S B.U B.a Lam).G) (v : SuTwo), ∃ c : PeriodicLatticeSite (scaleUp ell k Lu),
      ∑ b : Bond (scaleUp ell k Lu), ((((ell : ℝ) ^ AdalyFormal.M1.strat S k b.1)⁻¹)
        * Real.exp (phiC S ell M R k B.θ c b.1)
        * ‖(iE (gparams ell k Lu hell0 S B.U B.a Lam).G ((gparams ell k Lu hell0 S B.U B.a Lam).data.H
            (WithLp.toLp 2 (Pi.single p v) : FSp (gparams ell k Lu hell0 S B.U B.a Lam).G))) b‖) ^ 2
        ≤ (CH * Real.sqrt (B.a * ell)) ^ 2 * (ell : ℝ) ^ AdalyFormal.M1.strat S k c * ‖v‖ ^ 2 := by
  intro p v
  have hQs := qs_inj_of_hext hell0 S B.U B.a Lam bN hext
  set c := rowBase (geomOf ell k S) p with hc
  refine ⟨c, ?_⟩
  have hc0 : (B.toCT c).χ c = 0 := phiC_self B.hS B.θ c
  have hlev := rowBase_strat B.hS B.hR B.hM B.hell
    (le_trans (by omega : ell ≤ R) (Nat.le_mul_of_pos_right R (by have := B.hM; omega))) p
  have hκ1 : (gsplitR (B.toCT c) hell0 Lam ρ hρ hreg (hεγ c) (hcG c) cw hcw hW4 (3 * B.θ * ell) (θ'_nonneg B)
      (phiC_lip B.hS B.hR B.hM B.hell B.hθ.le c) hR8 Sstar Dr).kap < 1 := hκ
  have hcN' : 0 < 1 / (wschurR (B.toCT c) hell0 Lam ρ hρ hreg (hεγ c) (hcG c) cw hcw hW4 (3 * B.θ * ell) (θ'_nonneg B)
      (phiC_lip B.hS B.hR B.hM B.hell B.hθ.le c) hR8 Sstar Dr bN hbN hext hQs hκ1).bN
      - (wschurR (B.toCT c) hell0 Lam ρ hρ hreg (hεγ c) (hcG c) cw hcw hW4 (3 * B.θ * ell) (θ'_nonneg B)
      (phiC_lip B.hS B.hR B.hM B.hell B.hθ.le c) hR8 Sstar Dr bN hbN hext hQs hκ1).EN := sub_pos.mpr hcN
  have h := H_l2_colR (B.toCT c) hell0 Lam ρ hρ hreg (hεγ c) (hcG c) cw hcw hW4 (3 * B.θ * ell) (θ'_nonneg B)
      (phiC_lip B.hS B.hR B.hM B.hell B.hθ.le c) hR8 Sstar Dr bN hbN hext hQs hκ1 hcN' p v hc0 hlev
  refine h.trans ?_
  set J := wschurR (B.toCT c) hell0 Lam ρ hρ hreg (hεγ c) (hcG c) cw hcw hW4 (3 * B.θ * ell) (θ'_nonneg B)
      (phiC_lip B.hS B.hR B.hM B.hell B.hθ.le c) hR8 Sstar Dr bN hbN hext hQs hκ1 with hJ
  have hCHw : 0 ≤ J.CHw := by
    unfold WSchur.CHw; have := J.Cy_nonneg; have := J.hcw; positivity
  have hle : J.CHw ≤ CH := hCH
  have ha := B.hp.ha
  have hal : 0 ≤ B.a * (ell : ℝ) := by positivity
  have hsq : (CH * Real.sqrt (B.a * ell)) ^ 2 = CH ^ 2 * (B.a * ell) := by
    rw [mul_pow, Real.sq_sqrt hal]
  rw [hsq]
  have h2 : J.CHw ^ 2 ≤ CH ^ 2 := pow_le_pow_left₀ hCHw hle 2
  have hp0 : (0 : ℝ) ≤ (ell : ℝ) ^ AdalyFormal.M1.strat S k c * ‖v‖ ^ 2 := by positivity
  calc J.CHw ^ 2 * (B.a * ell) * (ell : ℝ) ^ AdalyFormal.M1.strat S k c * ‖v‖ ^ 2
      = J.CHw ^ 2 * ((B.a * ell) * ((ell : ℝ) ^ AdalyFormal.M1.strat S k c * ‖v‖ ^ 2)) := by ring
    _ ≤ CH ^ 2 * ((B.a * ell) * ((ell : ℝ) ^ AdalyFormal.M1.strat S k c * ‖v‖ ^ 2)) :=
        mul_le_mul_of_nonneg_right h2 (mul_nonneg hal hp0)
    _ = _ := by ring

end cfg

end AdalyFormal.M2OpLayer

#print axioms AdalyFormal.M2OpLayer.qs_inj_of_hext
#print axioms AdalyFormal.M2OpLayer.hHL2_cfg
