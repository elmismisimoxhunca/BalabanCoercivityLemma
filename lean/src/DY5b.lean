import DP1
import DY4b
import DY5a

/-!
# DY5b -- the SECOND clause of `DLayerStrat` (`hJ`) at one configuration, from the weighted columns of `H₁`
(M1 D-layer lane, clause 2, 2026-10-14)

DP1's setting (`CTBase B`, W4 `cw`, `hext` `bN`, `Q*` injective, `RegData`, `HolRegime`) plus the two bilinear bounds of
`Δ⁽²⁾` relative to `n = ‖wq ι·‖` (`δ₀` unconjugated, `δ₁` conjugated by the D2 weight centred at any `c`), `δ₀ < cw`.
* `kapB1`, `wsB1` : DY4b's perturbed split / Schur instance at the column centre `c`;
* **`H1_eq`** : the Schur `H` of `wsB1 c` is the printed `H₁` of the ingredient family;
* **`hH1col_B`** : the weighted columns of `H₁in` (unit-bond rows, `τ*`), uniform in the bond:
  `Σ_b ℓ^{-3 bstrat b} ‖(H₁in δ_e v)(b)‖ ≤ √(3ℓ⁷ a Cg)·CH1·‖v‖`;
* **`dlayer_clause2`** : `|⟪H₁in(D̃⁽²⁾ B), J⟫| ≤ (√(3ℓ⁷ a Cg) CH1 · SJ) · KD · ‖B‖²` (DS1 `hJ_strat`).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1DStrat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer
open AdalyFormal.M1Site
open AdalyFormal.M1IMS
open AdalyFormal.TowerLoc (RegData Estar)
open AdalyFormal.StatementLane (Tower Admissible bigSide scaleUp)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.M1 (M1Regular strat bstrat wnormSq)

section clause
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)} {W : ℕ}
  (B : CTBase ell M R k S W) (hell0 : 0 < ell) (Lam : Set (PeriodicLatticeSite Lu))
  (ρ : ℝ) (hρ : 0 ≤ ρ) (hreg : HolRegime S ell k B.U ρ)
  (hεγ : ∀ c, (B.toCT c).epsG * B.γ ≤ 1) (hcG : ∀ c, 0 < (B.toCT c).cG)
  (cw : ℝ) (hcw : 0 < cw)
  (hW4 : ∀ A : ↥(bondSupp (geomOf ell k S)),
    cw * wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))
      ≤ ⟪A, (gparams ell k Lu hell0 S B.U B.a Lam).data.Ginv A⟫)
  (hR8 : 8 * ell ≤ R) (Sstar : ℝ) (Dr : RegData ell k Lu S B.U Sstar)
  (bN : ℝ) (hbN : 0 < bN)
  (hext : ∀ v : FSp (geomOf ell k S), ∃ g : ↥(bondSupp (geomOf ell k S)),
    (gparams ell k Lu hell0 S B.U B.a Lam).data.Q g = v ∧
      ⟪g, (gparams ell k Lu hell0 S B.U B.a Lam).data.Ginv g⟫
        ≤ bN * ‖diagW (geomOf ell k S) (fun p => Real.sqrt (massW (geomOf ell k S) B.a p)) v‖ ^ 2)
  (hQs : Function.Injective (gparams ell k Lu hell0 S B.U B.a Lam).data.Qs)

  (δ0 δ1 : ℝ) (hδ0 : 0 ≤ δ0) (hδ1 : 0 ≤ δ1) (hlt : δ0 < cw)
  (hD0 : ∀ x y : ↥(bondSupp (geomOf ell k S)), |⟪x, (gparams ell k Lu hell0 S B.U B.a Lam).data.Delta2 (gparams ell k Lu hell0 S B.U B.a Lam).data_laws y⟫|
    ≤ δ0 * (nq S ell k (geomOf ell k S) x * nq S ell k (geomOf ell k S) y))
  (hD1 : ∀ (c : PeriodicLatticeSite (scaleUp ell k Lu)) (x y : ↥(bondSupp (geomOf ell k S))),
    |⟪(EWP (geomOf ell k S) (B.toCT c).χ).w x, (gparams ell k Lu hell0 S B.U B.a Lam).data.Delta2 (gparams ell k Lu hell0 S B.U B.a Lam).data_laws ((EWP (geomOf ell k S) (B.toCT c).χ).wi y)⟫|
      ≤ δ1 * (nq S ell k (geomOf ell k S) x * nq S ell k (geomOf ell k S) y))

/-- the perturbed split constant at the column centre `c` -/
noncomputable def kapB1 (c : PeriodicLatticeSite (scaleUp ell k Lu)) : ℝ :=
  ((B.toCT c).gsplit1 hell0 Lam ρ hρ hreg (hεγ c) (hcG c) cw hcw hW4 (3 * B.θ * ell) (θ'_nonneg B)
    (phiC_lip B.hS B.hR B.hM B.hell B.hθ.le c) hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0 (hD1 c)).kap

/-- the Schur instance of `H₁` at the column centre `c` -/
noncomputable def wsB1 (hκ1 : ∀ c, kapB1 B hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0 hD1 c < 1)
    (c : PeriodicLatticeSite (scaleUp ell k Lu)) :
    WSchur ↥(bondSupp (geomOf ell k S)) (FSp (geomOf ell k S)) :=
  (B.toCT c).wschur1 hell0 Lam ρ hρ hreg (hεγ c) (hcG c) cw hcw hW4 (3 * B.θ * ell) (θ'_nonneg B)
    (phiC_lip B.hS B.hR B.hM B.hell B.hθ.le c) hR8 Sstar Dr bN hbN hext hQs δ0 δ1 hδ0 hδ1 hlt hD0 (hD1 c) (hκ1 c)

/-- **the Schur `H` is the printed `H₁`** -/
theorem H1_eq (hκ1 : ∀ c, kapB1 B hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0 hD1 c < 1)
    (c : PeriodicLatticeSite (scaleUp ell k Lu)) :
    (gparams ell k Lu hell0 S B.U B.a Lam).data.H1 (gparams ell k Lu hell0 S B.U B.a Lam).G1inv
      = (wsB1 B hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 hR8 Sstar Dr bN hbN hext hQs δ0 δ1 hδ0 hδ1 hlt hD0 hD1 hκ1 c).H := by
  have hG1 : (gparams ell k Lu hell0 S B.U B.a Lam).G1inv = (gparams ell k Lu hell0 S B.U B.a Lam).data.Ginv - (gparams ell k Lu hell0 S B.U B.a Lam).data.Delta2 (gparams ell k Lu hell0 S B.U B.a Lam).data_laws :=
    (gparams ell k Lu hell0 S B.U B.a Lam).data.G1inv_unique (gparams ell k Lu hell0 S B.U B.a Lam).G1inv_spec ((gparams ell k Lu hell0 S B.U B.a Lam).data.isG1inv_sub (gparams ell k Lu hell0 S B.U B.a Lam).data_laws)
  rw [hG1]
  ext1 x; rfl

include hR8 in
/-- **the weighted columns of `H₁in`** -/
theorem hH1col_B (hκ1 : ∀ c, kapB1 B hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0 hD1 c < 1)
    (hcN : ∀ c, 0 < 1 / (wsB1 B hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 hR8 Sstar Dr bN hbN hext hQs δ0 δ1 hδ0 hδ1 hlt hD0 hD1
        hκ1 c).bN
      - (wsB1 B hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 hR8 Sstar Dr bN hbN hext hQs δ0 δ1 hδ0 hδ1 hlt hD0 hD1 hκ1 c).EN)
    (CH : ℝ) (hCH0 : 0 ≤ CH) (hCH : ∀ c, (wsB1 B hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 hR8 Sstar Dr bN hbN hext hQs δ0 δ1 hδ0 hδ1 hlt hD0
        hD1 hκ1 c).CHw ≤ CH)
    (hq : (ell : ℝ) ^ 3 * Real.exp (-(B.θ * (R * M))) ≤ 1 / 2)
    (e : Bond Lu) (v : SuTwo) :
    ∑ b, omJ S ell k b * ‖((gparams ell k Lu hell0 S B.U B.a Lam).H1in (WithLp.toLp 2 (Pi.single e v) : BondFnL2 Lu)) b‖
      ≤ (Real.sqrt (3 * (ell : ℝ) ^ 7 * B.a * Cgeo ell B.θ) * CH) * ‖v‖ := by
  classical
  have hell1 : 1 ≤ ell := by omega
  have hCg0 : 0 ≤ Cgeo ell B.θ := by unfold Cgeo; have := B.hθ; positivity
  have hτ := tau_adj_single ell k Lu hell0 S e v
  have hH : (gparams ell k Lu hell0 S B.U B.a Lam).H1in (WithLp.toLp 2 (Pi.single e v) : BondFnL2 Lu)
      = iE (geomOf ell k S) ((gparams ell k Lu hell0 S B.U B.a Lam).data.H1 (gparams ell k Lu hell0 S B.U B.a Lam).G1inv
        (ContinuousLinearMap.adjoint (tauExt ell k Lu hell0 S) (WithLp.toLp 2 (Pi.single e v) : BondFnL2 Lu))) := rfl
  rw [hH, hτ]
  split_ifs with hb
  · set p : BIdx (geomOf ell k S) := ⟨Fin.last k, ⟨unitBondEmb ell k Lu hell0 e, hb⟩⟩ with hp
    rw [H1_eq B hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 hR8 Sstar Dr bN hbN hext hQs δ0 δ1 hδ0 hδ1 hlt hD0 hD1 hκ1
      (rowBase (geomOf ell k S) p)]
    have hc0 : (B.toCT (rowBase (geomOf ell k S) p)).χ (rowBase (geomOf ell k S) p) = 0 :=
      phiC_self B.hS B.θ (rowBase (geomOf ell k S) p)
    have hCg := phiC_colsum B.hS B.hR B.hM hell1 B.hθ hq (rowBase (geomOf ell k S) p)
    have hlev := rowBase_strat B.hS B.hR B.hM B.hell
      (le_trans (by omega : ell ≤ R) (Nat.le_mul_of_pos_right R (by have := B.hM; omega))) p
    have h := (B.toCT (rowBase (geomOf ell k S) p)).H1_col hell0 Lam ρ hρ hreg (hεγ _) (hcG _) cw hcw hW4
      (3 * B.θ * ell) (θ'_nonneg B) (phiC_lip B.hS B.hR B.hM B.hell B.hθ.le _) hR8 Sstar Dr bN hbN hext hQs
      δ0 δ1 hδ0 hδ1 hlt hD0 (hD1 _) (hκ1 _) (hcN _) p v hc0 (Cgeo ell B.θ) hCg0 (by unfold Cgeo; exact hCg) hlev
    refine h.trans ?_
    have h2 := hCH (rowBase (geomOf ell k S) p)
    have hs0 : 0 ≤ Real.sqrt (3 * (ell : ℝ) ^ 7 * B.a * Cgeo ell B.θ) := Real.sqrt_nonneg _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hs0) (norm_nonneg _)
  · rw [map_zero, map_zero]
    simp only [PiLp.zero_apply, norm_zero, mul_zero, Finset.sum_const_zero]
    positivity

end clause

#print axioms kapB1
#print axioms wsB1
#print axioms H1_eq
#print axioms hH1col_B

end AdalyFormal.M1DStrat
