import OL5

/-!
# OL6 -- the `hHL2` column shape from the RowQ Schur instance (lane m2_oplayer_20261015)

* **`H_l2_colR`** : at one configuration, from the inputs of `wschurR` (OL5), `κ < 1`, `1/bN > EN`, `χ(rowBase p) = 0` and
  `lev p ≤ strat(rowBase p) + 1`:
  `Σ_b (ℓ^{-strat b₋} e^{χ(b₋)} ‖(H δ_p v)(b)‖)² ≤ CHw² · a ℓ · ℓ^{strat(rowBase p)} · ‖v‖²`
  (DC2 `H_cjp_w`; DH1 `H_col`'s first half, without the Cauchy–Schwarz step).
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
open AdalyFormal.TowerLoc (Estar)
open AdalyFormal.StatementLane (Tower Admissible bigSide scaleUp)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.CovariantHjMinimizer (PlaqFnL2)
open AdalyFormal.StatementLaneR6 (plaqMask plaqMask_apply plaqMask_symm deltaPrimeBilL2NormLoc)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantLM_L2)

section ws2
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)} {W : ℕ}
  (D : CTData ell M R k S W) (hell0 : 0 < ell) (Lam : Set (PeriodicLatticeSite Lu))
  (ρ : ℝ) (hρ : 0 ≤ ρ) (hreg : HolRegime S ell k D.U ρ)
  (hεγ : D.epsG * D.γ ≤ 1) (hcG : 0 < D.cG)
  (cw : ℝ) (hcw : 0 < cw)
  (hW4 : ∀ A : ↥(bondSupp (geomOf ell k S)),
    cw * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))
      ≤ ⟪A, (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv A⟫)
  (θ' : ℝ) (hθ' : 0 ≤ θ')
  (hL : ∀ (x : PeriodicLatticeSite (scaleUp ell k Lu)) (μ : Fin 3),
    |D.χ (periodicLatticeShift x μ) - D.χ x| ≤ θ' / (ell : ℝ) ^ AdalyFormal.M1.strat S k x)
  (hR8 : 8 * ell ≤ R) (Sstar : ℝ) (Dr : ∀ p : BIdx (geomOf ell k S), AdalyFormal.M2F123.RowQ ell k Lu S D.U Sstar p)
  (bN : ℝ) (hbN : 0 < bN)
  (hext : ∀ v : FSp (geomOf ell k S), ∃ g : ↥(bondSupp (geomOf ell k S)),
    (gparams ell k Lu hell0 S D.U D.a Lam).data.Q g = v ∧
      ⟪g, (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv g⟫
        ≤ bN * ‖diagW (geomOf ell k S) (fun p => Real.sqrt (massW (geomOf ell k S) D.a p)) v‖ ^ 2)
  (hQs : Function.Injective (gparams ell k Lu hell0 S D.U D.a Lam).data.Qs)
include hρ hreg hεγ hcG hcw hW4 hθ' hL hR8 hbN hext hQs in
/-- **the weighted-`ℓ²` column of the genuine `H`** (the `hHL2` shape of MZ5 `OpLayer`, centre `rowBase p`) -/
theorem H_l2_colR
    (hκ1 : (gsplitR D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr).kap < 1)
    (hcN : 0 < 1 / (wschurR D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr bN hbN hext hQs hκ1).bN
      - (wschurR D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr bN hbN hext hQs hκ1).EN)
    (p : BIdx (geomOf ell k S)) (v : SuTwo)
    (hc0 : D.χ (rowBase (geomOf ell k S) p) = 0)
    (hlev : (p.1 : ℕ) ≤ AdalyFormal.M1.strat S k (rowBase (geomOf ell k S) p) + 1) :
    ∑ b : Bond (scaleUp ell k Lu), ((((ell : ℝ) ^ AdalyFormal.M1.strat S k b.1)⁻¹) * Real.exp (D.χ b.1)
        * ‖(iE (geomOf ell k S) ((gparams ell k Lu hell0 S D.U D.a Lam).data.H
          (WithLp.toLp 2 (Pi.single p v) : FSp (geomOf ell k S)))) b‖) ^ 2
      ≤ ((wschurR D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr bN hbN hext hQs hκ1).CHw ^ 2
          * (D.a * ell)) * (ell : ℝ) ^ AdalyFormal.M1.strat S k (rowBase (geomOf ell k S) p) * ‖v‖ ^ 2 := by
  set J := wschurR D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr bN hbN hext hQs hκ1 with hJ
  have hell1 : 1 ≤ ell := by have := D.hell; omega
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast hell1
  have hl0 : (0 : ℝ) < ell := D.ell_pos
  have hH := J.H_cjp_w hcN (WithLp.toLp 2 (Pi.single p v) : FSp (geomOf ell k S))
  have hrw : rowWt (geomOf ell k S) (-D.χ) (WithLp.toLp 2 (Pi.single p v) : FSp (geomOf ell k S))
      = WithLp.toLp 2 (Pi.single p v) := by
    refine PiLp.ext (fun q => ?_)
    rw [rowWt_apply]
    by_cases hq : q = p
    · subst hq; simp [hc0]
    · simp [Pi.single_apply, hq]
  have e1 : J.Nw (cjp J.ωF J.ωE J.H (WithLp.toLp 2 (Pi.single p v) : FSp (geomOf ell k S)))
      = eW (geomOf ell k S) (-sigG (geomOf ell k S)) (eW (geomOf ell k S) D.χ
          ((gparams ell k Lu hell0 S D.U D.a Lam).data.H (WithLp.toLp 2 (Pi.single p v)))) := by
    rw [cjp_apply]
    show eW (geomOf ell k S) (-sigG (geomOf ell k S)) (eW (geomOf ell k S) D.χ
      (J.H (rowWt (geomOf ell k S) (-D.χ) (WithLp.toLp 2 (Pi.single p v))))) = _
    rw [hrw, wschur_HR D hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr bN hbN hext hQs hκ1]
  have e2 : ‖J.Mw.w (WithLp.toLp 2 (Pi.single p v) : FSp (geomOf ell k S))‖
      = Real.sqrt (massW (geomOf ell k S) D.a p) * ‖v‖ := by
    show ‖diagW (geomOf ell k S) (fun q => Real.sqrt (massW (geomOf ell k S) D.a q))
      (WithLp.toLp 2 (Pi.single p v))‖ = _
    have : diagW (geomOf ell k S) (fun q => Real.sqrt (massW (geomOf ell k S) D.a q)) (WithLp.toLp 2 (Pi.single p v))
        = (WithLp.toLp 2 (Pi.single p (Real.sqrt (massW (geomOf ell k S) D.a p) • v)) : FSp (geomOf ell k S)) := by
      refine PiLp.ext (fun q => ?_)
      rw [diagW_apply']
      by_cases hq : q = p
      · subst hq; simp
      · simp [Pi.single_apply, hq]
    rw [this, norm_single, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [e1, e2, norm_E, iE_eW, iE_eW] at hH
  set h := iE (geomOf ell k S) ((gparams ell k Lu hell0 S D.U D.a Lam).data.H
    (WithLp.toLp 2 (Pi.single p v) : FSp (geomOf ell k S))) with hh
  have hsite : ∀ x : PeriodicLatticeSite (scaleUp ell k Lu),
      Real.exp (sigG (geomOf ell k S) x) = (ell : ℝ) ^ AdalyFormal.M1.strat S k x := by
    intro x; rw [exp_sig (geomOf ell k S) hell0, ← strat_eq_stratG hell0 D.hS]; rfl
  have hpt : ∀ b : Bond (scaleUp ell k Lu), (((ell : ℝ) ^ AdalyFormal.M1.strat S k b.1)⁻¹) * Real.exp (D.χ b.1) * ‖h b‖
      = ‖(bondWt (-sigG (geomOf ell k S)) (bondWt D.χ h)) b‖ := by
    intro b
    rw [bondWt_apply, bondWt_apply, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    simp only [Pi.neg_apply]
    rw [Real.exp_neg, hsite]
    ring
  have hnorm : ∑ b : Bond (scaleUp ell k Lu), ‖(bondWt (-sigG (geomOf ell k S)) (bondWt D.χ h)) b‖ ^ 2
      = ‖bondWt (-sigG (geomOf ell k S)) (bondWt D.χ h)‖ ^ 2 := (PiLp.norm_sq_eq_of_L2 _ _).symm
  rw [Finset.sum_congr rfl (fun b _ => by rw [hpt b]), hnorm]
  have hCHw : 0 ≤ J.CHw := by
    unfold WSchur.CHw; have := J.Cy_nonneg; have := J.hcw; positivity
  have hN0 : 0 ≤ ‖bondWt (-sigG (geomOf ell k S)) (bondWt D.χ h)‖ := norm_nonneg _
  have h2 := pow_le_pow_left₀ hN0 hH 2
  set sc := AdalyFormal.M1.strat S k (rowBase (geomOf ell k S) p)
  have hmw : massW (geomOf ell k S) D.a p = D.a * (ell : ℝ) ^ (p.1 : ℕ) := rfl
  have ha := D.hp.ha
  have hlevr : (ell : ℝ) ^ (p.1 : ℕ) ≤ ell * (ell : ℝ) ^ sc := by
    rw [← pow_succ']; exact pow_le_pow_right₀ hellr hlev
  calc ‖bondWt (-sigG (geomOf ell k S)) (bondWt D.χ h)‖ ^ 2
      ≤ (J.CHw * (Real.sqrt (massW (geomOf ell k S) D.a p) * ‖v‖)) ^ 2 := h2
    _ = J.CHw ^ 2 * (D.a * (ell : ℝ) ^ (p.1 : ℕ)) * ‖v‖ ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by rw [hmw]; positivity), hmw]; ring
    _ ≤ J.CHw ^ 2 * (D.a * (ell * (ell : ℝ) ^ sc)) * ‖v‖ ^ 2 := by gcongr
    _ = _ := by ring

end ws2

end AdalyFormal.M1DStrat

#print axioms AdalyFormal.M1DStrat.H_l2_colR
