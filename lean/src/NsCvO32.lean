import NsCvO31

/-!
# CvO31 -- `Q = QfullOf` on Z-fields along the staggered path (lane omega)

For `G : TowerGeom L` with `G.ell = ell`, `U = stagCfg c t`, a Z-field `zfield f` and a level-`j` bond `p = (j,b)` (`j ≤ 2`) whose base is aligned at stride `ell^j`:
`QfullOf G U (zfield f) p = (ell^j)⁻¹ • [b.2 = 1] dgS (fSum ell j f b.1₀)`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverNested (cartan cartan_coe)
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.UbarTowerCov (UbarTower)

variable {L : PeriodicLatticeExtent}

/-- the angle field of `zfield f`. -/
def thetaF (f : ℕ → ℝ) : PeriodicLatticeEdge L → ℝ := fun b => if b.2 = 1 then f (b.1 0).val else 0

theorem suCoord_zfield (f : ℕ → ℝ) : suCoord (zfield f : BondFnL2 L) = aF (thetaF f) := by
  funext b
  show fromM2 ((zfun f b : SuTwo) : M2) = _
  unfold zfun thetaF aF
  by_cases h : b.2 = 1
  · simp only [if_pos h]; rw [dgS_coe, fromM2_dg]
  · simp only [if_neg h]
    show fromM2 ((0 : SuTwo) : M2) = _
    simp [fromM2]

theorem suCoordInv_aF (θ : PeriodicLatticeEdge L → ℝ) (b : PeriodicLatticeEdge L) :
    (suCoordInv (aF θ) : BondFnL2 L) b = dgS (θ b) := by
  show (⟨toM2 (aF θ b), toM2_mem _⟩ : SuTwo) = dgS (θ b)
  apply Subtype.ext
  show toM2 (aF θ b) = ((dgS (θ b) : SuTwo) : M2)
  rw [dgS_coe]; exact toM2_aF _

theorem formF_thetaF (f : ℕ → ℝ) : FormF 1 f (thetaF f : PeriodicLatticeEdge L → ℝ) := by
  intro z _ μ; rfl

/-- Q on Z-fields at level `j`: `QlinB` of `zfield f` is the Z-type field with profile sums. -/
theorem QlinB_zfield (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hE : StagPar L ell) (hell : 0 < ell) (hdiv : ∀ μ, ell * ell ∣ L μ + 1)
    (c : ℕ) (t : ℝ) (htπ : |t| < tcap ell) (hc1 : ell ≤ c) (hc2 : c + ell * ell < L 0 + 1) (f : ℕ → ℝ)
    (G : TowerGeom L) (hG : G.ell = ell) :
    (QlinB G (stagCfg c t) 1 (zfield f) : BondFnL2 L) = suCoordInv (aF (thetaSeq ell 1 (thetaF f))) ∧
    (QlinB G (stagCfg c t) 2 (zfield f) : BondFnL2 L) = suCoordInv (aF (thetaSeq ell 2 (thetaF f))) := by
  obtain ⟨h1, h2, -, -⟩ := stag_QlinCompX_Z hN hE hell hdiv c t htπ hc1 hc2 (formF_thetaF f)
  have e : bgTower G (stagCfg c t : Cfg L) = UbarTower su2LogExp ell (stagCfg c t : PeriodicLinkConfiguration SU2 L) := by
    unfold bgTower; rw [hG]
  have hreg := stag_regTower_u hN hE hell c t htπ hc1 hc2
  rw [QlinB_apply, QlinB_apply, e, hG, QlinCompL_eq_QlinCompX2 ell _ 2 hreg 1 (by norm_num),
    QlinCompL_eq_QlinCompX2 ell _ 2 hreg 2 le_rfl, suCoord_zfield, h1, h2]
  exact ⟨rfl, rfl⟩

/-- `QlinB` at level `0`. -/
theorem QlinB_zero' (G : TowerGeom L) (U : Cfg L) (A : BondFnL2 L) : QlinB G U 0 A = A := QlinB_zero G U A

/-- pointwise `QlinB` on a Z-field at an aligned bond. -/
theorem QlinB_zfield_apply (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hE : StagPar L ell) (hell : 0 < ell) (hdiv : ∀ μ, ell * ell ∣ L μ + 1)
    (c : ℕ) (t : ℝ) (htπ : |t| < tcap ell) (hc1 : ell ≤ c) (hc2 : c + ell * ell < L 0 + 1) (f : ℕ → ℝ)
    (G : TowerGeom L) (hG : G.ell = ell) (j : ℕ) (hj : j ≤ 2) (b : Bond L) (hb : Crs (ell ^ j) b.1) :
    ((QlinB G (stagCfg c t) j (zfield f) : BondFnL2 L) b : SuTwo) =
      (if b.2 = 1 then dgS (fSum ell j f (b.1 0).val) else (0 : SuTwo)) := by
  have hfm := (stag_QlinCompX_Z hN hE hell hdiv c t htπ hc1 hc2 (formF_thetaF f))
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with h0 | h1 | h2
  · subst h0
    rw [QlinB_zero]
    show (zfield f : BondFnL2 L) b = _
    simp only [zfield_apply, fSum]
  · subst h1
    rw [(QlinB_zfield hN hE hell hdiv c t htπ hc1 hc2 f G hG).1, suCoordInv_aF]
    have hcr' : Crs ell b.1 := by simpa using hb
    have := hfm.2.2.1 b.1 hcr' b.2
    show dgS (thetaSeq ell 1 (thetaF f) b) = _
    have e : thetaSeq ell 1 (thetaF f) b = if b.2 = 1 then fSum ell 1 f (b.1 0).val else 0 := this
    rw [e]
    split_ifs <;> first | rfl | exact dgS_zero
  · subst h2
    rw [(QlinB_zfield hN hE hell hdiv c t htπ hc1 hc2 f G hG).2, suCoordInv_aF]
    have := hfm.2.2.2 b.1 hb b.2
    show dgS (thetaSeq ell 2 (thetaF f) b) = _
    have e : thetaSeq ell 2 (thetaF f) b = if b.2 = 1 then fSum ell 2 f (b.1 0).val else 0 := this
    rw [e]
    split_ifs <;> first | rfl | exact dgS_zero

/-- **`Q = QfullOf` on a Z-field**: level-`j` row `(j,b)` (`b` aligned at stride `ell^j`) reads `(ell^j)⁻¹ [b.2 = 1] dgS (fSum ell j f b.1₀)`. -/
theorem Qfull_zfield (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hE : StagPar L ell) (hell : 0 < ell) (hdiv : ∀ μ, ell * ell ∣ L μ + 1)
    (c : ℕ) (t : ℝ) (htπ : |t| < tcap ell) (hc1 : ell ≤ c) (hc2 : c + ell * ell < L 0 + 1) (f : ℕ → ℝ)
    (G : TowerGeom L) (hG : G.ell = ell) (hk : G.k = 2)
    (hcrs : ∀ p : BIdx G, Crs (ell ^ (p.1 : ℕ)) p.2.1.1) (p : BIdx G) :
    (QfullOf G (stagCfg c t) (zfield f) : FSp G) p =
      ((ell : ℝ) ^ (p.1 : ℕ))⁻¹ • (if p.2.1.2 = 1 then dgS (fSum ell (p.1 : ℕ) f (p.2.1.1 0).val) else (0 : SuTwo)) := by
  have hj : (p.1 : ℕ) ≤ 2 := by have := p.1.2; omega
  show (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (QlinB G (stagCfg c t) p.1 (zfield f))) p.2.1 = _
  rw [hG, QlinB_zfield_apply hN hE hell hdiv c t htπ hc1 hc2 f G hG p.1 hj p.2.1 (hcrs p)]

#print axioms Qfull_zfield
#print axioms suCoord_zfield
#print axioms suCoordInv_aF
#print axioms QlinB_zfield

end AdalyFormal.CoverOmega
