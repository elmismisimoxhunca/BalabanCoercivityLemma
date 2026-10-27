import ZXG3J2
import ZXR3E
import PSC10f
import GN12

/-!
# PB1 -- item (1): the explicit scaled flat floor `scaled_G1inv2_simple` (text-ported to the r7 carrier as `PSC10f`)
delivered as the hypothesis `hflat` (`c1`) that the slice chain (GN7 / GN8 / GN10) consumes:

  `min(a,1)/1000 * ‖y‖² ≤ ell^(2k) * (Φ_1(y) + ‖R_1 D_1* y‖²)`      for every `y`, every `k`, `Lu`, `a > 0`,

i.e. `c1 = min a 1 / 1000`, `nsq = ell^(2k)`, with `Φ_1 = PhiF .. (trivialU _)` (genuine `Delta`, `MassFull`).
The identification `⟪x, G1inv x⟫ = Φ_1(iE x) + ‖R_1 D_1* iE x‖²` at flat `U` is proved here from r7 lemmas
(`Gen.G1inv_form`, `Delta_flat_form`, `mass_inner`), with `Tfull = Rproj ∘ gradAdj` by `rfl`.
Standard axioms only (each declaration's printed axiom line).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.PortSlice

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG
open AdalyFormal.GenuineU1
open AdalyFormal.SliceCoerc

/-- at flat `U`, with `Ω₀ = univ`: the genuine `G₁⁻¹` form is `Φ_1 + ‖R_1 D_1* ·‖²` (all fields). -/
theorem G1inv_form_eq_Phi (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (y : BondFnL2 (scaleUp ell k Lu)) :
    ⟪(⟨y, bondSupp_G ell k Lu y⟩ : ↥(bondSupp (PK ell k Lu hell a Lam).G)),
        (PK ell k Lu hell a Lam).G1inv ⟨y, bondSupp_G ell k Lu y⟩⟫
      = PhiF ell k Lu a (trivialU (scaleUp ell k Lu)) y
        + ‖Rproj (GF ell k Lu) (trivialU (scaleUp ell k Lu)) (gradAdj (trivialU (scaleUp ell k Lu)) y)‖ ^ 2 := by
  have hFS := PK_fullSupp ell k Lu hell a Lam
  set x : ↥(bondSupp (PK ell k Lu hell a Lam).G) := ⟨y, bondSupp_G ell k Lu y⟩ with hx
  have hform : ⟪x, (PK ell k Lu hell a Lam).G1inv x⟫
      = ‖AdalyFormal.Balaban.DeltaKFull.curlCovariantCLM_L2
          (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) y‖ ^ 2
        + ‖Rproj (GF ell k Lu) (trivialU (scaleUp ell k Lu))
            (gradAdj (trivialU (scaleUp ell k Lu)) y)‖ ^ 2
        + a * (ell : ℝ) ^ k * ‖(PK ell k Lu hell a Lam).data.Q x‖ ^ 2 :=
    Gen.G1inv_form (PK ell k Lu hell a Lam) hFS (PK_Om0_univ ell k Lu hell a Lam) rfl x
  have hmass : ⟪x, (PK ell k Lu hell a Lam).data.Mass x⟫
      = a * (ell : ℝ) ^ k * ‖(PK ell k Lu hell a Lam).data.Q x‖ ^ 2 :=
    Gen.mass_inner (PK ell k Lu hell a Lam) hFS x
  have h1 : ⟪x, (PK ell k Lu hell a Lam).data.Mass x⟫
      = ⟪y, MassFull (GF ell k Lu) a (bondSectorOf (GF ell k Lu) (trivialU (scaleUp ell k Lu))) y⟫ := by
    show ⟪x, (pE (PK ell k Lu hell a Lam).G) (MassFull (PK ell k Lu hell a Lam).G a (PK ell k Lu hell a Lam).sector
      (iE (PK ell k Lu hell a Lam).G x))⟫ = _
    rw [pE_inner_right]; rfl
  have hD := AdalyFormal.StatementLane3.Delta_flat_form (GF ell k Lu) y
  have hOm : (GF ell k Lu).Om0 = Set.univ := fullTower_Om0 ell k Lu
  rw [hOm, AdalyFormal.StatementLaneG.plaqIn_univ, AdalyFormal.StatementLaneR6.plaqMask_univ] at hD
  have hD' : ⟪y, Delta (GF ell k Lu) (trivialU (scaleUp ell k Lu)) y⟫
      = ‖AdalyFormal.Balaban.DeltaKFull.curlCovariantCLM_L2
          (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) y‖ ^ 2 := hD
  unfold PhiF
  linarith [hform, hmass, h1, hD']

/-- **ITEM (1).** the flat floor as the chain's hypothesis `hflat` with `c1 = min a 1 / 1000`, `nsq = ell^(2k)`. -/
theorem hflat_ported (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (a : ℝ) (ha : 0 < a)
    (y : BondFnL2 (scaleUp ell k Lu)) :
    min a 1 / 1000 * ‖y‖ ^ 2 ≤ ((ell : ℝ) ^ (2 * k)) *
      (PhiF ell k Lu a (trivialU (scaleUp ell k Lu)) y
        + ‖Rproj (GF ell k Lu) (trivialU (scaleUp ell k Lu)) (gradAdj (trivialU (scaleUp ell k Lu)) y)‖ ^ 2) := by
  have h := AdalyFormal.ScaledCoercivity.scaled_G1inv2_simple ell k hell a ha Lu ∅ ⟨y, bondSupp_G ell k Lu y⟩
  rw [G1inv_form_eq_Phi ell k Lu hell a ∅ y] at h
  exact h

#print axioms G1inv_form_eq_Phi
#print axioms hflat_ported

end AdalyFormal.PortSlice
