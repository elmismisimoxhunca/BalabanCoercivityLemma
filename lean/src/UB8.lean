import UC1
import GW2

/-!
# UB8 -- `ChartOK` from ONE local M1 chart (lane m2_unit_20261014)

`chartOK_of_M1` : a unit plaquette `q` (good box, within `RM − 17` of `Λ`) and a fine gauge `γ` such that `U^γ` AGREES on the fine
ball `Ball(embY q₀, 32 ℓ^k)` with a configuration `V` that is `M1Regular` (one global gauge FOR `V`, not for `U`) give the chart
conditions of UB5 with the M1 constants
  `s = ρ₁ = (4π+4)·12Mα₀`,  `κ₁ = kapM1(12Mα₀)`,  `ε l = epsM ℓ 12 M α₀ k l`.
Ingredients: GW2 `hlink_M1` (window links), DK2 `chart_bounds` + UA9 `unitBgU_chart_small` (unit base links),
TL6b `hcl_M1` + ZR8Read `bgTower_congr` (regional class on the four rows' cones), FE5a `emb_bondsLam` (rows).
This is the interface to Layer B: the bridge supplies `(γ, V)` per plaquette.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.M2Unit

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice blockOf)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.NonflatJet
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible scaleUp pdist)
open AdalyFormal.StatementLaneG (gparams LambdaOK2)
open AdalyFormal.StatementLaneR8 (Ball AgreeAt rhoT pdist_triangle pdist_coarseShift_le Ball_sub mem_Ball_self)
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.FlatEllGeneral (InBox)
open AdalyFormal.CurvBlock (dv)
open SmallnessBridge.Assemble (loopFactorBound)
open AdalyFormal.TowerLoc (rho1 epsM WM)
open AdalyFormal.M1DK (kapM1 qM1)

variable {L : PeriodicLatticeExtent}

/-- forward paths move the `pdist` by at most their length. -/
theorem pdist_of_reach {m : ℕ} {x z : PeriodicLatticeSite L} (h : AdalyFormal.DLayer.Reach m x z) : pdist x z ≤ m := by
  obtain ⟨l, hl, rfl⟩ := h
  have key : ∀ (l : List (Fin 3)) (x : PeriodicLatticeSite L),
      pdist x (l.foldl (fun w μ => periodicLatticeShift w μ) x) ≤ l.length := by
    intro l
    induction l with
    | nil => intro x; simp [AdalyFormal.StatementLaneR8.pdist_self]
    | cons μ rest ih =>
        intro x
        rw [List.foldl_cons, List.length_cons]
        have h1 := ih (periodicLatticeShift x μ)
        have h2 := AdalyFormal.StatementLaneR8.pdist_shift_le x μ
        have h3 := pdist_triangle x (periodicLatticeShift x μ) (rest.foldl (fun w μ => periodicLatticeShift w μ)
          (periodicLatticeShift x μ))
        omega
  exact le_trans (key l x) hl

/-- window sites are within `5 n` of the plaquette's corner. -/
theorem pdist_win {n : ℕ} (hn : 0 < n) (y : PeriodicLatticeSite L) (d : PeriodicPlaquetteDirections)
    {x : PeriodicLatticeSite L} (hx : x ∈ blockOf y n) {i j : ℕ} (hi : i < n) (hj : j < n) :
    pdist y (winPl d x i j).1 ≤ 5 * n := by
  have hx1 : x ∈ AdalyFormal.Balaban.QjComposite.stepBlockOf y 1 n := by
    rw [AdalyFormal.Balaban.QjComposite.stepBlockOf_one]; exact hx
  have h1 := AdalyFormal.DLayer.block_reach 1 n one_pos y x hx1
  have h2 := AdalyFormal.DLayer.Reach_coarseShift j x d.1.2
  have h3 := AdalyFormal.DLayer.Reach_coarseShift i (coarseShift x j d.1.2) d.1.1
  have h4 := AdalyFormal.DLayer.Reach_trans (AdalyFormal.DLayer.Reach_trans h1 h2) h3
  have h5 := pdist_of_reach h4
  show pdist y (coarseShift (coarseShift x j d.1.2) i d.1.1) ≤ 5 * n
  have : 3 * (n - 1) * 1 + j + i ≤ 5 * n := by omega
  omega

theorem agree_gauge {G : Type*} [Group G] {W : Set (PeriodicLatticeSite L)} {X Y : PeriodicLinkConfiguration G L}
    (h : AgreeAt W X Y) (g : PeriodicLatticeSite L → G) :
    AgreeAt W (periodicGaugeTransform g X) (periodicGaugeTransform g Y) := by
  intro z hz μ
  show g z * X (z, μ) * (g (periodicLatticeShift z μ))⁻¹ = g z * Y (z, μ) * (g (periodicLatticeShift z μ))⁻¹
  rw [h z hz μ]

end AdalyFormal.M2Unit

#print axioms AdalyFormal.M2Unit.pdist_of_reach
#print axioms AdalyFormal.M2Unit.pdist_win
#print axioms AdalyFormal.M2Unit.agree_gauge
