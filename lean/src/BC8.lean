import BC7
import NB21

/-!
# BC8 -- from the fine-level class `(e, q0)` (curvature_blocking `link_tower_na`) to `TowerClass`, and the discharge of
`hm`, `hQdrift` in `ginv_coercive_FE_named2` (`ginv_coercive_BC`).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.BondComposite

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SliceCoerc (coarseC Qtop GF PhiF)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.CurvBlock (dv pw link_tower_na)
open AdalyFormal.FlatExt (aFE bFE)
open AdalyFormal.NonflatJet (rhoOf)

/-- `link_tower_na` as a `TowerClass`: `ε_j = ell^j e + 3π (ell²)^j q0`. -/
theorem towerClass_of_blocking (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell2 : 2 ≤ ell)
    (U : Cfg (scaleUp ell k Lu)) (q0 e : ℝ) (hq0 : 0 ≤ q0)
    (h0 : ∀ y ν μ, dv (pw 1 U y ν μ) ≤ q0) (he : ∀ b, dv (U b) ≤ e)
    (hN : ∀ ρ, 2 * ell ^ k < scaleUp ell k Lu ρ + 1)
    (hsmall : 4000000 * (ell : ℝ) ^ 2 * (((ell : ℝ) ^ 2) ^ k * q0) ≤ 1) :
    TowerClass ell k Lu U (fun j => (ell : ℝ) ^ j * e + 3 * Real.pi * (((ell : ℝ) ^ 2) ^ j * q0)) := by
  intro j hj y hy μ
  have hell : 0 < ell := by omega
  exact link_tower_na ell hell2 U q0 e hq0 h0 he k
    (fun ρ => by rw [scaleUp_succ ell k Lu hell ρ]; exact Dvd.intro_left _ rfl) hN hsmall j hj.le (y, μ) hy

theorem ginv_coercive_BC (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (ha : 0 ≤ a) (Lam : Set (PeriodicLatticeSite Lu))
    (hreg : RegTower ell (bgTower (GF ell k Lu) U) k)
    (hu : IsUnit (DelpA (GF ell k Lu) U a + (1 - siteMask (GF ell k Lu).Om0)))
    (PU : ℝ) (hPU : 0 ≤ PU)
    (hPoincU : ∀ ν ∈ NQp (GF ell k Lu) U, ‖ν‖ ≤ PU * ‖gradL2 U ν‖)
    (nsq c1 t θ e P δ q : ℝ) (hn : 0 < nsq) (ht : 0 < t) (hP : 0 ≤ P)
    -- the tower class: the ONLY input replacing `hm` and `hQdrift`
    (ε : ℕ → ℝ) (hcl : TowerClass ell k Lu U ε) (hε0 : ∀ j, j < k → 0 ≤ ε j)
    (hsm : ∀ j, j < k → rhoOf ell (ε j) < Real.pi / 2)
    (hδdef : δ = Real.sqrt 12 * AdalyFormal.Balaban.RegularUPerturbation.frobSupBond U)
    (hedef : e = (1 + t) * θ + (1 + 1 / t) * ((4 * Real.sqrt 2 *
      AdalyFormal.Balaban.RegularUPerturbation.frobSupBond U) ^ 2 + deltaM ell k a ε ^ 2))
    (hqdef : q = Real.sqrt (1 / ((ell : ℝ) ^ k) ^ 3) + eps0Of ell k ε) (hε0nn : 0 ≤ eps0Of ell k ε)
    (hεa : eps0Of ell k ε * aFE ell k < 1)
    (hsmall : nsq * ((((bFE ell k + δ * aFE ell k) / (1 - eps0Of ell k ε * aFE ell k)) * q) * (δ * P
        + (((bFE ell k + δ * aFE ell k) / (1 - eps0Of ell k ε * aFE ell k)) * q) * P ^ 2
        * (δ + ((bFE ell k + δ * aFE ell k) / (1 - eps0Of ell k ε * aFE ell k)) * eps0Of ell k ε)) + δ) ^ 2
        + nsq * e < c1)
    (hflat : ∀ y : BondFnL2 (scaleUp ell k Lu),
      c1 * ‖y‖ ^ 2 ≤ nsq * (PhiF ell k Lu a (trivialU (scaleUp ell k Lu)) y
        + ‖Rproj (GF ell k Lu) (trivialU (scaleUp ell k Lu)) (gradAdj (trivialU (scaleUp ell k Lu)) y)‖ ^ 2))
    (hdp : ∀ x : BondFnL2 (scaleUp ell k Lu),
      |AdalyFormal.StatementLaneR6.deltaPrimeBilL2NormLoc U (plaqIn (GF ell k Lu).Om0) x x| ≤ θ * ‖x‖ ^ 2)
    (hPoinc1 : ∀ ν ∈ NQp (GF ell k Lu) (trivialU (scaleUp ell k Lu)),
      ‖ν‖ ≤ P * ‖gradL2 (trivialU (scaleUp ell k Lu)) ν‖)
    (x : ↥(bondSupp (GF ell k Lu))) :
    ‖x‖ ^ 2 ≤ max (2 / ((c1 - nsq * ((((bFE ell k + δ * aFE ell k) / (1 - eps0Of ell k ε * aFE ell k)) * q) * (δ * P
        + (((bFE ell k + δ * aFE ell k) / (1 - eps0Of ell k ε * aFE ell k)) * q) * P ^ 2
        * (δ + ((bFE ell k + δ * aFE ell k) / (1 - eps0Of ell k ε * aFE ell k)) * eps0Of ell k ε)) + δ) ^ 2
        - nsq * e) / (1 + t) / nsq)) (2 * PU ^ 2) *
      ⟪x, (IngrBParams.data ⟨ell, k, Lu, hell, fullTower ell k Lu, U, a, Lam⟩).Ginv x⟫ :=
  AdalyFormal.FlatExt.ginv_coercive_FE_named2 ell k Lu hell U a ha Lam hreg hu PU hPU hPoincU
    nsq c1 t θ (deltaM ell k a ε) e P δ q (eps0Of ell k ε) hn ht hP hδdef hedef hqdef hε0nn hεa hsmall
    hflat hdp (fun x => hm_of_tower ell k Lu hell U a ha ε hreg hcl hε0 hsm x) hPoinc1
    (fun f => hQdrift_of_tower ell k Lu hell U ε hcl f) x

#print axioms towerClass_of_blocking
#print axioms ginv_coercive_BC

end AdalyFormal.BondComposite
