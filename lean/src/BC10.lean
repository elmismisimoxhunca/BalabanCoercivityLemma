import BC9

/-!
# BC10 -- `ginv_coercive_BC_sup`: the chain's `hreg` (RegTower) AND the tower class are derived from ONE hypothesis,
the all-edge link-sup bound `frobSupBond (Ū^j) ≤ ε_j` with `(π/2)(loopFactorBound ell · ε_j) < r0` and `ε_j ≤ 1/(1000 ell⁴)`.
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
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.FlatExt (aFE bFE)
open AdalyFormal.NonflatJet (r0)
open SmallnessBridge.Assemble (loopFactorBound)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond)

theorem ginv_coercive_BC_sup (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (ha : 0 ≤ a) (Lam : Set (PeriodicLatticeSite Lu))
    (hu : IsUnit (DelpA (GF ell k Lu) U a + (1 - siteMask (GF ell k Lu).Om0)))
    (PU : ℝ) (hPU : 0 ≤ PU)
    (hPoincU : ∀ ν ∈ NQp (GF ell k Lu) U, ‖ν‖ ≤ PU * ‖gradL2 U ν‖)
    (nsq c1 t θ e P δ q : ℝ) (hn : 0 < nsq) (ht : 0 < t) (hP : 0 ≤ P)
    -- the tower class: the ONLY input replacing `hm` and `hQdrift`
    (ε : ℕ → ℝ) (hεnn : ∀ j, 0 ≤ ε j)
    (hsup : ∀ j, j < k → frobSupBond (bgTower (GF ell k Lu) U j) ≤ ε j)
    (hr : ∀ j, j < k → Real.pi / 2 * ((loopFactorBound ell : ℝ) * ε j) < r0)
    (hεs : ∀ j, j < k → ε j ≤ 1 / (1000 * (ell : ℝ) ^ 4))
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
  ginv_coercive_BC ell k Lu hell U a ha Lam (regTower_of_sup ell k Lu hell U ε hεnn hsup hr) hu PU hPU hPoincU
    nsq c1 t θ e P δ q hn ht hP ε (towerClass_of_sup ell k Lu U ε hsup) (fun j _ => hεnn j)
    (fun j hj => hsm_of_le ell hell (ε j) (hεnn j) (hεs j hj))
    hδdef hedef hqdef hε0nn hεa hsmall hflat hdp hPoinc1 x

#print axioms ginv_coercive_BC_sup

end AdalyFormal.BondComposite
