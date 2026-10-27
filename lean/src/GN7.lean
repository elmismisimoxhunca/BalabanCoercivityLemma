import GN6
import SL4

/-!
# GN7 -- slice coercivity at NON-FLAT `U` from the FLAT inequality (genuine objects, full tower, whole torus)

`Φ_V(y) = ⟪y, Δ(V) y⟫ + ⟪y, Q(V)* a Q(V) y⟫` (genuine `Delta`, `MassFull` with the genuine bond sector at `V`).
`slice_coercive_cond`: for every `x` in the `U`-slice (`R_U D_U* x = 0`)
  `(c1 - n²γ² - n²e)/(1+t) ‖x‖² ≤ n² Φ_U(x)`,   `γ = κ(δP + κP²(δ + bε)) + δ`,  `κ = b q`,
given (all on the genuine operators):
* `hflat`  : `c1‖y‖² ≤ n²(Φ_1(y) + ‖R_1 D_1* y‖²)` for all `y` (flat `Ginv` coercivity + B1 at `U = 1`);
* `hdrift` : `Φ_1(x) ≤ (1+t) Φ_U(x) + e‖x‖²` (curl, `Δ'` and mass drifts);
* `hPoinc1`: Poincare on `N(Q'(1))`, constant `P`;  `hd`: `‖(D_1 - D_U) f‖ ≤ δ‖f‖`;
* `hext`   : right inverse of `Q'_k(U)` on `Λ_k` with `‖D_U f‖ ≤ b‖w‖`;  `hQq`: `‖Q'_k(U) f‖ ≤ q‖f‖`;
* `hQN1`   : `‖Q'_k(U) ν‖ ≤ ε‖ν‖` on `N(Q'(1))` (transport drift of `Q'`).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.SliceCoerc

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.StatementLane (scaleUp)

/-- the full-tower geometry. -/
abbrev GF (ell k : ℕ) (Lu : PeriodicLatticeExtent) : TowerGeom (scaleUp ell k Lu) :=
  geomOf ell k (fullTower ell k Lu)

/-- `Φ_V(y) = ⟪y, Δ(V) y⟫ + ⟪y, Q(V)* a Q(V) y⟫` on the full tower. -/
noncomputable def PhiF (ell k : ℕ) (Lu : PeriodicLatticeExtent) (a : ℝ) (V : Cfg (scaleUp ell k Lu))
    (y : BondFnL2 (scaleUp ell k Lu)) : ℝ :=
  ⟪y, Delta (GF ell k Lu) V y⟫ + ⟪y, MassFull (GF ell k Lu) a (bondSectorOf (GF ell k Lu) V) y⟫

theorem slice_coercive_cond (ell k : ℕ) (Lu : PeriodicLatticeExtent)
    (U : Cfg (scaleUp ell k Lu)) (a : ℝ)
    (nsq c1 t e P δ b ε q : ℝ) (hn : 0 ≤ nsq) (ht : 0 ≤ t) (hP : 0 ≤ P) (hδ : 0 ≤ δ) (hb : 0 ≤ b)
    (hε : 0 ≤ ε) (hq : 0 ≤ q)
    (hflat : ∀ y : BondFnL2 (scaleUp ell k Lu),
      c1 * ‖y‖ ^ 2 ≤ nsq * (PhiF ell k Lu a (trivialU (scaleUp ell k Lu)) y
        + ‖Rproj (GF ell k Lu) (trivialU (scaleUp ell k Lu)) (gradAdj (trivialU (scaleUp ell k Lu)) y)‖ ^ 2))
    (hdrift : ∀ x : BondFnL2 (scaleUp ell k Lu),
      PhiF ell k Lu a (trivialU (scaleUp ell k Lu)) x ≤ (1 + t) * PhiF ell k Lu a U x + e * ‖x‖ ^ 2)
    (hPoinc1 : ∀ ν ∈ NQp (GF ell k Lu) (trivialU (scaleUp ell k Lu)),
      ‖ν‖ ≤ P * ‖gradL2 (trivialU (scaleUp ell k Lu)) ν‖)
    (hd : ∀ f, ‖gradL2 (trivialU (scaleUp ell k Lu)) f - gradL2 U f‖ ≤ δ * ‖f‖)
    (hext : ∀ w : coarseC (GF ell k Lu), ∃ f, Qtop (GF ell k Lu) U f = w ∧ ‖gradL2 U f‖ ≤ b * ‖w‖)
    (hQq : ∀ f, ‖Qtop (GF ell k Lu) U f‖ ≤ q * ‖f‖)
    (hQN1 : ∀ ν ∈ NQp (GF ell k Lu) (trivialU (scaleUp ell k Lu)), ‖Qtop (GF ell k Lu) U ν‖ ≤ ε * ‖ν‖)
    (x : BondFnL2 (scaleUp ell k Lu))
    (hx : Rproj (GF ell k Lu) U (gradAdj U x) = 0) :
    (c1 - nsq * ((b * q) * (δ * P + (b * q) * P ^ 2 * (δ + b * ε)) + δ) ^ 2 - nsq * e) / (1 + t)
        * ‖x‖ ^ 2 ≤ nsq * PhiF ell k Lu a U x := by
  have hOm : (GF ell k Lu).Om0 = Set.univ := fullTower_Om0 ell k Lu
  have hx' := (Rproj_eq_zero_iff (GF ell k Lu) hOm U _).mp hx
  have hNU : ∀ f, Qtop (GF ell k Lu) U f = 0 → f ∈ NQp (GF ell k Lu) U := mem_NQp_of_Qtop ell k Lu U
  have hharm : ∀ s, (∀ ν ∈ NQp (GF ell k Lu) U, ⟪gradL2 U s, gradL2 U ν⟫ = 0) →
      ‖gradL2 U s‖ ≤ b * q * ‖s‖ :=
    fun s hs => harmonic_energy_of_ext (gradL2 U) (Qtop (GF ell k Lu) U) (NQp (GF ell k Lu) U) hNU b q hb
      hext hQq s hs
  have hκ : 0 ≤ b * q := mul_nonneg hb hq
  have hS1 := slice_div_small_of_harm (gradL2 U) (gradAdj U) (NQp (GF ell k Lu) U) (gradAdj_adj U)
    (b * q) hκ hharm x hx'
  have hS2 := hharm (gradAdj U x) hx'
  have hR := R1_on_slice_le (gradL2 (trivialU (scaleUp ell k Lu))) (gradL2 U)
    (gradAdj (trivialU (scaleUp ell k Lu))) (gradAdj U)
    (Rproj (GF ell k Lu) (trivialU (scaleUp ell k Lu))) (Qtop (GF ell k Lu) U)
    (NQp (GF ell k Lu) (trivialU (scaleUp ell k Lu))) (NQp (GF ell k Lu) U)
    (gradAdj_adj (trivialU (scaleUp ell k Lu))) (gradAdj_adj U)
    (Rproj_norm_sq (GF ell k Lu) (trivialU (scaleUp ell k Lu)))
    (Rproj_mem_lap (GF ell k Lu) hOm (trivialU (scaleUp ell k Lu)))
    P δ b ε (b * q) hP hδ hb hε hκ hPoinc1 hd hext hNU hQN1 x hx' hS1 hS2
  have hγ0 : 0 ≤ (b * q) * (δ * P + (b * q) * P ^ 2 * (δ + b * ε)) + δ := by
    have := mul_nonneg hb hε
    positivity
  have hR2 : ‖Rproj (GF ell k Lu) (trivialU (scaleUp ell k Lu)) (gradAdj (trivialU (scaleUp ell k Lu)) x)‖ ^ 2
      ≤ ((b * q) * (δ * P + (b * q) * P ^ 2 * (δ + b * ε)) + δ) ^ 2 * ‖x‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hR 2
  exact slice_from_flat nsq c1 _ e t (‖x‖ ^ 2) _ _ _ hn ht (hflat x) hR2 (hdrift x)

#print axioms slice_coercive_cond

end AdalyFormal.SliceCoerc
