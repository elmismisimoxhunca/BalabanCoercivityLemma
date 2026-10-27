import NB16
/-!
# NB17 -- one level of NONABELIAN curvature blocking, every `ell` (CMP98 Prop. 1 for the tree's map)

`prop1_level`: let `m = s·ell`, `m ∣ N_ρ`, `2m < N_ρ`, and every stride-`s` plaquette word of `V` at an
`s`-aligned site have defect `≤ P` with `ell⁴ P ≤ 10⁻⁵`.  Then at every `m`-aligned site `y`:

  `dv (pw m (ubarSU2 s ell V) y ν μ) ≤ ell² P + 10⁶ ell⁴ P²`.

Proof: corner gauge at `y` (NB11-NB13), cone/box bookkeeping (NB14-NB16), chart with `k = 8 ell P`,
`prop1_chart` (NB9), gauge covariance of the blocking (`ubarSU2_gauge`) and of plaquette defects.

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Log su2Exp)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_mem_coarseLattice)
open AdalyFormal.Balaban.QjComposite (stepBlockOf coarseGaugeTransform)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2 ubarSU2_gauge)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice coarseLattice_mem_fits)

variable {L : PeriodicLatticeExtent}

theorem chart_of_box (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell) (V : PeriodicLinkConfiguration SU2 L)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L s) (hdvd : ∀ ρ, s ∣ L ρ + 1)
    (hN : ∀ ρ, 2 * (s * ell) < L ρ + 1) (P : ℝ)
    (hP : ∀ z ∈ CoarseLattice L s, ∀ ν μ : Fin 3, dv (pw s V z ν μ) ≤ P)
    (hsm : 4 * (ell : ℝ) * P ≤ 1) (b : PeriodicLatticeEdge L)
    (hb : Box y s (2 * (s * ell) - s) b.1) :
    Chart (coarseGaugeTransform s (cornerGauge s V y) V)
      (fun e => su2Log (coarseGaugeTransform s (cornerGauge s V y) V e)) (8 * ell * P) b := by
  have hP0 : 0 ≤ P := le_trans (dv_nonneg _) (hP y hy 0 0)
  have hm : s ≤ s * ell := Nat.le_mul_of_pos_right s hell
  have hdiv : ∀ σ, off y b.1 σ / s ≤ 2 * ell := fun σ => by
    apply Nat.div_le_of_le_mul
    have := (hb σ).2; rw [Nat.mul_comm s (2 * ell)]
    have : 2 * ell * s = 2 * (s * ell) := by ring
    omega
  have hax := axial_link s hs V y hy hdvd P hP b.1 b.2 (fun σ => (hb σ).1)
    (by have := (hb b.2).2; have := hN b.2; omega)
  have hd : dv (coarseGaugeTransform s (cornerGauge s V y) V b) ≤ 4 * ell * P := by
    refine le_trans hax ?_
    have h0 : ((off y b.1 0 / s : ℕ) : ℝ) ≤ 2 * ell := by exact_mod_cast hdiv 0
    have h1 : ((off y b.1 1 / s : ℕ) : ℝ) ≤ 2 * ell := by exact_mod_cast hdiv 1
    nlinarith
  obtain ⟨he, hsu, hn⟩ := chart_small _ (le_trans hd hsm)
  exact ⟨he.symm, hsu, by nlinarith⟩

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.chart_of_box
