import NsCvOF5
import MF6d
import GCg3

/-!
# CvON3 -- `H0` is bijective along the whole staggered path (lane omega/near)

The unit-level background of the nested staggered family is a temporal configuration with angle `av(v) = sum_{j<ell} D((ell^2 v + ell j) mod N0) t/2`
that sums to zero around the torus, hence a pure gauge `gamma 1 gamma^-1`; `H0` is gauge covariant (`GCg3.H0_bijective_iff`, `GCa5.Q1jet_gauge`),
and `H0` at the flat unit background is bijective (`M0Finish.R7.H0_bijective_of_small` at `eps0 = 0`).
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

/-- the unit-level angle profile of the staggered layer. -/
noncomputable def avF (c ell N0 : ℕ) (t : ℝ) (v : ℕ) : ℝ :=
  ∑ j ∈ range ell, Dfun c ell N0 ((ell ^ 2 * v + ell * j) % N0) * (t / 2)

/-- the profile sums to zero around the unit torus. -/
theorem avF_sum_zero (c ell N N0 : ℕ) (hN0 : N0 = ell ^ 2 * N) (t : ℝ) :
    ∑ v ∈ range N, avF c ell N0 t v = 0 := by
  classical
  let F : ℕ → ℝ := fun w => if w % N0 = c then 1 else 0
  have hD : ∀ w : ℕ, Dfun c ell N0 (w % N0) = F w - F (w + ell) := by
    intro w
    unfold Dfun
    simp only [F]
    have : (w % N0 + ell) % N0 = (w + ell) % N0 := by rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    rw [this]
  have hv : ∀ v : ℕ, avF c ell N0 t v = (F (ell ^ 2 * v) - F (ell ^ 2 * (v + 1))) * (t / 2) := by
    intro v
    unfold avF
    rw [← Finset.sum_mul]
    congr 1
    have : ∀ j : ℕ, Dfun c ell N0 ((ell ^ 2 * v + ell * j) % N0) = F (ell ^ 2 * v + ell * j) - F (ell ^ 2 * v + ell * (j + 1)) := by
      intro j
      rw [hD]
      congr 2
      ring
    simp_rw [this]
    rw [Finset.sum_range_sub']
    simp only [mul_zero, add_zero]
    congr 2
    ring
  simp_rw [hv]
  rw [← Finset.sum_mul, Finset.sum_range_sub']
  have : F (ell ^ 2 * N) = F (ell ^ 2 * 0) := by
    simp only [F, mul_zero]
    rw [← hN0, Nat.mod_self, Nat.zero_mod]
  rw [this, sub_self, zero_mul]


/-- the gauge `gamma(y) = cartan(-sum_{u < y_0} av u)`. -/
noncomputable def gT (L : PeriodicLatticeExtent) (av : ℕ → ℝ) : GaugeFn L :=
  fun y => cartan (-(∑ u ∈ range (y 0).val, av u))

/-- a temporal configuration with zero total angle is the gauge transform of the identity. -/
theorem temporal_eq_gauge {L : PeriodicLatticeExtent} {V : PeriodicLinkConfiguration SU2 L} {av : ℕ → ℝ}
    (hV : IsTemporal 1 V av) (hsum : ∑ u ∈ range (L 0 + 1), av u = 0) :
    V = periodicGaugeTransform (gT L av) (fun _ => (1 : SU2)) := by
  funext e
  obtain ⟨y, μ⟩ := e
  have hcrs : Crs 1 y := fun _ => one_dvd _
  obtain ⟨h0, h1, h2⟩ := hV y hcrs
  unfold periodicGaugeTransform gT
  simp only [mul_one]
  rcases (by omega : μ = 0 ∨ μ = 1 ∨ μ = 2) with rfl | rfl | rfl
  · show V (y, 0) = _
    rw [h0, cartan_inv, cartan_mul]
    congr 1
    have hiff : y 0 = Fin.last (L 0) ↔ (y 0).val = L 0 :=
      ⟨fun h => by rw [h]; rfl, fun h => Fin.ext h⟩
    have hshift : ((periodicLatticeShift y 0) 0).val = if (y 0).val = L 0 then 0 else (y 0).val + 1 := by
      simp only [periodicLatticeShift, Function.update_self, Fin.val_add_one, hiff]
    rw [hshift]
    split_ifs with hy
    · simp only [Finset.sum_range_zero, neg_zero]
      have : ∑ u ∈ range (y 0).val, av u + av (y 0).val = 0 := by
        rw [← Finset.sum_range_succ, hy]; exact hsum
      linarith
    · rw [Finset.sum_range_succ]; ring
  · show V (y, 1) = _
    rw [h1]
    have : (periodicLatticeShift y 1) 0 = y 0 := by simp [periodicLatticeShift]
    rw [this, cartan_inv, cartan_mul]; simp [cartan_zero]
  · show V (y, 2) = _
    rw [h2]
    have : (periodicLatticeShift y 2) 0 = y 0 := by simp [periodicLatticeShift]
    rw [this, cartan_inv, cartan_mul]; simp [cartan_zero]


open AdalyFormal.GaugeCov in
open AdalyFormal.Balaban.AlphaAnalyticity (gaugeActA) in
open AdalyFormal.Balaban.RMapLipschitz (frobNorm) in
open AdalyFormal.NonflatJet (numeric_small regBg_of_small r0_pos) in
/-- `H0` at the flat unit background is bijective (per-link smallness at `eps0 = 0`). -/
theorem H0_flat_bijective {L : PeriodicLatticeExtent} {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ L μ + 1)
    (Lam : Set (PeriodicLatticeSite L)) :
    Function.Bijective (H0 Lam (Q1jet ell (fun _ : PeriodicLatticeEdge L => (1 : SU2)))) := by
  have hV : ∀ e, frobNorm (((fun _ : PeriodicLatticeEdge L => (1 : SU2)) e : M2) - 1) ≤ 0 := by
    intro e
    have : (((1 : SU2) : M2) - 1) = 0 := by simp
    simp
  have hn := numeric_small hell 0 le_rfl (by positivity)
  have hreg := regBg_of_small (s := 1) (ell := ell) Nat.one_pos (fun _ : PeriodicLatticeEdge L => (1 : SU2)) 0 le_rfl hV
    (by simpa using AdalyFormal.NonflatJet.r0_pos)
  exact AdalyFormal.M0Finish.R7.H0_bijective_of_small hell hdvd Lam _ 0 le_rfl hV hn.1 hreg hn.2

open AdalyFormal.GaugeCov in
open AdalyFormal.Balaban.AlphaAnalyticity (gaugeActA) in
/-- `H0` of a temporal unit background with zero total angle is bijective (gauge covariance). -/
theorem H0_temporal_bijective {L : PeriodicLatticeExtent} {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ L μ + 1)
    (Lam : Set (PeriodicLatticeSite L)) {V : PeriodicLinkConfiguration SU2 L} {av : ℕ → ℝ}
    (hV : IsTemporal 1 V av) (hsum : ∑ u ∈ range (L 0 + 1), av u = 0) :
    Function.Bijective (H0 Lam (Q1jet ell V)) := by
  rw [temporal_eq_gauge hV hsum]
  have hQ : ∀ (B : Bond L → AdalyFormal.Balaban.CovariantOperators.SuTwo) (c : AdalyFormal.Balaban.LatticeOperators.CoarseBond L ell),
      Q1jet ell (periodicGaugeTransform (gT L av) (fun _ => (1 : SU2))) (gaugeActA (gT L av) B) c =
        AdalyFormal.Balaban.CovariantOperators.RMap (gT L av c.1.1) (Q1jet ell (fun _ => (1 : SU2)) B c) :=
    fun B c => congrFun (Q1jet_gauge ell (gT L av) (fun _ => (1 : SU2)) B) c
  exact (H0_bijective_iff (Lam := Lam) (g := gT L av) hQ).mpr (H0_flat_bijective hell hdvd Lam)

#print axioms avF_sum_zero
#print axioms temporal_eq_gauge
#print axioms H0_flat_bijective
#print axioms H0_temporal_bijective

end AdalyFormal.CoverOmega
