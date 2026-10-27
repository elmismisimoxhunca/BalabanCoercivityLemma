import BLC7
import MXQ_GG5
import MXQ_Base
import AC_BLC7

/-! AC copy of BLC7: affected declarations only (lane allc_20261016); 12 literal kept (control build). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace MXQ.M2BallCharts
open MXQ.AllC (CF CubeFamOK)
open AdalyFormal.M2BallCharts

open AdalyFormal.AllC MXQ.AllC
variable {Fm : CF} [CubeFamOK Fm]

open AdalyFormal.Target.ClayStatement AdalyFormal.M2Glue3 AdalyFormal.M2Glue2 AdalyFormal.M2GlueGeo
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (Ball)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 coe_mul coe_inv)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open Matrix

variable {L : PeriodicLatticeExtent}

/-- the plaquette bound from the class (every plaquette with its four corners in `Ω₀`). -/
theorem plq_classACΦ {ell M R k : ℕ} {S : Tower L} (hcov : CoversOmQ ell M Fm k S) (hell : 0 < ell)
    {α₀ η : ℝ} (hη : 0 < η) (hα : 0 ≤ α₀) {U : LinkCfg L} (hP : PerCubeRegular2HQ ell M Fm 12 k S α₀ η U)
    (hX : (12 : ℝ) * M * α₀ ≤ 1 / 2) {x : PeriodicLatticeSite L} {μ ν : Fin 3} (hμν : μ < ν)
    (h0 : x ∈ S.Om 0) (h1 : periodicLatticeShift x μ ∈ S.Om 0) (h2 : periodicLatticeShift x ν ∈ S.Om 0)
    (h3 : periodicLatticeShift (periodicLatticeShift x μ) ν ∈ S.Om 0)
    (hc : periodicLatticeShift (periodicLatticeShift x μ) ν = periodicLatticeShift (periodicLatticeShift x ν) μ)
    (γ : PeriodicLatticeSite L → SU2) :
    frobNorm (((plq U γ x μ ν : SU2) : M2) - 1) ≤ 4 * ((12 : ℝ) * M * α₀) := by
  have _hR : R = R := rfl
  set P : PeriodicLatticePlaquette L := (x, ⟨(μ, ν), hμν⟩) with hPdef
  have hedge : ∀ e ∈ periodicPlaquetteBoundaryEdges P, CubeBond (S.Om 0) e := by
    intro e he
    simp only [periodicPlaquetteBoundaryEdges, hPdef, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact ⟨h0, h1⟩
    · exact ⟨h1, h3⟩
    · exact ⟨h2, hc ▸ h3⟩
    · exact ⟨h0, h2⟩
  obtain ⟨sites, i, hq, hall⟩ := hcov.2 P hedge
  have hX0 : 0 ≤ (12 : ℝ) * M * α₀ := by positivity
  have hli : ((ell : ℝ) ^ i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast hell))
  have hli0 : 0 ≤ ((ell : ℝ) ^ i)⁻¹ := by positivity
  have ht : ((12 : ℕ) : ℝ) * M * α₀ * ((ell : ℝ) ^ i)⁻¹ ≤ (12 : ℝ) * M * α₀ := by
    push_cast; nlinarith
  have hsm : ((12 : ℕ) : ℝ) * M * α₀ * ((ell : ℝ) ^ i)⁻¹ + ((12 : ℕ) : ℝ) * M * α₀ * (((ell : ℝ) ^ i)⁻¹) ^ 2 ≤ 1 := by
    push_cast
    have : ((ell : ℝ) ^ i)⁻¹ ^ 2 ≤ 1 := by nlinarith
    nlinarith
  obtain ⟨gc, hgc⟩ := gchart_of_cubeHΦ hη hP hq hsm hell
  have eb : ∀ e ∈ periodicPlaquetteBoundaryEdges P,
      frobNorm (((periodicGaugeTransform gc U e : SU2) : M2) - 1) ≤ (12 : ℝ) * M * α₀ := by
    intro e he
    obtain ⟨a, b⟩ := hall e he
    exact (hgc.1 e.1 e.2 a b).trans ht
  have m : ∀ y τ, (y, τ) ∈ periodicPlaquetteBoundaryEdges P →
      frobNorm (((periodicGaugeTransform gc U (y, τ) : SU2) : M2) - 1) ≤ (12 : ℝ) * M * α₀ := fun y τ h => eb _ h
  have e1 := m x μ (by simp [periodicPlaquetteBoundaryEdges, hPdef])
  have e2 := m (periodicLatticeShift x μ) ν (by simp [periodicPlaquetteBoundaryEdges, hPdef])
  have e3 := m (periodicLatticeShift x ν) μ (by simp [periodicPlaquetteBoundaryEdges, hPdef])
  have e4 := m x ν (by simp [periodicPlaquetteBoundaryEdges, hPdef])
  have h4 := plq_le_four U gc x μ ν
  rw [plq_conj U γ gc x μ ν hc, frobNorm_conj_sub_one]
  linarith

end MXQ.M2BallCharts

