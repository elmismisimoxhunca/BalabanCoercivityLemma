import SoCov5
import SoA1
import CsA2

/-!
# SoA3 -- on the decoupled tower site coverage holds and plaquette coverage fails, at EVERY `ell >= 2` (odd `ell` included) (lane sites_only_20261019)

`not_covPlaqF_S`          : the central direction-0 bond `(soC, soC+1)` of `neS ell M R` lies in no class cube of factor `c`, hence the `(0,1)`-plaquette through it is covered by no class cube: `¬ CovPlaqF`.
`sites_not_imp_plaq_S`    : `CovSitesF ∧ ¬ CovPlaqF` on `neS ell M R` for the constant family `constFam c`, `ell ≥ 2`, `c ≥ 10`, `10 ≤ w`, `ell (w-1) = 2 (c-1)`, `c ≤ R` -- the converse of
`CovSplit.covPlaqF_imp_covSitesF` fails at these (c, ell), also for odd `ell` (where the analytic refutation `not_familyTorusSitesConstAt_S` is not built).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.SitesOnly

open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.NonVac (mem_box_N shift_val_N)
open MXQ.AllC
open NcwdhFam

section
variable [CfData]

theorem om0_of_val_S {ell M R c : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) (hrel : SoRel ell c) (hc : 10 ≤ c)
    (y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)))
    (hy : (y 0).val = soC ell M R c ∨ (y 0).val = soC ell M R c + 1) : y ∈ (neS ell M R).Om 0 := by
  have hCp := cpos_soC hell hM hR hrel hc
  have h1 := hCp.hge
  have h2 := hCp.hlt
  rw [neS_om0]
  omega

theorem not_covPlaqF_S {ell M R c : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hR1 : 1 ≤ R) (hrel : SoRel ell c) (hc : 10 ≤ c) :
    ¬ CovPlaqF ell M (constFam c (scaleUp ell 2 (neLu M R))) 2 (neS ell M R) := by
  intro hcov
  have hell0 : 0 < ell := by omega
  have hN := ne_scaleUp (ell := ell) (R := R) hell0 hM
  have hCp := cpos_soC hell hM hR1 hrel hc
  have hCN : soC ell M R c + 1 < neN ell M R := by
    have := hCp.hlt
    have := AdalyFormal.NcwdhTwo.ne_QN_two hell hM hR1
    omega
  have hN1 : 1 < neN ell M R := by omega
  let x : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)) :=
    fun μ => ⟨if μ = 0 then soC ell M R c else 0, by have := hN μ; split_ifs <;> omega⟩
  have hx0 : (x 0).val = soC ell M R c := by simp [x]
  have hv : ∀ (y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R))) (μ : Fin 3),
      ((periodicLatticeShift y μ) 0).val = if (0 : Fin 3) = μ then ((y 0).val + 1) % neN ell M R else (y 0).val :=
    fun y μ => shift_val_N hN hN1 y μ 0
  have hv0 : ∀ y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)), (y 0).val = soC ell M R c →
      ((periodicLatticeShift y 0) 0).val = soC ell M R c + 1 := by
    intro y hy
    rw [hv, if_pos rfl, hy]; exact Nat.mod_eq_of_lt hCN
  have hvn : ∀ (y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R))) (μ : Fin 3), μ ≠ 0 →
      ((periodicLatticeShift y μ) 0).val = (y 0).val := by
    intro y μ hμ
    rw [hv, if_neg (fun h => hμ h.symm)]
  have h1 : (1 : Fin 3) ≠ 0 := by decide
  have hx0' := hv0 x hx0
  have hx1 := hvn x 1 h1
  have h01 : ((0 : Fin 3), (1 : Fin 3)).1 < ((0 : Fin 3), (1 : Fin 3)).2 := by decide
  have hp := hcov (x, ⟨((0 : Fin 3), (1 : Fin 3)), h01⟩) (by
    intro e he
    simp only [periodicPlaquetteBoundaryEdges, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact ⟨om0_of_val_S hell hM hR1 hrel hc _ (Or.inl hx0), om0_of_val_S hell hM hR1 hrel hc _ (Or.inr hx0')⟩
    · refine ⟨om0_of_val_S hell hM hR1 hrel hc _ (Or.inr hx0'), om0_of_val_S hell hM hR1 hrel hc _ (Or.inr ?_)⟩
      rw [hvn _ 1 h1]; exact hx0'
    · refine ⟨om0_of_val_S hell hM hR1 hrel hc _ (Or.inl ?_), om0_of_val_S hell hM hR1 hrel hc _ (Or.inr ?_)⟩
      · rw [hx1]; exact hx0
      · rw [hv0 _ (by rw [hx1]; exact hx0)]
    · exact ⟨om0_of_val_S hell hM hR1 hrel hc _ (Or.inl hx0), om0_of_val_S hell hM hR1 hrel hc _ (Or.inl (by rw [hx1]; exact hx0))⟩)
  obtain ⟨sites, j, ⟨f, hmem, hq⟩, hcb⟩ := hp
  have hf : f = c := mem_constFam.1 hmem
  rw [hf] at hq
  have hb := hcb (x, 0) (by simp [periodicPlaquetteBoundaryEdges])
  exact so_bond_uncovered hell hM hR1 hrel (by omega) x hx0 sites j hq hb

/-- on the decoupled tower site coverage holds and plaquette coverage fails (any `ell ≥ 2`). -/
theorem sites_not_imp_plaq_S {ell M R c : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hR1 : 1 ≤ R) (hrel : SoRel ell c) (hc : 10 ≤ c) (hRc : c ≤ R) :
    CovSitesF ell M (constFam c (scaleUp ell 2 (neLu M R))) 2 (neS ell M R) ∧
      ¬ CovPlaqF ell M (constFam c (scaleUp ell 2 (neLu M R))) 2 (neS ell M R) :=
  ⟨covSitesF_so hell hM hR1 hrel hc hRc, not_covPlaqF_S hell hM hR1 hrel hc⟩

end

#print axioms not_covPlaqF_S
#print axioms sites_not_imp_plaq_S

end AdalyFormal.SitesOnly
