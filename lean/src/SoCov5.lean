import SoCov4

/-!
# SoCov5 -- the six cases assemble: `covSite_exists`, `covSitesF_so` (lane sites_only_20261019)
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
open MXQ.AllC
open NcwdhFam

section
variable [CfData]
local notation "cfv" => CfData.cf

theorem covSite_exists {ell M R c : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) (hrel : SoRel ell c) (hc : 10 ≤ c) (hRc : c ≤ R)
    (x : PeriodicLatticeSite (scaleUp ell 2 (neLu M R))) (hx : x ∈ (neS ell M R).Om 0) : CovEx ell M R c x := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin_two hell hM hR
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9⟩ := so_vals hell hM hR hrel hc
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩ := so_order hell hM hR hrel hc
  obtain ⟨hY1, cm1, e2, hcR, hc1, hc2⟩ := cov_arith (M := M) (R := R) hell hM hc hRc
  rw [neS_om0] at hx
  obtain ⟨hx1, hx2⟩ := hx
  by_cases c1 : (x 0).val < neP1 ell M R
  · exact cov_L0left hell hM hR hrel hc hRc x hx1 c1
  by_cases c6 : neQ1 ell M R ≤ (x 0).val
  · exact cov_L0right hell hM hR hrel hc hRc x c6 hx2
  by_cases th : neA' ell M R ≤ (x 0).val ∧ (x 0).val < neB' ell M R
  · by_cases hC : (x 0).val < neA' ell M R + (c - 1) * (ell * M)
    · exact cov_thinL hell hM hR hrel hc hRc x th.1 hC
    · exact cov_thinR hell hM hR hrel hc hRc x (by omega) th.2
  by_cases fat : neA ell M R ≤ (x 0).val ∧ (x 0).val < neB ell M R
  · exact cov_fat hell hM hR hrel hc hRc x fat.1 fat.2
  · exact cov_lev1 hell hM hR hrel hc hRc x (by omega) (by omega) th fat

/-- **site coverage on the decoupled nested tower** `neS ell M R` (thin width from the `CfData` instance, class factor `c`, `ell (cfv - 1) = 2 (c - 1)`), `ell ≥ 2`, `M > 0`, `c ≤ R`:
every site of `Ω₀` lies in a class cube of factor `c`.  Nothing is claimed for other admissible towers. -/
theorem covSitesF_so {ell M R c : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) (hrel : SoRel ell c) (hc : 10 ≤ c) (hRc : c ≤ R) :
    CovSitesF ell M (constFam c (scaleUp ell 2 (neLu M R))) 2 (neS ell M R) := by
  intro x hx
  obtain ⟨sites, j, hq, hxs⟩ := covSite_exists hell hM hR hrel hc hRc x hx
  exact ⟨sites, j, ⟨c, mem_constFam.2 rfl, hq⟩, hxs⟩


end

#print axioms covSitesF_so

end AdalyFormal.SitesOnly
