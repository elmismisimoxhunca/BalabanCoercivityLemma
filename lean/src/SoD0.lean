import SoGeo
import NuD0b

/-!
# SoD0 -- the direction-0 staggered family at the decoupled centre lies in the per-cube class of factor `c` (lane sites_only_20261019)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.SitesOnly

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.CoverNested
open AdalyFormal.NcwdhTwo
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.NoCover (perCube_one)

/-- **the direction-0 staggered family at `soC ell M R c` is in the factor-`c` class, for every `t`, `α₀ > 0`.** -/
theorem so_stag0_class [CfData] {ell M R c : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) (hrel : SoRel ell c) (hc : 10 ≤ c)
    (t : ℝ) {α₀ : ℝ} (hα : 0 < α₀) :
    PerCubeRegular2 ell M c 2 (neS ell M R) α₀ ((ell : ℝ) ^ 2)⁻¹
      (stag0Cfg (L := scaleUp ell 2 (neLu M R)) (soC ell M R c) t) := by
  have hell0 : 0 < ell := by omega
  have hη : (0 : ℝ) < ((ell : ℝ) ^ 2)⁻¹ := by
    have : (0 : ℝ) < ell := by exact_mod_cast hell0
    positivity
  refine perCube_congr' (perCube_one hell0 hM (by omega) hα hη) (fun e he => ?_)
  obtain ⟨sites, j, hq, hb⟩ := he
  by_cases h0 : (e.1 0).val = soC ell M R c ∧ e.2 = 0
  · obtain ⟨hx, he2⟩ := h0
    exfalso
    have hb' := hb
    obtain ⟨e1, e2⟩ := e
    simp only at hx he2
    subst he2
    exact so_bond_uncovered hell hM hR hrel (by omega) e1 hx sites j hq hb'
  · simp [stag0Cfg, h0]

#print axioms so_stag0_class

end AdalyFormal.SitesOnly
