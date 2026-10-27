import NuD0a

/-!
# NuD0b -- the direction-0 staggered family lies in the per-cube class (lane ncwdh_ell2_20261018)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.NcwdhTwo

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.CoverNested
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.NoCover (perCube_one)

/-- the class reads `U` only on cube bonds (both endpoints in a class cube). -/
theorem perCube_congr' {L : PeriodicLatticeExtent} {ell M f k : ℕ} {S : Tower L} {α₀ η : ℝ} {U U' : LinkCfg L}
    (h : PerCubeRegular2 ell M f k S α₀ η U)
    (hUU : ∀ e : Bond L, (∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ),
        IsClassCube ell M f k S sites j ∧ CubeBond sites e) → U' e = U e) :
    PerCubeRegular2 ell M f k S α₀ η U' := by
  intro sites j hq
  obtain ⟨g, A, h1, h2, h3⟩ := h sites j hq
  refine ⟨g, A, fun e he => ?_, h2, h3⟩
  have : periodicGaugeTransform g U' e = periodicGaugeTransform g U e := by
    simp only [periodicGaugeTransform, hUU e ⟨sites, j, hq, he⟩]
  rw [this]
  exact h1 e he

/-- **the direction-0 staggered family is in the factor-`cf` class at `ell = 2`, for every `t`, `α₀ > 0`.** -/
theorem stag0_class [CfData] {M R : ℕ} (hM : 0 < M) (hR : 1 ≤ R) (t : ℝ) {α₀ : ℝ} (hα : 0 < α₀) :
    PerCubeRegular2 2 M CfData.cf 2 (neS 2 M R) α₀ (((2 : ℕ) : ℝ) ^ 2)⁻¹
      (stag0Cfg (L := scaleUp 2 2 (neLu M R)) (neC0 2 M R) t) := by
  have hη : (0 : ℝ) < (((2 : ℕ) : ℝ) ^ 2)⁻¹ := by norm_num
  have hcf := CfData.hcf
  refine perCube_congr' (perCube_one (by norm_num) hM (by omega) hα hη) (fun e he => ?_)
  obtain ⟨sites, j, hq, hb⟩ := he
  by_cases h0 : (e.1 0).val = neC0 2 M R ∧ e.2 = 0
  · obtain ⟨hx, he2⟩ := h0
    exfalso
    have hb' := hb
    obtain ⟨e1, e2⟩ := e
    simp only at hx he2
    subst he2
    exact ne2_bond_uncovered hM hR e1 hx sites j hq hb'
  · simp [stag0Cfg, h0]

end AdalyFormal.NcwdhTwo
