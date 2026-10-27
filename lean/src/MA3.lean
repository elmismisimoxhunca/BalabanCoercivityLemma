import FE3c
import FE5a

/-!
# MA3 -- Stokes on the good unit boxes (lane m1_assembly_20261014)

`local_unit_stokes_good`: for ANY fine field `A` and the unit field `Bf` = level-`n` average of `A`,
`n * sum_{q good} ||curl Bf q||^2 <= sum_{p in plaqIn (Omega_k)} ||curl A p||^2`, `q` good = unit box inside `Omega_k`.
(Adaptation of FE3c `local_unit_stokes`: no support hypothesis on `Bf`; the right side is over `plaqIn (S.Om k)`, so only
top-stratum bonds are read.)  `window_plaqIn_k` = FE3b `window_plaqIn` with conclusion `plaqIn (S.Om k)`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000
namespace AdalyFormal.FlatEllGeneral

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.GenuineU1
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf)
open AdalyFormal.Balaban.CoarseCurl (coarseShift CoarsePlaquette)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue)
open AdalyFormal.Balaban.ThirdLevelStokes (coarseCurlSuTwo)

theorem window_plaqIn_k {ell M R k : ℕ} (hell : 0 < ell) {Lu : PeriodicLatticeExtent} (hu : ∀ ρ, 1 ≤ Lu ρ)
    {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S)
    (z : PeriodicLatticeSite Lu) (hgood : ∀ c, InBox z c → embY ell k Lu hell c ∈ S.Om k)
    (d : PeriodicPlaquetteDirections) (x : PeriodicLatticeSite (scaleUp ell k Lu))
    (hx : x ∈ blockOf (embY ell k Lu hell z) (ell ^ k)) (i j : ℕ) (hi : i < ell ^ k) (hj : j < ell ^ k) :
    (coarseShift (coarseShift x j d.1.2) i d.1.1, d) ∈ plaqIn (S.Om k) := by
  have hN := scaleUp_ge_one ell k Lu hell hu
  have hμν : d.1.1 ≠ d.1.2 := ne_of_lt d.2
  have hxN := nearCell_of_block hell z x hx
  have hclosed : BlockClosed (bigSide M ell k) (S.Om k) := hS.2.2.2.1 k le_rfl
  have key : ∀ w, ReachP ell k Lu d.1.1 d.1.2 (ell ^ k) (ell ^ k) x w → w ∈ S.Om k := by
    intro w hw
    obtain ⟨c, hc, hwc⟩ := box_of_reach hell hu z hxN hw
    have h1 : w ∈ S.Om k := mem_of_nearCell hell _ hclosed c (hgood c hc) w hwc
    exact h1
  have r0 := reach_refl (ell := ell) (k := k) (Lu := Lu) d.1.1 d.1.2 0 0 x
  have r1 := reach_coarse_nu hμν hN r0 j
  have r2 := reach_coarse_mu hN r1 i
  set w0 := coarseShift (coarseShift x j d.1.2) i d.1.1 with hw0
  have hle : ∀ a b : ℕ, a ≤ ell ^ k → b ≤ ell ^ k →
      ∀ w, ReachP ell k Lu d.1.1 d.1.2 a b x w → w ∈ S.Om k :=
    fun a b ha hb w hw => key w (reach_mono ha hb hw)
  intro e he
  simp only [periodicPlaquetteBoundaryEdges, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact ⟨hle i j (by omega) (by omega) _ (by simpa using r2),
      hle (i + 1) j (by omega) (by omega) _ (by simpa using reach_shift_mu hN r2)⟩
  · exact ⟨hle (i + 1) j (by omega) (by omega) _ (by simpa using reach_shift_mu hN r2),
      hle (i + 1) (j + 1) (by omega) (by omega) _ (by simpa using reach_shift_nu hμν hN (reach_shift_mu hN r2))⟩
  · exact ⟨hle i (j + 1) (by omega) (by omega) _ (by simpa using reach_shift_nu hμν hN r2),
      hle (i + 1) (j + 1) (by omega) (by omega) _ (by simpa using reach_shift_mu hN (reach_shift_nu hμν hN r2))⟩
  · exact ⟨hle i j (by omega) (by omega) _ (by simpa using r2),
      hle i (j + 1) (by omega) (by omega) _ (by simpa using reach_shift_nu hμν hN r2)⟩


open Classical in
theorem local_unit_stokes_good {ell k : ℕ} (hell : 0 < ell) {Lu : PeriodicLatticeExtent} (hu : ∀ ρ, 1 ≤ Lu ρ)
    {M R : ℕ} {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S)
    (A : Bond (scaleUp ell k Lu) → SuTwo) :
    ((ell ^ k : ℕ) : ℝ) * ∑ q ∈ (Finset.univ : Finset (PeriodicLatticePlaquette Lu)).filter
        (fun q => ∀ c, InBox q.1 c → embY ell k Lu hell c ∈ S.Om k),
        ‖flatCurlValue (unitField ell k Lu hell (lineCoarseRestrictSuTwo (ell ^ k) A)) q‖ ^ 2
      ≤ ∑ p ∈ (Finset.univ : Finset (PeriodicLatticePlaquette (scaleUp ell k Lu))).filter
            (fun p => p ∈ plaqIn (S.Om k)), ‖flatCurlValue A p‖ ^ 2 := by
  classical
  set Qg : Finset (PeriodicLatticePlaquette Lu) := Finset.univ.filter
    (fun q => ∀ c, InBox q.1 c → embY ell k Lu hell c ∈ S.Om k) with hQg
  have hcurl : ∀ q ∈ Qg, flatCurlValue (unitField ell k Lu hell (lineCoarseRestrictSuTwo (ell ^ k) A)) q =
      coarseCurlSuTwo (scaleUp_tiling ell k Lu hell) (lineCoarseRestrictSuTwo (ell ^ k) A) (plaqE ell k Lu hell q) := by
    intro q _
    rw [← curl_reindex ell k Lu hell hu]
  have h1 : ∑ q ∈ Qg, ‖flatCurlValue (unitField ell k Lu hell (lineCoarseRestrictSuTwo (ell ^ k) A)) q‖ ^ 2 =
      ∑ q ∈ Qg, ‖coarseCurlSuTwo (scaleUp_tiling ell k Lu hell) (lineCoarseRestrictSuTwo (ell ^ k) A)
        (plaqE ell k Lu hell q)‖ ^ 2 :=
    Finset.sum_congr rfl (fun q hq => by rw [hcurl q hq])
  set Y : Finset (CoarsePlaquette (scaleUp ell k Lu) (ell ^ k)) :=
    Qg.map (plaqE ell k Lu hell).toEmbedding with hY
  have h2 : ∑ q ∈ Qg, ‖coarseCurlSuTwo (scaleUp_tiling ell k Lu hell) (lineCoarseRestrictSuTwo (ell ^ k) A)
        (plaqE ell k Lu hell q)‖ ^ 2 =
      ∑ p ∈ Y, ‖coarseCurlSuTwo (scaleUp_tiling ell k Lu hell) (lineCoarseRestrictSuTwo (ell ^ k) A) p‖ ^ 2 := by
    rw [hY, Finset.sum_map]; rfl
  rw [h1, h2]
  refine local_stokes_suTwo (pow_pos hell k) (scaleUp_tiling ell k Lu hell) A Y _ ?_
  intro p hp x hx i hi j hj
  obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hp
  have hg := (Finset.mem_filter.mp hq).2
  rw [Finset.mem_range] at hi hj
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  exact window_plaqIn_k hell hu hS q.1 hg q.2 x hx i j hi hj

end AdalyFormal.FlatEllGeneral

#print axioms AdalyFormal.FlatEllGeneral.window_plaqIn_k
#print axioms AdalyFormal.FlatEllGeneral.local_unit_stokes_good
