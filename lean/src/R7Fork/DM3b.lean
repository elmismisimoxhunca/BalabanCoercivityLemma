import R7Fork.DM3a

/-!
# DM3b -- the window of a unit plaquette whose unit box lies in `Omega_k` lies in `plaqIn Omega_0`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000
namespace AdalyFormal.DirichletMono

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)

theorem scaleUp_ge_one (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (hu : ∀ ρ, 1 ≤ Lu ρ)
    (ρ : Fin 3) : 1 ≤ scaleUp ell k Lu ρ := by
  have h := scaleUp_succ ell k Lu hell ρ
  have h1 : 1 ≤ ell ^ k := Nat.one_le_pow _ _ hell
  have h2 : 2 ≤ (Lu ρ + 1) * ell ^ k := by
    have := hu ρ
    nlinarith
  omega

theorem window_plaqIn {ell M R k : ℕ} (hell : 0 < ell) {Lu : PeriodicLatticeExtent} (hu : ∀ ρ, 1 ≤ Lu ρ)
    {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S)
    (z : PeriodicLatticeSite Lu) (hgood : ∀ c, InBox z c → embY ell k Lu hell c ∈ S.Om k)
    (d : PeriodicPlaquetteDirections) (x : PeriodicLatticeSite (scaleUp ell k Lu))
    (hx : x ∈ blockOf (embY ell k Lu hell z) (ell ^ k)) (i j : ℕ) (hi : i < ell ^ k) (hj : j < ell ^ k) :
    (coarseShift (coarseShift x j d.1.2) i d.1.1, d) ∈ plaqIn (S.Om 0) := by
  have hN := scaleUp_ge_one ell k Lu hell hu
  have hμν : d.1.1 ≠ d.1.2 := ne_of_lt d.2
  have hxN := nearCell_of_block hell z x hx
  have hclosed : BlockClosed (bigSide M ell k) (S.Om k) := hS.2.2.2.1 k le_rfl
  have key : ∀ w, ReachP ell k Lu d.1.1 d.1.2 (ell ^ k) (ell ^ k) x w → w ∈ S.Om 0 := by
    intro w hw
    obtain ⟨c, hc, hwc⟩ := box_of_reach hell hu z hxN hw
    have h1 : w ∈ S.Om k := mem_of_nearCell hell _ hclosed c (hgood c hc) w hwc
    exact om_k_sub_om0 S hS.1 k h1
  have r0 := reach_refl (ell := ell) (k := k) (Lu := Lu) d.1.1 d.1.2 0 0 x
  have r1 := reach_coarse_nu hμν hN r0 j
  have r2 := reach_coarse_mu hN r1 i
  set w0 := coarseShift (coarseShift x j d.1.2) i d.1.1 with hw0
  have hle : ∀ a b : ℕ, a ≤ ell ^ k → b ≤ ell ^ k →
      ∀ w, ReachP ell k Lu d.1.1 d.1.2 a b x w → w ∈ S.Om 0 :=
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

#print axioms window_plaqIn

end AdalyFormal.DirichletMono
