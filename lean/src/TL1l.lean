import TL1k

set_option autoImplicit false
namespace AdalyFormal.Thin
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)

/-- lifted bond field -/
def liftA {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ) :
    Bond Lt → Matrix (Fin 2) (Fin 2) ℂ := fun e => A (projE h e)

theorem cubeBond_lift {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) {zt : PeriodicLatticeSite Lt} {s : ℕ}
    {e : Bond Lt} (he : CubeBond (siteBox zt s) e) : CubeBond (siteBox (projS h zt) s) (projE h e) := by
  refine ⟨box_proj_subset h zt _ s he.1, ?_⟩
  have := box_proj_subset h zt _ s he.2
  rw [projE_shift] at this
  exact this

theorem curlReads_lift {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) {zt : PeriodicLatticeSite Lt} {s : ℕ}
    {x : PeriodicLatticeSite Lt} {a b : Fin 3} (hr : CurlReads (siteBox zt s) x a b) :
    CurlReads (siteBox (projS h zt) s) (projS h x) a b := by
  obtain ⟨h1, h2, h3, h4⟩ := hr
  have e1 := cubeBond_lift h h1
  have e2 := cubeBond_lift h h2
  have e3 := cubeBond_lift h h3
  have e4 := cubeBond_lift h h4
  simp only [projE, projS_shift] at e1 e2 e3 e4
  exact ⟨e1, e2, e3, e4⟩

theorem curlA_lift {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (η : ℝ)
    (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ) (x : PeriodicLatticeSite Lt) (a b : Fin 3) :
    curlA η (liftA h A) x a b = curlA η A (projS h x) a b := by
  unfold curlA liftA projE
  simp only [projS_shift]

theorem ddA_lift {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (η : ℝ)
    (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ) (x : PeriodicLatticeSite Lt) (μ : Fin 3) :
    ddA η (liftA h A) x μ = ddA η A (projS h x) μ := by
  unfold ddA
  simp only [curlA_lift, projS_shiftBack]

theorem perCube_lift {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) {ell M R f k : ℕ} {S : Tower L}
    {α₀ η : ℝ} {U : LinkCfg L} (hS : Admissible ell M R k S) (hU : PerCubeRegular2 ell M f k S α₀ η U) :
    PerCubeRegular2 ell M f k (liftTower h S) α₀ η (liftU h U) := by
  obtain ⟨hmono, -, hbd, -, -, -⟩ := hS
  intro Ct j hCt
  obtain ⟨hj, ⟨zt, hgrid, rfl⟩, hsub, ⟨y, hy1, hy2⟩⟩ := hCt.1
  set s := f * bigSide M ell j with hs
  have hgrid' : GridCorner (bigSide M ell j) (projS h zt) := by
    intro μ
    show (zt μ).val % (L μ + 1) % bigSide M ell j = 0
    rw [Nat.mod_mod_of_dvd _ (hbd j hj μ)]; exact hgrid μ
  have hdesc : DescribedAt ell M f k S (siteBox (projS h zt) s) j := by
    refine ⟨hj, ⟨_, hgrid', rfl⟩, fun x hx => ?_, ?_⟩
    · obtain ⟨xt, hxt, hxx⟩ := box_proj_surj h zt x s hx
      have := hsub hxt
      rw [← hxx]; exact this
    · exact ⟨projS h y, box_proj_subset h zt y s hy1, hy2⟩
  obtain ⟨g, A, hA1, hA2, hA3⟩ := hU _ j (isClassCube_of_described hmono hdesc)
  refine ⟨fun x => g (projS h x), liftA h A, fun e he => ?_, fun μ ν x hx1 hx2 => ?_, fun μ x hx => ?_⟩
  · obtain ⟨c1, c2, c3⟩ := hA1 (projE h e) (cubeBond_lift h he)
    refine ⟨c1, ?_, c3⟩
    rw [gauge_lift]; exact c2
  · have hx1' := cubeBond_lift h hx1
    have hx2' := cubeBond_lift h hx2
    simp only [projE, projS_shift] at hx1' hx2'
    have := hA2 μ ν (projS h x) hx1' hx2'
    simp only [liftA, projE, projS_shift]
    exact this
  · have := hA3 μ (projS h x) (fun ν hν => by
      have h1 := curlReads_lift h (hx ν hν).1
      have h2 := curlReads_lift h (hx ν hν).2
      rw [projS_shiftBack] at h1
      exact ⟨h1, h2⟩)
    rw [ddA_lift]; exact this

end AdalyFormal.Thin
