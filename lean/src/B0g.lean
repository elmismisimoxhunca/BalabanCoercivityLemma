import B0f

/-!
# B0g -- the B0 identity for the genuine composite jet: `Q_j(U) D_U λ` is the coarse gradient of the level-`j` jet

Along the gauge curve `gLam λ t = exp(tλ)` the coordinates `aC j t` of the level-`j` pure-gauge fluctuation satisfy
* `hasDerivAt_aC`: `d/dt aC j t|₀ = (c ↦ fromM2 (dG j c₋ - Ū^j_c dG j c₊ (Ū^j_c)ᴴ))`, `c₊ = coarseShift c₋ (ell^j) c.2`;
* `qCompX_aC_eventually`: `qCompX ell bg j (aC 0 t) = aC j t` for `t` near `0` (no link equals `-1`);
* `QlinCompX_pureGauge` (chain rule + uniqueness of derivatives; needs `RegTower` for differentiability of `qCompX`):
  `QlinCompX ell bg j (aC'_0) = aC'_j`, i.e. the first-order jet of the genuine composite raw map maps the
  pure-gauge direction `-(D_U λ)` to the coarse pure-gauge direction `-(D̄ dG_j)`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.SliceCoerc

open scoped Matrix Matrix.Norms.Frobenius
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp su2Log su2Exp M2 SU2 su2Log_one su2NegOne mul_star_self)
open AdalyFormal.Balaban.CovariantOperators (SuTwo suTwo mem_suTwo_iff)
open AdalyFormal.Balaban.UbarTowerCov (UbarTower)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open Filter Topology

variable {L : PeriodicLatticeExtent}

/-- jet of `su2Log (a t · H · (b t)⁻¹ · H⁻¹)` at `t = 0` (`a 0 = b 0 = 1`). -/
theorem hasDerivAt_conjLoop (a b : ℝ → SU2) (H : SU2) (va vb : M2)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1) (ha : HasDerivAt (fun t => (a t : M2)) va 0)
    (hb : HasDerivAt (fun t => (b t : M2)) vb 0) (hvb : vbᴴ = -vb) :
    HasDerivAt (fun t => su2Log (a t * H * (b t)⁻¹ * H⁻¹)) (va - (H : M2) * vb * (H : M2)ᴴ) 0 := by
  apply hasDerivAt_su2Log_comp (fun t => a t * H * (b t)⁻¹ * H⁻¹)
  · have hbs : HasDerivAt (fun t => ((b t : SU2) : M2)ᴴ) vbᴴ 0 := by
      have := hb.star; exact this
    have h1 := ((ha.fun_mul (hasDerivAt_const (0 : ℝ) (H : M2))).fun_mul hbs).fun_mul
      (hasDerivAt_const (0 : ℝ) ((H : M2)ᴴ))
    have hHH : (H : M2) * (H : M2)ᴴ = 1 := mul_star_self H
    refine h1.congr_deriv ?_
    rw [ha0, hb0, hvb]
    simp only [OneMemClass.coe_one, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, mul_zero,
      add_zero]
    rw [add_mul, Matrix.mul_assoc va, hHH, Matrix.mul_one]
    noncomm_ring
  · rw [ha0, hb0]; group

theorem aC_zero (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L)
    (lam : PeriodicLatticeSite L → SuTwo) (j : ℕ) : aC ell bg (gLam lam 0) j = 0 := by
  have h0 := (gT_jets ell bg lam j).1
  funext e
  simp only [aC, pgV, h0]
  simp

theorem hasDerivAt_aC (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L)
    (lam : PeriodicLatticeSite L → SuTwo) (j : ℕ) :
    HasDerivAt (fun t => aC ell bg (gLam lam t) j)
      (fun c => fromM2 (dG ell bg lam j c.1 - ((bg j c : SU2) : M2)
        * dG ell bg lam j (coarseShift c.1 (ell ^ j) c.2) * ((bg j c : SU2) : M2)ᴴ)) 0 := by
  obtain ⟨h0, hd⟩ := gT_jets ell bg lam j
  rw [hasDerivAt_pi]
  intro c
  have hah := antiHerm_of_hasDerivAt (fun t => gT ell bg (gLam lam t) j (coarseShift c.1 (ell ^ j) c.2)) _
    (hd _) (h0 _)
  have hl := hasDerivAt_conjLoop (fun t => gT ell bg (gLam lam t) j c.1)
    (fun t => gT ell bg (gLam lam t) j (coarseShift c.1 (ell ^ j) c.2)) (bg j c) _ _ (h0 _) (h0 _)
    (hd _) (hd _) hah
  exact fromM2L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl

theorem eventually_ne_negOne (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L)
    (lam : PeriodicLatticeSite L → SuTwo) (j : ℕ) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i : Fin j, ∀ e, pgV (ell ^ (i : ℕ)) (bg i) (gT ell bg (gLam lam t) i) e ≠ su2NegOne := by
  rw [Filter.eventually_all]; intro i
  rw [Filter.eventually_all]; intro e
  obtain ⟨h0, hd⟩ := gT_jets ell bg lam i
  have hc1 := (hd e.1).continuousAt
  have hc2 := (hd (coarseShift e.1 (ell ^ (i : ℕ)) e.2)).continuousAt
  have hcont : ContinuousAt (fun t => ((pgV (ell ^ (i : ℕ)) (bg i) (gT ell bg (gLam lam t) i) e : SU2) : M2)) 0 := by
    have hs := hc2.star
    exact ((hc1.mul continuousAt_const).mul hs).mul continuousAt_const
  have hval : ((pgV (ell ^ (i : ℕ)) (bg i) (gT ell bg (gLam lam 0) i) e : SU2) : M2) = 1 := by
    simp only [pgV, h0]; simp
  have hne : (1 : M2) ≠ ((su2NegOne : SU2) : M2) := by
    intro h
    have := congrFun (congrFun h 0) 0
    simp [su2NegOne] at this
    norm_num at this
  have hopen : {M : M2 | M ≠ ((su2NegOne : SU2) : M2)}
      ∈ 𝓝 (((pgV (ell ^ (i : ℕ)) (bg i) (gT ell bg (gLam lam 0) i) e : SU2) : M2)) := by
    rw [hval]; exact isOpen_ne.mem_nhds hne
  filter_upwards [hcont.preimage_mem_nhds hopen] with t ht h
  exact ht (congrArg Subtype.val h)

theorem qCompX_aC_eventually (ell : ℕ) (U : PeriodicLinkConfiguration SU2 L)
    (lam : PeriodicLatticeSite L → SuTwo) (j : ℕ) :
    (fun t => qCompX ell (UbarTower su2LogExp ell U) j (aC ell (UbarTower su2LogExp ell U) (gLam lam t) 0))
      =ᶠ[𝓝 0] fun t => aC ell (UbarTower su2LogExp ell U) (gLam lam t) j := by
  filter_upwards [eventually_ne_negOne ell (UbarTower su2LogExp ell U) lam j] with t ht
  exact qCompX_aC ell U (gLam lam t) j (fun i hi e => ht ⟨i, hi⟩ e)

/-- **B0, jet form.** -/
theorem QlinCompX_pureGauge (ell : ℕ) (U : PeriodicLinkConfiguration SU2 L)
    (lam : PeriodicLatticeSite L → SuTwo) (J : ℕ) (hreg : RegTower ell (UbarTower su2LogExp ell U) J)
    (j : ℕ) (hj : j ≤ J) :
    QlinCompX ell (UbarTower su2LogExp ell U) j
        (fun c => fromM2 (dG ell (UbarTower su2LogExp ell U) lam 0 c.1
          - ((UbarTower su2LogExp ell U 0 c : SU2) : M2)
            * dG ell (UbarTower su2LogExp ell U) lam 0 (coarseShift c.1 (ell ^ 0) c.2)
            * ((UbarTower su2LogExp ell U 0 c : SU2) : M2)ᴴ))
      = fun c => fromM2 (dG ell (UbarTower su2LogExp ell U) lam j c.1
          - ((UbarTower su2LogExp ell U j c : SU2) : M2)
            * dG ell (UbarTower su2LogExp ell U) lam j (coarseShift c.1 (ell ^ j) c.2)
            * ((UbarTower su2LogExp ell U j c : SU2) : M2)ᴴ) := by
  set bg := UbarTower su2LogExp ell U with hbg
  have hq : HasFDerivAt (qCompX ell bg j) (QlinCompX ell bg j) 0 :=
    ((qCompX_contDiffAt ell bg J hreg j hj).differentiableAt (by simp)).hasFDerivAt
  have ha0 := hasDerivAt_aC ell bg lam 0
  have hcomp := hq.comp_hasDerivAt_of_eq (0 : ℝ) ha0 (aC_zero ell bg lam 0).symm
  have h1 := hcomp.congr_of_eventuallyEq (qCompX_aC_eventually ell U lam j).symm
  exact h1.unique (hasDerivAt_aC ell bg lam j)

#print axioms hasDerivAt_conjLoop
#print axioms aC_zero
#print axioms hasDerivAt_aC
#print axioms eventually_ne_negOne
#print axioms qCompX_aC_eventually
#print axioms QlinCompX_pureGauge

end AdalyFormal.SliceCoerc
