import NsCvOX2

/-!
# CvON1 -- generic-in-`t` reduction of `NearUnitsRest` (lane omega/near)

Pure analysis: a real-analytic `D` on `(-T, T)` (`0 < T <= π`) that is nonzero at one point has isolated zeros, so it is nonzero at
points `t` with `cos t` in `(cs, cs + eps)` for every `eps > 0` (`-1 < cs < 1`).

`AnUnits`: the five non-automatic units hold at every `t` where an analytic proxy `D` is nonzero, and `D` is nonzero somewhere.
`nearUnitsRest_of_anUnits`: `AnUnits` gives `NearUnitsRest`.  `not_WDH_of_anUnits`: `AnUnits` for infinitely many `(m, R)` refutes
`P428Target8NCWDH`.  NOTHING here proves `AnUnits` for the genuine family.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace Topology
open Filter Set
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.NcwdhStrong
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2

/-- an analytic function nonzero at one point of `(-T, T)` (`0 < T ≤ π`) is nonzero at points with `cos t` just above `cs`
(`cos T < cs < 1`). -/
theorem exists_nonzero_near_cos (T : ℝ) (hT0 : 0 < T) (hTπ : T ≤ Real.pi) (D : ℝ → ℝ) (hD : AnalyticOnNhd ℝ D (Ioo (-T) T))
    (t0 : ℝ) (ht0 : t0 ∈ Ioo (-T) T) (hD0 : D t0 ≠ 0) (cs : ℝ) (hcs1 : Real.cos T < cs) (hcs2 : cs < 1) :
    ∀ ε : ℝ, 0 < ε → ∃ t : ℝ, |t| < T ∧ cs < Real.cos t ∧ Real.cos t < cs + ε ∧ D t ≠ 0 := by
  intro ε hε
  have hcs1' : -1 < cs := lt_of_le_of_lt (Real.neg_one_le_cos T) hcs1
  set s := Real.arccos cs with hs
  have hs0 : 0 < s := Real.arccos_pos.mpr hcs2
  have hsπ : s < Real.pi := Real.arccos_lt_pi.mpr hcs1'
  have hcos : Real.cos s = cs := Real.cos_arccos hcs1'.le hcs2.le
  have hsT : s < T := by
    by_contra hcon
    push Not at hcon
    have := Real.strictAntiOn_cos.antitoneOn ⟨hT0.le, hTπ⟩ ⟨hs0.le, hsπ.le⟩ hcon
    rw [hcos] at this
    linarith
  have hsmem : s ∈ Ioo (-T) T := ⟨by linarith, hsT⟩
  have han : AnalyticAt ℝ D s := hD s hsmem
  rcases han.eventually_eq_zero_or_eventually_ne_zero with hz | hnz
  · exfalso
    have := hD.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Ioo hsmem hz
    exact hD0 (this ht0)
  · -- left neighbourhood of s
    have h1 : ∀ᶠ t in 𝓝[<] s, D t ≠ 0 := hnz.filter_mono (nhdsWithin_mono s (fun x (hx : x < s) => ne_of_lt hx))
    have h2 : ∀ᶠ t in 𝓝[<] s, Real.cos t < cs + ε := by
      have hc : ContinuousAt Real.cos s := Real.continuous_cos.continuousAt
      have : ∀ᶠ t in 𝓝 s, Real.cos t < cs + ε := hc.eventually (gt_mem_nhds (by rw [hcos]; linarith))
      exact nhdsWithin_le_nhds this
    have h3 : ∀ᶠ t in 𝓝[<] s, 0 < t ∧ t < s := by
      refine Filter.Eventually.and ?_ self_mem_nhdsWithin
      have : ∀ᶠ t in 𝓝 s, 0 < t := lt_mem_nhds hs0
      exact nhdsWithin_le_nhds this
    obtain ⟨t, ht1, ht2, ⟨ht3, ht4⟩⟩ := (h1.and (h2.and h3)).exists
    refine ⟨t, ?_, ?_, ht2, ht1⟩
    · rw [abs_lt]; constructor <;> linarith
    · rw [← hcos]
      exact Real.strictAntiOn_cos ⟨ht3.le, by linarith⟩ ⟨hs0.le, hsπ.le⟩ ht4

/-- two analytic functions on an interval, each nonzero somewhere, have a product nonzero somewhere. -/
theorem exists_mul_ne_zero {T : ℝ} {f g : ℝ → ℝ} (hf : AnalyticOnNhd ℝ f (Ioo (-T) T)) (hg : AnalyticOnNhd ℝ g (Ioo (-T) T))
    {t0 t1 : ℝ} (h0 : t0 ∈ Ioo (-T) T) (h1 : t1 ∈ Ioo (-T) T) (hf0 : f t0 ≠ 0) (hg1 : g t1 ≠ 0) :
    ∃ t ∈ Ioo (-T) T, f t * g t ≠ 0 := by
  by_contra H
  push Not at H
  have hfn : ∀ᶠ t in 𝓝 t0, f t ≠ 0 := (hf t0 h0).continuousAt.eventually_ne hf0
  have hmem : ∀ᶠ t in 𝓝 t0, t ∈ Ioo (-T) T := isOpen_Ioo.mem_nhds h0
  have hgz : g =ᶠ[𝓝 t0] 0 := by
    filter_upwards [hfn, hmem] with t ht1 ht2
    have := H t ht2
    exact (mul_eq_zero.mp this).resolve_left ht1
  have := hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Ioo h0 hgz
  exact hg1 (this h1)

#print axioms exists_nonzero_near_cos

end AdalyFormal.CoverOmega
