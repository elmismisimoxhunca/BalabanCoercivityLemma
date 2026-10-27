import NsPtG0

/-!
# PtG1 -- bonds of the nested tower: level-0 membership, vanishing off `Ω₁`, and the plaquette lemma (lane omega/near2/point)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)

variable {ell M R : ℕ}

theorem coarseShift_one' {L : PeriodicLatticeExtent} (y : PeriodicLatticeSite L) (μ : Fin 3) :
    coarseShift y 1 μ = periodicLatticeShift y μ := by
  unfold coarseShift
  simp

theorem bondsLam0_of (hg : NGeo ell M R) (hM : 0 < M) (b : Bond (scaleUp ell 2 (neLu M R)))
    (hO : b ∈ bondsOm0 (geomOf ell 2 (neS ell M R)))
    (h1 : ¬ Omv ell M R 1 (b.1 0).val) (h2 : ¬ Omv ell M R 1 ((periodicLatticeShift b.1 b.2) 0).val) :
    b ∈ bondsLam (geomOf ell 2 (neS ell M R)) 0 := by
  have hell : 0 < ell := by have := hg.hell; omega
  have hG : (geomOf ell 2 (neS ell M R)).ell = ell := rfl
  unfold bondsLam
  simp only [Set.mem_setOf_eq, hG, pow_zero]
  rw [coarseShift_one']
  rw [mem_Lam 0 b.1 ∅, mem_Lam 0 (periodicLatticeShift b.1 b.2) ∅, omGe_iff _ b.1 hell hM,
    omGe_iff _ (periodicLatticeShift b.1 b.2) hell hM, omGe0_1 hg, omGe0_1 hg]
  have hO' : Omv ell M R 0 (b.1 0).val ∨ Omv ell M R 0 ((periodicLatticeShift b.1 b.2) 0).val := by
    rcases hO with h | h
    · exact Or.inl ((Omv_site 0 _).mp h)
    · exact Or.inr ((Omv_site 0 _).mp h)
  have e1 : ¬ (neP1 ell M R ≤ (b.1 0).val ∧ (b.1 0).val < neQ1 ell M R) := h1
  have e2 : ¬ (neP1 ell M R ≤ ((periodicLatticeShift b.1 b.2) 0).val ∧ ((periodicLatticeShift b.1 b.2) 0).val < neQ1 ell M R) := h2
  refine ⟨?_, by tauto⟩
  rcases hO' with h | h
  · exact Or.inl ⟨fun _ => one_dvd _, h, h1⟩
  · exact Or.inr ⟨fun _ => one_dvd _, h, h2⟩


section curlflat
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2 curlCovariantCLM_L2_toLp)
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue curlCovariantLM_trivialU_eq_flatCurlLM)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 curlCovariantLM curlValueCovariant)

theorem curl_flat_apply {L : PeriodicLatticeExtent} (x : BondFnL2 L) (p : PeriodicLatticePlaquette L) :
    (curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) x) p
      = flatCurlValue (WithLp.ofLp x) p := by
  have hx : x = WithLp.toLp 2 (WithLp.ofLp x) := rfl
  rw [hx, curlCovariantCLM_L2_toLp]
  have hc : curlCovariantLM (trivialU L) (WithLp.ofLp x) = flatCurlValue (WithLp.ofLp x) := by
    rw [curlCovariantLM_trivialU_eq_flatCurlLM]; rfl
  have := congrFun hc p
  exact this

end curlflat

/-- arithmetic of the vertices of a plaquette: if a vertex lies in `Ω₁`, all vertices lie in `Ω₀`. -/
theorem vtx_arith (w0 s N p0 p1 q1 q0 : ℕ) (hw : w0 < N) (hN : q0 ≤ N) (hp0 : 1 ≤ p0)
    (h : s = w0 ∨ s = (w0 + 1) % N) (hs : p1 ≤ s ∧ s < q1) (hp : p0 + 2 ≤ p1) (hq : q1 + 2 ≤ q0) :
    ∀ t, (t = w0 ∨ t = (w0 + 1) % N) → p0 ≤ t ∧ t < q0 := by
  by_cases hlt : w0 + 1 < N
  · rw [Nat.mod_eq_of_lt hlt] at h ⊢
    intro t ht
    omega
  · have hN' : w0 + 1 = N := by omega
    have hz : (w0 + 1) % N = 0 := by rw [hN']; exact Nat.mod_self N
    rw [hz] at h ⊢
    intro t ht
    omega

end AdalyFormal.CoverOmega
