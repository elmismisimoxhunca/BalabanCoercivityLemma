import NuPtG1

/-!
# PtG2 -- kernel data: vanishing off `Ω₁`, global curl-freeness (lane omega/near2/point)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.CoverOmegaTwo
open AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)

section vertex
variable {L : PeriodicLatticeExtent}

theorem shift_x0 (z : PeriodicLatticeSite L) (μ : Fin 3) :
    ((periodicLatticeShift z μ) 0).val = if μ = 0 then ((z 0).val + 1) % (L 0 + 1) else (z 0).val := by
  by_cases h : μ = 0
  · subst h
    simp only [if_true]
    exact shift_val_self z 0
  · rw [if_neg h, shift_val_ne z μ 0 (Ne.symm h)]

/-- the `x₀` coordinates of the vertices of a plaquette. -/
theorem edge_vertex_x0 (p : PeriodicLatticePlaquette L) :
    ∀ e ∈ periodicPlaquetteBoundaryEdges p,
      (((e.1 0).val = (p.1 0).val ∨ (e.1 0).val = ((p.1 0).val + 1) % (L 0 + 1)) ∧
       (((periodicLatticeShift e.1 e.2) 0).val = (p.1 0).val ∨ ((periodicLatticeShift e.1 e.2) 0).val = ((p.1 0).val + 1) % (L 0 + 1))) := by
  obtain ⟨w, ⟨⟨μ, ν⟩, hlt⟩⟩ := p
  have hν : ν ≠ 0 := by
    intro h; subst h
    exact absurd hlt (by simp [Fin.not_lt_zero])
  intro e he
  simp only [periodicPlaquetteBoundaryEdges, Finset.mem_insert, Finset.mem_singleton] at he
  simp only
  rcases he with rfl | rfl | rfl | rfl <;>
    simp only [shift_x0, if_neg hν] <;>
    by_cases hμ : μ = 0 <;> simp [hμ, shift_x0, if_neg hν]

theorem edge_vertex_x0' (p : PeriodicLatticePlaquette L) (n : ℕ) (hn : L 0 + 1 = n) :
    ∀ e ∈ periodicPlaquetteBoundaryEdges p,
      (((e.1 0).val = (p.1 0).val ∨ (e.1 0).val = ((p.1 0).val + 1) % n) ∧
       (((periodicLatticeShift e.1 e.2) 0).val = (p.1 0).val ∨ ((periodicLatticeShift e.1 e.2) 0).val = ((p.1 0).val + 1) % n)) := by
  subst hn
  exact edge_vertex_x0 p

end vertex


variable {ell M R : ℕ}

/-- the kernel data of a bond field at the flat point of the nested instance. -/
structure KD (ell M R : ℕ) (x : BondFnL2 (scaleUp ell 2 (neLu M R))) : Prop where
  hs : ∀ b : Bond (scaleUp ell 2 (neLu M R)), b ∉ bondsOm0 (geomOf ell 2 (neS ell M R)) → x b = 0
  hQ : QfullOf (geomOf ell 2 (neS ell M R)) (flatCfg : Cfg (scaleUp ell 2 (neLu M R))) x = 0
  hc : AdalyFormal.StatementLaneR6.plaqMask (plaqIn (geomOf ell 2 (neS ell M R)).Om0)
        (curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell 2 (neLu M R))) x) = 0

theorem KD.zero_off1 {x : BondFnL2 (scaleUp ell 2 (neLu M R))} (hk : KD ell M R x) (hg : NGeo ell M R) (hM : 0 < M)
    (b : Bond (scaleUp ell 2 (neLu M R)))
    (h1 : ¬ Omv ell M R 1 (b.1 0).val) (h2 : ¬ Omv ell M R 1 ((periodicLatticeShift b.1 b.2) 0).val) : x b = 0 := by
  by_cases hO : b ∈ bondsOm0 (geomOf ell 2 (neS ell M R))
  · have hl := bondsLam0_of hg hM b hO h1 h2
    have := congrFun (congrArg WithLp.ofLp hk.hQ) ⟨(⟨0, Nat.succ_pos _⟩ : Fin ((geomOf ell 2 (neS ell M R)).k + 1)), ⟨b, hl⟩⟩
    have h0 : (QfullOf (geomOf ell 2 (neS ell M R)) (flatCfg : Cfg (scaleUp ell 2 (neLu M R))) x)
        ⟨(⟨0, Nat.succ_pos _⟩ : Fin ((geomOf ell 2 (neS ell M R)).k + 1)), ⟨b, hl⟩⟩ = 0 := by
      rw [hk.hQ]; rfl
    have e : (QfullOf (geomOf ell 2 (neS ell M R)) (flatCfg : Cfg (scaleUp ell 2 (neLu M R))) x)
        ⟨(⟨0, Nat.succ_pos _⟩ : Fin ((geomOf ell 2 (neS ell M R)).k + 1)), ⟨b, hl⟩⟩ = x b := by
      show (((((geomOf ell 2 (neS ell M R)).ell : ℝ) ^ (0 : ℕ))⁻¹) • (WithLp.ofLp (QlinB (geomOf ell 2 (neS ell M R))
        (flatCfg : Cfg (scaleUp ell 2 (neLu M R))) 0 x)) b) = x b
      rw [QlinB_zero]; simp
    rw [← e]; exact h0
  · exact hk.hs b hO

/-- a plaquette having an edge that touches `Ω₁` is a plaquette of `Ω₀`. -/
theorem plaq_of_touch (hP : PGeo ell M R) (p : PeriodicLatticePlaquette (scaleUp ell 2 (neLu M R)))
    (e0 : Bond (scaleUp ell 2 (neLu M R))) (he0 : e0 ∈ periodicPlaquetteBoundaryEdges p)
    (ht : Omv ell M R 1 (e0.1 0).val ∨ Omv ell M R 1 ((periodicLatticeShift e0.1 e0.2) 0).val) :
    p ∈ plaqIn (geomOf ell 2 (neS ell M R)).Om0 := by
  intro e he
  have hN : scaleUp ell 2 (neLu M R) 0 + 1 = neN ell M R := ne_scaleUp (by have := hP.hell; omega) hP.hM 0
  have hw : (p.1 0).val < neN ell M R := by rw [← hN]; exact (p.1 0).isLt
  have hv := edge_vertex_x0' p (neN ell M R) hN
  obtain ⟨a1, a2⟩ := hv e0 he0
  obtain ⟨b1, b2⟩ := hv e he
  have hp : neP0 ell M R + 2 ≤ neP1 ell M R := by have := hP.collar_p; have := hP.rm2; omega
  have hq : neQ1 ell M R + 2 ≤ neQ0 ell M R := by have := hP.collar_q; have := hP.rm2; omega
  have hqN : neQ0 ell M R ≤ neN ell M R := by have := hP.hqN; omega
  refine ⟨(Omv_site 0 _).mpr ?_, (Omv_site 0 _).mpr ?_⟩
  · rcases ht with h | h
    · exact vtx_arith _ _ _ _ _ _ _ hw hqN hP.p0pos a1 h hp hq _ b1
    · exact vtx_arith _ _ _ _ _ _ _ hw hqN hP.p0pos a2 h hp hq _ b1
  · rcases ht with h | h
    · exact vtx_arith _ _ _ _ _ _ _ hw hqN hP.p0pos a1 h hp hq _ b2
    · exact vtx_arith _ _ _ _ _ _ _ hw hqN hP.p0pos a2 h hp hq _ b2

end AdalyFormal.CoverOmegaTwo
