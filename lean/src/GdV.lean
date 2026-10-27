import GdPlaq

/-!
# GdV -- on fields vanishing on the level-0 bonds, the literal `Ginv` of the twist family does not depend on `θ`.

For `A ∈ E₀` with `A = 0` on every level-0 bond (this holds for every `A ∈ ker Q`, and for every `A` with `Q A` having zero level-0 part):
the gauge-fixed field `X = W A = A - D f`, `f = G' R D* A`, vanishes on every bond of every plaquette that contains a `Zb Ω₀` bond (a bond with no endpoint in `Ω₀`),
because all four corners of such a plaquette lie outside `Ω₁` (collar), hence in `Λ₀ ∪ Ω₀ᶜ`, where `f = 0` (`GdNQ`) and `A = 0`.
Hence `(Δ_θ - Δ_0) X = 0` (`GdPlaq`) and `Ginv(θ) A = Ginv(0) A`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.D1Guarded

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.StatementLaneR8
open AdalyFormal.StatementLaneR6
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

variable {L : PeriodicLatticeExtent}

/-- plaquettes that contain a bond with no endpoint in `Om`. -/
def PZ (Om : Set (PeriodicLatticeSite L)) : Set (PeriodicLatticePlaquette L) :=
  {p | ∃ e ∈ periodicPlaquetteBoundaryEdges p, e ∈ Zb Om}

theorem pdist_shift2_le (x : PeriodicLatticeSite L) (μ ν : Fin 3) :
    pdist (periodicLatticeShift (periodicLatticeShift x μ) ν) x ≤ 2 := by
  have h1 := AdalyFormal.StatementLaneR8.pdist_shift_le x μ
  have h2 := AdalyFormal.StatementLaneR8.pdist_shift_le (periodicLatticeShift x μ) ν
  have h3 := AdalyFormal.StatementLaneR8.pdist_triangle (periodicLatticeShift (periodicLatticeShift x μ) ν) (periodicLatticeShift x μ) x
  have c1 := AdalyFormal.StatementLaneR8.pdist_comm x (periodicLatticeShift x μ)
  have c2 := AdalyFormal.StatementLaneR8.pdist_comm (periodicLatticeShift x μ) (periodicLatticeShift (periodicLatticeShift x μ) ν)
  omega

/-- both endpoints of every bond of a plaquette are within distance `2` of its base point. -/
theorem edge_ends_near {p : PeriodicLatticePlaquette L} {e : Bond L} (he : e ∈ periodicPlaquetteBoundaryEdges p) :
    pdist e.1 p.1 ≤ 2 ∧ pdist (periodicLatticeShift e.1 e.2) p.1 ≤ 2 := by
  have s1 := AdalyFormal.StatementLaneR8.pdist_shift_le p.1 p.2.1.1
  have s2 := AdalyFormal.StatementLaneR8.pdist_shift_le p.1 p.2.1.2
  have s1' := AdalyFormal.StatementLaneR8.pdist_comm p.1 (periodicLatticeShift p.1 p.2.1.1)
  have s2' := AdalyFormal.StatementLaneR8.pdist_comm p.1 (periodicLatticeShift p.1 p.2.1.2)
  have t1 := pdist_shift2_le p.1 p.2.1.1 p.2.1.2
  have t2 := pdist_shift2_le p.1 p.2.1.2 p.2.1.1
  rcases (edge_mem p e).mp he with rfl | rfl | rfl | rfl
  · simp only [AdalyFormal.StatementLaneR8.pdist_self]
    omega
  · simp only []
    omega
  · simp only []
    omega
  · simp only [AdalyFormal.StatementLaneR8.pdist_self]
    omega

/-- all four corners of a plaquette containing a `Zb Ω₀` bond lie outside `Ω₁` (collar `4 ≤ R M`). -/
theorem edge_ends_not_om1 {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (h4 : 4 ≤ R * M)
    {p : PeriodicLatticePlaquette L} {e e' : Bond L} (he : e ∈ periodicPlaquetteBoundaryEdges p) (hz : e ∈ Zb (S.Om 0))
    (he' : e' ∈ periodicPlaquetteBoundaryEdges p) :
    e'.1 ∉ S.Om 1 ∧ periodicLatticeShift e'.1 e'.2 ∉ S.Om 1 := by
  obtain ⟨n1, n2⟩ := edge_ends_near he
  obtain ⟨m1, m2⟩ := edge_ends_near he'
  have hz0 : e.1 ∉ S.Om 0 := hz.1
  have key : ∀ c, pdist c p.1 ≤ 2 → c ∈ S.Om 1 → False := by
    intro c hc hc1
    have h := AdalyFormal.StatementLaneR8.pdist_triangle e.1 p.1 c
    rw [AdalyFormal.StatementLaneR8.pdist_comm p.1 c] at h
    exact hz0 (near_om1 hS hc1 (by omega) (Nat.zero_le _))
  exact ⟨fun h => key _ m1 h, fun h => key _ m2 h⟩

section assembled
variable {ell M R k : ℕ} {S : Tower L}

/-- **the gauge-fixed field vanishes on the bonds of every `PZ` plaquette** (for fields vanishing on level-0 bonds). -/
theorem Wop_zero_on_PZ (hS : Admissible ell M R k S) (hell0 : 0 < ell) (h4 : 4 ≤ R * M) (U : Cfg L) (a : ℝ)
    (A : ↥(bondSupp (geomOf ell k S))) (hA0 : ∀ b ∈ bondsLam (geomOf ell k S) 0, (WithLp.ofLp (iE (geomOf ell k S) A)) b = 0)
    {p : PeriodicLatticePlaquette L} (hp : p ∈ PZ (S.Om 0)) (e' : Bond L) (he' : e' ∈ periodicPlaquetteBoundaryEdges p) :
    (WithLp.ofLp (Wop (geomOf ell k S) U a (iE (geomOf ell k S) A))) e' = 0 := by
  obtain ⟨e, he, hz⟩ := hp
  obtain ⟨n1, n2⟩ := edge_ends_not_om1 hS h4 he hz he'
  have hfz : ∀ c : PeriodicLatticeSite L, c ∉ S.Om 1 →
      (WithLp.ofLp (Gp (geomOf ell k S) U a (Rproj (geomOf ell k S) U (gradAdj U (iE (geomOf ell k S) A))))) c = 0 := by
    intro c hc
    by_cases hc0 : c ∈ S.Om 0
    · refine Gp_Rproj_lam0 (geomOf ell k S) U a _ (x := c) ?_
      refine ⟨fun μ => by simp, hc0, ?_⟩
      simpa using hc
    · exact Gp_Rproj_out (geomOf ell k S) U a _ (x := c) hc0
  have hgrad : (WithLp.ofLp (gradL2 U (Gp (geomOf ell k S) U a (Rproj (geomOf ell k S) U (gradAdj U (iE (geomOf ell k S) A)))))) e' = 0 := by
    rw [gradL2_apply]
    unfold AdalyFormal.Balaban.CovariantOperators.gradValueCovariant
    rw [hfz _ n1, hfz _ n2]
    simp
  have hA : (WithLp.ofLp (iE (geomOf ell k S) A)) e' = 0 := by
    by_cases hb : e' ∈ bondsOm0 (geomOf ell k S)
    · by_contra hne
      have hnl : e' ∉ bondsLam (geomOf ell k S) 0 := fun h => hne (hA0 e' h)
      rcases endpoint_om1 hell0 hS e' hb hnl with h | h
      · exact n1 h
      · exact n2 h
    · exact A.2 e' hb
  have hW : Wop (geomOf ell k S) U a (iE (geomOf ell k S) A) = iE (geomOf ell k S) A - gradL2 U (Gp (geomOf ell k S) U a (Rproj (geomOf ell k S) U (gradAdj U (iE (geomOf ell k S) A)))) := rfl
  rw [hW]
  show (WithLp.ofLp (iE (geomOf ell k S) A)) e' - (WithLp.ofLp (gradL2 U (Gp (geomOf ell k S) U a (Rproj (geomOf ell k S) U (gradAdj U (iE (geomOf ell k S) A)))))) e' = 0
  rw [hA, hgrad, sub_zero]

/-- **`Ginv(θ) A = Ginv(0) A` for `A` vanishing on the level-0 bonds.** -/
theorem Fth_theta_apply_eq (sJ : PlaqSel) (hell0 : 0 < ell) {Lu : PeriodicLatticeExtent}
    {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (θ : ℝ) (A : ↥(bondSupp (geomOf ell k S)))
    (hA0 : ∀ b ∈ bondsLam (geomOf ell k S) 0, (WithLp.ofLp (iE (geomOf ell k S) A)) b = 0) :
    Fth sJ ell k Lu hell0 S a Lam θ A = Fth sJ ell k Lu hell0 S a Lam 0 A := by
  have h4 : 4 ≤ R * M := by omega
  rw [Fth_diff sJ hell0 hS hell hroom a Lam θ]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply]
  have hcong : AdalyFormal.StatementLaneR6.deltaKLocCLM (Uth (S.Om 0) θ) Set.univ
        (Wop (geomOf ell k S) (Uth (S.Om 0) 0) a (iE (geomOf ell k S) A))
      = AdalyFormal.StatementLaneR6.deltaKLocCLM (Uth (S.Om 0) 0) Set.univ
        (Wop (geomOf ell k S) (Uth (S.Om 0) 0) a (iE (geomOf ell k S) A)) := by
    refine deltaK_univ_congr_apply (PZ (S.Om 0)) (fun p hp e he => ?_) _ (fun p hp e he => ?_)
    · refine Uth_eq_off_Z _ _ _ e (fun hz => hp ⟨e, he, hz⟩)
    · exact Wop_zero_on_PZ hS hell0 h4 _ a A hA0 hp e he
  rw [hcong, sub_self]
  simp

#print axioms edge_ends_near
#print axioms edge_ends_not_om1
#print axioms Wop_zero_on_PZ
#print axioms Fth_theta_apply_eq

end assembled

end AdalyFormal.D1Guarded
