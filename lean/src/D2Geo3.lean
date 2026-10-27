import D2Geo2

/-!
# D2Geo3 -- per-plaquette values of the literal `Δ` form on the two-layer field at `θ = π`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace AdalyFormal.D1Literal

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLaneR8
open AdalyFormal.NonVac
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.StatementLaneR6
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack periodicLatticeShiftBack_shift)

variable {L : PeriodicLatticeExtent} {Om : Set (PeriodicLatticeSite L)} {P Q N : ℕ}

theorem hsInner_smul_smul (c : ℝ) (X : SuTwo) : hsInner (c • X) (c • X) = c ^ 2 * hsInner X X := by
  unfold hsInner
  simp only [Submodule.coe_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul, Complex.smul_re,
    smul_eq_mul]
  ring

theorem curl_PM_gen (U : PeriodicLinkConfiguration SU2m L) (hU : ∀ e, PM (U e)) (A : Bond L → SuTwo)
    (p : PeriodicLatticePlaquette L) :
    curlValueCovariant U A p = A (p.1, p.2.1.1) + A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)
      - A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) - A (p.1, p.2.1.2) := by
  unfold curlValueCovariant
  rw [RMap_PM (hU _), RMap_PM (hU _)]

/-- the plaquette direction pair `(0,1)`. -/
def d01 : PeriodicPlaquetteDirections := ⟨((0 : Fin 3), (1 : Fin 3)), by decide⟩

/-- value of the `(0,1)` plaquette at layer `l`: `-25, 9, 4` at `l = Q-1, Q-2, Q-3` (times `⟨X,X⟩`). -/
def Gv (Q : ℕ) (n : ℝ) (l : ℕ) : ℝ :=
  (if l + 1 = Q then -25 else if l + 2 = Q then 9 else if l + 3 = Q then 4 else 0) * n

theorem SlabH.bdpt (H : SlabH Om P Q N) (z : PeriodicLatticeSite L) (hz : (z 0).val + 1 = Q) : BdPt Om z := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [H.mem]; have := H.hPQ; omega
  · rw [H.mem, H.shift0_val z]
    have := H.hQN
    rw [if_pos (by omega)]
    omega
  · intro y ν hν
    rw [H.mem, H.mem, H.shiftT y hν]
  · intro ν hxe
    have h1 := congrArg (fun y : PeriodicLatticeSite L => (y ν).val) hxe
    rw [shift_val_N H.hN H.hN1, if_pos rfl] at h1
    have hx : (z ν).val < N := by
      have := (z ν).isLt; have e := H.hN ν; omega
    have h2 := H.hN1
    rcases Nat.lt_or_ge ((z ν).val + 1) N with h | h
    · rw [Nat.mod_eq_of_lt h] at h1; omega
    · have : (z ν).val + 1 = N := by omega
      rw [this, Nat.mod_self] at h1
      omega

theorem hol01_flat (H : SlabH Om P Q N) (z : PeriodicLatticeSite L) (hz : (z 0).val + 2 = Q ∨ (z 0).val + 3 = Q) :
    ((holonomyElem (Uth Om Real.pi) (z, d01) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  have hPQ := H.hPQ
  have hz0 : z ∈ Om := by rw [H.mem]; omega
  have hz1 : periodicLatticeShift z 0 ∈ Om := by
    rw [H.mem, H.shift0_val z, if_pos (by have := H.hQN; omega)]; omega
  have hz2 : periodicLatticeShift z 1 ∈ Om := by
    rw [H.mem, H.shiftT z (by decide)]; rw [H.mem] at hz0; exact hz0
  have e1 : Uth Om Real.pi (z, (0 : Fin 3)) = 1 := Uth_in Om _ _ hz0
  have e2 : Uth Om Real.pi (periodicLatticeShift z 0, (1 : Fin 3)) = 1 := Uth_in Om _ _ hz1
  have e3 : Uth Om Real.pi (periodicLatticeShift z 1, (0 : Fin 3)) = 1 := Uth_in Om _ _ hz2
  have e4 : Uth Om Real.pi (z, (1 : Fin 3)) = 1 := Uth_in Om _ _ hz0
  show ((periodicPlaquetteHolonomy (Uth Om Real.pi) (z, d01) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = 1
  unfold periodicPlaquetteHolonomy d01
  simp only
  rw [e1, e2, e3, e4]
  simp

theorem hol01_top (H : SlabH Om P Q N) (z : PeriodicLatticeSite L) (hz : (z 0).val + 1 = Q) :
    ((holonomyElem (Uth Om Real.pi) (z, d01) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
  have hb := H.bdpt z hz
  have := hb.holonomy1 Real.pi ⟨1, by decide⟩
  have e : (P1 z ⟨1, by decide⟩ : PeriodicLatticePlaquette L) = (z, d01) := rfl
  rw [e] at this
  rw [this]
  exact uθ_pi_coe

theorem amp_a {Q l : ℕ} (h : l + 1 = Q) : amp Q l = 5 := by unfold amp; rw [if_pos h]
theorem amp_b {Q l : ℕ} (h : l + 2 = Q) : amp Q l = 2 := by
  unfold amp; rw [if_neg (by omega), if_pos h]
theorem amp_z {Q l : ℕ} (h1 : l + 1 ≠ Q) (h2 : l + 2 ≠ Q) : amp Q l = 0 := by
  unfold amp; rw [if_neg h1, if_neg h2]

/-- the contribution of one plaquette to `⟨A, ΔA⟩`. -/
noncomputable def contrib (U : PeriodicLinkConfiguration SU2m L) (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) : ℝ :=
  hsInner (curlValueCovariant U A p) (curlValueCovariant U A p) + (1 / 2 : ℝ) * bilPlaq U p A A

theorem contrib_Afield (H : SlabH Om P Q N) (X : SuTwo) (z : PeriodicLatticeSite L)
    (d : PeriodicPlaquetteDirections) :
    contrib (Uth Om Real.pi) (WithLp.ofLp (Afield Q X)) (z, d) =
      if d = d01 then Gv Q (hsInner X X) (z 0).val else 0 := by
  have hQ := H.hPQ
  have hQN := H.hQN
  obtain ⟨⟨μ, ν⟩, hmν⟩ := d
  have hc : (μ = 0 ∧ ν = 1) ∨ (μ = 0 ∧ ν = 2) ∨ (μ = 1 ∧ ν = 2) := by
    revert hmν; revert μ ν; decide
  have hpm := holonomy_PM (Uth Om Real.pi) (Uth_PM Om) (z, ⟨(μ, ν), hmν⟩)
  have hcurl := curl_PM_gen (Uth Om Real.pi) (Uth_PM Om) (WithLp.ofLp (Afield Q X)) (z, ⟨(μ, ν), hmν⟩)
  have A0 : ∀ y : PeriodicLatticeSite L, ∀ m : Fin 3, m ≠ 1 → (WithLp.ofLp (Afield Q X)) (y, m) = 0 := by
    intro y m hm
    rw [show (WithLp.ofLp (Afield Q X)) (y, m) = (Afield Q X) (y, m) from rfl, Afield_apply]
    simp [hm]
  have A1 : ∀ y : PeriodicLatticeSite L, (WithLp.ofLp (Afield Q X)) (y, 1) = (amp Q (y 0).val) • X := by
    intro y
    rw [show (WithLp.ofLp (Afield Q X)) (y, 1) = (Afield Q X) (y, 1) from rfl, Afield_apply]
    simp
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- (0,1)
    have hd : (⟨((0 : Fin 3), (1 : Fin 3)), hmν⟩ : PeriodicPlaquetteDirections) = d01 := rfl
    rw [hd] at hpm hcurl ⊢
    rw [if_pos rfl]
    simp only [d01] at hcurl
    rw [A0 z 0 (by decide), A0 (periodicLatticeShift z 1) 0 (by decide), A1, A1] at hcurl
    have hlt := H.lt z
    set l := (z 0).val with hl
    have hl' := H.shift0_val z
    rw [← hl] at hl'
    have hcz : curlValueCovariant (Uth Om Real.pi) (WithLp.ofLp (Afield Q X)) (z, d01)
        = (amp Q ((periodicLatticeShift z 0) 0).val - amp Q l) • X := by
      refine Eq.trans hcurl ?_
      simp [sub_smul]
    have hl1 : ((periodicLatticeShift z 0) 0).val = if l + 1 < N then l + 1 else 0 := hl'
    unfold contrib
    rw [hcz]
    by_cases h1 : l + 1 = Q
    · have hl1' : ((periodicLatticeShift z 0) 0).val = Q := by rw [hl1, if_pos (by omega)]; omega
      have := plaq_central (Uth Om Real.pi) (z, d01) (WithLp.ofLp (Afield Q X)) (hol01_top H z h1)
      rw [hcz, hl1', amp_a h1, show amp Q Q = 0 from amp_z (by omega) (by omega), hsInner_smul_smul] at this
      unfold Gv
      rw [if_pos h1, hl1', amp_a h1, show amp Q Q = 0 from amp_z (by omega) (by omega), hsInner_smul_smul]
      linarith
    · by_cases h2 : l + 2 = Q
      · have hl1' : ((periodicLatticeShift z 0) 0).val = l + 1 := by rw [hl1, if_pos (by omega)]
        have := plaq_flat (Uth Om Real.pi) (z, d01) (WithLp.ofLp (Afield Q X)) (hol01_flat H z (Or.inl h2))
        rw [hcz, hl1', amp_a (show l + 1 + 1 = Q by omega), amp_b h2, hsInner_smul_smul] at this
        unfold Gv
        rw [if_neg h1, if_pos h2, hl1', amp_a (show l + 1 + 1 = Q by omega), amp_b h2, hsInner_smul_smul]
        linarith
      · by_cases h3 : l + 3 = Q
        · have hl1' : ((periodicLatticeShift z 0) 0).val = l + 1 := by rw [hl1, if_pos (by omega)]
          have := plaq_flat (Uth Om Real.pi) (z, d01) (WithLp.ofLp (Afield Q X)) (hol01_flat H z (Or.inr h3))
          rw [hcz, hl1', amp_b (show l + 1 + 2 = Q by omega), amp_z h1 h2, hsInner_smul_smul] at this
          unfold Gv
          rw [if_neg h1, if_neg h2, if_pos h3, hl1', amp_b (show l + 1 + 2 = Q by omega), amp_z h1 h2, hsInner_smul_smul]
          linarith
        · have hz0 : amp Q ((periodicLatticeShift z 0) 0).val = 0 := by
            rw [hl1]
            split_ifs with hh
            · exact amp_z (by omega) (by omega)
            · exact amp_z (by omega) (by omega)
          have hcz0 : curlValueCovariant (Uth Om Real.pi) (WithLp.ofLp (Afield Q X)) (z, d01) = 0 := by
            rw [hcz, hz0, amp_z h1 h2]; simp
          have h0 : hsInner (0 : SuTwo) 0 = 0 := by unfold hsInner; simp
          have := plaq_PM_zero (Uth Om Real.pi) (z, d01) (WithLp.ofLp (Afield Q X)) hpm hcz0
          rw [hcz0, h0] at this
          unfold Gv
          rw [if_neg h1, if_neg h2, if_neg h3, hz0, amp_z h1 h2]
          simp [h0]
          linarith
  · -- (0,2)
    have hne : (⟨((0 : Fin 3), (2 : Fin 3)), hmν⟩ : PeriodicPlaquetteDirections) ≠ d01 := by
      intro h; have := congrArg (fun d : PeriodicPlaquetteDirections => d.1.2) h; simp [d01] at this
    rw [if_neg hne]
    have hc0 : curlValueCovariant (Uth Om Real.pi) (WithLp.ofLp (Afield Q X)) (z, ⟨((0 : Fin 3), (2 : Fin 3)), hmν⟩) = 0 := by
      rw [hcurl]
      simp only
      rw [A0 z 0 (by decide), A0 _ 2 (by decide), A0 _ 0 (by decide), A0 z 2 (by decide)]
      simp
    exact plaq_PM_zero _ _ _ hpm hc0
  · -- (1,2)
    have hne : (⟨((1 : Fin 3), (2 : Fin 3)), hmν⟩ : PeriodicPlaquetteDirections) ≠ d01 := by
      intro h; have := congrArg (fun d : PeriodicPlaquetteDirections => d.1.1) h; simp [d01] at this
    rw [if_neg hne]
    have hc0 : curlValueCovariant (Uth Om Real.pi) (WithLp.ofLp (Afield Q X)) (z, ⟨((1 : Fin 3), (2 : Fin 3)), hmν⟩) = 0 := by
      rw [hcurl]
      simp only
      rw [A1 z, A0 _ 2 (by decide), A1 (periodicLatticeShift z 2), A0 z 2 (by decide), H.shiftT z (by decide)]
      simp
    exact plaq_PM_zero _ _ _ hpm hc0

#print axioms contrib_Afield
#print axioms hol01_top
#print axioms hol01_flat

end AdalyFormal.D1Literal
