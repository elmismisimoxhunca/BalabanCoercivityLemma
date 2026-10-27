import D2Geo1

/-!
# D2Geo2 -- the two-layer test field `A = amp(layer) X` on the `1`-bonds next to the boundary of a slab `Ω₀`, and its elementary properties (support, `D*A = 0`, `T A = 0`, `W A = A`).
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
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
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.StatementLaneR6
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack periodicLatticeShiftBack_shift gradCovariantAdjointValue)

variable {L : PeriodicLatticeExtent}

/-- `Ω₀` is the slab `P ≤ x₀ < Q` on a cubic torus of side `N`, with room for three layers and no wrap. -/
structure SlabH (Om : Set (PeriodicLatticeSite L)) (P Q N : ℕ) : Prop where
  hN : ∀ μ, L μ + 1 = N
  mem : ∀ z, z ∈ Om ↔ P ≤ (z 0).val ∧ (z 0).val < Q
  hPQ : P + 3 ≤ Q
  hQN : Q < N

variable {Om : Set (PeriodicLatticeSite L)} {P Q N : ℕ}

theorem SlabH.hN1 (H : SlabH Om P Q N) : 1 < N := by have := H.hPQ; have := H.hQN; omega

theorem SlabH.shift0 (H : SlabH Om P Q N) (z : PeriodicLatticeSite L) :
    ((periodicLatticeShift z 0) 0).val = ((z 0).val + 1) % N := by
  rw [shift_val_N H.hN H.hN1, if_pos rfl]

theorem SlabH.shiftT (H : SlabH Om P Q N) (z : PeriodicLatticeSite L) {ν : Fin 3} (hν : ν ≠ 0) :
    ((periodicLatticeShift z ν) 0).val = (z 0).val := by
  rw [shift_val_N H.hN H.hN1, if_neg (Ne.symm hν)]

theorem SlabH.shiftBackT (H : SlabH Om P Q N) (z : PeriodicLatticeSite L) {ν : Fin 3} (hν : ν ≠ 0) :
    ((periodicLatticeShiftBack z ν) 0).val = (z 0).val := by
  have := shiftBack_ne z (Ne.symm hν)
  rw [this]

theorem SlabH.lt (H : SlabH Om P Q N) (z : PeriodicLatticeSite L) : (z 0).val < N := by
  have := (z 0).isLt; have e := H.hN 0; omega

/-- layer after a step in direction `0`, as a natural number. -/
theorem SlabH.shift0_val (H : SlabH Om P Q N) (z : PeriodicLatticeSite L) :
    ((periodicLatticeShift z 0) 0).val = if (z 0).val + 1 < N then (z 0).val + 1 else 0 := by
  rw [H.shift0]
  have := H.lt z
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have : (z 0).val + 1 = N := by omega
    rw [this, Nat.mod_self]

/-- the amplitude profile: `5` at the last layer of `Ω₀`, `2` at the one before. -/
def amp (Q ℓ : ℕ) : ℝ := if ℓ + 1 = Q then 5 else if ℓ + 2 = Q then 2 else 0

open Classical in
/-- the test field. -/
noncomputable def Afield (Q : ℕ) (X : SuTwo) : BondFnL2 L :=
  WithLp.toLp 2 (fun b : Bond L => if b.2 = 1 then (amp Q (b.1 0).val) • X else 0)

theorem Afield_apply (Q : ℕ) (X : SuTwo) (b : Bond L) :
    (Afield Q X) b = if b.2 = 1 then (amp Q (b.1 0).val) • X else 0 := by
  classical
  rfl

theorem amp_ne_zero {Q ℓ : ℕ} (h : amp Q ℓ ≠ 0) : ℓ + 1 = Q ∨ ℓ + 2 = Q := by
  unfold amp at h
  by_contra hc
  push_neg at hc
  rw [if_neg hc.1, if_neg hc.2] at h
  exact h rfl

theorem Afield_supp (H : SlabH Om P Q N) (X : SuTwo) (b : Bond L) (hb : (Afield Q X) b ≠ 0) :
    b.2 = 1 ∧ b.1 ∈ Om ∧ ((b.1 0).val + 1 = Q ∨ (b.1 0).val + 2 = Q) := by
  rw [Afield_apply] at hb
  by_cases h1 : b.2 = 1
  · rw [if_pos h1] at hb
    have hamp : amp Q (b.1 0).val ≠ 0 := by
      intro h0; rw [h0, zero_smul] at hb; exact hb rfl
    have h2 := amp_ne_zero hamp
    refine ⟨h1, (H.mem _).mpr ⟨?_, ?_⟩, h2⟩
    · have := H.hPQ; omega
    · omega
  · rw [if_neg h1] at hb; exact absurd rfl hb

/-- `A` lives on bonds with both endpoints in `Ω₀`. -/
theorem Afield_bothIn (H : SlabH Om P Q N) (X : SuTwo) (b : Bond L) (hb : (Afield Q X) b ≠ 0) : BothIn Om b := by
  obtain ⟨h1, h2, h3⟩ := Afield_supp H X b hb
  refine ⟨h2, ?_⟩
  have hs : periodicLatticeShift b.1 b.2 ∈ Om := by
    rw [H.mem] at h2 ⊢
    have : b.2 ≠ 0 := by rw [h1]; decide
    rw [H.shiftT b.1 this]; exact h2
  exact hs

theorem gradAdj_Afield (H : SlabH Om P Q N) (X : SuTwo) (U : Cfg L) (hU : ∀ e, PM (U e)) :
    gradAdj U (Afield Q X) = 0 := by
  refine PiLp.ext (fun z => ?_)
  show (WithLp.ofLp (gradAdj U (Afield Q X))) z = 0
  rw [gradAdj_apply]
  refine gradAdjValue_PM U hU _ z (fun μ => ?_)
  by_cases hμ : μ = 1
  · subst hμ
    have e1 := Afield_apply (L := L) Q X (periodicLatticeShiftBack z 1, 1)
    have e2 := Afield_apply (L := L) Q X (z, 1)
    show RMap (U (periodicLatticeShiftBack z 1, 1))⁻¹ ((Afield Q X) (periodicLatticeShiftBack z 1, 1)) - (Afield Q X) (z, 1) = 0
    rw [e1, e2, if_pos rfl, if_pos rfl, H.shiftBackT z (by decide), RMap_PM (PM_inv (hU _)), sub_self]
  · have e1 := Afield_apply (L := L) Q X (periodicLatticeShiftBack z μ, μ)
    have e2 := Afield_apply (L := L) Q X (z, μ)
    show RMap (U (periodicLatticeShiftBack z μ, μ))⁻¹ ((Afield Q X) (periodicLatticeShiftBack z μ, μ)) - (Afield Q X) (z, μ) = 0
    rw [e1, e2, if_neg hμ, if_neg hμ]
    simp

theorem Afield_mem_bondSupp (H : SlabH Om P Q N) (G : TowerGeom L) (hG : G.Om0 = Om) (X : SuTwo) :
    Afield Q X ∈ bondSupp G := by
  intro b hb
  by_contra hne
  apply hb
  show b.1 ∈ G.Om0 ∨ _
  exact Or.inl (by rw [hG]; exact (Afield_supp H X b hne).2.1)

theorem bondMask_both_Afield (H : SlabH Om P Q N) (X : SuTwo) :
    bondMask {b | BothIn Om b} (Afield Q X) = Afield Q X :=
  bondMask_eq_self _ _ (fun b hb => by
    by_contra hne
    exact hb (Afield_bothIn H X b hne))

theorem Tfull_Afield {ell k : ℕ} {S : Tower L} (H : SlabH (S.Om 0) P Q N) (X : SuTwo) (U : Cfg L) (hU : ∀ e, PM (U e)) :
    Tfull (geomOf ell k S) U (Afield Q X) = 0 := by
  unfold Tfull
  simp only [ContinuousLinearMap.comp_apply]
  rw [gradAdj_Afield H X U hU]
  simp

theorem Wop_Afield {ell k : ℕ} {S : Tower L} (H : SlabH (S.Om 0) P Q N) (X : SuTwo) (U : Cfg L) (hU : ∀ e, PM (U e)) (a : ℝ) :
    Wop (geomOf ell k S) U a (Afield Q X) = Afield Q X := by
  unfold Wop
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, ContinuousLinearMap.comp_apply]
  rw [gradAdj_Afield H X U hU]
  simp

#print axioms Wop_Afield
#print axioms Tfull_Afield
#print axioms Afield_bothIn

end AdalyFormal.D1Literal
