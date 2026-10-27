import D2Geo5

/-!
# D2Geo6 -- the masked (both-endpoint) literal `Ginv` has a negative direction at `θ = π` for `a < 12/29`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.D1Literal

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLaneR8
open AdalyFormal.NonVac
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.StatementLaneR6

variable {L : PeriodicLatticeExtent} {Om : Set (PeriodicLatticeSite L)} {P Q N : ℕ}

theorem Afield_hsupp (H : SlabH Om P Q N) (X : SuTwo) (e : Bond L) (he : (Afield Q X) e ≠ 0) :
    ∃ w : PeriodicLatticeSite L, w ∉ Om ∧ pdist e.1 w ≤ 2 := by
  obtain ⟨-, -, h3⟩ := Afield_supp H X e he
  have hlt := H.lt e.1
  have hQN := H.hQN
  have hPQ := H.hPQ
  rcases h3 with h | h
  · refine ⟨periodicLatticeShift e.1 0, ?_, ?_⟩
    · rw [H.mem, H.shift0_val, if_pos (by omega)]; omega
    · have := pdist_shift_le e.1 0; omega
  · refine ⟨periodicLatticeShift (periodicLatticeShift e.1 0) 0, ?_, ?_⟩
    · have h1 : ((periodicLatticeShift e.1 0) 0).val = (e.1 0).val + 1 := by
        rw [H.shift0_val, if_pos (by omega)]
      rw [H.mem, H.shift0_val, h1, if_pos (by omega)]; omega
    · have t1 := pdist_shift_le e.1 0
      have t2 := pdist_shift_le (periodicLatticeShift e.1 0) 0
      have t3 := pdist_triangle e.1 (periodicLatticeShift e.1 0) (periodicLatticeShift (periodicLatticeShift e.1 0) 0)
      omega

section
variable (sJ : PlaqSel) {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell)
  {S : Tower (scaleUp ell k Lu)} (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))

theorem FthM_both_pi_neg (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M)
    {P Q N : ℕ} (H : SlabH (S.Om 0) P Q N) (ha : 0 ≤ a) (ha' : 29 * a < 12) (X : SuTwo) (hX : X ≠ 0) :
    ∃ v : ↥(bondSupp (geomOf ell k S)), ⟪v, FthM sJ bothSel hell0 a Lam (S := S) Real.pi v⟫ < 0 := by
  have h9 : 9 * ell ≤ R * M := by omega
  have hmem : Afield Q X ∈ bondSupp (geomOf ell k S) := Afield_mem_bondSupp H _ rfl X
  refine ⟨⟨Afield Q X, hmem⟩, ?_⟩
  have hn : 0 < hsInner X X := by
    have h0 : 0 ≤ hsInner X X := real_inner_self_nonneg (x := X)
    rcases h0.lt_or_eq with h | h
    · exact h
    · exact absurd (AdalyFormal.Balaban.SuTwoInner.hsInner_self_eq_zero h.symm) hX
  have hK := Kcol_pos (scaleUp ell k Lu)
  show ⟪(⟨Afield Q X, hmem⟩ : ↥(bondSupp (Pth ell k Lu hell0 S a Lam Real.pi).G)),
    (dataM selAll sJ bothSel (Pth ell k Lu hell0 S a Lam Real.pi)).Ginv ⟨Afield Q X, hmem⟩⟫ < 0
  rw [BaseDataS.inner_Ginv]
  have hDpi : ⟪(⟨Afield Q X, hmem⟩ : ↥(bondSupp (Pth ell k Lu hell0 S a Lam Real.pi).G)),
      (dataM selAll sJ bothSel (Pth ell k Lu hell0 S a Lam Real.pi)).Dpi ⟨Afield Q X, hmem⟩⟫
        = -12 * Kcol (scaleUp ell k Lu) * hsInner X X := by
    have e := E0_DpiM_inner selAll bothSel (geomOf ell k S) (Uth (S.Om 0) Real.pi) a ⟨Afield Q X, hmem⟩
    refine e.trans ?_
    have hW : Wop (geomOf ell k S) (Uth (S.Om 0) Real.pi) a (iE (geomOf ell k S) ⟨Afield Q X, hmem⟩) = Afield Q X :=
      Wop_Afield H X _ (Uth_PM _) a
    rw [hW]
    unfold DeltaM
    simp only [ContinuousLinearMap.comp_apply]
    rw [← bondMask_symm]
    have hm : bondMask (bothSel _ (geomOf ell k S)) (Afield Q X) = Afield Q X := bondMask_both_Afield H X
    rw [hm]
    exact form_value H X
  have hT : (dataM selAll sJ bothSel (Pth ell k Lu hell0 S a Lam Real.pi)).T ⟨Afield Q X, hmem⟩ = 0 := by
    show (Tfull (geomOf ell k S) (Uth (S.Om 0) Real.pi)) (iE (geomOf ell k S) ⟨Afield Q X, hmem⟩) = 0
    exact Tfull_Afield H X _ (Uth_PM _)
  have hM : ⟪(⟨Afield Q X, hmem⟩ : ↥(bondSupp (Pth ell k Lu hell0 S a Lam Real.pi).G)),
      (dataM selAll sJ bothSel (Pth ell k Lu hell0 S a Lam Real.pi)).Mass ⟨Afield Q X, hmem⟩⟫
        ≤ a * (29 * Kcol (scaleUp ell k Lu) * hsInner X X) := by
    have e2 : ⟪(⟨Afield Q X, hmem⟩ : ↥(bondSupp (geomOf ell k S))), ((pE (geomOf ell k S)).comp ((MassFull (geomOf ell k S) a
        (bondSectorOf (geomOf ell k S) (Uth (S.Om 0) Real.pi))).comp (iE (geomOf ell k S)))) ⟨Afield Q X, hmem⟩⟫
        = ⟪Afield Q X, MassFull (geomOf ell k S) a (bondSectorOf (geomOf ell k S) (Uth (S.Om 0) Real.pi)) (Afield Q X)⟫ := by
      simp only [ContinuousLinearMap.comp_apply]
      rw [pE_inner_right]; rfl
    refine le_trans (le_of_eq e2) ?_
    have := Mass_supp_le hS hell h9 (Uth (S.Om 0) Real.pi) a ha (Afield Q X) (Afield_hsupp H X)
    rw [normsq_Afield H X] at this
    exact this
  rw [hDpi, hT]
  simp only [norm_zero]
  nlinarith [mul_pos hK hn]

end

#print axioms FthM_both_pi_neg

end AdalyFormal.D1Literal
