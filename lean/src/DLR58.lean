import DLR57

/-!
# DL58 -- **`LocRep.J_local_bound`** : `‖J(x,μ)‖ ≤ η³ (a₃ + 40a₁a₂ + 4144a₁³ + 8192ηa₁⁴)`

`J(x,μ) − η³ ddA(x,μ) = Σ_{ν≠μ} (D*_ν F_{νμ}(x) − η²(curlA(x−ν;ν,μ) − curlA(x;ν,μ)))` and each summand is bounded by
`LocRep.Dstar_err` (DL57); `‖ddA(x,μ)‖ ≤ a₃` is clause 3 of the class.
-/
set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 20000

namespace AdalyFormal.DLayer

open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.RMapLipschitz (frobSq frobNorm frobSq_nonneg frobNorm_nonneg frobNorm_sq)
open AdalyFormal.Balaban.SourceJ (piProj FnuMu DstarDir Jfield)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack
  periodicLatticeShiftBack_shift)
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.StatementLane2 (curlA ddA)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

local notation "Mt" => Matrix (Fin 2) (Fin 2) ℂ

variable {L : PeriodicLatticeExtent}

theorem sum_ite_ne (μ : Fin 3) (c : ℝ) : ∑ ν : Fin 3, (if ν = μ then (0 : ℝ) else c) = 2 * c := by
  fin_cases μ <;> simp [Fin.sum_univ_three] <;> ring

theorem fN_sum3 (f : Fin 3 → Mt) : frobNorm (∑ ν : Fin 3, f ν) ≤ ∑ ν : Fin 3, frobNorm (f ν) := by
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  exact (fN_add _ _).trans (add_le_add (fN_add _ _) le_rfl)

section Local
variable {V : PeriodicLinkConfiguration SU2 L} {η : ℝ} {A : Bond L → Mt} {a1 a2 : ℝ} {InC : Bond L → Prop}

theorem LocRep.J_local_bound (h : LocRep V η A a1 a2 InC) (x : PeriodicLatticeSite L) (μ : Fin 3) (a3 : ℝ)
    (hb : ∀ ν, ν ≠ μ → NeedBonds InC (periodicLatticeShiftBack x ν) ν μ)
    (h3 : frobNorm (ddA η A x μ) ≤ a3) :
    frobNorm (Jfield V x μ) ≤ η ^ 3 * (a3 + 40 * a1 * a2 + 4144 * a1 ^ 3 + 8192 * η * a1 ^ 4) := by
  have hη := h.hη
  set B := η ^ 3 * (20 * a1 * a2 + 2072 * a1 ^ 3 + 4096 * η * a1 ^ 4) with hB
  -- each direction
  have hdir : ∀ ν, ν ≠ μ →
      frobNorm (DstarDir V ν (fun z => FnuMu V ν μ z) x
        - (η ^ 2 : ℝ) • (curlA η A (periodicLatticeShiftBack x ν) ν μ - curlA η A x ν μ)) ≤ B := by
    intro ν hν
    have := h.Dstar_err ν μ hν (periodicLatticeShiftBack x ν) (hb ν hν)
    rwa [periodicLatticeShift_shiftBack] at this
  -- the leading term
  have hdd : (η ^ 3 : ℝ) • ddA η A x μ
      = ∑ ν : Fin 3, (if ν = μ then (0 : Mt)
          else (η ^ 2 : ℝ) • (curlA η A (periodicLatticeShiftBack x ν) ν μ - curlA η A x ν μ)) := by
    unfold ddA
    rw [smul_smul, show η ^ 3 * η⁻¹ = η ^ 2 by field_simp, Finset.smul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun ν _ => ?_)
    by_cases hν : ν = μ
    · rw [if_neg (not_not.mpr hν), if_pos hν]
    · rw [if_pos hν, if_neg hν]
  have hJ : Jfield V x μ = ∑ ν : Fin 3, (if ν = μ then (0 : Mt) else DstarDir V ν (fun z => FnuMu V ν μ z) x) := rfl
  have hsplit : Jfield V x μ = (η ^ 3 : ℝ) • ddA η A x μ
      + ∑ ν : Fin 3, (if ν = μ then (0 : Mt) else (DstarDir V ν (fun z => FnuMu V ν μ z) x
          - (η ^ 2 : ℝ) • (curlA η A (periodicLatticeShiftBack x ν) ν μ - curlA η A x ν μ))) := by
    rw [hdd, hJ, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun ν _ => ?_)
    split_ifs <;> abel
  rw [hsplit]
  refine (fN_add _ _).trans ?_
  have h1 : frobNorm ((η ^ 3 : ℝ) • ddA η A x μ) ≤ η ^ 3 * a3 := by
    rw [fN_rsmul, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  have h2 : frobNorm (∑ ν : Fin 3, (if ν = μ then (0 : Mt) else (DstarDir V ν (fun z => FnuMu V ν μ z) x
          - (η ^ 2 : ℝ) • (curlA η A (periodicLatticeShiftBack x ν) ν μ - curlA η A x ν μ)))) ≤ 2 * B := by
    refine (fN_sum3 _).trans ?_
    rw [← sum_ite_ne μ B]
    refine Finset.sum_le_sum (fun ν _ => ?_)
    by_cases hν : ν = μ
    · rw [if_pos hν, if_pos hν, fN_zero]
    · rw [if_neg hν, if_neg hν]; exact hdir ν hν
  rw [hB] at h2
  nlinarith [h1, h2]

end Local

#print axioms sum_ite_ne
#print axioms LocRep.J_local_bound

end AdalyFormal.DLayer
