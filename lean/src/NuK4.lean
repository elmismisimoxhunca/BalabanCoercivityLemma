import NuK1
import NtCvOF16

/-!
# NuK4 -- the pattern competitor lies in `Λ̃`: `OnLambdaT` and `OnLambdaTildeIn` at `ell = 2` (lane ncwdh_ell2_20261018)

* staircase bonds in direction `1` sit at an even `u₀` and an even `u₁`; the odd slice carries the pattern only where `u₁, u₂` are both odd;
* the dropped direction-`1` bond of a coarse bond sits at `u₀`, `u₂` even.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.NcwdhTwo

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverOmega
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.ReparamCDisjoint (droppedBondLast)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2 SuTwo)
open AdalyFormal.CoverJacobi

section
variable [CfData]
variable {M R : ℕ}

theorem betaPat_zero_of {L : PeriodicLatticeExtent} {uE : ℕ} (huE : uE % 2 = 0) {x : PeriodicLatticeSite L}
    (hx0 : (x 0).val % 2 = 0) (h : (x 1).val % 2 = 0 ∨ (x 2).val % 2 = 0) : betaPat uE x = 0 := by
  unfold betaPat
  have h1 : (x 0).val ≠ uE + 1 := by omega
  rw [if_neg h1, zero_add]
  split_ifs with h2 h3
  · exfalso; omega
  · rfl
  · rfl

theorem Bpatf_dir_ne {L : PeriodicLatticeExtent} (uE : ℕ) {b : Bond L} (hb : b.2 ≠ 1) : Bpatf uE b = 0 := by
  unfold Bpatf; rw [if_neg hb]

theorem onLambdaT_Bpat (uE : ℕ) (hlo : neLo M R ≤ uE) (hhi : uE + 1 < neLo M R + M) :
    OnLambdaT (neLam M R) (Bpatf (L := neLu M R) uE) := by
  intro b hb
  unfold Bpatf
  split_ifs with h1
  · by_contra hne
    apply hb
    left
    have hb0 : betaPat uE b.1 ≠ 0 := by
      intro h0; apply hne; rw [h0, dgS_zero]
    have hv : (b.1 0).val = uE + 1 ∨ (b.1 0).val = uE := by
      unfold betaPat at hb0
      by_contra hcon
      push Not at hcon
      apply hb0
      rw [if_neg hcon.1, if_neg hcon.2]; simp
    unfold neLam
    rcases hv with h | h <;> (refine ⟨?_, ?_⟩ <;> simp only [Set.mem_setOf_eq, h] <;> omega)
  · rfl

theorem onLambdaTildeIn_Bpat (uE : ℕ) (huE : uE % 2 = 0) :
    OnLambdaTildeIn (neLam M R) 2 (Bpatf (L := neLu M R) uE) := by
  refine ⟨?_, ?_⟩
  · intro y hy x hx b hb
    have hyc : ∀ μ : Fin 3, (y μ).val % 2 = 0 := mem_CoarseLattice.mp hy.1
    have hxb := mem_blockOf.mp hx
    unfold staircasePath at hb
    simp only [Finset.mem_union] at hb
    rcases hb with (hb | hb) | hb
    · exact Bpatf_dir_ne uE (by rw [mem_axisSegment] at hb; rw [hb.1]; decide)
    · rw [mem_axisSegment] at hb
      obtain ⟨hb2, hbc, hba, hbb⟩ := hb
      unfold Bpatf
      rw [if_pos hb2]
      have hb0 : (b.1 0).val = (y 0).val := by
        have := hbc 0 (by decide)
        rw [this]
        simp only [corner1, Function.update_of_ne (show (0 : Fin 3) ≠ 2 by decide)]
      have hb1 : (b.1 1).val % 2 = 0 := by
        have h1 := hxb 1
        have : (b.1 1).val = (y 1).val := by omega
        rw [this]; exact hyc 1
      rw [betaPat_zero_of huE (by rw [hb0]; exact hyc 0) (Or.inl hb1), dgS_zero]
    · exact Bpatf_dir_ne uE (by rw [mem_axisSegment] at hb; rw [hb.1]; decide)
  · intro b hb
    obtain ⟨c, hc, rfl⟩ := hb
    have hcc : ∀ μ : Fin 3, (c.1.1 μ).val % 2 = 0 := mem_CoarseLattice.mp c.1.2
    by_cases hc1 : c.2 = 1
    · have hps : ∀ i : ℕ, ∀ ν : Fin 3, ν ≠ 1 → (pathSite c.1.1 c.2 i) ν = c.1.1 ν := by
        intro i ν hν
        induction i with
        | zero => rfl
        | succ i ih =>
          rw [AdalyFormal.Balaban.QOne.pathSite_succ,
            shift_coord_ne (pathSite c.1.1 c.2 i) c.2 ν (by rw [hc1]; exact hν), ih]
      have hb1 : (droppedBondLast 2 c).2 = 1 := hc1
      unfold Bpatf
      rw [if_pos hb1]
      have e0 : ((droppedBondLast 2 c).1 0).val % 2 = 0 := by
        show ((pathSite c.1.1 c.2 (2 - 1)) 0).val % 2 = 0
        rw [hps _ 0 (by decide)]; exact hcc 0
      have e2 : ((droppedBondLast 2 c).1 2).val % 2 = 0 := by
        show ((pathSite c.1.1 c.2 (2 - 1)) 2).val % 2 = 0
        rw [hps _ 2 (by decide)]; exact hcc 2
      rw [betaPat_zero_of huE e0 (Or.inr e2), dgS_zero]
    · exact Bpatf_dir_ne uE (by show c.2 ≠ 1; exact hc1)

end

end AdalyFormal.NcwdhTwo
