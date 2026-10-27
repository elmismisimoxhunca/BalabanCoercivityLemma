import SoK1
import NuK4

/-!
# SoK4 -- the pattern competitor lies in `Λ̃` for general `ell`: `OnLambdaT` and `OnLambdaTildeIn` (lane sites_only_20261019)

* staircase bonds in direction `1` sit at an aligned `u₀` and at `u₁ ≢ ell - 1 (mod ell)` (the staircase offset in direction 1 is `≤ ell - 2`); the slice `uE + 1` carries the pattern only
  at `u₀ = uE + 1`, which is not aligned;
* the dropped direction-`1` bond of a coarse bond sits at `u₀`, `u₂` aligned, hence `u₂ ≢ ell - 1`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.SitesOnly

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
open AdalyFormal.NcwdhTwo

section
variable [CfData]
variable {M R : ℕ}

theorem betaPat_zero_of {L : PeriodicLatticeExtent} {ell uE : ℕ} (hell : 2 ≤ ell) (huE : uE % ell + 2 ≤ ell) {x : PeriodicLatticeSite L}
    (hx0 : (x 0).val % ell = 0)
    (h : (x 0).val = uE → (x 1).val % ell ≠ ell - 1 ∨ (x 2).val % ell ≠ ell - 1) : betaPat ell uE x = 0 := by
  unfold betaPat
  have h1 : (x 0).val ≠ uE + 1 := by
    intro h'
    have e : uE = ell * (uE / ell) + uE % ell := (Nat.div_add_mod uE ell).symm
    have : (uE + 1) % ell = uE % ell + 1 := by
      have h3 : uE + 1 = ell * (uE / ell) + (uE % ell + 1) := by omega
      rw [h3, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    rw [h', this] at hx0
    omega
  rw [if_neg h1, zero_add]
  split_ifs with h2 h3
  · exfalso; rcases h h2 with h | h <;> [exact h h3.1; exact h h3.2]
  · rfl
  · rfl

theorem Bpatf_dir_ne {L : PeriodicLatticeExtent} (ell uE : ℕ) {b : Bond L} (hb : b.2 ≠ 1) : Bpatf ell uE b = 0 := by
  unfold Bpatf; rw [if_neg hb]

theorem onLambdaT_Bpat (ell uE : ℕ) (hlo : neLo M R ≤ uE) (hhi : uE + 1 < neLo M R + M) :
    OnLambdaT (neLam M R) (Bpatf (L := neLu M R) ell uE) := by
  intro b hb
  unfold Bpatf
  split_ifs with h1
  · by_contra hne
    apply hb
    left
    have hb0 : betaPat ell uE b.1 ≠ 0 := by
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

/-- `b % ell ≠ ell - 1` when `b` is within `ell - 2` above an aligned point. -/
theorem mod_ne_last {ell y b : ℕ} (hell : 2 ≤ ell) (hy : y % ell = 0) (h1 : y ≤ b) (h2 : b + 1 < y + ell) : b % ell ≠ ell - 1 := by
  obtain ⟨q, hq⟩ : ell ∣ y := Nat.dvd_of_mod_eq_zero hy
  have hlt : b - ell * q < ell - 1 := by omega
  have e : b = ell * q + (b - ell * q) := by omega
  rw [e, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  omega

theorem onLambdaTildeIn_Bpat (ell uE : ℕ) (hell : 2 ≤ ell) (huE : uE % ell + 2 ≤ ell) :
    OnLambdaTildeIn (neLam M R) ell (Bpatf (L := neLu M R) ell uE) := by
  refine ⟨?_, ?_⟩
  · intro y hy x hx b hb
    have hyc : ∀ μ : Fin 3, (y μ).val % ell = 0 := mem_CoarseLattice.mp hy.1
    have hxb := mem_blockOf.mp hx
    unfold staircasePath at hb
    simp only [Finset.mem_union] at hb
    rcases hb with (hb | hb) | hb
    · exact Bpatf_dir_ne ell uE (by rw [mem_axisSegment] at hb; rw [hb.1]; decide)
    · rw [mem_axisSegment] at hb
      obtain ⟨hb2, hbc, hba, hbb⟩ := hb
      unfold Bpatf
      rw [if_pos hb2]
      have hb0 : (b.1 0).val = (y 0).val := by
        have := hbc 0 (by decide)
        rw [this]
        simp only [corner1, Function.update_of_ne (show (0 : Fin 3) ≠ 2 by decide)]
      have hb1 : (b.1 1).val % ell ≠ ell - 1 := by
        have h1 := hxb 1
        exact mod_ne_last hell (hyc 1) (by omega) (by omega)
      rw [betaPat_zero_of hell huE (by rw [hb0]; exact hyc 0) (fun _ => Or.inl hb1), dgS_zero]
    · exact Bpatf_dir_ne ell uE (by rw [mem_axisSegment] at hb; rw [hb.1]; decide)
  · intro b hb
    obtain ⟨c, hc, rfl⟩ := hb
    have hcc : ∀ μ : Fin 3, (c.1.1 μ).val % ell = 0 := mem_CoarseLattice.mp c.1.2
    by_cases hc1 : c.2 = 1
    · have hps : ∀ i : ℕ, ∀ ν : Fin 3, ν ≠ 1 → (pathSite c.1.1 c.2 i) ν = c.1.1 ν := by
        intro i ν hν
        induction i with
        | zero => rfl
        | succ i ih =>
          rw [AdalyFormal.Balaban.QOne.pathSite_succ,
            shift_coord_ne (pathSite c.1.1 c.2 i) c.2 ν (by rw [hc1]; exact hν), ih]
      have hb1 : (droppedBondLast ell c).2 = 1 := hc1
      unfold Bpatf
      rw [if_pos hb1]
      have e0 : ((droppedBondLast ell c).1 0).val % ell = 0 := by
        show ((pathSite c.1.1 c.2 (ell - 1)) 0).val % ell = 0
        rw [hps _ 0 (by decide)]; exact hcc 0
      have e2 : ((droppedBondLast ell c).1 2).val % ell ≠ ell - 1 := by
        show ((pathSite c.1.1 c.2 (ell - 1)) 2).val % ell ≠ ell - 1
        rw [hps _ 2 (by decide), hcc 2]; omega
      rw [betaPat_zero_of hell huE e0 (fun _ => Or.inr e2), dgS_zero]
    · exact Bpatf_dir_ne ell uE (by show c.2 ≠ 1; exact hc1)

end

#print axioms onLambdaTildeIn_Bpat
#print axioms onLambdaT_Bpat

end AdalyFormal.SitesOnly
