import FE2b
import ZXG3H
import ZR2B3

/-!
# FE3a -- fine-cell geometry: the window of a unit plaquette whose unit-cube box lies in `Omega_k` lies in `plaqIn Omega_0`.
`ReachP mu nu a b x w`: `w` is obtained from `x` by at most `a` shifts along `mu` and `b` along `nu` (coordinatewise mod N).
For `x` in the fine cube of the unit site `z` and budgets `<= n = ell^k`, every reached site lies in the fine cube of a site of the unit box of `z`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000
namespace AdalyFormal.FlatEllGeneral

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2 (shift_apply fin_succ_val)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)


theorem cell_shift_arith (U n z r t : ℕ) (hn : 0 < n) (hz : z < U + 1) (hr : r < n) (ht : t ≤ n) :
    ((n * z + r + t) % ((U + 1) * n)) / n = z ∨
      ((n * z + r + t) % ((U + 1) * n)) / n = (z + 1) % (U + 1) := by
  set u := n * z + r + t with hu
  have hN : n * z + n ≤ (U + 1) * n := by nlinarith
  by_cases hlt : u < (U + 1) * n
  · rw [Nat.mod_eq_of_lt hlt]
    by_cases h1 : u < (z + 1) * n
    · left
      apply Nat.div_eq_of_lt_le
      · nlinarith
      · nlinarith
    · right
      have hz1 : z + 1 < U + 1 := by
        by_contra hc
        have : U + 1 ≤ z + 1 := by omega
        have : (U + 1) * n ≤ (z + 1) * n := Nat.mul_le_mul_right n this
        omega
      rw [Nat.mod_eq_of_lt hz1]
      apply Nat.div_eq_of_lt_le
      · nlinarith
      · nlinarith
  · have hzU : z = U := by
      by_contra hc
      have : z + 1 < U + 1 := by omega
      have : (z + 1) * n < (U + 1) * n := Nat.mul_lt_mul_of_pos_right this hn
      nlinarith
    subst hzU
    have h2 : u < 2 * ((z + 1) * n) := by nlinarith
    have : u % ((z + 1) * n) = u - (z + 1) * n := by
      rw [Nat.mod_eq_sub_mod (by omega)]
      apply Nat.mod_eq_of_lt
      omega
    rw [this]
    right
    have : (z + 1) % (z + 1) = 0 := Nat.mod_self _
    rw [this]
    apply Nat.div_eq_of_lt_le
    · omega
    · have e : (z + 1) * n = n * z + n := by ring
      rw [e, hu]
      generalize n * z = m
      omega

section reach
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent)

def ReachP (μ ν : Fin 3) (a b : ℕ) (x w : PeriodicLatticeSite (scaleUp ell k Lu)) : Prop :=
  ∀ ρ : Fin 3, ∃ t : ℕ, t ≤ (if ρ = μ then a else if ρ = ν then b else 0) ∧
    (w ρ).val = ((x ρ).val + t) % (scaleUp ell k Lu ρ + 1)

variable {ell k Lu}

theorem reach_refl (μ ν : Fin 3) (a b : ℕ) (x : PeriodicLatticeSite (scaleUp ell k Lu)) :
    ReachP ell k Lu μ ν a b x x := fun ρ =>
  ⟨0, Nat.zero_le _, by simpa using (Nat.mod_eq_of_lt (x ρ).isLt).symm⟩

theorem reach_mono {μ ν : Fin 3} {a b a' b' : ℕ} (ha : a ≤ a') (hb : b ≤ b')
    {x w : PeriodicLatticeSite (scaleUp ell k Lu)} (h : ReachP ell k Lu μ ν a b x w) :
    ReachP ell k Lu μ ν a' b' x w := by
  intro ρ
  obtain ⟨t, ht, hw⟩ := h ρ
  refine ⟨t, le_trans ht ?_, hw⟩
  by_cases h1 : ρ = μ
  · subst h1; simp [ha]
  · by_cases h2 : ρ = ν
    · subst h2; simp [h1, hb]
    · simp [h1, h2]

theorem reach_shift_mu {μ ν : Fin 3} {a b : ℕ} (hN : ∀ ρ, 1 ≤ scaleUp ell k Lu ρ)
    {x w : PeriodicLatticeSite (scaleUp ell k Lu)} (h : ReachP ell k Lu μ ν a b x w) :
    ReachP ell k Lu μ ν (a + 1) b x (periodicLatticeShift w μ) := by
  intro ρ
  obtain ⟨t, ht, hw⟩ := h ρ
  by_cases hρ : ρ = μ
  · subst hρ
    refine ⟨t + 1, by simpa using ht, ?_⟩
    rw [shift_apply]; simp only [if_true]
    rw [fin_succ_val ρ (hN ρ), hw, Nat.mod_add_mod, add_assoc]
  · refine ⟨t, ?_, ?_⟩
    · by_cases h2 : ρ = ν
      · subst h2; simpa [hρ] using ht
      · simpa [hρ, h2] using ht
    · rw [shift_apply]; simp only [hρ, if_false]; exact hw

theorem reach_shift_nu {μ ν : Fin 3} (hμν : μ ≠ ν) {a b : ℕ} (hN : ∀ ρ, 1 ≤ scaleUp ell k Lu ρ)
    {x w : PeriodicLatticeSite (scaleUp ell k Lu)} (h : ReachP ell k Lu μ ν a b x w) :
    ReachP ell k Lu μ ν a (b + 1) x (periodicLatticeShift w ν) := by
  intro ρ
  obtain ⟨t, ht, hw⟩ := h ρ
  by_cases hρ : ρ = ν
  · subst hρ
    refine ⟨t + 1, by simpa [Ne.symm hμν] using ht, ?_⟩
    rw [shift_apply]; simp only [if_true]
    rw [fin_succ_val ρ (hN ρ), hw, Nat.mod_add_mod, add_assoc]
  · refine ⟨t, ?_, ?_⟩
    · by_cases h2 : ρ = μ
      · subst h2; simpa [hρ] using ht
      · simpa [hρ, h2] using ht
    · rw [shift_apply]; simp only [hρ, if_false]; exact hw

theorem reach_coarse_mu {μ ν : Fin 3} {a b : ℕ} (hN : ∀ ρ, 1 ≤ scaleUp ell k Lu ρ)
    {x w : PeriodicLatticeSite (scaleUp ell k Lu)} (h : ReachP ell k Lu μ ν a b x w) (t : ℕ) :
    ReachP ell k Lu μ ν (a + t) b x (coarseShift w t μ) := by
  induction t with
  | zero => simpa [coarseShift] using h
  | succ t ih =>
    have : coarseShift w (t + 1) μ = periodicLatticeShift (coarseShift w t μ) μ := by
      unfold coarseShift; rw [Function.iterate_succ_apply']
    rw [this, ← add_assoc]
    exact reach_shift_mu hN ih

theorem reach_coarse_nu {μ ν : Fin 3} (hμν : μ ≠ ν) {a b : ℕ} (hN : ∀ ρ, 1 ≤ scaleUp ell k Lu ρ)
    {x w : PeriodicLatticeSite (scaleUp ell k Lu)} (h : ReachP ell k Lu μ ν a b x w) (t : ℕ) :
    ReachP ell k Lu μ ν a (b + t) x (coarseShift w t ν) := by
  induction t with
  | zero => simpa [coarseShift] using h
  | succ t ih =>
    have : coarseShift w (t + 1) ν = periodicLatticeShift (coarseShift w t ν) ν := by
      unfold coarseShift; rw [Function.iterate_succ_apply']
    rw [this, ← add_assoc]
    exact reach_shift_nu hμν hN ih

end reach

/-- the unit box of `z`: every coordinate `z ρ` or `z ρ + 1` -/
def InBox {Lu : PeriodicLatticeExtent} (z c : PeriodicLatticeSite Lu) : Prop :=
  ∀ ρ : Fin 3, c ρ = z ρ ∨ c ρ = z ρ + 1

section cells
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)

/-- the fine site `w` lies in the fine cube of the unit site `c` -/
def NearCell (w : PeriodicLatticeSite (scaleUp ell k Lu)) (c : PeriodicLatticeSite Lu) : Prop :=
  ∀ ρ : Fin 3, (w ρ).val / ell ^ k = (c ρ).val


variable {ell k Lu}

theorem nearCell_of_block (z : PeriodicLatticeSite Lu) (x : PeriodicLatticeSite (scaleUp ell k Lu))
    (hx : x ∈ blockOf (embY ell k Lu hell z) (ell ^ k)) : NearCell ell k Lu x z := by
  intro ρ
  have h := (mem_blockOf.mp hx) ρ
  rw [embY_val] at h
  apply Nat.div_eq_of_lt_le
  · rw [mul_comm]; exact h.1
  · rw [add_mul, one_mul, mul_comm]; exact h.2

theorem om_k_sub_om0 {L : PeriodicLatticeExtent} (S : Tower L) (hS : ∀ j, S.Om (j + 1) ⊆ S.Om j) (i : ℕ) :
    S.Om i ⊆ S.Om 0 := by
  induction i with
  | zero => exact fun _ h => h
  | succ i ih => exact fun x hx => ih (hS i hx)

theorem mem_of_nearCell (hell : 0 < ell) {M : ℕ} (S : Set (PeriodicLatticeSite (scaleUp ell k Lu)))
    (hS : BlockClosed (bigSide M ell k) S) (c : PeriodicLatticeSite Lu) (hc : embY ell k Lu hell c ∈ S)
    (w : PeriodicLatticeSite (scaleUp ell k Lu)) (hw : NearCell ell k Lu w c) : w ∈ S := by
  refine hS _ hc w (fun ρ => ?_)
  have e1 : (w ρ).val / (ell ^ k * M) = (c ρ).val / M := by
    rw [← Nat.div_div_eq_div_mul, hw ρ]
  have e2 : ((embY ell k Lu hell c) ρ).val / (ell ^ k * M) = (c ρ).val / M := by
    rw [embY_val]; exact Nat.mul_div_mul_left _ _ (pow_pos hell k)
  unfold bigSide
  rw [mul_comm M, e1, e2]

theorem box_of_reach (hell : 0 < ell) {μ ν : Fin 3} (hu : ∀ ρ, 1 ≤ Lu ρ)
    (z : PeriodicLatticeSite Lu) {x w : PeriodicLatticeSite (scaleUp ell k Lu)}
    (hx : NearCell ell k Lu x z) (hr : ReachP ell k Lu μ ν (ell ^ k) (ell ^ k) x w) :
    ∃ c : PeriodicLatticeSite Lu, InBox z c ∧ NearCell ell k Lu w c := by
  have hn : 0 < ell ^ k := pow_pos hell k
  have hbd : ∀ ρ : Fin 3, (w ρ).val / ell ^ k < Lu ρ + 1 := by
    intro ρ
    have h1 : (w ρ).val < (Lu ρ + 1) * ell ^ k :=
      lt_of_lt_of_eq (w ρ).isLt (scaleUp_succ ell k Lu hell ρ)
    exact Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact h1)
  refine ⟨fun ρ => ⟨(w ρ).val / ell ^ k, hbd ρ⟩, ?_, fun ρ => rfl⟩
  intro ρ
  obtain ⟨t, ht, hw⟩ := hr ρ
  have ht' : t ≤ ell ^ k := by
    refine le_trans ht ?_
    by_cases h1 : ρ = μ
    · simp [h1]
    · by_cases h2 : ρ = ν
      · simp [h1, h2]
      · simp [h1, h2]
  have hxr : (x ρ).val = ell ^ k * (z ρ).val + (x ρ).val % ell ^ k := by
    have := Nat.div_add_mod (x ρ).val (ell ^ k)
    rw [hx ρ] at this
    exact this.symm
  have hr' : (x ρ).val % ell ^ k < ell ^ k := Nat.mod_lt _ hn
  have key := cell_shift_arith (Lu ρ) (ell ^ k) (z ρ).val ((x ρ).val % ell ^ k) t hn (z ρ).isLt hr' ht'
  have hxw : (w ρ).val = (ell ^ k * (z ρ).val + (x ρ).val % ell ^ k + t) % ((Lu ρ + 1) * ell ^ k) := by
    have h3 : (w ρ).val = ((x ρ).val + t) % ((Lu ρ + 1) * ell ^ k) := by
      rw [hw]; exact congrArg (fun m => ((x ρ).val + t) % m) (scaleUp_succ ell k Lu hell ρ)
    rw [h3]; congr 1; rw [← hxr]
  rw [← hxw] at key
  rcases key with h | h
  · left; exact Fin.ext h
  · right
    apply Fin.ext
    rw [fin_succ_val ρ (hu ρ)]
    exact h

end cells

#print axioms cell_shift_arith
#print axioms box_of_reach

end AdalyFormal.FlatEllGeneral
