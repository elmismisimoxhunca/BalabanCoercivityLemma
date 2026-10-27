import M2B5a

/-!
# M2B5b -- the lattice cutoff `chi z F x = ∏_σ F σ (offc z x σ)` and its difference calculus (m2_bridge_20261014, Layer B1)

`ProfSpec f τ1 τ2 lo hi` : a one-variable profile (for `f = prof a b w`: `τ1 = 1/w`, `τ2 = 2/w²`, `lo = a - 2w + 2`, `hi = b - 1`).
`CoordSpec n F τ1 τ2` : what the calculus needs of the factor used in a coordinate of length `N = n + 1` -- values in `[0,1]`, forward / backward first
differences `≤ τ1`, centred second difference `≤ τ2`, and compatibility of `F` with the circular shift (`F ((o+1) % N) = F (o+1)`, `F ((o+n) % N) = F (o-1)`).
Two instances: `coordSpec_prof` (a narrow coordinate: the cube side `s ≤ N`, profile vanishing near the faces) and `coordSpec_one` (a WIDE coordinate,
`N < s`: the cube wraps, no cutoff is needed, `F ≡ 1`).
With `hF : ∀ σ, CoordSpec (L σ) (F σ) τ1 τ2`:
* `chi_nonneg`, `chi_le_one`;
* `chi_first_fwd` : `|χ(x+e_μ) - χ(x)| ≤ τ1`;   `chi_first_bwd` : `|χ(x-e_μ) - χ(x)| ≤ τ1`;
* `chi_second` : `|χ(x+e_ν) + χ(x-e_ν) - 2χ(x)| ≤ τ2`;
* `chi_mixed` : for `ν ≠ μ`, `|(χ(x+e_μ) - χ(x)) - (χ(x-e_ν+e_μ) - χ(x-e_ν))| ≤ τ1²`;
* `chi_support_box` : coordinatewise `Reach` (`F σ (offc x) ≠ 0` and `pcd ≤ 6` give `offc y < s`) yields: `χ x ≠ 0` and `pdist x y ≤ 6` give `y ∈ siteBox z s`;
* `chi_one` : `χ x = 1` when every factor is `1`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M2Bridge

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)

variable {L : PeriodicLatticeExtent}

structure ProfSpec (f : ℕ → ℝ) (τ1 τ2 : ℝ) (lo hi : ℕ) : Prop where
  nonneg : ∀ o, 0 ≤ f o
  le_one : ∀ o, f o ≤ 1
  first : ∀ o, |f (o + 1) - f o| ≤ τ1
  second : ∀ o, |f (o + 2) + f o - 2 * f (o + 1)| ≤ τ2
  supp : ∀ o, f o ≠ 0 → lo ≤ o ∧ o ≤ hi
  lo2 : 2 ≤ lo

theorem ProfSpec.f0 {f : ℕ → ℝ} {τ1 τ2 : ℝ} {lo hi : ℕ} (hs : ProfSpec f τ1 τ2 lo hi) : f 0 = 0 := by
  by_contra hne; have := (hs.supp 0 hne).1; have := hs.lo2; omega

theorem ProfSpec.fbig {f : ℕ → ℝ} {τ1 τ2 : ℝ} {lo hi : ℕ} (hs : ProfSpec f τ1 τ2 lo hi) {o : ℕ} (ho : hi < o) : f o = 0 := by
  by_contra hne; have := (hs.supp o hne).2; omega

theorem ProfSpec.tau1_nonneg {f : ℕ → ℝ} {τ1 τ2 : ℝ} {lo hi : ℕ} (hs : ProfSpec f τ1 τ2 lo hi) : 0 ≤ τ1 :=
  le_trans (abs_nonneg _) (hs.first 0)

theorem ProfSpec.tau2_nonneg {f : ℕ → ℝ} {τ1 τ2 : ℝ} {lo hi : ℕ} (hs : ProfSpec f τ1 τ2 lo hi) : 0 ≤ τ2 :=
  le_trans (abs_nonneg _) (hs.second 0)

theorem f_shift {f : ℕ → ℝ} {τ1 τ2 : ℝ} {lo hi : ℕ} (hs : ProfSpec f τ1 τ2 lo hi) {N o : ℕ} (hN : hi + 2 ≤ N) (ho : o < N) :
    f ((o + 1) % N) = f (o + 1) := by
  by_cases h : o + 1 < N
  · rw [Nat.mod_eq_of_lt h]
  · have h1 : o + 1 = N := by omega
    rw [h1, Nat.mod_self, hs.f0, hs.fbig (by omega)]

theorem f_back {f : ℕ → ℝ} {τ1 τ2 : ℝ} {lo hi : ℕ} (hs : ProfSpec f τ1 τ2 lo hi) {n o : ℕ} (hN : hi + 1 ≤ n) (ho : o < n + 1) :
    f ((o + n) % (n + 1)) = f (o - 1) := by
  rcases Nat.eq_zero_or_pos o with h0 | hpos
  · subst h0
    have : (0 + n) % (n + 1) = n := by rw [zero_add]; exact Nat.mod_eq_of_lt (by omega)
    rw [this, hs.fbig (by omega)]
    simp [hs.f0]
  · have : (o + n) % (n + 1) = o - 1 := by
      have e : o + n = (o - 1) + (n + 1) := by omega
      rw [e, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [this]

theorem f_first_back {f : ℕ → ℝ} {τ1 τ2 : ℝ} {lo hi : ℕ} (hs : ProfSpec f τ1 τ2 lo hi) (o : ℕ) :
    |f (o - 1) - f o| ≤ τ1 := by
  rcases o with _ | o
  · simp [hs.tau1_nonneg]
  · simpa [abs_sub_comm] using hs.first o

theorem f_second_back {f : ℕ → ℝ} {τ1 τ2 : ℝ} {lo hi : ℕ} (hs : ProfSpec f τ1 τ2 lo hi) (o : ℕ) :
    |f (o + 1) + f (o - 1) - 2 * f o| ≤ τ2 := by
  rcases o with _ | o
  · have h1 : f 1 = 0 := by
      by_contra hne; have := (hs.supp 1 hne).1; have := hs.lo2; omega
    simp [h1, hs.f0, hs.tau2_nonneg]
  · have := hs.second o
    simpa [add_assoc, add_comm, add_left_comm] using this

/-- what the difference calculus needs of the factor used in one coordinate of length `n + 1`. -/
structure CoordSpec (n : ℕ) (F : ℕ → ℝ) (τ1 τ2 : ℝ) : Prop where
  nonneg : ∀ o, 0 ≤ F o
  le_one : ∀ o, F o ≤ 1
  tau1 : 0 ≤ τ1
  first : ∀ o, |F (o + 1) - F o| ≤ τ1
  first_back : ∀ o, |F (o - 1) - F o| ≤ τ1
  second_back : ∀ o, |F (o + 1) + F (o - 1) - 2 * F o| ≤ τ2
  shift_eq : ∀ o, o < n + 1 → F ((o + 1) % (n + 1)) = F (o + 1)
  back_eq : ∀ o, o < n + 1 → F ((o + n) % (n + 1)) = F (o - 1)

theorem coordSpec_prof {f : ℕ → ℝ} {τ1 τ2 : ℝ} {lo hi n : ℕ} (hs : ProfSpec f τ1 τ2 lo hi) (hn : hi + 1 ≤ n) :
    CoordSpec n f τ1 τ2 where
  nonneg := hs.nonneg
  le_one := hs.le_one
  tau1 := hs.tau1_nonneg
  first := hs.first
  first_back := f_first_back hs
  second_back := f_second_back hs
  shift_eq := fun o ho => f_shift hs (N := n + 1) (by omega) ho
  back_eq := fun o ho => f_back hs hn ho

theorem coordSpec_one {n : ℕ} {τ1 τ2 : ℝ} (h1 : 0 ≤ τ1) (h2 : 0 ≤ τ2) : CoordSpec n (fun _ => (1 : ℝ)) τ1 τ2 where
  nonneg := fun _ => by norm_num
  le_one := fun _ => le_rfl
  tau1 := h1
  first := fun _ => by simpa using h1
  first_back := fun _ => by simpa using h1
  second_back := fun _ => by norm_num; exact h2
  shift_eq := fun _ _ => rfl
  back_eq := fun _ _ => rfl

/-- product over three coordinates, a separate factor in each. -/
def Fprod (F : Fin 3 → ℕ → ℝ) (O : Fin 3 → ℕ) : ℝ := ∏ σ, F σ (O σ)

theorem Fprod_eq (F : Fin 3 → ℕ → ℝ) (O : Fin 3 → ℕ) (μ : Fin 3) :
    Fprod F O = F μ (O μ) * ∏ σ ∈ univ.erase μ, F σ (O σ) :=
  (Finset.mul_prod_erase univ (fun σ => F σ (O σ)) (mem_univ μ)).symm

theorem Fprod_update (F : Fin 3 → ℕ → ℝ) (O : Fin 3 → ℕ) (μ : Fin 3) (v : ℕ) :
    Fprod F (Function.update O μ v) = F μ v * ∏ σ ∈ univ.erase μ, F σ (O σ) := by
  rw [Fprod_eq F _ μ]
  simp only [Function.update_self]
  congr 1
  apply prod_congr rfl
  intro σ hσ
  rw [Function.update_of_ne (ne_of_mem_erase hσ)]

theorem rest_nonneg {F : Fin 3 → ℕ → ℝ} (h0 : ∀ σ o, 0 ≤ F σ o) (O : Fin 3 → ℕ) (μ : Fin 3) :
    0 ≤ ∏ σ ∈ univ.erase μ, F σ (O σ) :=
  prod_nonneg (fun σ _ => h0 _ _)

theorem rest_le_one {F : Fin 3 → ℕ → ℝ} (h0 : ∀ σ o, 0 ≤ F σ o) (h1 : ∀ σ o, F σ o ≤ 1) (O : Fin 3 → ℕ) (μ : Fin 3) :
    ∏ σ ∈ univ.erase μ, F σ (O σ) ≤ 1 :=
  prod_le_one (fun σ _ => h0 _ _) (fun σ _ => h1 _ _)

/-- the two-update formula (`ν ≠ μ`). -/
theorem Fprod_update2 (F : Fin 3 → ℕ → ℝ) (O : Fin 3 → ℕ) {μ ν : Fin 3} (hne : ν ≠ μ) (v w : ℕ) :
    Fprod F (Function.update (Function.update O ν w) μ v)
      = F μ v * F ν w * ∏ σ ∈ (univ.erase μ).erase ν, F σ (O σ) := by
  rw [Fprod_update]
  have hν : ν ∈ univ.erase μ := mem_erase.mpr ⟨hne, mem_univ ν⟩
  rw [← Finset.mul_prod_erase (univ.erase μ) (fun σ => F σ (Function.update O ν w σ)) hν]
  simp only [Function.update_self]
  rw [mul_assoc]
  congr 2
  apply prod_congr rfl
  intro σ hσ
  rw [Function.update_of_ne (ne_of_mem_erase hσ)]

/-- the lattice cutoff -/
def chi (z : PeriodicLatticeSite L) (F : Fin 3 → ℕ → ℝ) (x : PeriodicLatticeSite L) : ℝ := Fprod F (offc z x)

theorem offc_shift_eq (hL : ∀ σ, 1 ≤ L σ) (z x : PeriodicLatticeSite L) (μ : Fin 3) :
    offc z (periodicLatticeShift x μ) = Function.update (offc z x) μ ((offc z x μ + 1) % (L μ + 1)) := by
  funext σ
  by_cases h : σ = μ
  · subst h; rw [Function.update_self]; exact offc_shift_same hL z x σ
  · rw [Function.update_of_ne h]; exact offc_shift_ne z x h

theorem offc_shiftBack_eq (hL : ∀ σ, 1 ≤ L σ) (z x : PeriodicLatticeSite L) (μ : Fin 3) :
    offc z (periodicLatticeShiftBack x μ) = Function.update (offc z x) μ ((offc z x μ + L μ) % (L μ + 1)) := by
  funext σ
  by_cases h : σ = μ
  · subst h; rw [Function.update_self]; exact offc_shiftBack_same hL z x σ
  · rw [Function.update_of_ne h]; exact offc_shiftBack_ne z x h

theorem offc_near {N z u v o ρ : ℕ} (hz : z < N) (hu : u < N) (hv : v < N) (ho : o = (u + (N - z)) % N)
    (hlo : ρ ≤ o) (hhi : o + ρ < N) (hp : pcd N u v ≤ ρ) : (v + (N - z)) % N ≤ o + ρ := by
  have hu' : (u + (N - z)) % N = if u < z then u + (N - z) else u - z := by
    split_ifs with h
    · exact Nat.mod_eq_of_lt (by omega)
    · rw [show u + (N - z) = (u - z) + N by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
  have hv' : (v + (N - z)) % N = if v < z then v + (N - z) else v - z := by
    split_ifs with h
    · exact Nat.mod_eq_of_lt (by omega)
    · rw [show v + (N - z) = (v - z) + N by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
  rw [hu'] at ho
  rw [hv']
  unfold pcd at hp
  split_ifs at ho hp ⊢ <;> omega

/-- reach of a factor: where the factor is nonzero, every site within circular distance `6` (coordinatewise) is inside the box (offset `< s`). -/
def Reach (z : PeriodicLatticeSite L) (σ : Fin 3) (s : ℕ) (F : ℕ → ℝ) : Prop :=
  ∀ x y : PeriodicLatticeSite L, F (offc z x σ) ≠ 0 → pcd (L σ + 1) (x σ).val (y σ).val ≤ 6 → offc z y σ < s

theorem reach_prof (z : PeriodicLatticeSite L) (σ : Fin 3) {s : ℕ} {f : ℕ → ℝ} {τ1 τ2 : ℝ} {lo hi : ℕ}
    (hs : ProfSpec f τ1 τ2 lo hi) (hlo : 6 ≤ lo) (hhi : hi + 6 < s) (hsN : s ≤ L σ + 1) : Reach z σ s f := by
  intro x y hx hp
  obtain ⟨h1, h2⟩ := hs.supp _ hx
  have := offc_near (N := L σ + 1) (z := (z σ).val) (u := (x σ).val) (v := (y σ).val) (o := offc z x σ) (ρ := 6)
    (z σ).isLt (x σ).isLt (y σ).isLt rfl (by omega) (by omega) hp
  show offc z y σ < s
  unfold offc
  omega

theorem reach_one (z : PeriodicLatticeSite L) (σ : Fin 3) {s : ℕ} (hw : L σ + 1 < s) : Reach z σ s (fun _ => (1 : ℝ)) := by
  intro x y _ _
  have := offc_lt z y σ
  omega

section calculus

variable {F : Fin 3 → ℕ → ℝ} {τ1 τ2 : ℝ} (hF : ∀ σ, CoordSpec (L σ) (F σ) τ1 τ2) (hL : ∀ σ, 1 ≤ L σ)
  (z : PeriodicLatticeSite L)

theorem chi_self (x : PeriodicLatticeSite L) (μ : Fin 3) :
    chi z F x = F μ (offc z x μ) * ∏ σ ∈ univ.erase μ, F σ (offc z x σ) := Fprod_eq F _ μ

include hF hL

theorem chi_shift (x : PeriodicLatticeSite L) (μ : Fin 3) :
    chi z F (periodicLatticeShift x μ) = F μ (offc z x μ + 1) * ∏ σ ∈ univ.erase μ, F σ (offc z x σ) := by
  unfold chi
  rw [offc_shift_eq hL, Fprod_update, (hF μ).shift_eq _ (offc_lt z x μ)]

theorem chi_shiftBack (x : PeriodicLatticeSite L) (μ : Fin 3) :
    chi z F (periodicLatticeShiftBack x μ) = F μ (offc z x μ - 1) * ∏ σ ∈ univ.erase μ, F σ (offc z x σ) := by
  unfold chi
  rw [offc_shiftBack_eq hL, Fprod_update, (hF μ).back_eq _ (offc_lt z x μ)]

theorem chi_nonneg (x : PeriodicLatticeSite L) : 0 ≤ chi z F x := by
  unfold chi Fprod
  exact prod_nonneg (fun σ _ => (hF σ).nonneg _)

theorem chi_le_one (x : PeriodicLatticeSite L) : chi z F x ≤ 1 := by
  unfold chi Fprod
  exact prod_le_one (fun σ _ => (hF σ).nonneg _) (fun σ _ => (hF σ).le_one _)

theorem chi_first_fwd (x : PeriodicLatticeSite L) (μ : Fin 3) :
    |chi z F (periodicLatticeShift x μ) - chi z F x| ≤ τ1 := by
  rw [chi_shift hF hL z x μ, chi_self z x μ, ← sub_mul, abs_mul]
  have h0 := rest_nonneg (fun σ o => (hF σ).nonneg o) (offc z x) μ
  have h1 := rest_le_one (fun σ o => (hF σ).nonneg o) (fun σ o => (hF σ).le_one o) (offc z x) μ
  rw [abs_of_nonneg h0]
  calc |F μ (offc z x μ + 1) - F μ (offc z x μ)| * ∏ σ ∈ univ.erase μ, F σ (offc z x σ)
      ≤ τ1 * 1 := mul_le_mul ((hF μ).first _) h1 h0 (hF μ).tau1
    _ = τ1 := mul_one _

theorem chi_first_bwd (x : PeriodicLatticeSite L) (μ : Fin 3) :
    |chi z F (periodicLatticeShiftBack x μ) - chi z F x| ≤ τ1 := by
  rw [chi_shiftBack hF hL z x μ, chi_self z x μ, ← sub_mul, abs_mul]
  have h0 := rest_nonneg (fun σ o => (hF σ).nonneg o) (offc z x) μ
  have h1 := rest_le_one (fun σ o => (hF σ).nonneg o) (fun σ o => (hF σ).le_one o) (offc z x) μ
  rw [abs_of_nonneg h0]
  calc |F μ (offc z x μ - 1) - F μ (offc z x μ)| * ∏ σ ∈ univ.erase μ, F σ (offc z x σ)
      ≤ τ1 * 1 := mul_le_mul ((hF μ).first_back _) h1 h0 (hF μ).tau1
    _ = τ1 := mul_one _

theorem chi_second (x : PeriodicLatticeSite L) (ν : Fin 3) :
    |chi z F (periodicLatticeShift x ν) + chi z F (periodicLatticeShiftBack x ν) - 2 * chi z F x| ≤ τ2 := by
  rw [chi_shift hF hL z x ν, chi_shiftBack hF hL z x ν, chi_self z x ν]
  have h0 := rest_nonneg (fun σ o => (hF σ).nonneg o) (offc z x) ν
  have h1 := rest_le_one (fun σ o => (hF σ).nonneg o) (fun σ o => (hF σ).le_one o) (offc z x) ν
  have τ2nn : 0 ≤ τ2 := le_trans (abs_nonneg _) ((hF ν).second_back 0)
  have e : F ν (offc z x ν + 1) * (∏ σ ∈ univ.erase ν, F σ (offc z x σ))
        + F ν (offc z x ν - 1) * (∏ σ ∈ univ.erase ν, F σ (offc z x σ))
      - 2 * (F ν (offc z x ν) * ∏ σ ∈ univ.erase ν, F σ (offc z x σ))
      = (F ν (offc z x ν + 1) + F ν (offc z x ν - 1) - 2 * F ν (offc z x ν)) * ∏ σ ∈ univ.erase ν, F σ (offc z x σ) := by ring
  rw [e, abs_mul, abs_of_nonneg h0]
  calc |F ν (offc z x ν + 1) + F ν (offc z x ν - 1) - 2 * F ν (offc z x ν)| * ∏ σ ∈ univ.erase ν, F σ (offc z x σ)
      ≤ τ2 * 1 := mul_le_mul ((hF ν).second_back _) h1 h0 τ2nn
    _ = τ2 := mul_one _

theorem chi_mixed (x : PeriodicLatticeSite L) {μ ν : Fin 3} (hne : ν ≠ μ) :
    |(chi z F (periodicLatticeShift x μ) - chi z F x)
      - (chi z F (periodicLatticeShift (periodicLatticeShiftBack x ν) μ) - chi z F (periodicLatticeShiftBack x ν))| ≤ τ1 ^ 2 := by
  set O := offc z x with hO
  set T : ℝ := ∏ σ ∈ (univ.erase μ).erase ν, F σ (O σ) with hT
  have hν : ν ∈ univ.erase μ := mem_erase.mpr ⟨hne, mem_univ ν⟩
  have hμ : μ ∈ univ.erase ν := mem_erase.mpr ⟨hne.symm, mem_univ μ⟩
  have hT0 : 0 ≤ T := prod_nonneg (fun σ _ => (hF σ).nonneg _)
  have hT1 : T ≤ 1 := prod_le_one (fun σ _ => (hF σ).nonneg _) (fun σ _ => (hF σ).le_one _)
  have rμ : ∏ σ ∈ univ.erase μ, F σ (O σ) = F ν (O ν) * T :=
    (Finset.mul_prod_erase (univ.erase μ) (fun σ => F σ (O σ)) hν).symm
  have rν : ∏ σ ∈ univ.erase ν, F σ (O σ) = F μ (O μ) * T := by
    rw [← Finset.mul_prod_erase (univ.erase ν) (fun σ => F σ (O σ)) hμ, Finset.erase_right_comm]
  have c1 : chi z F (periodicLatticeShift x μ) = F μ (O μ + 1) * (F ν (O ν) * T) := by
    rw [chi_shift hF hL z x μ, rμ]
  have c2 : chi z F x = F μ (O μ) * (F ν (O ν) * T) := by
    rw [chi_self z x μ, rμ]
  have c3 : chi z F (periodicLatticeShiftBack x ν) = F ν (O ν - 1) * (F μ (O μ) * T) := by
    rw [chi_shiftBack hF hL z x ν, rν]
  have hoff : offc z (periodicLatticeShift (periodicLatticeShiftBack x ν) μ)
      = Function.update (Function.update O ν ((O ν + L ν) % (L ν + 1))) μ ((O μ + 1) % (L μ + 1)) := by
    rw [offc_shift_eq hL z (periodicLatticeShiftBack x ν) μ, offc_shiftBack_eq hL z x ν,
      Function.update_of_ne hne.symm]
  have c4 : chi z F (periodicLatticeShift (periodicLatticeShiftBack x ν) μ) = F μ (O μ + 1) * F ν (O ν - 1) * T := by
    unfold chi
    rw [hoff, Fprod_update2 F O hne, (hF μ).shift_eq _ (offc_lt z x μ), (hF ν).back_eq _ (offc_lt z x ν)]
  rw [c1, c2, c3, c4]
  have e : F μ (O μ + 1) * (F ν (O ν) * T) - F μ (O μ) * (F ν (O ν) * T)
      - (F μ (O μ + 1) * F ν (O ν - 1) * T - F ν (O ν - 1) * (F μ (O μ) * T))
      = ((F μ (O μ + 1) - F μ (O μ)) * (F ν (O ν) - F ν (O ν - 1))) * T := by ring
  rw [e, abs_mul, abs_mul, abs_of_nonneg hT0]
  have h1 := (hF μ).first (O μ)
  have h2 : |F ν (O ν) - F ν (O ν - 1)| ≤ τ1 := by rw [abs_sub_comm]; exact (hF ν).first_back _
  have h3 : |F μ (O μ + 1) - F μ (O μ)| * |F ν (O ν) - F ν (O ν - 1)| ≤ τ1 * τ1 :=
    mul_le_mul h1 h2 (abs_nonneg _) (hF μ).tau1
  calc |F μ (O μ + 1) - F μ (O μ)| * |F ν (O ν) - F ν (O ν - 1)| * T ≤ τ1 * τ1 * 1 :=
        mul_le_mul h3 hT1 hT0 (mul_nonneg (hF μ).tau1 (hF μ).tau1)
    _ = τ1 ^ 2 := by ring

theorem chi_one (x : PeriodicLatticeSite L) (h : ∀ σ, F σ (offc z x σ) = 1) : chi z F x = 1 := by
  unfold chi Fprod
  exact prod_eq_one (fun σ _ => h σ)

theorem chi_support_box {s : ℕ} (hR : ∀ σ, Reach z σ s (F σ))
    (x : PeriodicLatticeSite L) (hx : chi z F x ≠ 0) (y : PeriodicLatticeSite L) (hy : pdist x y ≤ 6) :
    y ∈ siteBox z s := by
  rw [mem_siteBox_offc]
  intro σ
  unfold chi Fprod at hx
  have hxσ := (Finset.prod_ne_zero_iff.mp hx) σ (mem_univ σ)
  have hp : pcd (L σ + 1) (x σ).val (y σ).val ≤ 6 :=
    le_trans (Finset.single_le_sum (f := fun μ : Fin 3 => pcd (L μ + 1) (x μ).val (y μ).val)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ σ)) hy
  exact hR σ x y hxσ hp

end calculus

end AdalyFormal.M2Bridge

#print axioms AdalyFormal.M2Bridge.chi_first_fwd
#print axioms AdalyFormal.M2Bridge.chi_mixed
#print axioms AdalyFormal.M2Bridge.chi_support_box
