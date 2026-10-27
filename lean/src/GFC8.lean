import GFC7
import AdalyFormal.Target.ClayStatement

/-!
# GFC8 -- torus arithmetic: embeddings `ιc : Cell n → Site L`, `ι : ℤ³ → Site L`, and the fundamental-domain sum.
Standard axioms only.
-/
set_option autoImplicit false
open scoped BigOperators
open AdalyFormal.Target.ClayStatement

namespace AdalyFormal.FlatCoercivity

variable {L : PeriodicLatticeExtent} {n : ℕ}

abbrev Site (L : PeriodicLatticeExtent) := PeriodicLatticeSite L

/-- unit vector of the torus -/
def eU (L : PeriodicLatticeExtent) (μ : Fin 3) : Site L := Pi.single μ 1

theorem shift_eq (x : Site L) (μ : Fin 3) : periodicLatticeShift x μ = x + eU L μ := by
  unfold periodicLatticeShift eU
  funext ν
  by_cases h : ν = μ
  · subst h; simp
  · simp [h]

theorem n_le (hdvd : ∀ μ, n ∣ L μ + 1) (μ : Fin 3) : n ≤ L μ + 1 :=
  Nat.le_of_dvd (Nat.succ_pos _) (hdvd μ)

/-- embedding of the cell into the torus -/
def ιc (hdvd : ∀ μ, n ∣ L μ + 1) (t : Cell n) : Site L :=
  fun μ => ⟨t μ, lt_of_lt_of_le (t μ).isLt (n_le hdvd μ)⟩

/-- reduction of an integer modulo `N` as an element of `Fin N` -/
def fmod (N : ℕ) (hN : 0 < N) (a : ℤ) : Fin N :=
  ⟨(a % (N : ℤ)).toNat, by
    have h1 : 0 ≤ a % (N : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hN.ne')
    have h2 : a % (N : ℤ) < N := Int.emod_lt_of_pos _ (by exact_mod_cast hN)
    omega⟩

theorem fmod_val (N : ℕ) (hN : 0 < N) (a : ℤ) : (((fmod N hN a).val : ℕ) : ℤ) = a % (N : ℤ) := by
  have h1 : 0 ≤ a % (N : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hN.ne')
  simp only [fmod]
  omega

theorem fmod_add (N : ℕ) (hN : 0 < N) (a b : ℤ) : fmod N hN (a + b) = fmod N hN a + fmod N hN b := by
  apply Fin.ext
  have hNz : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  apply Nat.cast_injective (R := ℤ)
  rw [Fin.val_add]
  push_cast
  rw [fmod_val, fmod_val, fmod_val]
  exact Int.add_emod a b N

theorem fmod_zero (N : ℕ) (hN : 0 < N) : fmod N hN 0 = ⟨0, hN⟩ := by
  apply Fin.ext; simp [fmod]

/-- `ℤ³ → Site L` (mod the side lengths) -/
def ιz (L : PeriodicLatticeExtent) (x : Z3) : Site L := fun μ => fmod (L μ + 1) (Nat.succ_pos _) (x μ)

theorem ιz_add (a b : Z3) : ιz L (a + b) = ιz L a + ιz L b := by
  funext μ; simp only [ιz, Pi.add_apply]; exact fmod_add _ _ _ _

theorem ιz_zero : ιz L (0 : Z3) = 0 := by funext μ; simp only [ιz, Pi.zero_apply]; exact fmod_zero _ _

theorem ιz_nsmul (m : ℕ) (a : Z3) : ιz L (m • a) = m • ιz L a := by
  induction m with
  | zero => simp [ιz_zero]
  | succ m ih => rw [succ_nsmul, succ_nsmul, ιz_add, ih]

theorem fmod_one (N : ℕ) [NeZero N] : fmod N (Nat.pos_of_ne_zero (NeZero.ne N)) 1 = 1 := by
  apply Fin.ext
  rw [Fin.val_one']
  apply Nat.cast_injective (R := ℤ)
  rw [fmod_val]
  push_cast
  rfl

theorem ιz_ev (μ : Fin 3) : ιz L (ev μ) = eU L μ := by
  funext ν
  by_cases hν : ν = μ
  · subst hν
    simp only [ιz, eU, ev, Pi.single_eq_same]
    exact fmod_one _
  · simp only [ιz, eU, ev, Pi.single_eq_of_ne hν]
    exact fmod_zero _ _

theorem ιz_cc (hdvd : ∀ μ, n ∣ L μ + 1) (t : Cell n) : ιz L (cc t) = ιc hdvd t := by
  funext μ
  apply Fin.ext
  have h1 : (t μ : ℕ) < L μ + 1 := lt_of_lt_of_le (t μ).isLt (n_le hdvd μ)
  have h := fmod_val (L μ + 1) (Nat.succ_pos _) (cc t μ)
  simp only [ιz, ιc]
  have : cc t μ % ((L μ + 1 : ℕ) : ℤ) = cc t μ := Int.emod_eq_of_lt (by simp [cc]) (by simp only [cc]; exact_mod_cast h1)
  rw [this] at h
  simp only [cc] at h
  exact_mod_cast h


/-- side lengths in cells -/
def Mc (L : PeriodicLatticeExtent) (n : ℕ) (μ : Fin 3) : ℕ := (L μ + 1) / n

theorem Mc_mul (hdvd : ∀ μ, n ∣ L μ + 1) (μ : Fin 3) : n * Mc L n μ = L μ + 1 :=
  Nat.mul_div_cancel' (hdvd μ)

theorem Mc_pos (hn : 0 < n) (hdvd : ∀ μ, n ∣ L μ + 1) (μ : Fin 3) : 0 < Mc L n μ := by
  have := Mc_mul hdvd μ
  rcases Nat.eq_zero_or_pos (Mc L n μ) with h | h
  · rw [h] at this; omega
  · exact h

theorem Mc_le (hn : 0 < n) (hdvd : ∀ μ, n ∣ L μ + 1) (μ : Fin 3) : Mc L n μ ≤ L μ + 1 := by
  have := Mc_mul hdvd μ
  nlinarith [Mc_pos hn hdvd μ]

/-- the parametrisation `(t, c) ↦ t + n c` of the torus -/
def Phi8 (hn : 0 < n) (hdvd : ∀ μ, n ∣ L μ + 1) (p : Cell n × (∀ μ : Fin 3, Fin (Mc L n μ))) : Site L :=
  fun μ => ⟨(p.1 μ : ℕ) + n * (p.2 μ : ℕ), by
    have h1 := (p.1 μ).isLt
    have h2 := (p.2 μ).isLt
    have h3 := Mc_mul hdvd μ
    nlinarith [h1, h2, h3]⟩

theorem Phi8_inj (hn : 0 < n) (hdvd : ∀ μ, n ∣ L μ + 1) : Function.Injective (Phi8 hn hdvd) := by
  intro p q h
  have h' : ∀ μ, (p.1 μ : ℕ) + n * (p.2 μ : ℕ) = (q.1 μ : ℕ) + n * (q.2 μ : ℕ) := fun μ => by
    have := congrFun h μ
    exact Fin.mk.inj_iff.mp this
  have hd : ∀ μ, (p.1 μ : ℕ) = (q.1 μ : ℕ) ∧ (p.2 μ : ℕ) = (q.2 μ : ℕ) := by
    intro μ
    have e1 := h' μ
    have a1 := (p.1 μ).isLt
    have a2 := (q.1 μ).isLt
    have m1 : ((p.1 μ : ℕ) + n * (p.2 μ : ℕ)) % n = (p.1 μ : ℕ) := by
      rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt a1
    have m2 : ((q.1 μ : ℕ) + n * (q.2 μ : ℕ)) % n = (q.1 μ : ℕ) := by
      rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt a2
    have d1 : ((p.1 μ : ℕ) + n * (p.2 μ : ℕ)) / n = (p.2 μ : ℕ) := by
      rw [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt a1, zero_add]
    have d2 : ((q.1 μ : ℕ) + n * (q.2 μ : ℕ)) / n = (q.2 μ : ℕ) := by
      rw [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt a2, zero_add]
    refine ⟨?_, ?_⟩
    · rw [← m1, ← m2, e1]
    · rw [← d1, ← d2, e1]
  refine Prod.ext ?_ ?_
  · funext μ; exact Fin.ext (hd μ).1
  · funext μ; exact Fin.ext (hd μ).2

theorem card_cell (n : ℕ) : Fintype.card (Cell n) = n ^ 3 := by
  simp [Cell, Fintype.card_pi]

theorem Phi8_bij (hn : 0 < n) (hdvd : ∀ μ, n ∣ L μ + 1) : Function.Bijective (Phi8 hn hdvd) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨Phi8_inj hn hdvd, ?_⟩
  rw [Fintype.card_prod, card_cell]
  simp only [Fintype.card_pi, Fintype.card_fin, PeriodicLatticeSite]
  have : ∀ μ : Fin 3, L μ + 1 = n * Mc L n μ := fun μ => (Mc_mul hdvd μ).symm
  simp only [this]
  rw [Finset.prod_mul_distrib]
  simp [Finset.prod_const]

theorem fin_val_nsmul (N : ℕ) [NeZero N] (m : ℕ) (x : Fin N) : ((m • x : Fin N) : ℕ) = (m * (x : ℕ)) % N := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [succ_nsmul, Fin.val_add, ih, Nat.succ_mul, Nat.mod_add_mod]

theorem Phi8_eq (hn : 0 < n) (hdvd : ∀ μ, n ∣ L μ + 1) (t : Cell n) (c : ∀ μ : Fin 3, Fin (Mc L n μ)) :
    Phi8 hn hdvd (t, c) = ιc hdvd t + n • (fun μ => (⟨(c μ : ℕ), lt_of_lt_of_le (c μ).isLt (Mc_le hn hdvd μ)⟩ : Fin (L μ + 1))) := by
  funext μ
  apply Fin.ext
  have h1 := (t μ).isLt
  have h2 := (c μ).isLt
  have h3 := Mc_mul hdvd μ
  simp only [Phi8, ιc, Pi.add_apply, Pi.smul_apply, Fin.val_add]
  rw [fin_val_nsmul]
  have h4 : n * (c μ : ℕ) < L μ + 1 := by nlinarith [h1, h2, h3, hn]
  rw [Nat.mod_eq_of_lt h4, Nat.mod_eq_of_lt (by nlinarith [h1, h2, h3, hn])]


/-- **fundamental-domain sum**: a `nΓ`-periodic function sums over the torus as `∏ M_μ` times its sum over the cell -/
theorem sum_site_eq (hn : 0 < n) (hdvd : ∀ μ, n ∣ L μ + 1) (f : Site L → ℂ)
    (hf : ∀ (g x : Site L), f (x + n • g) = f x) :
    ∑ x, f x = ((∏ μ, Mc L n μ : ℕ) : ℂ) * ∑ t : Cell n, f (ιc hdvd t) := by
  rw [← Fintype.sum_bijective (Phi8 hn hdvd) (Phi8_bij hn hdvd) (fun p => f (Phi8 hn hdvd p)) f (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  have : ∀ (t : Cell n) (c : ∀ μ : Fin 3, Fin (Mc L n μ)), f (Phi8 hn hdvd (t, c)) = f (ιc hdvd t) := by
    intro t c
    rw [Phi8_eq hn hdvd, hf]
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum]


#print axioms sum_site_eq
#print axioms ιz_add
#print axioms ιz_ev
#print axioms ιz_cc

end AdalyFormal.FlatCoercivity
