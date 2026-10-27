import NsPtA2
import NtCvON5
import PSiteC3
import ZGU1B
import ZHodgeFinal

/-!
# PtB -- torus coordinate calculus (lane omega/near2/point)

`mkS L a b c` is the site with coordinates `(a, b, c)` reduced mod the side.  Cube sums over `blockOf` become `cube` sums; shifts and paths are coordinate shifts.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped RealInnerProductSpace
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero pathSite_succ)

section torus
variable {L : PeriodicLatticeExtent}

/-- the site with coordinates `(a,b,c)` mod the side. -/
def mkS (L : PeriodicLatticeExtent) (a b c : ℕ) : PeriodicLatticeSite L :=
  fun μ => ⟨(![a, b, c] μ) % (L μ + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

theorem mkS_val (a b c : ℕ) (μ : Fin 3) : ((mkS L a b c) μ).val = (![a, b, c] μ) % (L μ + 1) := rfl

theorem mkS_val0 (a b c : ℕ) : ((mkS L a b c) 0).val = a % (L 0 + 1) := rfl
theorem mkS_val1 (a b c : ℕ) : ((mkS L a b c) 1).val = b % (L 1 + 1) := rfl
theorem mkS_val2 (a b c : ℕ) : ((mkS L a b c) 2).val = c % (L 2 + 1) := rfl

theorem mkS_eta (x : PeriodicLatticeSite L) : mkS L (x 0).val (x 1).val (x 2).val = x := by
  funext μ
  apply Fin.ext
  rw [mkS_val]
  fin_cases μ
  · simp [Nat.mod_eq_of_lt (x 0).isLt]
  · simp [Nat.mod_eq_of_lt (x 1).isLt]
  · simp [Nat.mod_eq_of_lt (x 2).isLt]

theorem mkS_ext {a b c a' b' c' : ℕ} (h0 : a % (L 0 + 1) = a' % (L 0 + 1)) (h1 : b % (L 1 + 1) = b' % (L 1 + 1))
    (h2 : c % (L 2 + 1) = c' % (L 2 + 1)) : mkS L a b c = mkS L a' b' c' := by
  funext μ
  apply Fin.ext
  rw [mkS_val, mkS_val]
  fin_cases μ
  · simpa using h0
  · simpa using h1
  · simpa using h2

theorem shift_val_self (x : PeriodicLatticeSite L) (μ : Fin 3) :
    ((periodicLatticeShift x μ) μ).val = ((x μ).val + 1) % (L μ + 1) := by
  simp [periodicLatticeShift, Fin.val_add]

theorem shift_val_ne (x : PeriodicLatticeSite L) (μ ν : Fin 3) (h : ν ≠ μ) :
    ((periodicLatticeShift x μ) ν) = x ν := by
  simp [periodicLatticeShift, Function.update_of_ne h]

theorem shift_mkS0 (a b c : ℕ) : periodicLatticeShift (mkS L a b c) 0 = mkS L (a + 1) b c := by
  funext ν
  apply Fin.ext
  by_cases h : ν = 0
  · subst h
    rw [shift_val_self, mkS_val0, mkS_val0, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  · rw [shift_val_ne _ _ _ h, mkS_val, mkS_val]
    fin_cases ν <;> simp_all

theorem shift_mkS1 (a b c : ℕ) : periodicLatticeShift (mkS L a b c) 1 = mkS L a (b + 1) c := by
  funext ν
  apply Fin.ext
  by_cases h : ν = 1
  · subst h
    rw [shift_val_self, mkS_val1, mkS_val1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  · rw [shift_val_ne _ _ _ h, mkS_val, mkS_val]
    fin_cases ν <;> simp_all

theorem shift_mkS2 (a b c : ℕ) : periodicLatticeShift (mkS L a b c) 2 = mkS L a b (c + 1) := by
  funext ν
  apply Fin.ext
  by_cases h : ν = 2
  · subst h
    rw [shift_val_self, mkS_val2, mkS_val2, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  · rw [shift_val_ne _ _ _ h, mkS_val, mkS_val]
    fin_cases ν <;> simp_all

theorem pathSite_mkS0 (a b c i : ℕ) : pathSite (mkS L a b c) 0 i = mkS L (a + i) b c := by
  induction i with
  | zero => rfl
  | succ i ih => rw [pathSite_succ, ih, shift_mkS0]; rfl

theorem pathSite_mkS1 (a b c i : ℕ) : pathSite (mkS L a b c) 1 i = mkS L a (b + i) c := by
  induction i with
  | zero => rfl
  | succ i ih => rw [pathSite_succ, ih, shift_mkS1]; rfl

theorem pathSite_mkS2 (a b c i : ℕ) : pathSite (mkS L a b c) 2 i = mkS L a b (c + i) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [pathSite_succ, ih, shift_mkS2]; rfl

/-- membership of `mkS` in a block. -/
theorem mkS_mem_block (Y : PeriodicLatticeSite L) (n : ℕ) (hfit : ∀ μ, (Y μ).val + n ≤ L μ + 1)
    (i j k : ℕ) (hi : i < n) (hj : j < n) (hk : k < n) :
    mkS L ((Y 0).val + i) ((Y 1).val + j) ((Y 2).val + k) ∈ blockOf Y n := by
  rw [mem_blockOf]
  intro μ
  have h0 := hfit 0; have h1 := hfit 1; have h2 := hfit 2
  fin_cases μ
  · simp only [Fin.zero_eta, mkS_val0]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · simp only [Fin.mk_one, mkS_val1]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · simp only [Fin.reduceFinMk, mkS_val2]
    rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- cube sums over `blockOf` are `cube` sums of `F ∘ mkS`. -/
theorem sum_block_eq_cube {E : Type*} [AddCommGroup E] [Module ℝ E] (Y : PeriodicLatticeSite L) (n : ℕ)
    (hfit : ∀ μ, (Y μ).val + n ≤ L μ + 1) (F : PeriodicLatticeSite L → E) :
    ∑ x ∈ blockOf Y n, F x = cube (fun a b c => F (mkS L a b c)) n (Y 0).val (Y 1).val (Y 2).val := by
  classical
  unfold cube
  have e : ∑ i ∈ range n, ∑ j ∈ range n, ∑ k ∈ range n, F (mkS L ((Y 0).val + i) ((Y 1).val + j) ((Y 2).val + k))
      = ∑ p ∈ range n ×ˢ (range n ×ˢ range n), F (mkS L ((Y 0).val + p.1) ((Y 1).val + p.2.1) ((Y 2).val + p.2.2)) := by
    simp only [Finset.sum_product]
  rw [e]
  symm
  refine Finset.sum_nbij' (fun p => mkS L ((Y 0).val + p.1) ((Y 1).val + p.2.1) ((Y 2).val + p.2.2))
    (fun x => ((x 0).val - (Y 0).val, (x 1).val - (Y 1).val, (x 2).val - (Y 2).val)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    exact mkS_mem_block Y n hfit _ _ _ hp.1 hp.2.1 hp.2.2
  · intro x hx
    rw [mem_blockOf] at hx
    simp only [Finset.mem_product, Finset.mem_range]
    refine ⟨?_, ?_, ?_⟩
    · have := hx 0; omega
    · have := hx 1; omega
    · have := hx 2; omega
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    have h0 := hfit 0; have h1 := hfit 1; have h2 := hfit 2
    simp only [mkS_val0, mkS_val1, mkS_val2]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp
  · intro x hx
    rw [mem_blockOf] at hx
    have a0 := hx 0; have a1 := hx 1; have a2 := hx 2
    have e0 : (Y 0).val + ((x 0).val - (Y 0).val) = (x 0).val := by omega
    have e1 : (Y 1).val + ((x 1).val - (Y 1).val) = (x 1).val := by omega
    have e2 : (Y 2).val + ((x 2).val - (Y 2).val) = (x 2).val := by omega
    simp only [e0, e1, e2]
    exact mkS_eta x
  · intro p hp
    rfl

end torus

end AdalyFormal.CoverOmega
