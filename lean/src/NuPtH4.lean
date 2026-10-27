import NuPtH3

/-!
# PtH4 -- potential data of a kernel field and the left/right constants (lane omega/near2/point)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.CoverOmegaTwo
open AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped RealInnerProductSpace
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)

variable {ell M R : ℕ}

/-- potential data: `g` is a corrected potential of `x` (bond relation in all directions, periodic transversally). -/
structure PD (ell M R : ℕ) (x : BondFnL2 (scaleUp ell 2 (neLu M R))) (g : ℕ → ℕ → ℕ → SuTwo) : Prop where
  rel0 : ∀ a b d, x (mkS (scaleUp ell 2 (neLu M R)) a b d, 0) = g (a + 1) b d - g a b d
  rel1 : ∀ a b d, x (mkS (scaleUp ell 2 (neLu M R)) a b d, 1) = g a (b + 1) d - g a b d
  rel2 : ∀ a b d, x (mkS (scaleUp ell 2 (neLu M R)) a b d, 2) = g a b (d + 1) - g a b d
  mod1 : ∀ a b d, g a (b % neN ell M R) d = g a b d
  mod2 : ∀ a b d, g a b (d % neN ell M R) = g a b d

theorem nat_chain {E : Type*} (f : ℕ → E) (K : ℕ) (h : ∀ n, n < K → f (n + 1) = f n) :
    ∀ n, n ≤ K → f n = f 0 := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih => intro hn; rw [h n (by omega), ih (by omega)]

theorem nat_chain_from {E : Type*} (f : ℕ → E) (s K : ℕ) (h : ∀ n, s ≤ n → n < K → f (n + 1) = f n) :
    ∀ n, s ≤ n → n ≤ K → f n = f s := by
  intro n hn hnK
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have := nat_chain (fun m => f (s + m)) (K - s) (fun m hm => by
    have := h (s + m) (by omega) (by omega)
    simpa [← add_assoc] using this) m (by omega)
  simpa using this

theorem x0val (hP : PGeo ell M R) (a b d : ℕ) (h : a < neN ell M R) :
    ((mkS (scaleUp ell 2 (neLu M R)) a b d) 0).val = a :=
  (mkS_val0 a b d).trans (Nat.mod_eq_of_lt (lt_of_lt_of_eq h (hNLμ hP 0).symm))

section consts
variable {x : BondFnL2 (scaleUp ell 2 (neLu M R))} {g : ℕ → ℕ → ℕ → SuTwo}

theorem x_zero0 (hP : PGeo ell M R) (hk : KD ell M R x) (a b d : ℕ) (ha : a + 1 < neN ell M R)
    (h1 : ¬ Omv ell M R 1 a) (h2 : ¬ Omv ell M R 1 (a + 1)) :
    x (mkS (scaleUp ell 2 (neLu M R)) a b d, 0) = 0 := by
  have hg : NGeo ell M R := AdalyFormal.NcwdhTwo.nGeo_two hP.hell hP.hdell hP.hM hP.hR
  refine hk.zero_off1 hg hP.hM (mkS (scaleUp ell 2 (neLu M R)) a b d, 0) ?_ ?_
  · show ¬ Omv ell M R 1 ((mkS (scaleUp ell 2 (neLu M R)) a b d) 0).val
    rw [x0val hP a b d (by omega)]; exact h1
  · show ¬ Omv ell M R 1 ((periodicLatticeShift (mkS (scaleUp ell 2 (neLu M R)) a b d) 0) 0).val
    rw [shift_mkS0, x0val hP (a + 1) b d ha]; exact h2

theorem x_zero1 (hP : PGeo ell M R) (hk : KD ell M R x) (a b d : ℕ) (ha : a < neN ell M R)
    (h1 : ¬ Omv ell M R 1 a) :
    x (mkS (scaleUp ell 2 (neLu M R)) a b d, 1) = 0 := by
  have hg : NGeo ell M R := AdalyFormal.NcwdhTwo.nGeo_two hP.hell hP.hdell hP.hM hP.hR
  refine hk.zero_off1 hg hP.hM (mkS (scaleUp ell 2 (neLu M R)) a b d, 1) ?_ ?_
  · show ¬ Omv ell M R 1 ((mkS (scaleUp ell 2 (neLu M R)) a b d) 0).val
    rw [x0val hP a b d ha]; exact h1
  · show ¬ Omv ell M R 1 ((periodicLatticeShift (mkS (scaleUp ell 2 (neLu M R)) a b d) 1) 0).val
    rw [shift_mkS1, x0val hP a (b + 1) d ha]; exact h1

theorem x_zero2 (hP : PGeo ell M R) (hk : KD ell M R x) (a b d : ℕ) (ha : a < neN ell M R)
    (h1 : ¬ Omv ell M R 1 a) :
    x (mkS (scaleUp ell 2 (neLu M R)) a b d, 2) = 0 := by
  have hg : NGeo ell M R := AdalyFormal.NcwdhTwo.nGeo_two hP.hell hP.hdell hP.hM hP.hR
  refine hk.zero_off1 hg hP.hM (mkS (scaleUp ell 2 (neLu M R)) a b d, 2) ?_ ?_
  · show ¬ Omv ell M R 1 ((mkS (scaleUp ell 2 (neLu M R)) a b d) 0).val
    rw [x0val hP a b d ha]; exact h1
  · show ¬ Omv ell M R 1 ((periodicLatticeShift (mkS (scaleUp ell 2 (neLu M R)) a b d) 2) 0).val
    rw [shift_mkS2, x0val hP a b (d + 1) ha]; exact h1

/-- transverse constancy of `g` on a slab where `x` vanishes on the transverse bonds. -/
theorem trans_const (hP : PGeo ell M R) (hk : KD ell M R x) (hpd : PD ell M R x g) (a : ℕ) (ha : a < neN ell M R)
    (h1 : ¬ Omv ell M R 1 a) : ∀ b d, g a b d = g a 0 0 := by
  have s1 : ∀ b d, g a (b + 1) d = g a b d := by
    intro b d
    have := hpd.rel1 a b d
    rw [x_zero1 hP hk a b d ha h1] at this
    exact (sub_eq_zero.mp this.symm)
  have s2 : ∀ b d, g a b (d + 1) = g a b d := by
    intro b d
    have := hpd.rel2 a b d
    rw [x_zero2 hP hk a b d ha h1] at this
    exact (sub_eq_zero.mp this.symm)
  intro b d
  have hb : ∀ b, g a b d = g a 0 d := by
    intro b
    induction b with
    | zero => rfl
    | succ b ih => rw [s1, ih]
  have hd : ∀ d, g a 0 d = g a 0 0 := by
    intro d
    induction d with
    | zero => rfl
    | succ d ih => rw [s2, ih]
  rw [hb b, hd d]

/-- the left constant. -/
theorem left_const (hP : PGeo ell M R) (hk : KD ell M R x) (hpd : PD ell M R x g) :
    ∀ a, a < neP1 ell M R → ∀ b d, g a b d = g 0 0 0 := by
  have hN := hP.hqN
  have hl := hP.hpa
  have hq := hP.hq1q0
  have hell2 : 1 ≤ ell ^ 2 := Nat.one_le_pow _ _ (by have := hP.hell; omega)
  have hb := hP.hab; have hc := hP.hba; have hd := hP.hab2; have he := hP.hbq
  intro a ha b d
  have ha' : a < neN ell M R := by omega
  rw [trans_const hP hk hpd a ha' (by simp only [Omv]; omega) b d]
  have := nat_chain (fun n => g n 0 0) (neP1 ell M R - 1) (fun n hn => by
    have h := hpd.rel0 n 0 0
    rw [x_zero0 hP hk n 0 0 (by omega) (by simp only [Omv]; omega) (by simp only [Omv]; omega)] at h
    exact sub_eq_zero.mp h.symm) a (by omega)
  exact this

/-- the right constant. -/
theorem right_const (hP : PGeo ell M R) (hk : KD ell M R x) (hpd : PD ell M R x g) :
    ∀ a, neQ1 ell M R ≤ a → a < neN ell M R → ∀ b d, g a b d = g (neQ1 ell M R) 0 0 := by
  have hN := hP.hqN
  have hq := hP.hq1q0
  have hell2 : 1 ≤ ell ^ 2 := Nat.one_le_pow _ _ (by have := hP.hell; omega)
  intro a ha1 ha2 b d
  rw [trans_const hP hk hpd a ha2 (by simp only [Omv]; omega) b d]
  exact nat_chain_from (fun n => g n 0 0) (neQ1 ell M R) (neN ell M R - 1) (fun n hn hnK => by
    have h := hpd.rel0 n 0 0
    rw [x_zero0 hP hk n 0 0 (by omega) (by simp only [Omv]; omega) (by simp only [Omv]; omega)] at h
    exact sub_eq_zero.mp h.symm) a ha1 (by omega)

end consts

end AdalyFormal.CoverOmegaTwo
