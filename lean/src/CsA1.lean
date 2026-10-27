import CaT1

/-!
# CsA1 -- plaquette coverage implies site coverage (lane cov_split_20261019)

For an admissible tower with `2 ≤ M`, every site `x` of `Ω₀` is a corner of a unit `(0,1)`-plaquette all of whose four corners lie in the
`M`-block of `x` (so in `Ω₀`, since `Ω₀` is `M`-block-closed and `M` divides every extent).  `CovPlaqF` then puts the four boundary bonds
of that plaquette in one class cube, hence `x` in that cube.  So `CovPlaqF ⇒ CovSitesF`, for every family `F`, every `ell`, every `k`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace CovSplit

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open NcwdhFam
open MXQ.AllC
open MXQ.Total

theorem div_aux {M : ℕ} (hM0 : 0 < M) (q s : ℕ) (hs : s < M) : (M * q + s) / M = q := by
  rw [Nat.mul_add_div hM0, Nat.div_eq_of_lt hs]; simp

/-- the Nat core: the base coordinate of a unit plaquette containing `x` inside its `M`-block. -/
theorem adj_nat {M ext x : ℕ} (hM : 2 ≤ M) (hd : M ∣ ext) (hx : x < ext) :
    (if x % M + 1 = M then x - 1 else x) + 1 < ext ∧
    (if x % M + 1 = M then x - 1 else x) / M = x / M ∧
    ((if x % M + 1 = M then x - 1 else x) + 1) / M = x / M ∧
    (x = (if x % M + 1 = M then x - 1 else x) ∨ x = (if x % M + 1 = M then x - 1 else x) + 1) := by
  have hM0 : 0 < M := by omega
  have hdm : M * (x / M) + x % M = x := Nat.div_add_mod x M
  have hr : x % M < M := Nat.mod_lt x hM0
  obtain ⟨e, he⟩ := hd
  by_cases h : x % M + 1 = M
  · rw [if_pos h]
    have h1 : 1 ≤ x % M := by omega
    have hq : (x - 1) / M = x / M := by
      have : x - 1 = M * (x / M) + (x % M - 1) := by omega
      rw [this]; exact div_aux hM0 _ _ (by omega)
    have hq2 : (x - 1 + 1) / M = x / M := by
      have : x - 1 + 1 = x := by omega
      rw [this]
    exact ⟨by omega, hq, hq2, Or.inr (by omega)⟩
  · rw [if_neg h]
    have hq2 : (x + 1) / M = x / M := by
      have : x + 1 = M * (x / M) + (x % M + 1) := by omega
      rw [this]; exact div_aux hM0 _ _ (by omega)
    have hlt : x + 1 < ext := by
      rcases Nat.lt_or_ge (x + 1) ext with h2 | h2
      · exact h2
      · exfalso
        have hxe : x + 1 = ext := by omega
        have h3 : (x + 1) / M = e := by rw [hxe, he]; exact Nat.mul_div_cancel_left e hM0
        have hq3 : e = x / M := by rw [← h3, hq2]
        have : x + 1 = M * (x / M) := by rw [hxe, he, hq3]
        omega
    exact ⟨hlt, rfl, hq2, Or.inl rfl⟩

theorem covPlaqF_imp_covSitesF {L : PeriodicLatticeExtent} {ell M R k : ℕ} {F : CubeFam L} {S : Tower L}
    (hA : Admissible ell M R k S) (hM : 2 ≤ M) (h : CovPlaqF ell M F k S) : CovSitesF ell M F k S := by
  intro x hx
  obtain ⟨-, -, hdiv, hblk, -, -⟩ := hA
  have hd : ∀ μ : Fin 3, M ∣ (L μ + 1) := fun μ => by
    have := hdiv 0 (Nat.zero_le _) μ
    simpa [bigSide] using this
  have hbc : BlockClosed M (S.Om 0) := by
    have := hblk 0 (Nat.zero_le _)
    simpa [bigSide] using this
  let bvf : Fin 3 → ℕ := fun μ => if μ = 2 then (x μ).val else
    (if (x μ).val % M + 1 = M then (x μ).val - 1 else (x μ).val)
  have adj : ∀ μ : Fin 3, μ ≠ 2 → bvf μ + 1 < L μ + 1 ∧ bvf μ / M = (x μ).val / M ∧
      (bvf μ + 1) / M = (x μ).val / M ∧ ((x μ).val = bvf μ ∨ (x μ).val = bvf μ + 1) := by
    intro μ hμ
    have := adj_nat (M := M) (ext := L μ + 1) (x := (x μ).val) hM (hd μ) (x μ).isLt
    simp only [bvf, if_neg hμ]
    exact this
  have hlt : ∀ μ : Fin 3, bvf μ < L μ + 1 := by
    intro μ
    by_cases hμ : μ = 2
    · have := (x μ).isLt
      simp only [bvf, if_pos hμ]; exact this
    · have := (adj μ hμ).1; omega
  let b : PeriodicLatticeSite L := fun μ => ⟨bvf μ, hlt μ⟩
  have hquo : ∀ μ : Fin 3, (b μ).val / M = (x μ).val / M := by
    intro μ
    by_cases hμ : μ = 2
    · subst hμ; simp [b, bvf]
    · exact (adj μ hμ).2.1
  have hsh : ∀ μ : Fin 3, ∀ hμ : μ ≠ 2, b μ + 1 = ⟨bvf μ + 1, (adj μ hμ).1⟩ := by
    intro μ hμ
    apply Fin.ext
    rw [Fin.val_add_one_of_lt]
    · rw [Fin.lt_iff_val_lt_val, Fin.val_last]
      have := (adj μ hμ).1
      show bvf μ < L μ
      omega
  let cor : Bool → Bool → PeriodicLatticeSite L := fun s0 s1 μ =>
    if h0 : μ = 0 then (if s0 then ⟨bvf μ + 1, (adj μ (by rw [h0]; decide)).1⟩ else b μ)
    else if h1 : μ = 1 then (if s1 then ⟨bvf μ + 1, (adj μ (by rw [h1]; decide)).1⟩ else b μ)
    else b μ
  have hcorq : ∀ s0 s1 : Bool, ∀ μ : Fin 3, (cor s0 s1 μ).val / M = (x μ).val / M := by
    intro s0 s1 μ
    by_cases h0 : μ = 0
    · subst h0; cases s0 <;> simp [cor, hquo] <;> exact (adj 0 (by decide)).2.2.1
    · by_cases h1 : μ = 1
      · subst h1; cases s1 <;> simp [cor, h0, hquo] <;> exact (adj 1 (by decide)).2.2.1
      · simp [cor, h0, h1, hquo]
  have hcorom : ∀ s0 s1 : Bool, cor s0 s1 ∈ S.Om 0 := fun s0 s1 => hbc x hx _ (hcorq s0 s1)
  have hb : b = cor false false := by
    funext μ; by_cases h0 : μ = 0 <;> by_cases h1 : μ = 1 <;> simp [cor, h0, h1]
  have hs0 : periodicLatticeShift b 0 = cor true false := by
    funext μ
    by_cases h0 : μ = 0
    · subst h0; simp [periodicLatticeShift, cor, hsh 0 (by decide)]
    · by_cases h1 : μ = 1 <;> simp [periodicLatticeShift, cor, h0, h1]
  have hs1 : periodicLatticeShift b 1 = cor false true := by
    funext μ
    by_cases h1 : μ = 1
    · subst h1; simp [periodicLatticeShift, cor, hsh 1 (by decide)]
    · by_cases h0 : μ = 0 <;> simp [periodicLatticeShift, cor, h0, h1]
  have hs01 : periodicLatticeShift (periodicLatticeShift b 0) 1 = cor true true := by
    rw [hs0]
    funext μ
    by_cases h1 : μ = 1
    · subst h1; simp [periodicLatticeShift, cor]
      exact hsh 1 (by decide)
    · by_cases h0 : μ = 0 <;> simp [periodicLatticeShift, cor, h0, h1]
  have hs10 : periodicLatticeShift (periodicLatticeShift b 1) 0 = cor true true := by
    rw [hs1]
    funext μ
    by_cases h0 : μ = 0
    · subst h0; simp [periodicLatticeShift, cor]
      exact hsh 0 (by decide)
    · by_cases h1 : μ = 1 <;> simp [periodicLatticeShift, cor, h0, h1]
  let p : PeriodicLatticePlaquette L := (b, ⟨((0 : Fin 3), (1 : Fin 3)), by decide⟩)
  have hedges : ∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond (S.Om 0) e := by
    intro e he
    simp only [periodicPlaquetteBoundaryEdges, p, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    · refine ⟨?_, ?_⟩
      · rw [hb]; exact hcorom _ _
      · show periodicLatticeShift b 0 ∈ _
        rw [hs0]; exact hcorom _ _
    · refine ⟨?_, ?_⟩
      · show periodicLatticeShift b 0 ∈ _
        rw [hs0]; exact hcorom _ _
      · show periodicLatticeShift (periodicLatticeShift b 0) 1 ∈ _
        rw [hs01]; exact hcorom _ _
    · refine ⟨?_, ?_⟩
      · show periodicLatticeShift b 1 ∈ _
        rw [hs1]; exact hcorom _ _
      · show periodicLatticeShift (periodicLatticeShift b 1) 0 ∈ _
        rw [hs10]; exact hcorom _ _
    · refine ⟨?_, ?_⟩
      · rw [hb]; exact hcorom _ _
      · show periodicLatticeShift b 1 ∈ _
        rw [hs1]; exact hcorom _ _
  obtain ⟨sites, j, hc, hbd⟩ := h p hedges
  refine ⟨sites, j, hc, ?_⟩
  have e00 : (b, (0 : Fin 3)) ∈ periodicPlaquetteBoundaryEdges p := by
    simp [periodicPlaquetteBoundaryEdges, p]
  have e01 : (b, (1 : Fin 3)) ∈ periodicPlaquetteBoundaryEdges p := by
    simp [periodicPlaquetteBoundaryEdges, p]
  have e10 : (periodicLatticeShift b 0, (1 : Fin 3)) ∈ periodicPlaquetteBoundaryEdges p := by
    simp [periodicPlaquetteBoundaryEdges, p]
  have c00 : cor false false ∈ sites := by rw [← hb]; exact (hbd _ e00).1
  have c10 : cor true false ∈ sites := by rw [← hs0]; exact (hbd _ e00).2
  have c01 : cor false true ∈ sites := by rw [← hs1]; exact (hbd _ e01).2
  have c11 : cor true true ∈ sites := by rw [← hs01]; exact (hbd _ e10).2
  have hx2 : x 2 = b 2 := by
    apply Fin.ext; simp [b, bvf]
  have hx0 := (adj 0 (by decide)).2.2.2
  have hx1 := (adj 1 (by decide)).2.2.2
  have key : ∀ s0 s1 : Bool, (s0 = true → x 0 = cor true s1 0) → True := fun _ _ _ => trivial
  rcases hx0 with h0 | h0 <;> rcases hx1 with h1 | h1
  · have : x = cor false false := by
      funext μ
      by_cases e0 : μ = 0
      · subst e0; apply Fin.ext; simpa [cor, b] using h0
      · by_cases e1 : μ = 1
        · subst e1; apply Fin.ext; simpa [cor, b] using h1
        · have : μ = 2 := by omega
          subst this; simp [cor, hx2]
    rw [this]; exact c00
  · have : x = cor false true := by
      funext μ
      by_cases e0 : μ = 0
      · subst e0; apply Fin.ext; simpa [cor, b] using h0
      · by_cases e1 : μ = 1
        · subst e1; apply Fin.ext; simpa [cor, b] using h1
        · have : μ = 2 := by omega
          subst this; simp [cor, hx2]
    rw [this]; exact c01
  · have : x = cor true false := by
      funext μ
      by_cases e0 : μ = 0
      · subst e0; apply Fin.ext; simpa [cor, b] using h0
      · by_cases e1 : μ = 1
        · subst e1; apply Fin.ext; simpa [cor, b] using h1
        · have : μ = 2 := by omega
          subst this; simp [cor, hx2]
    rw [this]; exact c10
  · have : x = cor true true := by
      funext μ
      by_cases e0 : μ = 0
      · subst e0; apply Fin.ext; simpa [cor, b] using h0
      · by_cases e1 : μ = 1
        · subst e1; apply Fin.ext; simpa [cor, b] using h1
        · have : μ = 2 := by omega
          subst this; simp [cor, hx2]
    rw [this]; exact c11

#print axioms covPlaqF_imp_covSitesF

end CovSplit
