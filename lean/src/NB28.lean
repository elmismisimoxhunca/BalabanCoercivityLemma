import NB27
/-!
# NB28 -- cones inside forward boxes (reduces "cone in the cube" to "a box of radius O(ell^l) in the cube")

* `goodPl_of_box`: if `R` holds at every site with all forward offsets from `y` at most `3 ell^l`, then
  `GoodPl ell R l y` (needs `3 ell^n < N`, `l ≤ n`, `ell ≥ 2`).
* `goodL_of_box`: if `Rl` holds at every bond whose base has forward offsets `≤ ell^l` from `c.1`, then
  `goodL ell Rl l c` (needs `ell^n < N`).

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)

variable {L : PeriodicLatticeExtent}

theorem goodPl_of_box (ell : ℕ) (hell : 2 ≤ ell) (R : PeriodicLatticeSite L → Prop) (n : ℕ)
    (hN : ∀ ρ, 3 * ell ^ n < L ρ + 1) :
    ∀ l ≤ n, ∀ y : PeriodicLatticeSite L,
      (∀ z, (∀ σ, off y z σ ≤ 3 * ell ^ l) → R z) → GoodPl ell R l y := by
  intro l
  induction l with
  | zero => intro _ y h; exact h y (fun σ => by rw [off_self]; omega)
  | succ k ih =>
      intro hk y h z _ hz
      refine ih (by omega) z (fun z' hz' => h z' (fun σ => ?_))
      have hb := (hz σ).2
      have h1 := hz' σ
      have hpk : ell ^ (k + 1) = ell ^ k * ell := pow_succ ell k
      have hle : ell ^ (k + 1) ≤ ell ^ n := Nat.pow_le_pow_right (by omega) hk
      have h2 : 2 * ell ^ k ≤ ell ^ k * ell := by
        rw [Nat.mul_comm 2]; exact Nat.mul_le_mul_left _ hell
      have hNσ := hN σ
      rw [off_add y z z' σ (by omega)]
      omega

theorem off_shift_base (z : PeriodicLatticeSite L) (n : ℕ) (ρ σ : Fin 3)
    (h : n < L ρ + 1) : off z (coarseShift z n ρ) σ ≤ n := by
  by_cases hσ : σ = ρ
  · rw [hσ, off_shift_val _ _ _ _ (by rw [off_self]; omega), off_self]; omega
  · rw [off_shift_ne _ _ _ hσ, off_self]; omega

theorem goodL_of_box (ell : ℕ) (hell : 1 ≤ ell) (Rl : PeriodicLatticeEdge L → Prop) (n : ℕ)
    (hN : ∀ ρ, ell ^ n < L ρ + 1) :
    ∀ l ≤ n, ∀ c : PeriodicLatticeEdge L,
      (∀ b : PeriodicLatticeEdge L, (∀ σ, off c.1 b.1 σ ≤ ell ^ l) → Rl b) → goodL ell Rl l c := by
  intro l
  induction l with
  | zero => intro _ c h; exact h c (fun σ => by rw [off_self]; omega)
  | succ k ih =>
      intro hk c h b hb
      obtain ⟨t, ht, rfl⟩ := mem_pathBonds_rep (ell ^ k) c.2 ell c.1 b hb
      refine ih (by omega) _ (fun b' hb' => h b' (fun σ => ?_))
      have hpk : ell ^ (k + 1) = ell ^ k * ell := pow_succ ell k
      have hle : ell ^ (k + 1) ≤ ell ^ n := Nat.pow_le_pow_right (by omega) hk
      have hst : ell ^ k * t + ell ^ k ≤ ell ^ k * ell := by
        have := Nat.mul_le_mul_left (ell ^ k) (Nat.succ_le_of_lt ht); rwa [Nat.mul_succ] at this
      have hNσ := hN σ
      have hNρ := hN c.2
      have h0 := off_shift_base c.1 (ell ^ k * t) c.2 σ (by omega)
      have h1 := hb' σ
      simp only at h1
      rw [off_add c.1 (coarseShift c.1 (ell ^ k * t) c.2) b'.1 σ (by omega)]
      omega

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.goodPl_of_box
#print axioms AdalyFormal.CurvBlock.goodL_of_box
