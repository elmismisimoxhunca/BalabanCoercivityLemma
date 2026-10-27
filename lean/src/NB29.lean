import NB28
/-!
# NB29 -- `goodBd_of_box`: the defect cone of a level-`l` bond lies in a forward box of radius `5 ell^l`

If `R` holds at every site with forward offsets `≤ 5 ell^l` from `c.1`, then `GoodBd ell R l c`
(`ell ≥ 2`, `l ≤ n`, `5 ell^n < N`, `ell^n ∣ N`, `c.1` aligned at `ell^l`).

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice coarseLattice_mem_fits)

variable {L : PeriodicLatticeExtent}

theorem mem_ladPlaqs (s : ℕ) (μ : Fin 3) (n : ℕ) : ∀ (p : List (Fin 3)) (z : PeriodicLatticeSite L)
    (t : PlaqT L), t ∈ ladPlaqs s μ n z p →
      ∃ b ∈ pathBonds s z p, ∃ j < n, t.1 = coarseShift b.1 (s * j) μ := by
  intro p
  induction p with
  | nil => intro z t ht; simp [ladPlaqs] at ht
  | cons ν rest ih =>
      intro z t ht
      rcases List.mem_append.mp ht with h | h
      · obtain ⟨j, hj, rfl⟩ := mem_rungPlaqs s ν μ n z t h
        exact ⟨(z, ν), List.mem_cons_self .., j, hj, rfl⟩
      · obtain ⟨b, hb, j, hj, e⟩ := ih _ t h
        exact ⟨b, List.mem_cons_of_mem _ hb, j, hj, e⟩

theorem goodBd_of_box (ell : ℕ) (hell : 2 ≤ ell) (R : PeriodicLatticeSite L → Prop) (n : ℕ)
    (hN : ∀ ρ, 5 * ell ^ n < L ρ + 1) (hdvd : ∀ ρ, ell ^ n ∣ L ρ + 1) :
    ∀ l ≤ n, ∀ c : PeriodicLatticeEdge L, c.1 ∈ CoarseLattice L (ell ^ l) →
      (∀ z, (∀ σ, off c.1 z σ ≤ 5 * ell ^ l) → R z) → GoodBd ell R l c := by
  have hell0 : 0 < ell := by omega
  have hN3 : ∀ ρ, 3 * ell ^ n < L ρ + 1 := fun ρ => by have := hN ρ; omega
  intro l
  induction l with
  | zero => intro _ c _ _; trivial
  | succ k ih =>
      intro hk c hc h
      have hs : 0 < ell ^ k := pow_pos hell0 k
      have hpk : ell ^ (k + 1) = ell ^ k * ell := pow_succ ell k
      have hle : ell ^ (k + 1) ≤ ell ^ n := Nat.pow_le_pow_right hell0 hk
      have hd1 : ∀ ρ, ell ^ k * ell ∣ L ρ + 1 := fun ρ =>
        Nat.dvd_trans (by rw [← pow_succ]; exact Nat.pow_dvd_pow ell hk) (hdvd ρ)
      have hd0 : ∀ ρ, ell ^ k ∣ L ρ + 1 := fun ρ =>
        Nat.dvd_trans (Nat.pow_dvd_pow ell (by omega)) (hdvd ρ)
      have hc' : c.1 ∈ CoarseLattice L (ell ^ k * ell) := by rw [← pow_succ]; exact hc
      have hck := cl_mono (ell ^ k) ell hc'
      have h2 : 2 * ell ^ k ≤ ell ^ k * ell := by
        rw [Nat.mul_comm 2]; exact Nat.mul_le_mul_left _ hell
      refine ⟨fun b hb => ?_, fun x hx t ht => ?_⟩
      · obtain ⟨t, ht, rfl⟩ := mem_pathBonds_rep (ell ^ k) c.2 ell c.1 b hb
        have hst : ell ^ k * t + ell ^ k ≤ ell ^ k * ell := by
          have := Nat.mul_le_mul_left (ell ^ k) (Nat.succ_le_of_lt ht); rwa [Nat.mul_succ] at this
        refine ih (by omega) _ (pathBonds_aligned _ hd0 _ _ hck _ hb) (fun z hz => h z (fun σ => ?_))
        have hNσ := hN σ
        have hNρ := hN c.2
        have h0 := off_shift_base c.1 (ell ^ k * t) c.2 σ (by omega)
        have h1 := hz σ
        simp only at h1
        rw [off_add c.1 (coarseShift c.1 (ell ^ k * t) c.2) z σ (by omega)]
        omega
      · -- ladder plaquette base: within 2(ell-1) ell^k of c.1
        obtain ⟨b, hb, j, hj, hte⟩ := mem_ladPlaqs (ell ^ k) c.2 ell _ c.1 t ht
        have hfit := coarseLattice_mem_fits hd1 hc'
        have hxo := block_offsets (ell ^ k) ell c.1 x hfit hx
        have hmul : ∀ σ, ell ^ k * (off c.1 x σ / ell ^ k) = off c.1 x σ := fun σ =>
          Nat.mul_div_cancel' (hxo σ).1
        have hy0 : Box c.1 (ell ^ k) (ell ^ k * ell) c.1 := fun σ => by
          rw [off_self]; exact ⟨dvd_zero _, Nat.zero_le _⟩
        have hbB : Box c.1 (ell ^ k) (ell ^ k * ell) b.1 := by
          rw [gamma_eq] at hb
          refine box_stair c.1 c.1 (ell ^ k) (ell ^ k * ell) _ _ _ hy0 ?_ ?_ ?_
            (fun ρ => by have := hN ρ; omega) b hb
          · rw [off_self, hmul]; have := (hxo 2).2; omega
          · rw [off_self, hmul]; have := (hxo 1).2; omega
          · rw [off_self, hmul]; have := (hxo 0).2; omega
        have hst : ell ^ k * j + ell ^ k ≤ ell ^ k * ell := by
          have := Nat.mul_le_mul_left (ell ^ k) (Nat.succ_le_of_lt hj); rwa [Nat.mul_succ] at this
        have hto : ∀ σ, off c.1 t.1 σ ≤ 2 * (ell ^ k * ell) := by
          intro σ
          rw [hte]
          have hb1 := (hbB σ).2
          have hNσ := hN σ
          have hNρ := hN c.2
          have h0 := off_shift_base b.1 (ell ^ k * j) c.2 σ (by omega)
          rw [off_add c.1 b.1 (coarseShift b.1 (ell ^ k * j) c.2) σ (by omega)]
          omega
        refine goodPl_of_box ell hell R n hN3 k (by omega) t.1 (fun z hz => h z (fun σ => ?_))
        have hNσ := hN σ
        have h1 := hz σ
        have h0 := hto σ
        rw [off_add c.1 t.1 z σ (by omega)]
        omega

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.goodBd_of_box
