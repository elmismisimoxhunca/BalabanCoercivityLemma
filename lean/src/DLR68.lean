import DLR29

/-!
# DL68 -- the one-step visible set is ALIGNED, and its multiplicity is at most 192

With `s ∣ L ν + 1` (every `ν`):
* `onPath_dvd`, `block_dvd`, `cPlusS_dvd`, **`visStep_dvd`** : if `s ∣ c₋` then every edge read by the stride-`s` step at `c`
  is based at an `s`-aligned site (the step never reads off the level-`s` sublattice);
* **`card_vis_le`** : for `n = s·ell` with `n ∣ L ν + 1`, every edge `e` is read by at most `3·4³ = 192` of the `n`-aligned
  bonds `c` (`VisStep_reach` (DL29): `c₋` reaches `e₋` within `Rstep = (4ell−3)s`; `card_reach_coarse_le`);
* **`sum_vis_le`** : `Σ_{c n-aligned} Σ_{e ∈ Vis(c)} g e ≤ 192 Σ_{e s-aligned} g e` for `g ≥ 0`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.DLayer

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.UbarTowerCov (cPlusS cPlusS_eq)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath)

variable {L : PeriodicLatticeExtent}

theorem mod_dvd_of (s a t N : ℕ) (hN : s ∣ N) (ha : s ∣ a) (ht : s ∣ t) : s ∣ (a + t) % N := by
  have h := Nat.mod_add_div (a + t) N
  have h2 : s ∣ (a + t) := dvd_add ha ht
  have h3 : s ∣ N * ((a + t) / N) := dvd_mul_of_dvd_left hN _
  have : (a + t) % N = (a + t) - N * ((a + t) / N) := by omega
  rw [this]; exact Nat.dvd_sub h2 h3

theorem shift_dvd (s t : ℕ) (hL : ∀ ν, s ∣ L ν + 1) (y : PeriodicLatticeSite L) (hy : ∀ ν, s ∣ (y ν).val)
    (ht : s ∣ t) (μ : Fin 3) : ∀ ν, s ∣ ((coarseShift y t μ) ν).val := by
  intro ν
  by_cases h : ν = μ
  · subst h; rw [coarseShift_val_eq]; exact mod_dvd_of s _ _ _ (hL ν) (hy ν) ht
  · rw [coarseShift_apply_ne y t μ ν h]; exact hy ν

theorem onPath_dvd (s : ℕ) (hL : ∀ ν, s ∣ L ν + 1) :
    ∀ (p : List (Fin 3)) (y : PeriodicLatticeSite L) (e : PeriodicLatticeEdge L), (∀ ν, s ∣ (y ν).val) →
      OnPath s y p e → ∀ ν, s ∣ (e.1 ν).val := by
  intro p
  induction p with
  | nil => intro y e _ h; exact h.elim
  | cons μ rest ih =>
      intro y e hy h
      rcases h with h | h
      · subst h; exact hy
      · exact ih _ e (shift_dvd s s hL y hy (dvd_refl s) μ) h

theorem block_dvd (s ell : ℕ) (y x : PeriodicLatticeSite L) (hy : ∀ ν, s ∣ (y ν).val)
    (hx : x ∈ stepBlockOf y s ell) : ∀ ν, s ∣ (x ν).val := by
  intro ν
  rw [mem_stepBlockOf] at hx
  obtain ⟨h1, _, h3⟩ := hx ν
  have := Nat.dvd_add h3 (hy ν)
  rwa [Nat.sub_add_cancel h1] at this

theorem cPlusS_dvd (s ell : ℕ) (hL : ∀ ν, s ∣ L ν + 1) (c : PeriodicLatticeEdge L) (hc : ∀ ν, s ∣ (c.1 ν).val) :
    ∀ ν, s ∣ ((cPlusS s ell c) ν).val := by
  rw [cPlusS_eq]
  exact shift_dvd s (s * ell) hL c.1 hc (dvd_mul_right s ell) c.2

theorem visStep_dvd (s ell : ℕ) (hL : ∀ ν, s ∣ L ν + 1) (c e : PeriodicLatticeEdge L) (hc : ∀ ν, s ∣ (c.1 ν).val)
    (h : VisStep s ell c e) : ∀ ν, s ∣ (e.1 ν).val := by
  have hp := cPlusS_dvd s ell hL c hc
  rcases h with ⟨x, _, he⟩ | ⟨x, _, he⟩ | ⟨x, hx, he⟩ | ⟨x, _, he⟩ | he
  · exact onPath_dvd s hL _ _ e hc he
  · exact onPath_dvd s hL _ _ e hp he
  · exact onPath_dvd s hL _ _ e (block_dvd s ell c.1 x hc hx) he
  · exact onPath_dvd s hL _ _ e hp he
  · exact onPath_dvd s hL _ _ e hc he

theorem Rstep_div (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell) : Rstep ell s / (s * ell) ≤ 3 := by
  unfold Rstep
  rw [mul_comm s ell, Nat.mul_div_mul_right _ _ hs]
  rw [Nat.div_le_iff_le_mul_add_pred hell]
  omega

open Classical in
theorem card_vis_le (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell) (hn : ∀ ν, s * ell ∣ L ν + 1)
    (e : PeriodicLatticeEdge L) :
    (Finset.univ.filter (fun c : CoarseBond L (s * ell) => VisStep s ell (c.1.1, c.2) e)).card ≤ 192 := by
  set R := Rstep ell s
  set Y := Finset.univ.filter (fun y : PeriodicLatticeSite L => (∀ ν, s * ell ∣ (y ν).val) ∧ Reach R y e.1)
  have hY : Y.card ≤ 64 := by
    have h1 := card_reach_coarse_le (s * ell) (Nat.mul_pos hs hell) hn R e.1
    have h2 : R / (s * ell) ≤ 3 := Rstep_div s ell hs hell
    have h3 : (R / (s * ell) + 1) ^ 3 ≤ 4 ^ 3 := Nat.pow_le_pow_left (by omega) 3
    calc Y.card ≤ (R / (s * ell) + 1) ^ 3 := h1
      _ ≤ 4 ^ 3 := h3
      _ = 64 := by norm_num
  have hinj : Set.InjOn (fun c : CoarseBond L (s * ell) => (c.1.1, c.2))
      ↑(Finset.univ.filter (fun c : CoarseBond L (s * ell) => VisStep s ell (c.1.1, c.2) e)) := by
    intro c _ c' _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Subtype.ext h.1) h.2
  have hmaps : ∀ c ∈ Finset.univ.filter (fun c : CoarseBond L (s * ell) => VisStep s ell (c.1.1, c.2) e),
      (fun c : CoarseBond L (s * ell) => (c.1.1, c.2)) c ∈ Y ×ˢ (Finset.univ : Finset (Fin 3)) := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    simp only [Finset.mem_product, Finset.mem_univ, and_true, Y, Finset.mem_filter, true_and]
    refine ⟨fun ν => Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp c.1.2 ν), ?_⟩
    exact VisStep_reach s ell hs (c.1.1, c.2) e hc
  have := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin] at this
  omega

open Classical in
/-- **double counting over the visible sets** -/
theorem sum_vis_le (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell) (hn : ∀ ν, s * ell ∣ L ν + 1)
    (g : PeriodicLatticeEdge L → ℝ) (hg : ∀ e, 0 ≤ g e) :
    ∑ c : CoarseBond L (s * ell), ∑ e ∈ Finset.univ.filter (fun e => VisStep s ell (c.1.1, c.2) e), g e
      ≤ 192 * ∑ e : CoarseBond L s, g (e.1.1, e.2) := by
  have hL : ∀ ν, s ∣ L ν + 1 := fun ν => dvd_trans (dvd_mul_right s ell) (hn ν)
  -- restrict the inner sums to aligned edges
  set Al := Finset.univ.filter (fun e : PeriodicLatticeEdge L => ∀ ν, s ∣ (e.1 ν).val) with hAl
  have hin : ∀ c : CoarseBond L (s * ell),
      ∑ e ∈ Finset.univ.filter (fun e => VisStep s ell (c.1.1, c.2) e), g e
        = ∑ e ∈ Al, if VisStep s ell (c.1.1, c.2) e then g e else 0 := by
    intro c
    rw [Finset.sum_filter]
    symm
    refine Finset.sum_subset (Finset.subset_univ _) (fun e _ he => ?_)
    have hc : ∀ ν, s ∣ (c.1.1 ν).val := fun ν =>
      dvd_trans (dvd_mul_right s ell) (Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp c.1.2 ν))
    by_cases hv : VisStep s ell (c.1.1, c.2) e
    · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, visStep_dvd s ell hL (c.1.1, c.2) e hc hv⟩) he
    · rw [if_neg hv]
  rw [Finset.sum_congr rfl (fun c _ => hin c), Finset.sum_comm]
  have hcount : ∀ e ∈ Al, ∑ c : CoarseBond L (s * ell), (if VisStep s ell (c.1.1, c.2) e then g e else 0)
      ≤ 192 * g e := by
    intro e _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have := card_vis_le s ell hs hell hn e
    have h' : ((Finset.univ.filter (fun c : CoarseBond L (s * ell) => VisStep s ell (c.1.1, c.2) e)).card : ℝ) ≤ 192 := by
      exact_mod_cast this
    exact mul_le_mul_of_nonneg_right h' (hg e)
  refine (Finset.sum_le_sum hcount).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (by norm_num)
  -- aligned edges ↔ `CoarseBond L s`
  refine Finset.sum_bij' (fun e he => ((⟨e.1, mem_CoarseLattice.mpr (fun ν => Nat.mod_eq_zero_of_dvd
      ((Finset.mem_filter.mp he).2 ν))⟩, e.2) : CoarseBond L s))
    (fun c _ => ((c.1.1, c.2) : PeriodicLatticeEdge L)) ?_ ?_ ?_ ?_ ?_
  · intro e _; exact Finset.mem_univ _
  · intro c _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun ν => Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp c.1.2 ν)⟩
  · intro e _; rfl
  · intro c _; rfl
  · intro e _; rfl

#print axioms visStep_dvd
#print axioms card_vis_le
#print axioms sum_vis_le

end AdalyFormal.DLayer
