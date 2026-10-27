import MS7
import NB25

/-!
# MS8 -- the cone predicates of `link_tower_na_loc` (curvature_blocking NB24/NB25) from a REGION condition

`link_tower_na_loc` (NB25) bounds the averaged link `Ū^{(l)}(c)` at an `ℓ^l`-aligned bond `c` from fine-link and fine-plaquette
bounds on CONES `goodL`, `GoodBd` (with the plaquette cone `GoodPl`, NB24) — recursive predicates.  Here: each cone is
contained in the forward offset box of side `4 ℓ^l` at `c` (`off c.1 w σ ≤ 4ℓ^l` for every direction `σ`):
* `goodPl_of_region`, `goodL_of_region`, `goodBd_of_region` (`ℓ ≥ 2`, no wrap `4ℓ^l < L_σ + 1`, `c` aligned and fitting);
* helpers `ladPlaqs_base`, `coarseShift_mul_mem_coarse`, `pcd_le_off`, `pdist_le_off_sum`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1Site

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)
open AdalyFormal.Balaban.PoincareBridge (coarseLattice_fits)
open AdalyFormal.CurvBlock (off Box GoodPl GoodBd goodL pathBonds ladPlaqs rungPlaqs mem_pathBonds_rep mem_rungPlaqs
  off_add off_shift_val off_shift_ne off_self box_stair gamma_eq block_offsets)

variable {L : PeriodicLatticeExtent}

theorem ladPlaqs_base (s : ℕ) (μ : Fin 3) (n : ℕ) : ∀ (p : List (Fin 3)) (z : PeriodicLatticeSite L)
    (t : PeriodicLatticeSite L × Fin 3 × Fin 3), t ∈ ladPlaqs s μ n z p →
      ∃ b ∈ pathBonds s z p, ∃ m < n, t.1 = coarseShift b.1 (s * m) μ := by
  intro p
  induction p with
  | nil => intro z t ht; simp [ladPlaqs] at ht
  | cons ν rest ih =>
      intro z t ht
      rcases List.mem_append.mp ht with h | h
      · obtain ⟨m, hm, rfl⟩ := mem_rungPlaqs s ν μ n z t h
        exact ⟨(z, ν), List.mem_cons_self .., m, hm, rfl⟩
      · obtain ⟨b, hb, m, hm, hbt⟩ := ih _ t h
        exact ⟨b, List.mem_cons_of_mem _ hb, m, hm, hbt⟩

theorem coarseShift_mul_mem_coarse (s t : ℕ) (hdvd : ∀ ν, s ∣ L ν + 1) (y : PeriodicLatticeSite L)
    (hy : y ∈ CoarseLattice L s) (μ : Fin 3) : coarseShift y (s * t) μ ∈ CoarseLattice L s := by
  rw [mem_CoarseLattice] at hy ⊢
  intro ν
  by_cases hν : ν = μ
  · subst hν
    rw [coarseShift_val_eq, Nat.mod_mod_of_dvd _ (hdvd ν), Nat.add_mul_mod_self_left]
    exact hy ν
  · rw [coarseShift_apply_ne y _ μ ν hν]; exact hy ν

/-- the plaquette cone sits in the forward box of side `4ℓ^l` -/
theorem goodPl_of_region (ell : ℕ) (hell : 2 ≤ ell) (R : PeriodicLatticeSite L → Prop) :
    ∀ (l : ℕ) (y : PeriodicLatticeSite L), (∀ σ, 4 * ell ^ l < L σ + 1) →
      (∀ w, (∀ σ, off y w σ ≤ 4 * ell ^ l) → R w) → GoodPl ell R l y := by
  intro l
  induction l with
  | zero =>
    intro y _ h
    exact h y (fun σ => by rw [off_self]; omega)
  | succ l ih =>
    intro y hwr h z _ hbox
    have hp : 1 ≤ ell ^ l := Nat.one_le_pow _ _ (by omega)
    have hq : ell ^ l * 2 ≤ ell ^ l * ell := Nat.mul_le_mul_left _ hell
    have hsucc : ell ^ (l + 1) = ell ^ l * ell := pow_succ ell l
    refine ih z (fun σ => by have := hwr σ; rw [hsucc] at this; omega) (fun w hw => h w (fun σ => ?_))
    have hb := (hbox σ).2
    have hw' := hw σ
    have hwr' := hwr σ
    rw [hsucc] at hwr' ⊢
    have hsum : off z w σ + off y z σ < L σ + 1 := by omega
    rw [off_add y z w σ hsum]
    omega

/-- the straight-link cone -/
theorem goodL_of_region (ell : ℕ) (hell : 2 ≤ ell) (Rl : PeriodicLatticeEdge L → Prop) :
    ∀ (l : ℕ) (c : PeriodicLatticeEdge L), (∀ σ, 4 * ell ^ l < L σ + 1) →
      (∀ b : PeriodicLatticeEdge L, b.2 = c.2 → (∀ σ, off c.1 b.1 σ ≤ 4 * ell ^ l) → Rl b) → goodL ell Rl l c := by
  intro l
  induction l with
  | zero =>
    intro c _ h
    exact h c rfl (fun σ => by rw [off_self]; omega)
  | succ l ih =>
    intro c hwr h b hb
    obtain ⟨t, ht, rfl⟩ := mem_pathBonds_rep (ell ^ l) c.2 ell c.1 b hb
    have hp : 1 ≤ ell ^ l := Nat.one_le_pow _ _ (by omega)
    have hq : ell ^ l * 2 ≤ ell ^ l * ell := Nat.mul_le_mul_left _ hell
    have hsucc : ell ^ (l + 1) = ell ^ l * ell := pow_succ ell l
    have hst : ell ^ l * t + ell ^ l ≤ ell ^ l * ell := by
      have := Nat.mul_le_mul_left (ell ^ l) (Nat.succ_le_of_lt ht); rwa [Nat.mul_succ] at this
    have hoffb : ∀ σ, off c.1 (coarseShift c.1 (ell ^ l * t) c.2) σ ≤ ell ^ l * t := by
      intro σ
      by_cases hσ : σ = c.2
      · subst hσ
        have := hwr c.2; rw [hsucc] at this
        rw [off_shift_val _ _ _ _ (by rw [off_self]; omega), off_self]; omega
      · rw [off_shift_ne _ _ _ hσ, off_self]; omega
    refine ih _ (fun σ => by have := hwr σ; rw [hsucc] at this; omega) (fun b' hb'2 hb' => h b' hb'2 (fun σ => ?_))
    have h1 : off (coarseShift c.1 (ell ^ l * t) c.2) b'.1 σ ≤ 4 * ell ^ l := hb' σ
    have h2 := hoffb σ
    have hwr' := hwr σ
    rw [hsucc] at hwr' ⊢
    have hsum : off (coarseShift c.1 (ell ^ l * t) c.2) b'.1 σ + off c.1 (coarseShift c.1 (ell ^ l * t) c.2) σ
        < L σ + 1 := by omega
    rw [off_add c.1 _ b'.1 σ hsum]
    omega

/-- the bond cone (links and ladder plaquettes) -/
theorem goodBd_of_region (ell : ℕ) (hell : 2 ≤ ell) (R : PeriodicLatticeSite L → Prop) :
    ∀ (l : ℕ) (c : PeriodicLatticeEdge L), c.1 ∈ CoarseLattice L (ell ^ l) → (∀ σ, ell ^ l ∣ L σ + 1) →
      (∀ σ, 4 * ell ^ l < L σ + 1) →
      (∀ w, (∀ σ, off c.1 w σ ≤ 4 * ell ^ l) → R w) → GoodBd ell R l c := by
  intro l
  induction l with
  | zero => intro c _ _ _ _; trivial
  | succ l ih =>
    intro c hc hdvd hwr h
    have hell0 : 0 < ell := by omega
    have hp : 1 ≤ ell ^ l := Nat.one_le_pow _ _ hell0
    have hq : ell ^ l * 2 ≤ ell ^ l * ell := Nat.mul_le_mul_left _ hell
    have hsucc : ell ^ (l + 1) = ell ^ l * ell := pow_succ ell l
    have hdvdl : ∀ σ, ell ^ l ∣ L σ + 1 := fun σ => Dvd.dvd.trans (pow_dvd_pow ell (Nat.le_succ l)) (hdvd σ)
    have hcl : c.1 ∈ CoarseLattice L (ell ^ l) := by
      rw [mem_CoarseLattice] at hc ⊢
      intro ν
      exact Nat.mod_eq_zero_of_dvd (dvd_trans (pow_dvd_pow ell (Nat.le_succ l)) (Nat.dvd_of_mod_eq_zero (hc ν)))
    have hfit : ∀ σ, (c.1 σ).val + ell ^ l * ell ≤ L σ + 1 := by
      have := coarseLattice_fits hdvd hc
      intro σ; have := this σ; rwa [hsucc] at this
    refine ⟨fun b hb => ?_, fun x hx t ht => ?_⟩
    · -- straight bonds
      obtain ⟨t, ht, rfl⟩ := mem_pathBonds_rep (ell ^ l) c.2 ell c.1 b hb
      have hst : ell ^ l * t + ell ^ l ≤ ell ^ l * ell := by
        have := Nat.mul_le_mul_left (ell ^ l) (Nat.succ_le_of_lt ht); rwa [Nat.mul_succ] at this
      have hoffb : ∀ σ, off c.1 (coarseShift c.1 (ell ^ l * t) c.2) σ ≤ ell ^ l * t := by
        intro σ
        by_cases hσ : σ = c.2
        · subst hσ
          have := hwr c.2; rw [hsucc] at this
          rw [off_shift_val _ _ _ _ (by rw [off_self]; omega), off_self]; omega
        · rw [off_shift_ne _ _ _ hσ, off_self]; omega
      refine ih _ (coarseShift_mul_mem_coarse (ell ^ l) t hdvdl c.1 hcl c.2) hdvdl
        (fun σ => by have := hwr σ; rw [hsucc] at this; omega) (fun w hw => h w (fun σ => ?_))
      have h1 : off (coarseShift c.1 (ell ^ l * t) c.2) w σ ≤ 4 * ell ^ l := hw σ
      have h2 := hoffb σ
      have hwr' := hwr σ
      rw [hsucc] at hwr' ⊢
      have hsum : off (coarseShift c.1 (ell ^ l * t) c.2) w σ + off c.1 (coarseShift c.1 (ell ^ l * t) c.2) σ
          < L σ + 1 := by omega
      rw [off_add c.1 _ w σ hsum]
      omega
    · -- ladder plaquettes
      set s := ell ^ l with hs
      have hxo := block_offsets s ell c.1 x hfit hx
      have hmul : ∀ σ, s * (off c.1 x σ / s) = off c.1 x σ := fun σ => Nat.mul_div_cancel' (hxo σ).1
      set B := s * ell - s with hB
      have hBL : ∀ ρ, B < L ρ + 1 := fun ρ => by have := hwr ρ; rw [hsucc] at this; omega
      have hbox0 : Box c.1 s B c.1 := fun σ => by rw [off_self]; exact ⟨dvd_zero _, Nat.zero_le _⟩
      obtain ⟨b, hb, m, hm, hbt⟩ := ladPlaqs_base s c.2 ell (coarseGammaPath s c.1 x) c.1 t ht
      rw [gamma_eq] at hb
      have hbB := box_stair c.1 c.1 s B _ _ _ hbox0
        (by rw [off_self, hmul]; have := (hxo 2).2; omega)
        (by rw [off_self, hmul]; have := (hxo 1).2; omega)
        (by rw [off_self, hmul]; have := (hxo 0).2; omega) hBL b hb
      have hsm : s * m + s ≤ s * ell := by
        have := Nat.mul_le_mul_left s (Nat.succ_le_of_lt hm); rwa [Nat.mul_succ] at this
      have hofft : ∀ σ, off c.1 t.1 σ ≤ 2 * (s * ell - s) := by
        intro σ
        rw [hbt]
        by_cases hσ : σ = c.2
        · subst hσ
          have hb2 := (hbB c.2).2
          have := hwr c.2; rw [hsucc] at this
          rw [off_shift_val _ _ _ _ (by omega)]
          omega
        · rw [off_shift_ne _ _ _ hσ]; have := (hbB σ).2; omega
      refine goodPl_of_region ell hell R l t.1 (fun σ => by have := hwr σ; rw [hsucc] at this; omega)
        (fun w hw => h w (fun σ => ?_))
      have h1 := hw σ
      have h2 := hofft σ
      have hwr' := hwr σ
      rw [hsucc] at hwr' ⊢
      have hsum : off t.1 w σ + off c.1 t.1 σ < L σ + 1 := by omega
      rw [off_add c.1 t.1 w σ hsum]
      omega

#print axioms ladPlaqs_base
#print axioms coarseShift_mul_mem_coarse
#print axioms goodPl_of_region
#print axioms goodL_of_region
#print axioms goodBd_of_region

end AdalyFormal.M1Site
