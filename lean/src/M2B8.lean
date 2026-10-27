import M2B7
import M2B2

/-!
# M2B8 -- B0 POSITIVE side: when a patch ball lies in the core of a class cube, and the composite `patch_regime`
(m2_bridge_20261014, Layer B0/B5)

* `offc_ball`, `ball_core` : if the offsets of `w₀` have margin `r + 2W + 4` / `r + 2W + 5` from the faces of the box `siteBox z s`, every site `y`
  with `pdist w₀ y ≤ r` lies in the core where the cutoff is `1`.
* `cube_isClass` : (port of percube `cover_class_cube` to r8) a grid-aligned box of side `f·M·ell^j` inside `Ω_j` that meets `B^j` is a class cube of
  index `j` when `3f ≤ R·ell`.
* `patch_regime` : composite -- class + such a box + ball margin  ⟹  a GLOBAL `M1Regular` configuration `V` (at `ell³·2α₀`) that equals `U^g` on every
  bond whose base lies in the ball.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.M2Bridge

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (pdist_comm pdist_shift_le pdist_triangle)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.M1 (M1Regular om_anti)

variable {L : PeriodicLatticeExtent}

theorem offc_ball {N z u v h r : ℕ} (hz : z < N) (hu : u < N) (hv : v < N) (hh : (u + (N - z)) % N = h)
    (hrh : r ≤ h) (hhN : h + r < N) (hp : pcd N u v ≤ r) :
    h ≤ (v + (N - z)) % N + r ∧ (v + (N - z)) % N ≤ h + r := by
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
  rw [hu'] at hh
  rw [hv']
  unfold pcd at hp
  split_ifs at hh hp ⊢ <;> omega

theorem ball_core {z w₀ : PeriodicLatticeSite L} {s W r : ℕ} (hsN : ∀ σ, s ≤ L σ + 1)
    (hmarg : ∀ σ, r + 2 * W + 4 ≤ offc z w₀ σ ∧ offc z w₀ σ + r + 2 * W + 5 ≤ s)
    {y : PeriodicLatticeSite L} (hy : pdist w₀ y ≤ r) :
    ∀ σ, 2 * W + 4 ≤ offc z y σ ∧ offc z y σ + 2 * W + 5 ≤ s := by
  intro σ
  have hp : pcd (L σ + 1) (w₀ σ).val (y σ).val ≤ r :=
    le_trans (Finset.single_le_sum (f := fun μ : Fin 3 => pcd (L μ + 1) (w₀ μ).val (y μ).val)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ σ)) hy
  have hs := hsN σ
  have hm := hmarg σ
  have := offc_ball (N := L σ + 1) (z := (z σ).val) (u := (w₀ σ).val) (v := (y σ).val) (h := offc z w₀ σ) (r := r)
    (z σ).isLt (w₀ σ).isLt (y σ).isLt rfl (by omega) (by omega) hp
  unfold offc at this hm ⊢
  omega

/-! ## port of `cover_class_cube` -/

theorem pdist_lt_three_s' {z0 y q : PeriodicLatticeSite L} {s : ℕ} (hy : y ∈ siteBox z0 s) (hq : q ∈ siteBox z0 s) :
    pdist y q < 3 * s := by
  unfold siteBox at hy hq
  simp only [Set.mem_setOf_eq] at hy hq
  unfold pdist
  have : ∀ σ : Fin 3, pcd (L σ + 1) (y σ).val (q σ).val < s := fun σ =>
    pcd_lt_of_offs (L σ + 1) _ _ (z0 σ).val (s := s) (Nat.succ_pos _) (y σ).isLt (q σ).isLt (z0 σ).isLt (hy σ) (hq σ)
  rw [Fin.sum_univ_three]
  have h0 := this 0; have h1 := this 1; have h2 := this 2
  omega

theorem towerBj_disjoint' {ell M R k : ℕ} {S : Tower L} (h : Admissible ell M R k S) {a b : ℕ} (hab : a < b)
    {x : PeriodicLatticeSite L} (hxa : x ∈ towerBj S a) (hxb : x ∈ towerBj S b) : False := by
  have : S.Om b ⊆ S.Om (a + 1) := om_anti h hab
  exact hxa.2 (this hxb.1)

theorem cube_isClass {ell M R k f j : ℕ} {S : Tower L} (h : Admissible ell M R k S) (hjk : j ≤ k)
    {z0 : PeriodicLatticeSite L} (hgrid : GridCorner (bigSide M ell j) z0)
    (hsub : siteBox z0 (f * bigSide M ell j) ⊆ S.Om j) {y : PeriodicLatticeSite L}
    (hyQ : y ∈ siteBox z0 (f * bigSide M ell j)) (hy : y ∈ towerBj S j) (hR : 3 * f ≤ R * ell) :
    IsClassCube ell M f k S (siteBox z0 (f * bigSide M ell j)) j := by
  have hnot : ∀ q ∈ siteBox z0 (f * bigSide M ell j), q ∉ S.Om (j + 2) := by
    intro q hq hq2
    by_cases hjk' : j < k
    · have h5 := h.2.2.2.2.1 (j + 1) (by omega) y hy.2 q hq2
      have h3 := pdist_lt_three_s' hyQ hq
      have hb : bigSide M ell (j + 1) = bigSide M ell j * ell := by unfold bigSide; ring
      have : R * bigSide M ell (j + 1) ≥ 3 * (f * bigSide M ell j) := by
        rw [hb]
        have : R * (bigSide M ell j * ell) = (R * ell) * bigSide M ell j := by ring
        rw [this]
        calc 3 * (f * bigSide M ell j) = (3 * f) * bigSide M ell j := by ring
          _ ≤ (R * ell) * bigSide M ell j := Nat.mul_le_mul_right _ hR
      omega
    · have : k < j + 2 := by omega
      rw [h.2.1 (j + 2) this] at hq2
      exact hq2
  have hdesc : DescribedAt ell M f k S (siteBox z0 (f * bigSide M ell j)) j := by
    refine ⟨hjk, ⟨z0, hgrid, rfl⟩, ?_, ⟨y, hyQ, hy⟩⟩
    intro q hq
    by_cases hq1 : q ∈ S.Om (j + 1)
    · right; exact ⟨hq1, hnot q hq⟩
    · left; exact ⟨hsub hq, hq1⟩
  refine ⟨hdesc, ?_⟩
  intro i hi
  obtain ⟨-, -, hsubi, ⟨w, hwQ, hwi⟩⟩ := hi
  have hj1 : j = i ∨ j = i + 1 := by
    rcases hsubi hyQ with h1 | h1
    · rcases lt_trichotomy i j with hl | hl | hl
      · exact absurd (towerBj_disjoint' h hl h1 hy) id
      · exact Or.inl hl.symm
      · exact absurd (towerBj_disjoint' h hl hy h1) id
    · rcases lt_trichotomy (i + 1) j with hl | hl | hl
      · exact absurd (towerBj_disjoint' h hl h1 hy) id
      · exact Or.inr hl.symm
      · exact absurd (towerBj_disjoint' h hl hy h1) id
  have hi1 : i = j ∨ i = j + 1 := by
    rcases hdesc.2.2.1 hwQ with h1 | h1
    · rcases lt_trichotomy i j with hl | hl | hl
      · exact absurd (towerBj_disjoint' h hl hwi h1) id
      · exact Or.inl hl
      · exact absurd (towerBj_disjoint' h hl h1 hwi) id
    · rcases lt_trichotomy i (j + 1) with hl | hl | hl
      · exact absurd (towerBj_disjoint' h hl hwi h1) id
      · exact Or.inr hl
      · exact absurd (towerBj_disjoint' h hl h1 hwi) id
  omega

/-! ## composite -/

section composite

variable {ell M R f k j : ℕ} {S : Tower L} {α₀ η : ℝ}

theorem patch_regime (hA : Admissible ell M R k S) (hell : 1 ≤ ell) (hf : 1 ≤ f) (hM : 1 ≤ M)
    (hα : 0 < α₀) (hη : 0 < η) {U : LinkCfg L} (hP : PerCubeRegular2 ell M f k S α₀ η U)
    (hjk : j ≤ k) {z : PeriodicLatticeSite L} (hgrid : GridCorner (bigSide M ell j) z)
    (hsub : siteBox z (f * bigSide M ell j) ⊆ S.Om j)
    (hmeet : ∃ y ∈ siteBox z (f * bigSide M ell j), y ∈ towerBj S j) (hR : 3 * f ≤ R * ell)
    (hL : ∀ σ, 1 ≤ L σ) {W : ℕ} (hW : 64 * ell ^ j ≤ W) (hs7 : 7 ≤ f * bigSide M ell j)
    (hsN : ∀ σ, f * bigSide M ell j ≤ L σ + 1) {w₀ : PeriodicLatticeSite L} {r : ℕ}
    (hmarg : ∀ σ, r + 2 * W + 4 ≤ offc z w₀ σ ∧ offc z w₀ σ + r + 2 * W + 5 ≤ f * bigSide M ell j) :
    ∃ (V : LinkCfg L) (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ),
      M1Regular ell M f k S ((ell : ℝ) ^ 3 * (2 * α₀)) η V ∧
      ∀ e : Bond L, pdist w₀ e.1 ≤ r → V e = periodicGaugeTransform g U e := by
  obtain ⟨y, hyQ, hy⟩ := hmeet
  have hq := cube_isClass hA hjk hgrid hsub hyQ hy hR
  obtain ⟨g, χ, V, hreg, -, hsupp, hcore, hagree⟩ :=
    regime_of_class hA hell hf hM hα hη hP hq (z := z) rfl hL hW hs7
  refine ⟨V, g, hreg, ?_⟩
  intro e he
  have hχ : χ e.1 = 1 := hcore e.1 (fun σ _ => ball_core hsN hmarg he σ)
  have hne : χ e.1 ≠ 0 := by rw [hχ]; norm_num
  have hs := hsupp e.1 hne
  have hcb : CubeBond (siteBox z (f * bigSide M ell j)) e := by
    refine ⟨hs e.1 (by rw [pdist_self']; norm_num), hs _ ?_⟩
    have := pdist_shift_le e.1 e.2
    omega
  exact hagree e hcb hχ

end composite

end AdalyFormal.M2Bridge
