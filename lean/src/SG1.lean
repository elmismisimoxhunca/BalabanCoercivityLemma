import SK1

/-!
# SG1 -- an index-`i` class cube around a site `x` for ANY level `i ≤ k` (lane m2_fields123_20261015)

Generalisation of `M2UnitCharts.class_cube_at` (index `k` around a unit site, using `LambdaOK2`) to a general index `i`, with the
geometric input stated as three plain hypotheses on the tower (no `Λ`):
* `hbox`  : the `ℓ^∞`-box of radius `7 M ℓ^i` around `x` lies in `Ω_i`;
* `hout`  : that box misses `Ω_{i+2}`;
* `hw`    : some `w` within `pdist ≤ 5 M ℓ^i` of `x` is in `Ω_i` but not in `Ω_{i+1}` (so the cube meets `B^i`).
Conclusion: a grid-aligned `12 M ℓ^i`-box that is a class cube of index `i` and whose core (margin `128 n + 4`, `n = ℓ^i`) contains `Ball x r`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
namespace AdalyFormal.M2F123

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneR8 (Ball pdist_triangle pdist_comm)
open AdalyFormal.M2Bridge (offc offc_lt mem_siteBox_offc)
open AdalyFormal.M2UnitCharts (cornerOf cornerOf_grid corner_off_ball box_pcd om_anti)

theorem class_cube_gen {ell M R k : ℕ} {L : PeriodicLatticeExtent} (hell : 0 < ell) (hM : 0 < M)
    {S : Tower L} (hS : Admissible ell M R k S) {i : ℕ} (hi : i ≤ k) (x : PeriodicLatticeSite L)
    (hbox : ∀ x'' : PeriodicLatticeSite L,
      (∀ σ : Fin 3, pcd (L σ + 1) (x σ).val (x'' σ).val ≤ 7 * (M * ell ^ i)) → x'' ∈ S.Om i)
    (hout : ∀ x'' : PeriodicLatticeSite L,
      (∀ σ : Fin 3, pcd (L σ + 1) (x σ).val (x'' σ).val ≤ 7 * (M * ell ^ i)) → x'' ∉ S.Om (i + 2))
    (w : PeriodicLatticeSite L) (hw : pdist x w ≤ 5 * (M * ell ^ i)) (hwO : w ∉ S.Om (i + 1))
    (r : ℕ) (hr : r + 128 * ell ^ i + 5 ≤ 5 * (M * ell ^ i)) :
    ∃ z : PeriodicLatticeSite L,
      IsClassCube ell M 12 k S (siteBox z (12 * bigSide M ell i)) i ∧
      ∀ x' ∈ Ball x r, ∀ σ : Fin 3, 12 * bigSide M ell i ≤ L σ + 1 →
        2 * (64 * ell ^ i) + 4 ≤ offc z x' σ ∧ offc z x' σ + 2 * (64 * ell ^ i) + 5 ≤ 12 * bigSide M ell i := by
  set n := ell ^ i with hn0
  have hnpos : 0 < n := pow_pos hell i
  have hB : 0 < M * n := Nat.mul_pos hM hnpos
  have hbs : bigSide M ell i = M * n := rfl
  set z := cornerOf (M * n) x with hz
  have hgrid := cornerOf_grid hB (fun σ => hS.2.2.1 i hi σ) x
  have hr5 : r ≤ 5 * (M * n) := by omega
  have hOm : ∀ x'' ∈ siteBox z (12 * bigSide M ell i), x'' ∈ S.Om i := by
    intro x'' hx''
    rw [hbs] at hx''
    exact hbox x'' (fun σ => box_pcd hB x x'' hx'' σ)
  have hOut : ∀ x'' ∈ siteBox z (12 * bigSide M ell i), x'' ∉ S.Om (i + 2) := by
    intro x'' hx''
    rw [hbs] at hx''
    exact hout x'' (fun σ => box_pcd hB x x'' hx'' σ)
  have hwin : w ∈ siteBox z (12 * bigSide M ell i) := by
    rw [hbs, mem_siteBox_offc]
    intro σ
    by_cases h12 : 12 * (M * n) ≤ L σ + 1
    · have : 5 * (M * n) ≤ offc z w σ + 5 * (M * n) ∧ offc z w σ + 1 ≤ 6 * (M * n) + 5 * (M * n) :=
        corner_off_ball (x := x) (x' := w) hB (le_refl (5 * (M * n))) σ h12 hw
      omega
    · have := offc_lt z w σ; omega
  have hwOm : w ∈ S.Om i := hOm w hwin
  have hdesc : DescribedAt ell M 12 k S (siteBox z (12 * bigSide M ell i)) i := by
    refine ⟨hi, ⟨z, hgrid, rfl⟩, ?_, ⟨w, hwin, ?_⟩⟩
    · intro y hy
      by_cases h1 : y ∈ S.Om (i + 1)
      · right; exact ⟨h1, hOut y hy⟩
      · left; exact ⟨hOm y hy, h1⟩
    · exact ⟨hwOm, hwO⟩
  refine ⟨z, ⟨hdesc, ?_⟩, ?_⟩
  · intro i' hi'
    obtain ⟨-, -, hsub, v, hvin, hvB⟩ := hi'
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : v ∈ S.Om i := hOm v hvin
      have h2 : S.Om i ⊆ S.Om (i' + 1) := om_anti hS.1 (by omega)
      exact hvB.2 (h2 h1)
    · have h3 := hsub hwin
      have h4 : S.Om i' ⊆ S.Om (i + 1) := om_anti hS.1 (by omega)
      rcases h3 with h | h
      · exact hwO (h4 h.1)
      · have h5 : S.Om (i' + 1) ⊆ S.Om (i + 1) := om_anti hS.1 (by omega)
        exact hwO (h5 h.1)
  · intro x' hx' σ h12
    have hp : pdist x x' ≤ r := hx'
    have : 5 * (M * n) ≤ offc z x' σ + r ∧ offc z x' σ + 1 ≤ 6 * (M * n) + r :=
      corner_off_ball (x := x) (x' := x') hB hr5 σ (by rw [hbs] at h12; exact h12) hp
    rw [hbs]
    omega

end AdalyFormal.M2F123

#print axioms AdalyFormal.M2F123.class_cube_gen
