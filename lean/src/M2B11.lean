import M2B8

/-!
# M2B11 -- `b0_positive` : the centred-box criterion (B0, positive direction) (m2_bridge_20261014, Layer B0/B5)

For a G3 patch `(j, w)` with `κ = 1`, `c = 5` (the ball of radius `5·M·ell^j` about the `M·ell^j`-grid corner `w`) the only class cubes that can contain it with room for the
cutoff are the boxes `siteBox z (12·M·ell^j)` with `offc z w σ = 6·M·ell^j` (`w` at their centre).  `centered_corner` produces that corner; `b0_positive` says:
if that centred box lies in `Ω_j` (and `M ≥ 133`, `3·12 ≤ R·ell`) then lane B's regime `M1Regular` (at `ell³·2α₀`) holds for a configuration `V` that agrees with the cube
gauge `U^g` on every bond whose base is in the patch.  (The converse -- when the centred box pokes out of `Ω_j` -- is `patch_inter_not_in_class_cube` in the down-case.)
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.M2Bridge

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (pdist_comm)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.M1 (M1Regular IsPatch gsp strat strat_eq_iff om_anti)

variable {L : PeriodicLatticeExtent}

theorem centered_corner {B : ℕ} (hB : 0 < B) (hdiv : ∀ σ, B ∣ L σ + 1) (hN : ∀ σ, 12 * B ≤ L σ + 1)
    {w : PeriodicLatticeSite L} (hw : GridCorner B w) :
    ∃ z : PeriodicLatticeSite L, GridCorner B z ∧ ∀ σ, offc z w σ = 6 * B := by
  have hlt : ∀ σ, (((w σ).val + (L σ + 1 - 6 * B)) % (L σ + 1)) < L σ + 1 := fun σ => Nat.mod_lt _ (Nat.succ_pos _)
  refine ⟨fun σ => ⟨((w σ).val + (L σ + 1 - 6 * B)) % (L σ + 1), hlt σ⟩, ?_, ?_⟩
  · intro σ
    show (((w σ).val + (L σ + 1 - 6 * B)) % (L σ + 1)) % B = 0
    have h1 : B ∣ (w σ).val := Nat.dvd_of_mod_eq_zero (hw σ)
    have h2 : B ∣ (w σ).val + (L σ + 1 - 6 * B) :=
      Nat.dvd_add h1 (Nat.dvd_sub (hdiv σ) (Dvd.intro_left 6 rfl))
    exact Nat.mod_eq_zero_of_dvd ((Nat.dvd_mod_iff (hdiv σ)).mpr h2)
  · intro σ
    unfold offc
    have hN' := hN σ
    have hu := (w σ).isLt
    show ((w σ).val + (L σ + 1 - (((w σ).val + (L σ + 1 - 6 * B)) % (L σ + 1)))) % (L σ + 1) = 6 * B
    by_cases hc : (w σ).val < 6 * B
    · have e1 : ((w σ).val + (L σ + 1 - 6 * B)) % (L σ + 1) = (w σ).val + (L σ + 1 - 6 * B) :=
        Nat.mod_eq_of_lt (by omega)
      rw [e1, show (w σ).val + (L σ + 1 - ((w σ).val + (L σ + 1 - 6 * B))) = 6 * B by omega]
      exact Nat.mod_eq_of_lt (by omega)
    · have e1 : ((w σ).val + (L σ + 1 - 6 * B)) % (L σ + 1) = (w σ).val - 6 * B := by
        rw [show (w σ).val + (L σ + 1 - 6 * B) = ((w σ).val - 6 * B) + (L σ + 1) by omega, Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (by omega)
      rw [e1, show (w σ).val + (L σ + 1 - ((w σ).val - 6 * B)) = 6 * B + (L σ + 1) by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)

section pos

variable {ell M R k j : ℕ} {S : Tower L} {α₀ η : ℝ}

theorem b0_positive (hA : Admissible ell M R k S) (hell : 1 ≤ ell) (hM : 133 ≤ M) (hα : 0 < α₀) (hη : 0 < η)
    {U : LinkCfg L} (hP : PerCubeRegular2 ell M 12 k S α₀ η U) (hjk : j ≤ k)
    {w : PeriodicLatticeSite L} (hp : IsPatch ell M k 1 S j w)
    (hdiv : ∀ σ, bigSide M ell j ∣ L σ + 1) (hN12 : ∀ σ, 12 * bigSide M ell j ≤ L σ + 1)
    (hbox : ∀ z : PeriodicLatticeSite L, (∀ σ, offc z w σ = 6 * bigSide M ell j) →
        siteBox z (12 * bigSide M ell j) ⊆ S.Om j)
    (hR : 3 * 12 ≤ R * ell) (hL : ∀ σ, 1 ≤ L σ) :
    ∃ (V : LinkCfg L) (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ),
      M1Regular ell M 12 k S ((ell : ℝ) ^ 3 * (2 * α₀)) η V ∧
      ∀ e : Bond L, pdist w e.1 ≤ 5 * gsp ell M 1 j → V e = periodicGaugeTransform g U e := by
  have hE1 : 1 ≤ ell ^ j := Nat.one_le_pow _ _ hell
  have hMpos : 0 < M := by omega
  have hbs : bigSide M ell j = M * ell ^ j := rfl
  have hBpos : 0 < bigSide M ell j := by rw [hbs]; exact Nat.mul_pos hMpos (by omega)
  have hB133 : 133 * ell ^ j ≤ bigSide M ell j := by rw [hbs]; exact Nat.mul_le_mul_right _ hM
  have hgsp : gsp ell M 1 j = bigSide M ell j := by unfold gsp; ring
  obtain ⟨x₀, hx0j, hxs, hd0⟩ := hp.anchor (by norm_num) hMpos (by omega)
  have hgridw : GridCorner (bigSide M ell j) w := by have := hp.2.1; rwa [hgsp] at this
  rw [hgsp] at hd0
  obtain ⟨z, hgrid, hz⟩ := centered_corner hBpos hdiv hN12 hgridw
  have hsub := hbox z hz
  have hx0box : x₀ ∈ siteBox z (12 * bigSide M ell j) := by
    rw [mem_siteBox_offc]
    have hc := ball_core (z := z) (w₀ := w) (s := 12 * bigSide M ell j) (W := 0) (r := 3 * bigSide M ell j) hN12
      (fun σ => by rw [hz σ]; omega) (y := x₀) (by rw [pdist_comm]; exact hd0)
    intro σ
    have := hc σ
    omega
  have hxB : x₀ ∈ towerBj S j := (strat_eq_iff hA hjk x₀).mpr ⟨om_anti hA (Nat.zero_le j) hx0j, hxs⟩
  have := patch_regime hA hell (by norm_num : 1 ≤ 12) (by omega : 1 ≤ M) hα hη hP hjk hgrid hsub ⟨x₀, hx0box, hxB⟩ hR hL
    (W := 64 * ell ^ j) le_rfl (by omega) hN12 (w₀ := w) (r := 5 * bigSide M ell j)
    (fun σ => by rw [hz σ]; constructor <;> omega)
  rw [hgsp]
  exact this

end pos

end AdalyFormal.M2Bridge

#print axioms AdalyFormal.M2Bridge.centered_corner
#print axioms AdalyFormal.M2Bridge.b0_positive
