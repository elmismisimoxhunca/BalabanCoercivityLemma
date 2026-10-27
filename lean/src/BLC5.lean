import BLC4

/-!
# BLC5 -- vertex charts in ball coordinates, from the tower (m2_ballcharts, 2026-10-15)

`vertex_zch`: for every grid index `n`, a chart (`ZCh` in the coordinates of the ball centre `w`) on `Ib (qv n) univ`
(the vertex box of radius `s - 4` cut to `Box r`), at the GE7 constants with `R' = s - 4`.  If that cut box is empty the
statement is vacuous; otherwise the vertex `v = ι_w(qv n)` is a grid vertex (`cst_grid`), within reach of the anchor
`x0 ∈ Ω_j` (`hnear` with `R ≥ 45ℓ + 30`), and `ι_v` is injective on `Box (s-1)` (the torus side is `≥ M ℓ^k ≥ 2s`).
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M2BallCharts

open AdalyFormal.Target.ClayStatement AdalyFormal.M2Glue3 AdalyFormal.M2Glue2 AdalyFormal.M2GlueGeo
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.M2Bridge (pdist_lt_three_s')
open AdalyFormal.StatementLaneR8 (pdist_triangle)

variable {L : PeriodicLatticeExtent}

/-- `t₂ + 43 t₁²` at the cube constants of index `m`. -/
noncomputable def Fv (ell M m : ℕ) (α₀ : ℝ) : ℝ :=
  (1 + 4 * ((12 : ℝ) * M * α₀ * ((ell : ℝ) ^ m)⁻¹)) * ((12 : ℝ) * M * α₀ * (((ell : ℝ) ^ m)⁻¹) ^ 2)
    + 43 * ((12 : ℝ) * M * α₀ * ((ell : ℝ) ^ m)⁻¹) ^ 2

theorem iota_zero (w : PeriodicLatticeSite L) : iota w 0 = w := by
  funext μ; simp [iota]

theorem grid_of_qv {r s : ℕ} (hs : 0 < s) (hsN : ∀ μ, s ∣ L μ + 1) (w : PeriodicLatticeSite L) (n : Fin 3 → ℕ)
    (μ : Fin 3) : (iota w (qv r s w n) μ).val % s = 0 := by
  have h1 := iota_val_int w (qv r s w n) μ
  have hd : (s : ℤ) ∣ ((L μ + 1 : ℕ) : ℤ) := by exact_mod_cast hsN μ
  have h2 : (((iota w (qv r s w n) μ).val : ℤ)) % (s : ℤ) = 0 := by
    rw [h1, Int.emod_emod_of_dvd _ hd]
    simp only [qv]
    rw [show ((w μ).val : ℤ) + (cst r s w μ + (s : ℤ) * (n μ : ℤ))
        = (((w μ).val : ℤ) + cst r s w μ) + (s : ℤ) * (n μ : ℤ) by ring, Int.add_mul_emod_self_left]
    exact cst_grid r s w μ
  have : (((iota w (qv r s w n) μ).val % s : ℕ) : ℤ) = 0 := by push_cast; exact h2
  exact_mod_cast this

theorem vertex_zch {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S)
    (hcov : CoversOm0p ell M 12 k S) (hell : 2 ≤ ell) (hM : 0 < M) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {x0 : PeriodicLatticeSite L} (hx0 : x0 ∈ S.Om j) {w : PeriodicLatticeSite L} (hw : pdist w x0 ≤ 3 * (M * ell ^ j))
    {r : ℕ} (hr7 : r ≤ 7 * M * ell ^ j) (hR : 45 * ell + 30 ≤ R) (hs : 24 ≤ bigSide M ell (j - 1))
    {α₀ η : ℝ} (hη : 0 < η) (hα : 0 ≤ α₀) {U : LinkCfg L} (hP : PerCubeRegular2 ell M 12 k S α₀ η U)
    (hsm : (12 : ℝ) * M * α₀ * ((ell : ℝ) ^ (j - 1))⁻¹ + 12 * M * α₀ * (((ell : ℝ) ^ (j - 1))⁻¹) ^ 2 ≤ 1)
    (ht12 : (12 : ℝ) * M * α₀ * ((ell : ℝ) ^ (j - 1))⁻¹ ≤ 2)
    (hsmall : (4 * cB 1152 5 + 1) * (3 * ((bigSide M ell (j - 1) - 4 : ℕ) : ℝ) + 2) ^ 2 * Fv ell M (j - 1) α₀ ≤ 1)
    (n : Fin 3 → ℕ) :
    ∃ g : PeriodicLatticeSite L → SU2,
      ZCh U g w (Ib r (bigSide M ell (j - 1)) (qv r (bigSide M ell (j - 1)) w n) Finset.univ)
        (fun _ => KT1 4 1152 * (3 * ((bigSide M ell (j - 1) - 4 : ℕ) : ℝ) + 2) * Fv ell M (j - 1) α₀)
        (fun _ => KT2 4 1152 * Fv ell M (j - 1) α₀) := by
  set s := bigSide M ell (j - 1) with hsdef
  set q := qv r s w n with hq
  by_cases hne : (Ib r s q Finset.univ).Nonempty
  · obtain ⟨p0, hp0⟩ := hne
    obtain ⟨hb0, ht0⟩ := mem_Ib.mp hp0
    have hqb : ∀ i, |q i| ≤ (r : ℤ) + ((s : ℤ) - 4) := by
      intro i
      have a := hb0 i; have b := ht0 i (Finset.mem_univ i)
      rw [abs_le] at a b ⊢; constructor <;> omega
    have hs0 : 0 < s := by omega
    have hmk : j - 1 ≤ k := by omega
    have hsN : ∀ μ, s ∣ L μ + 1 := fun μ => hS.2.2.1 (j - 1) hmk μ
    set v := iota w q with hv
    have hgrid : ∀ μ, (v μ).val % s = 0 := grid_of_qv hs0 hsN w n
    -- the scale relation `M ell^j = ell s`
    have hMl : M * ell ^ j = ell * s := by
      rw [hsdef, bigSide]
      have : ell ^ j = ell * ell ^ (j - 1) := by rw [← pow_succ']; congr 1; omega
      rw [this]; ring
    have hnear : ∀ p ∈ BoxS s, pdist (iota v p) x0 + 18 * s ≤ R * s := by
      intro p hp
      set Sb := r + 2 * s with hSb
      have hqp : q + p ∈ BoxS Sb := by
        intro i
        have a := hqb i; have b := hp i
        rw [abs_le] at a
        simp only [Pi.add_apply]
        constructor <;> push_cast <;> omega
      have h0 : (0 : Z3) ∈ BoxS Sb := by
        intro i; simp only [Pi.zero_apply]; constructor <;> push_cast <;> omega
      have h6 := pdist_lt_three_s' (iota_mem_box (v := w) hqp) (iota_mem_box (v := w) h0)
      rw [iota_zero] at h6
      have h7 := pdist_triangle (iota v p) w x0
      rw [hv, iota_iota] at h7
      have hRs : (45 * ell + 30) * s ≤ R * s := Nat.mul_le_mul_right _ hR
      have e1 : (45 * ell + 30) * s = 45 * (ell * s) + 30 * s := by ring
      have e2 : 7 * M * ell ^ j = 7 * (ell * s) := by rw [mul_assoc, hMl]
      rw [hMl] at hw
      rw [e2] at hr7
      rw [hv, iota_iota]
      omega
    have hinj : Set.InjOn (iota v) (Box (s - 4 + 3)) := by
      apply iota_injOn
      intro μ
      have hdk := hS.2.2.1 k le_rfl μ
      have hpos : 0 < L μ + 1 := by omega
      have h1 := Nat.le_of_dvd hpos hdk
      have h2 : bigSide M ell j ≤ bigSide M ell k := by
        unfold bigSide
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hjk)
      have h3 : bigSide M ell j = ell * s := by rw [bigSide]; exact hMl
      have h4 : 2 * s ≤ ell * s := Nat.mul_le_mul_right _ hell
      omega
    have hx0' : x0 ∈ S.Om (j - 1 + 1) := by rw [Nat.sub_add_cancel hj1]; exact hx0
    obtain ⟨gv, hgv⟩ := vertex_chart_of_tower hS hcov hell hM hmk hx0' hgrid hnear hη hα hP hsm
      (R' := s - 4) (by omega) (by omega) hinj ht12 hsmall
    refine ⟨gv, zch_of_lift q hgv (fun p hp => ?_)⟩
    intro i
    have := (mem_Ib.mp hp).2 i (Finset.mem_univ i)
    simp only [Pi.sub_apply]
    have e : ((s - 4 : ℕ) : ℤ) = (s : ℤ) - 4 := by omega
    rw [e]; exact this
  · refine ⟨fun _ => 1, fun p ν hp _ => absurd ⟨p, hp⟩ hne, fun p μ ν hp _ _ _ => absurd ⟨p, hp⟩ hne⟩

end AdalyFormal.M2BallCharts
