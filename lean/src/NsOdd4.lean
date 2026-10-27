import NsOdd3

/-!
# NsOdd4 -- exact loop angles of an alternating "shape" field at an ODD stride (lane ncwdh_strong_20261017)

`shapeFld t D T Ef a p` is the Cartan angle field
`θ(z,0) = t (-1)^{z₁} D(z₀) a(z₁,z₂)`, `θ(z,1) = t (-1)^{z₁} (T(z₀) + Ef(z₀) p(z₁,z₂))`, `θ(z,2) = 0`
(this contains the level-0 layer `D = 0, T = [· = c]`, the first blocked level `phi1o`, and the unit-level background).
For an odd stride `s` and an even transverse side `N₁`, `(-1)^{(z₁ + s j) mod N₁} = (-1)^{z₁} (-1)^j`, which turns the staircase and
segment angles into explicit alternating sums (`gamma_shape`, `seg0_shape`, `seg1_shape`).
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge loopVar coarseBondVar gammaVarStrided cPlusS cPlusS_eq)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarsePathEndpoint coarseGammaPath coarseCoordSteps coarseStraightSegment)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)

variable {L : PeriodicLatticeExtent}

theorem sgn_shift (N : ℕ) (hN : 2 ∣ N) (s b j : ℕ) (hs : s % 2 = 1) : sgnNat ((b + s * j) % N) = sgnNat b * pmN j := by
  rw [sgnNat_mod N (b + s * j) hN]
  have hsj : (s * j) % 2 = j % 2 := by rw [Nat.mul_mod, hs]; simp
  unfold sgnNat pmN
  by_cases hb : b % 2 = 0 <;> by_cases hj : j % 2 = 0
  · have : (b + s * j) % 2 = 0 := by omega
    simp [hb, hj, this]
  · have : (b + s * j) % 2 ≠ 0 := by omega
    simp [hb, hj, this]
  · have : (b + s * j) % 2 ≠ 0 := by omega
    simp [hb, hj, this]
  · have : (b + s * j) % 2 = 0 := by omega
    simp [hb, hj, this]

/-- the alternating shape field. -/
noncomputable def shapeFld (t : ℝ) (D T Ef : ℕ → ℝ) (a p : ℕ → ℕ → ℝ) : PeriodicLatticeEdge L → ℝ :=
  fld (fun z0 z1 z2 => t * sgnNat z1 * (D z0 * a z1 z2)) (fun z0 z1 z2 => t * sgnNat z1 * (T z0 + Ef z0 * p z1 z2))

theorem seg0_shape (hN : 2 ∣ L 1 + 1) (s ell : ℕ) (t : ℝ) (D T Ef : ℕ → ℝ) (a p : ℕ → ℕ → ℝ) (z : PeriodicLatticeSite L) :
    pathAngG s (shapeFld t D T Ef a p) z (List.replicate ell 0) =
      t * sgnNat (z 1).val * ((∑ j ∈ Finset.range ell, D (((z 0).val + s * j) % (L 0 + 1))) * a (z 1).val (z 2).val) := by
  unfold shapeFld
  rw [pathAngG_fld_rep0, Finset.sum_mul, Finset.mul_sum]

theorem seg1_shape (hN : 2 ∣ L 1 + 1) (s ell : ℕ) (hs : s % 2 = 1) (t : ℝ) (D T Ef : ℕ → ℝ) (a p : ℕ → ℕ → ℝ)
    (z : PeriodicLatticeSite L) :
    pathAngG s (shapeFld t D T Ef a p) z (List.replicate ell 1) =
      t * sgnNat (z 1).val * (∑ j ∈ Finset.range ell, pmN j * (T (z 0).val + Ef (z 0).val * p (((z 1).val + s * j) % (L 1 + 1)) (z 2).val)) := by
  unfold shapeFld
  rw [pathAngG_fld_rep1, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [sgn_shift (L 1 + 1) hN s (z 1).val j hs]
  ring

theorem seg2_shape (s ell : ℕ) (t : ℝ) (D T Ef : ℕ → ℝ) (a p : ℕ → ℕ → ℝ) (z : PeriodicLatticeSite L) :
    pathAngG s (shapeFld t D T Ef a p) z (List.replicate ell 2) = 0 := by
  unfold shapeFld
  exact pathAngG_fld_rep2 s _ _ ell z

theorem gamma_shape (hN : 2 ∣ L 1 + 1) (s : ℕ) (hs : s % 2 = 1) (t : ℝ) (D T Ef : ℕ → ℝ) (a p : ℕ → ℕ → ℝ)
    (w y x : PeriodicLatticeSite L) :
    pathAngG s (shapeFld t D T Ef a p) w (coarseGammaPath s y x) =
      t * sgnNat (w 1).val *
        ((∑ j ∈ Finset.range (((x 1 - (Function.update y 2 (x 2)) 1).val) / s),
            pmN j * (T (w 0).val + Ef (w 0).val * p (((w 1).val + s * j) % (L 1 + 1)) (((w 2).val + s * (((x 2 - y 2).val) / s)) % (L 2 + 1)))) +
         pmN (((x 1 - (Function.update y 2 (x 2)) 1).val) / s) *
          ((∑ i ∈ Finset.range (((x 0 - (Function.update (Function.update y 2 (x 2)) 1 (x 1)) 0).val) / s),
              D (((w 0).val + s * i) % (L 0 + 1))) *
            a (((w 1).val + s * (((x 1 - (Function.update y 2 (x 2)) 1).val) / s)) % (L 1 + 1))
              (((w 2).val + s * (((x 2 - y 2).val) / s)) % (L 2 + 1)))) := by
  unfold shapeFld
  rw [pathAngG_fld_gamma]
  rw [mul_add]
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [sgn_shift (L 1 + 1) hN s (w 1).val j hs]
    ring
  · rw [sgn_shift (L 1 + 1) hN s (w 1).val _ hs, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring

theorem cPlusS_val (s ell : ℕ) (y : PeriodicLatticeSite L) (μ ν : Fin 3) :
    ((cPlusS s ell (y, μ)) ν).val = if ν = μ then ((y μ).val + s * ell) % (L μ + 1) else (y ν).val := by
  rw [cPlusS_eq]
  by_cases h : ν = μ
  · subst h; simp [coarseShift_val_eq]
  · rw [coarseShift_apply_ne y (s * ell) μ ν h]; simp [h]

/-- the staircase-loop angle of a shape field, direction `2` (raw form: two staircases, the second based at `y + s·ell·e₂`). -/
theorem loop_shape_dir2 (hN : 2 ∣ L 1 + 1) (s ell : ℕ) (hs : s % 2 = 1) (t : ℝ) (D T Ef : ℕ → ℝ) (a p : ℕ → ℕ → ℝ)
    (y x : PeriodicLatticeSite L) :
    loopAngG s ell (shapeFld t D T Ef a p) y 2 x =
      t * sgnNat (y 1).val *
        ((∑ j ∈ Finset.range (((x 1 - (Function.update y 2 (x 2)) 1).val) / s),
            pmN j * (T (y 0).val + Ef (y 0).val * p (((y 1).val + s * j) % (L 1 + 1)) (((y 2).val + s * (((x 2 - y 2).val) / s)) % (L 2 + 1)))) +
         pmN (((x 1 - (Function.update y 2 (x 2)) 1).val) / s) *
          ((∑ i ∈ Finset.range (((x 0 - (Function.update (Function.update y 2 (x 2)) 1 (x 1)) 0).val) / s),
              D (((y 0).val + s * i) % (L 0 + 1))) *
            a (((y 1).val + s * (((x 1 - (Function.update y 2 (x 2)) 1).val) / s)) % (L 1 + 1))
              (((y 2).val + s * (((x 2 - y 2).val) / s)) % (L 2 + 1)))) -
      t * sgnNat (y 1).val *
        ((∑ j ∈ Finset.range (((x 1 - (Function.update y 2 (x 2)) 1).val) / s),
            pmN j * (T (y 0).val + Ef (y 0).val * p (((y 1).val + s * j) % (L 1 + 1))
              ((((y 2).val + s * ell) % (L 2 + 1) + s * (((x 2 - y 2).val) / s)) % (L 2 + 1)))) +
         pmN (((x 1 - (Function.update y 2 (x 2)) 1).val) / s) *
          ((∑ i ∈ Finset.range (((x 0 - (Function.update (Function.update y 2 (x 2)) 1 (x 1)) 0).val) / s),
              D (((y 0).val + s * i) % (L 0 + 1))) *
            a (((y 1).val + s * (((x 1 - (Function.update y 2 (x 2)) 1).val) / s)) % (L 1 + 1))
              ((((y 2).val + s * ell) % (L 2 + 1) + s * (((x 2 - y 2).val) / s)) % (L 2 + 1)))) := by
  unfold loopAngG
  rw [gamma_shape hN s hs, gamma_shape hN s hs, seg2_shape, seg2_shape]
  simp only [cPlusS_val, if_neg (show ¬ ((0 : Fin 3) = 2) by decide), if_neg (show ¬ ((1 : Fin 3) = 2) by decide), if_true]
  ring

/-- direction `0` (raw form). -/
theorem loop_shape_dir0 (hN : 2 ∣ L 1 + 1) (s ell : ℕ) (hs : s % 2 = 1) (t : ℝ) (D T Ef : ℕ → ℝ) (a p : ℕ → ℕ → ℝ)
    (y x : PeriodicLatticeSite L) :
    loopAngG s ell (shapeFld t D T Ef a p) y 0 x =
      t * sgnNat (y 1).val *
        ((∑ j ∈ Finset.range (((x 1 - (Function.update y 2 (x 2)) 1).val) / s),
            pmN j * (T (y 0).val + Ef (y 0).val * p (((y 1).val + s * j) % (L 1 + 1)) (((y 2).val + s * (((x 2 - y 2).val) / s)) % (L 2 + 1)))) +
         pmN (((x 1 - (Function.update y 2 (x 2)) 1).val) / s) *
          ((∑ i ∈ Finset.range (((x 0 - (Function.update (Function.update y 2 (x 2)) 1 (x 1)) 0).val) / s),
              D (((y 0).val + s * i) % (L 0 + 1))) *
            a (((y 1).val + s * (((x 1 - (Function.update y 2 (x 2)) 1).val) / s)) % (L 1 + 1))
              (((y 2).val + s * (((x 2 - y 2).val) / s)) % (L 2 + 1)))) +
      t * sgnNat (x 1).val * ((∑ j ∈ Finset.range ell, D (((x 0).val + s * j) % (L 0 + 1))) * a (x 1).val (x 2).val) -
      t * sgnNat (y 1).val *
        ((∑ j ∈ Finset.range (((x 1 - (Function.update y 2 (x 2)) 1).val) / s),
            pmN j * (T (((y 0).val + s * ell) % (L 0 + 1)) + Ef (((y 0).val + s * ell) % (L 0 + 1)) *
              p (((y 1).val + s * j) % (L 1 + 1)) (((y 2).val + s * (((x 2 - y 2).val) / s)) % (L 2 + 1)))) +
         pmN (((x 1 - (Function.update y 2 (x 2)) 1).val) / s) *
          ((∑ i ∈ Finset.range (((x 0 - (Function.update (Function.update y 2 (x 2)) 1 (x 1)) 0).val) / s),
              D (((((y 0).val + s * ell) % (L 0 + 1)) + s * i) % (L 0 + 1))) *
            a (((y 1).val + s * (((x 1 - (Function.update y 2 (x 2)) 1).val) / s)) % (L 1 + 1))
              (((y 2).val + s * (((x 2 - y 2).val) / s)) % (L 2 + 1)))) -
      t * sgnNat (y 1).val * ((∑ j ∈ Finset.range ell, D (((y 0).val + s * j) % (L 0 + 1))) * a (y 1).val (y 2).val) := by
  unfold loopAngG
  rw [gamma_shape hN s hs, gamma_shape hN s hs, seg0_shape hN, seg0_shape hN]
  simp only [cPlusS_val, if_true, if_neg (show ¬ ((1 : Fin 3) = 0) by decide), if_neg (show ¬ ((2 : Fin 3) = 0) by decide)]

/-- direction `1` (raw form; the shifted staircase is based at `(y₀, y₁ + s·ell, y₂)`). -/
theorem loop_shape_dir1 (hN : 2 ∣ L 1 + 1) (s ell : ℕ) (hs : s % 2 = 1) (t : ℝ) (D T Ef : ℕ → ℝ) (a p : ℕ → ℕ → ℝ)
    (y x : PeriodicLatticeSite L) :
    loopAngG s ell (shapeFld t D T Ef a p) y 1 x =
      t * sgnNat (y 1).val *
        ((∑ j ∈ Finset.range (((x 1 - (Function.update y 2 (x 2)) 1).val) / s),
            pmN j * (T (y 0).val + Ef (y 0).val * p (((y 1).val + s * j) % (L 1 + 1)) (((y 2).val + s * (((x 2 - y 2).val) / s)) % (L 2 + 1)))) +
         pmN (((x 1 - (Function.update y 2 (x 2)) 1).val) / s) *
          ((∑ i ∈ Finset.range (((x 0 - (Function.update (Function.update y 2 (x 2)) 1 (x 1)) 0).val) / s),
              D (((y 0).val + s * i) % (L 0 + 1))) *
            a (((y 1).val + s * (((x 1 - (Function.update y 2 (x 2)) 1).val) / s)) % (L 1 + 1))
              (((y 2).val + s * (((x 2 - y 2).val) / s)) % (L 2 + 1)))) +
      t * sgnNat (x 1).val * (∑ j ∈ Finset.range ell, pmN j * (T (x 0).val + Ef (x 0).val * p (((x 1).val + s * j) % (L 1 + 1)) (x 2).val)) -
      t * sgnNat (((y 1).val + s * ell) % (L 1 + 1)) *
        ((∑ j ∈ Finset.range (((x 1 - (Function.update y 2 (x 2)) 1).val) / s),
            pmN j * (T (y 0).val + Ef (y 0).val * p ((((y 1).val + s * ell) % (L 1 + 1) + s * j) % (L 1 + 1))
              (((y 2).val + s * (((x 2 - y 2).val) / s)) % (L 2 + 1)))) +
         pmN (((x 1 - (Function.update y 2 (x 2)) 1).val) / s) *
          ((∑ i ∈ Finset.range (((x 0 - (Function.update (Function.update y 2 (x 2)) 1 (x 1)) 0).val) / s),
              D (((y 0).val + s * i) % (L 0 + 1))) *
            a ((((y 1).val + s * ell) % (L 1 + 1) + s * (((x 1 - (Function.update y 2 (x 2)) 1).val) / s)) % (L 1 + 1))
              (((y 2).val + s * (((x 2 - y 2).val) / s)) % (L 2 + 1)))) -
      t * sgnNat (y 1).val * (∑ j ∈ Finset.range ell, pmN j * (T (y 0).val + Ef (y 0).val * p (((y 1).val + s * j) % (L 1 + 1)) (y 2).val)) := by
  unfold loopAngG
  rw [gamma_shape hN s hs, gamma_shape hN s hs, seg1_shape hN s ell hs, seg1_shape hN s ell hs]
  simp only [cPlusS_val, if_true, if_neg (show ¬ ((0 : Fin 3) = 1) by decide), if_neg (show ¬ ((2 : Fin 3) = 1) by decide)]

end AdalyFormal.CoverOmega
