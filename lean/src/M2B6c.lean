import M2B6b

/-!
# M2B6c -- the Leibniz estimate for `ddA` of the cut-off field (m2_bridge_20261014, Layer B1)

For a cube field `A` (`CubeData`: the three printed clauses on `CubeBond sites`, scale `X = (ell^i η)⁻¹`, `K = f M α₀`) and a cutoff `χ` (`CutSpec`),
at a point `x` where the `4`-ball lies in the cube:
`ddA η (cutA χ A) x μ = χ x • ddA η A x μ + η⁻¹ • Σ_ν η⁻¹ • Rv χ A x μ ν`   (`ddA_cut_decomp`)
`‖Rv‖ ≤ 8 τ1 (η K X²) + (τ2 + τ1²) K X`                                     (`Rv_bound`).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.M2Bridge

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (pdist_comm pdist_shift_le pdist_triangle)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack)

variable {L : PeriodicLatticeExtent}

/-- the class data of one cube, as `PerCubeRegular2` delivers it (index `i`, scale `X = (ell^i η)⁻¹`). -/
structure CubeData (ell M f k : ℕ) (α₀ η : ℝ) (sites : Set (PeriodicLatticeSite L)) (i : ℕ) (A : Bond L → M2m) : Prop where
  ht : ∀ e : Bond L, CubeBond sites e → HT (A e)
  c1 : ∀ e : Bond L, CubeBond sites e → frobNorm (A e) < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ i * η)⁻¹ ^ 1)
  c2 : ∀ (μ ν : Fin 3) (x : PeriodicLatticeSite L), CubeBond sites ((x, ν) : Bond L) →
      CubeBond sites ((periodicLatticeShift x μ, ν) : Bond L) →
      frobNorm ((η⁻¹ : ℝ) • (A (periodicLatticeShift x μ, ν) - A (x, ν))) < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ i * η)⁻¹ ^ 2)
  c3 : ∀ (μ : Fin 3) (x : PeriodicLatticeSite L),
      (∀ ν : Fin 3, ν ≠ μ → CurlReads sites (periodicLatticeShiftBack x ν) ν μ ∧ CurlReads sites x ν μ) →
      frobNorm (ddA η A x μ) < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ i * η)⁻¹ ^ 3)

/-- the Leibniz remainder at `(x, μ, ν)` -/
noncomputable def Rv (χ : PeriodicLatticeSite L → ℝ) (A : Bond L → M2m) (x : PeriodicLatticeSite L) (μ ν : Fin 3) : M2m :=
  (-(χ (periodicLatticeShift x ν) - χ x)) • (A (periodicLatticeShift x ν, μ) - A (x, μ))
  - (χ (periodicLatticeShiftBack x ν) - χ x) • (A (periodicLatticeShiftBack x ν, μ) - A (x, μ))
  + (χ (periodicLatticeShift x μ) - χ x) • (A (periodicLatticeShift x μ, ν) - A (x, ν))
  - (χ (periodicLatticeShift (periodicLatticeShiftBack x ν) μ) - χ x)
      • (A (periodicLatticeShift (periodicLatticeShiftBack x ν) μ, ν) - A (x, ν))
  + (χ (periodicLatticeShiftBack x ν) - χ x) • (A (periodicLatticeShiftBack x ν, ν) - A (x, ν))
  - ((χ (periodicLatticeShift x ν) - χ x) + (χ (periodicLatticeShiftBack x ν) - χ x)) • A (x, μ)
  + (((χ (periodicLatticeShift x μ) - χ x) - (χ (periodicLatticeShift (periodicLatticeShiftBack x ν) μ) - χ x))
      + (χ (periodicLatticeShiftBack x ν) - χ x)) • A (x, ν)

theorem ddTerm_cut (η : ℝ) (χ : PeriodicLatticeSite L → ℝ) (A : Bond L → M2m) (x : PeriodicLatticeSite L) (μ ν : Fin 3) :
    (curlA η (cutA χ A) (periodicLatticeShiftBack x ν) ν μ - curlA η (cutA χ A) x ν μ)
      - χ x • (curlA η A (periodicLatticeShiftBack x ν) ν μ - curlA η A x ν μ)
    = (η⁻¹ : ℝ) • Rv χ A x μ ν := by
  rw [ddTerm_eq, ddTerm_eq]
  have h := Rid (χ x) (χ (periodicLatticeShift x ν)) (χ (periodicLatticeShiftBack x ν)) (χ (periodicLatticeShift x μ))
    (χ (periodicLatticeShift (periodicLatticeShiftBack x ν) μ)) (A (x, μ)) (A (periodicLatticeShift x ν, μ))
    (A (periodicLatticeShiftBack x ν, μ)) (A (periodicLatticeShift x μ, ν)) (A (x, ν))
    (A (periodicLatticeShift (periodicLatticeShiftBack x ν) μ, ν)) (A (periodicLatticeShiftBack x ν, ν))
  unfold Rv
  rw [← h]
  dsimp only [cutA]
  module

theorem ddA_cut_decomp (η : ℝ) (χ : PeriodicLatticeSite L → ℝ) (A : Bond L → M2m) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    ddA η (cutA χ A) x μ = χ x • ddA η A x μ
      + (η⁻¹ : ℝ) • ∑ ν ∈ Finset.univ.filter (fun ν : Fin 3 => ν ≠ μ), (η⁻¹ : ℝ) • Rv χ A x μ ν := by
  rw [ddA_def, ddA_def]
  have hsum : ∑ ν ∈ Finset.univ.filter (fun ν : Fin 3 => ν ≠ μ),
        (curlA η (cutA χ A) (periodicLatticeShiftBack x ν) ν μ - curlA η (cutA χ A) x ν μ)
      = ∑ ν ∈ Finset.univ.filter (fun ν : Fin 3 => ν ≠ μ),
        (χ x • (curlA η A (periodicLatticeShiftBack x ν) ν μ - curlA η A x ν μ) + (η⁻¹ : ℝ) • Rv χ A x μ ν) := by
    apply Finset.sum_congr rfl
    intro ν _
    exact sub_eq_iff_eq_add'.mp (ddTerm_cut η χ A x μ ν)
  rw [hsum, Finset.sum_add_distrib, ← Finset.smul_sum, smul_add, smul_comm (η⁻¹ : ℝ) (χ x)]

theorem term_le {c : ℝ} {m : M2m} {s B : ℝ} (hc : |c| ≤ s) (hm : frobNorm m ≤ B) :
    frobNorm (c • m) ≤ s * B := by
  rw [frob_smul]
  exact mul_le_mul hc hm (AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _) (le_trans (abs_nonneg _) hc)

theorem frob7 (u1 u2 u3 u4 u5 u6 u7 : M2m) :
    frobNorm (u1 - u2 + u3 - u4 + u5 - u6 + u7)
      ≤ frobNorm u1 + frobNorm u2 + frobNorm u3 + frobNorm u4 + frobNorm u5 + frobNorm u6 + frobNorm u7 := by
  have a1 := frob_add_le (u1 - u2 + u3 - u4 + u5 - u6) u7
  have a2 := frob_sub_le (u1 - u2 + u3 - u4 + u5) u6
  have a3 := frob_add_le (u1 - u2 + u3 - u4) u5
  have a4 := frob_sub_le (u1 - u2 + u3) u4
  have a5 := frob_add_le (u1 - u2) u3
  have a6 := frob_sub_le u1 u2
  linarith

section bound

variable {ell M f k i : ℕ} {α₀ η : ℝ} {sites : Set (PeriodicLatticeSite L)} {A : Bond L → M2m}
  {χ : PeriodicLatticeSite L → ℝ} {τ1 τ2 : ℝ}

theorem Rv_bound (hd : CubeData ell M f k α₀ η sites i A) (hc : CutSpec sites χ τ1 τ2) (hη : 0 < η)
    {x : PeriodicLatticeSite L} (hx4 : ∀ y, pdist x y ≤ 4 → y ∈ sites) {μ ν : Fin 3} (hne : ν ≠ μ) :
    frobNorm (Rv χ A x μ ν)
      ≤ 8 * τ1 * (η * ((f : ℝ) * M * α₀ * (((ell : ℝ) ^ i * η)⁻¹ ^ 2)))
        + (τ2 + τ1 ^ 2) * ((f : ℝ) * M * α₀ * (((ell : ℝ) ^ i * η)⁻¹ ^ 1)) := by
  set D : ℝ := η * ((f : ℝ) * M * α₀ * (((ell : ℝ) ^ i * η)⁻¹ ^ 2)) with hD
  set C : ℝ := (f : ℝ) * M * α₀ * (((ell : ℝ) ^ i * η)⁻¹ ^ 1) with hC
  have τ1nn : 0 ≤ τ1 := le_trans (abs_nonneg _) (hc.fwd x μ)
  have dPp : pdist x (periodicLatticeShift x ν) ≤ 1 := pdist_shift_le x ν
  have dPm : pdist x (periodicLatticeShiftBack x ν) ≤ 1 := pdist_shiftBack_le x ν
  have dPq : pdist x (periodicLatticeShift x μ) ≤ 1 := pdist_shift_le x μ
  have dPr : pdist x (periodicLatticeShift (periodicLatticeShiftBack x ν) μ) ≤ 2 := by
    have h1 := pdist_triangle x (periodicLatticeShiftBack x ν) (periodicLatticeShift (periodicLatticeShiftBack x ν) μ)
    have h2 := pdist_shift_le (periodicLatticeShiftBack x ν) μ
    omega
  have d0 : pdist x x ≤ 3 := by rw [pdist_self']; norm_num
  have cb : ∀ (y : PeriodicLatticeSite L) (c : Fin 3), pdist x y ≤ 3 → CubeBond sites ((y, c) : Bond L) :=
    fun y c hy => cubeBond_of_near hx4 (e := (y, c)) hy
  -- forward differences of A
  have hD1 : ∀ (y : PeriodicLatticeSite L) (a b : Fin 3), pdist x y ≤ 2 →
      frobNorm (A (periodicLatticeShift y a, b) - A (y, b)) ≤ D := by
    intro y a b hy
    have hsy : pdist x (periodicLatticeShift y a) ≤ 3 := by
      have h1 := pdist_triangle x y (periodicLatticeShift y a)
      have h2 := pdist_shift_le y a
      omega
    have := hd.c2 a b y (cb y b (by omega)) (cb _ b hsy)
    exact frob_scaled hη this.le
  have dMm : pdist x (periodicLatticeShiftBack x ν) ≤ 2 := by omega
  -- the five differences
  have eP : frobNorm (A (periodicLatticeShift x ν, μ) - A (x, μ)) ≤ D := hD1 x ν μ (by rw [pdist_self']; norm_num)
  have eM : frobNorm (A (periodicLatticeShiftBack x ν, μ) - A (x, μ)) ≤ D := by
    have := hD1 (periodicLatticeShiftBack x ν) ν μ dMm
    rw [periodicLatticeShift_shiftBack] at this
    rw [show A (periodicLatticeShiftBack x ν, μ) - A (x, μ) = -(A (x, μ) - A (periodicLatticeShiftBack x ν, μ)) by abel, frob_neg]
    exact this
  have eQ : frobNorm (A (periodicLatticeShift x μ, ν) - A (x, ν)) ≤ D := hD1 x μ ν (by rw [pdist_self']; norm_num)
  have eR : frobNorm (A (periodicLatticeShift (periodicLatticeShiftBack x ν) μ, ν) - A (periodicLatticeShiftBack x ν, ν)) ≤ D :=
    hD1 (periodicLatticeShiftBack x ν) μ ν dMm
  have eN : frobNorm (A (x, ν) - A (periodicLatticeShiftBack x ν, ν)) ≤ D := by
    have := hD1 (periodicLatticeShiftBack x ν) ν ν dMm
    rw [periodicLatticeShift_shiftBack] at this
    exact this
  have eN' : frobNorm (A (periodicLatticeShiftBack x ν, ν) - A (x, ν)) ≤ D := by
    rw [show A (periodicLatticeShiftBack x ν, ν) - A (x, ν) = -(A (x, ν) - A (periodicLatticeShiftBack x ν, ν)) by abel, frob_neg]
    exact eN
  have eRb : frobNorm (A (periodicLatticeShift (periodicLatticeShiftBack x ν) μ, ν) - A (x, ν)) ≤ D + D := by
    have := frob_add_le (A (periodicLatticeShift (periodicLatticeShiftBack x ν) μ, ν) - A (periodicLatticeShiftBack x ν, ν))
      (A (periodicLatticeShiftBack x ν, ν) - A (x, ν))
    rw [show A (periodicLatticeShift (periodicLatticeShiftBack x ν) μ, ν) - A (periodicLatticeShiftBack x ν, ν)
        + (A (periodicLatticeShiftBack x ν, ν) - A (x, ν))
        = A (periodicLatticeShift (periodicLatticeShiftBack x ν) μ, ν) - A (x, ν) by abel] at this
    linarith
  -- sizes of A at the base bonds
  have a0 : frobNorm (A (x, μ)) ≤ C := (hd.c1 (x, μ) (cb x μ d0)).le
  have b0 : frobNorm (A (x, ν)) ≤ C := (hd.c1 (x, ν) (cb x ν d0)).le
  -- cutoff differences
  have p1 : |χ (periodicLatticeShift x ν) - χ x| ≤ τ1 := hc.fwd x ν
  have m1 : |χ (periodicLatticeShiftBack x ν) - χ x| ≤ τ1 := hc.bwd x ν
  have q1 : |χ (periodicLatticeShift x μ) - χ x| ≤ τ1 := hc.fwd x μ
  have r1 : |χ (periodicLatticeShift (periodicLatticeShiftBack x ν) μ) - χ x| ≤ 2 * τ1 := by
    have h := hc.fwd (periodicLatticeShiftBack x ν) μ
    have e : χ (periodicLatticeShift (periodicLatticeShiftBack x ν) μ) - χ x
        = (χ (periodicLatticeShift (periodicLatticeShiftBack x ν) μ) - χ (periodicLatticeShiftBack x ν))
          + (χ (periodicLatticeShiftBack x ν) - χ x) := by ring
    rw [e]
    calc _ ≤ |χ (periodicLatticeShift (periodicLatticeShiftBack x ν) μ) - χ (periodicLatticeShiftBack x ν)|
          + |χ (periodicLatticeShiftBack x ν) - χ x| := abs_add_le _ _
      _ ≤ 2 * τ1 := by linarith
  have s2 : |(χ (periodicLatticeShift x ν) - χ x) + (χ (periodicLatticeShiftBack x ν) - χ x)| ≤ τ2 := by
    have := hc.sec x ν
    rwa [show (χ (periodicLatticeShift x ν) - χ x) + (χ (periodicLatticeShiftBack x ν) - χ x)
        = χ (periodicLatticeShift x ν) + χ (periodicLatticeShiftBack x ν) - 2 * χ x by ring]
  have s3 : |((χ (periodicLatticeShift x μ) - χ x) - (χ (periodicLatticeShift (periodicLatticeShiftBack x ν) μ) - χ x))
      + (χ (periodicLatticeShiftBack x ν) - χ x)| ≤ τ1 ^ 2 := by
    have := hc.mixed x μ ν hne
    rwa [show ((χ (periodicLatticeShift x μ) - χ x) - (χ (periodicLatticeShift (periodicLatticeShiftBack x ν) μ) - χ x))
        + (χ (periodicLatticeShiftBack x ν) - χ x)
        = (χ (periodicLatticeShift x μ) - χ x)
          - (χ (periodicLatticeShift (periodicLatticeShiftBack x ν) μ) - χ (periodicLatticeShiftBack x ν)) by ring]
  have p1' : |-(χ (periodicLatticeShift x ν) - χ x)| ≤ τ1 := by rwa [abs_neg]
  unfold Rv
  refine le_trans (frob7 _ _ _ _ _ _ _) ?_
  have t1 := term_le p1' eP
  have t2 := term_le m1 eM
  have t3 := term_le q1 eQ
  have t4 := term_le r1 eRb
  have t5 := term_le m1 eN'
  have t6 := term_le s2 a0
  have t7 := term_le s3 b0
  nlinarith [t1, t2, t3, t4, t5, t6, t7]

end bound

end AdalyFormal.M2Bridge

#print axioms AdalyFormal.M2Bridge.ddTerm_cut
#print axioms AdalyFormal.M2Bridge.ddA_cut_decomp
#print axioms AdalyFormal.M2Bridge.Rv_bound
