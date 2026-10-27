import THL3
import THL6
import THL5

/-!
# THL8 -- a curved NON-RADIAL thin-layer witness (lane thin_layer_20261019)

The slab tower of lane nonvac_c_20261017 with DIFFERENT layer widths on the two sides: `Omega_0 = [P1 - R M, Q1 + Rb M)` (left layer `R M`, right layer `Rb M`, `1 <= R < Rb <= T`),
`Omega_1 = [P1, Q1)`, `Omega_2 = [P2, Q2)` (`k = 2`).  It satisfies
* `AdmSplitNB ell M R (fun _ => Rb) 2 S` (level-0 collar `R`, level-`>= 1` collar `Rb`; no base law);
* `∀ R0 Rs, ¬ AdmSplit ell M R0 Rs 2 S` (no radius makes the layer radial: the layer is not an `R0 M`-neighbourhood of `Omega_1` for any `R0`);
* `LambdaOK2 ell M Rb 2 S Lam`; a curved non-pure-gauge `U` in `ClassCoupled ell M c 2 S alpha_0 (ell^2)^-1 U`; all three strata non-empty; a nonzero `B~`.
`SlabGeoW`, `cube_nbhdW`, `slab3_coverspW` are the lemmas `SlabGeo`, `cube_nbhd`, `slab3_coversp` of NVC1/NVC4/NVC5 with the structure `SlabGeoW` (the arithmetic facts of
the coverage proof, WITHOUT the base-law equations `c0P, c0Q`); the proofs are copied.  `ThinScan.AdalyFormal.M1.perCube_of_M1` (the replayed bridge, THL5) supplies the
per-cube regularity on an `AdmT` tower.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 64000000

namespace AdalyFormal.NonVacC

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.ThinLayer (AdmSplitNB)

/-- the arithmetic facts of the coverage proof and of the collars, without the base-law equations. -/
structure SlabGeoW (M ell N P0 Q0 P1 Q1 P2 Q2 : ℕ) : Prop where
  hM : 0 < M
  hell : 0 < ell
  nest01 : P0 ≤ P1
  nest12 : P1 ≤ P2
  nestw : P2 < Q2
  nest21 : Q2 ≤ Q1
  nest10 : Q1 ≤ Q0
  QN : Q0 ≤ N
  d0 : M ∣ N
  d1 : M * ell ∣ N
  d2 : M * ell ^ 2 ∣ N
  b0P : M ∣ P0
  b0Q : M ∣ Q0
  b1P : M * ell ∣ P1
  b1Q : M * ell ∣ Q1
  b2P : M * ell ^ 2 ∣ P2
  b2Q : M * ell ^ 2 ∣ Q2

theorem slab3_nest_W {L : PeriodicLatticeExtent} {M ell N P0 Q0 P1 Q1 P2 Q2 : ℕ} (G : SlabGeoW M ell N P0 Q0 P1 Q1 P2 Q2) :
    ∀ j, (slab3 L P0 Q0 P1 Q1 P2 Q2).Om (j + 1) ⊆ (slab3 L P0 Q0 P1 Q1 P2 Q2).Om j := by
  intro j x hx
  rcases Nat.lt_or_ge j 2 with hj | hj
  · have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · rw [om1_mem] at hx; rw [om0_mem]; have := G.nest01; have := G.nest10; omega
    · rw [om2_mem] at hx; rw [om1_mem]; have := G.nest12; have := G.nest21; omega
  · exact absurd hx (om3_mem (j + 1) (by omega) x)

section cov
variable {c M ell N P0 Q0 P1 Q1 P2 Q2 : ℕ}

theorem cube_nbhdW (hc : 2 ≤ c) (G : SlabGeoW M ell N P0 Q0 P1 Q1 P2 Q2)
    (w0L : P0 + c * M ≤ P2) (w0R : Q2 + c * M ≤ Q0) (w1 : P1 + c * (M * ell) ≤ Q1)
    (w2 : P2 + c * (M * ell ^ 2) ≤ Q2) (hQN : Q0 < N) (hP12 : P1 < P2) (hQ21 : Q2 < Q1) (hQ10 : Q1 < Q0)
    {L : PeriodicLatticeExtent} (hN : ∀ μ, L μ + 1 = N) (x : PeriodicLatticeSite L)
    (hx : P0 ≤ (x 0).val ∧ (x 0).val < Q0) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube ell M c 2 (slab3 L P0 Q0 P1 Q1 P2 Q2) sites j ∧
      ∀ y : PeriodicLatticeSite L, Adj N x y → P0 ≤ (y 0).val → (y 0).val < Q0 → y ∈ sites := by
  have hnest : ∀ j, (slab3 L P0 Q0 P1 Q1 P2 Q2).Om (j + 1) ⊆ (slab3 L P0 Q0 P1 Q1 P2 Q2).Om j :=
    slab3_nest_W G
  have hM := G.hM
  have hell := G.hell
  have hs0 : bigSide M ell 0 = M := by simp [bigSide]
  have hs1 : bigSide M ell 1 = M * ell := by simp [bigSide]
  have hs2 : bigSide M ell 2 = M * ell ^ 2 := by simp [bigSide]
  have hp1 : 0 < M * ell := Nat.mul_pos hM hell
  have hp2 : 0 < M * ell ^ 2 := Nat.mul_pos hM (pow_pos hell 2)
  have hM2 : M ∣ P2 := Dvd.dvd.trans (Dvd.intro _ rfl) G.b2P
  have hM2' : M ∣ Q2 := Dvd.dvd.trans (Dvd.intro _ rfl) G.b2Q
  have hv := hx
  have hx1 : (x 0).val + 1 < N := by omega
  have hQ2N : Q2 ≤ N := by have := G.nest21; have := G.nest10; have := G.QN; omega
  have hQ1N : Q1 ≤ N := by have := G.nest10; have := G.QN; omega
  have hP2N : P2 ≤ N := by have := G.nestw; omega
  by_cases hA : (x 0).val < P1
  · -- index 0, left shell, region [P0, P2)
    obtain ⟨sites, hc, hall⟩ := cube_of_region hc (ell := ell) (M := M) (j := 0) hN hnest (by norm_num) (lo := P0) (hi := P2)
      (by rw [hs0]; exact hM) (by rw [hs0]; exact G.b0P) (by rw [hs0]; exact hM2) (by rw [hs0]; exact w0L) hP2N
      x ((x 0).val + 1) hx.1 (by omega) le_rfl (by omega) hx1
      (by
        intro y h1 h2
        by_cases h3 : (y 0).val < P1
        · left; rw [bj0]; omega
        · right; rw [bj1]; omega)
      ⟨(x 0).val, Or.inl rfl, by omega, by intro y hy; rw [bj0]; omega⟩
    refine ⟨sites, 0, hc, fun y hy h1 h2 => hall y hy ?_⟩
    rcases adj0 hy hx1 with h | h <;> omega
  · by_cases hB : (x 0).val < P2
    · -- index 1, region [P1, Q1)
      obtain ⟨sites, hc, hall⟩ := cube_of_region hc (ell := ell) (M := M) (j := 1) hN hnest (by norm_num) (lo := P1) (hi := Q1)
        (by rw [hs1]; exact hp1) (by rw [hs1]; exact G.b1P) (by rw [hs1]; exact G.b1Q) (by rw [hs1]; exact w1) hQ1N
        x ((x 0).val + 1) (by omega) (by omega) le_rfl (by omega) hx1
        (by
          intro y h1 h2
          by_cases h3 : P2 ≤ (y 0).val ∧ (y 0).val < Q2
          · right; rw [bj2]; exact h3
          · left; rw [bj1]; omega)
        ⟨(x 0).val, Or.inl rfl, by omega, by intro y hy; rw [bj1]; omega⟩
      refine ⟨sites, 1, hc, fun y hy h1 h2 => hall y hy ?_⟩
      rcases adj0 hy hx1 with h | h <;> omega
    · by_cases hC : (x 0).val + 1 < Q2
      · -- index 2, region [P2, Q2)
        obtain ⟨sites, hc, hall⟩ := cube_of_region hc (ell := ell) (M := M) (j := 2) hN hnest (by norm_num) (lo := P2) (hi := Q2)
          (by rw [hs2]; exact hp2) (by rw [hs2]; exact G.b2P) (by rw [hs2]; exact G.b2Q) (by rw [hs2]; exact w2) hQ2N
          x ((x 0).val + 1) (by omega) (by omega) le_rfl (by omega) hx1
          (by
            intro y h1 h2
            left; rw [bj2]; omega)
          ⟨(x 0).val, Or.inl rfl, by omega, by intro y hy; rw [bj2]; omega⟩
        refine ⟨sites, 2, hc, fun y hy h1 h2 => hall y hy ?_⟩
        rcases adj0 hy hx1 with h | h <;> omega
      · by_cases hD : (x 0).val + 1 < Q1
        · -- index 1 again, window straddling the top of Ω₂
          obtain ⟨sites, hc, hall⟩ := cube_of_region hc (ell := ell) (M := M) (j := 1) hN hnest (by norm_num) (lo := P1) (hi := Q1)
            (by rw [hs1]; exact hp1) (by rw [hs1]; exact G.b1P) (by rw [hs1]; exact G.b1Q) (by rw [hs1]; exact w1) hQ1N
            x ((x 0).val + 1) (by omega) (by omega) le_rfl (by omega) hx1
            (by
              intro y h1 h2
              by_cases h3 : P2 ≤ (y 0).val ∧ (y 0).val < Q2
              · right; rw [bj2]; exact h3
              · left; rw [bj1]; omega)
            ⟨(x 0).val + 1, Or.inr rfl, le_rfl, by intro y hy; rw [bj1]; omega⟩
          refine ⟨sites, 1, hc, fun y hy h1 h2 => hall y hy ?_⟩
          rcases adj0 hy hx1 with h | h <;> omega
        · -- index 0, right shell, region [Q2, Q0)
          obtain ⟨sites, hc, hall⟩ := cube_of_region hc (ell := ell) (M := M) (j := 0) hN hnest (by norm_num) (lo := Q2) (hi := Q0)
            (by rw [hs0]; exact hM) (by rw [hs0]; exact hM2') (by rw [hs0]; exact G.b0Q) (by rw [hs0]; exact w0R) G.QN
            x (min ((x 0).val + 1) (Q0 - 1)) (by omega) (by omega) (by omega) (by omega) hx1
            (by
              intro y h1 h2
              by_cases h3 : Q1 ≤ (y 0).val
              · left; rw [bj0]; omega
              · right; rw [bj1]; omega)
            ⟨if Q1 ≤ (x 0).val then (x 0).val else (x 0).val + 1, by split_ifs <;> simp, by split_ifs <;> omega,
              by intro y hy; rw [bj0]; split_ifs at hy <;> omega⟩
          refine ⟨sites, 0, hc, fun y hy h1 h2 => hall y hy ?_⟩
          rcases adj0 hy hx1 with h | h <;> omega


end cov

section
variable {c M ell N P0 Q0 P1 Q1 P2 Q2 : ℕ}

theorem slab3_coverspW (hc : 2 ≤ c) (G : SlabGeoW M ell N P0 Q0 P1 Q1 P2 Q2)
    (w0L : P0 + c * M ≤ P2) (w0R : Q2 + c * M ≤ Q0) (w1 : P1 + c * (M * ell) ≤ Q1)
    (w2 : P2 + c * (M * ell ^ 2) ≤ Q2) (hQN : Q0 < N) (hP12 : P1 < P2) (hQ21 : Q2 < Q1) (hQ10 : Q1 < Q0)
    {L : PeriodicLatticeExtent} (hN : ∀ μ, L μ + 1 = N) :
    CoversOm0p ell M c 2 (slab3 L P0 Q0 P1 Q1 P2 Q2) := by
  have hN1 : 1 < N := by
    have := G.nest21; have := G.nest10; have := G.nestw; omega
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [om0_mem] at hx
    obtain ⟨sites, j, hc, hall⟩ := cube_nbhdW hc G w0L w0R w1 w2 hQN hP12 hQ21 hQ10 hN x hx
    exact ⟨sites, j, hc, hall x (adj_refl N x) hx.1 hx.2⟩
  · intro p hp
    have hmu : p.2.1.1 ≠ p.2.1.2 := ne_of_lt p.2.2
    have hnu : p.2.1.2 ≠ p.2.1.1 := fun h => hmu h.symm
    have hmem : ∀ e : PeriodicLatticeEdge L, e ∈ periodicPlaquetteBoundaryEdges p ↔
        (e = (p.1, p.2.1.1) ∨ e = (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) ∨
          e = (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) ∨ e = (p.1, p.2.1.2)) := by
      intro e
      simp [periodicPlaquetteBoundaryEdges]
    have hx : P0 ≤ (p.1 0).val ∧ (p.1 0).val < Q0 := by
      have := (hp (p.1, p.2.1.1) ((hmem _).mpr (Or.inl rfl))).1
      rwa [om0_mem] at this
    obtain ⟨sites, j, hc, hall⟩ := cube_nbhdW hc G w0L w0R w1 w2 hQN hP12 hQ21 hQ10 hN p.1 hx
    refine ⟨sites, j, hc, fun e he => ?_⟩
    have hcb := hp e he
    obtain ⟨hcb1, hcb2⟩ := hcb
    rw [om0_mem] at hcb1 hcb2
    have a0 : Adj N p.1 p.1 := adj_refl N _
    have aμ : Adj N p.1 (periodicLatticeShift p.1 p.2.1.1) := adj_shift_N hN hN1 a0 _ rfl
    have aν : Adj N p.1 (periodicLatticeShift p.1 p.2.1.2) := adj_shift_N hN hN1 a0 _ rfl
    have aμν : Adj N p.1 (periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2) :=
      adj_shift_N hN hN1 aμ _ (adj_shift_coord_N hN hN1 _ hnu)
    have aνμ : Adj N p.1 (periodicLatticeShift (periodicLatticeShift p.1 p.2.1.2) p.2.1.1) :=
      adj_shift_N hN hN1 aν _ (adj_shift_coord_N hN hN1 _ hmu)
    refine ⟨?_, ?_⟩
    · rcases (hmem e).mp he with rfl | rfl | rfl | rfl
      · exact hall _ a0 hcb1.1 hcb1.2
      · exact hall _ aμ hcb1.1 hcb1.2
      · exact hall _ aν hcb1.1 hcb1.2
      · exact hall _ a0 hcb1.1 hcb1.2
    · rcases (hmem e).mp he with rfl | rfl | rfl | rfl
      · exact hall _ aμ hcb2.1 hcb2.2
      · exact hall _ aμν hcb2.1 hcb2.2
      · exact hall _ aνμ hcb2.1 hcb2.2
      · exact hall _ aν hcb2.1 hcb2.2

end

/-- `pdist` of two sites on the 0-axis is the circular distance of the coordinates. -/
theorem pdist_siteAt0 {ell M T : ℕ} (hell : 0 < ell) (hM : 0 < M) {v w : ℕ} (hv : v < nvcN ell M T) (hw : w < nvcN ell M T) :
    pdist (siteAt0 (T := T) hell hM v hv) (siteAt0 (T := T) hell hM w hw) = pcd (nvcN ell M T) v w := by
  have hN := scaleUp_nvc (ell := ell) (T := T) hell hM
  unfold pdist
  rw [Fin.sum_univ_three]
  have e0 : pcd (scaleUp ell 2 (nvcLu M T) 0 + 1) (siteAt0 (T := T) hell hM v hv 0).val (siteAt0 (T := T) hell hM w hw 0).val
      = pcd (nvcN ell M T) v w := by
    rw [siteAt0_val, siteAt0_val, hN 0]
  have e1 : pcd (scaleUp ell 2 (nvcLu M T) 1 + 1) (siteAt0 (T := T) hell hM v hv 1).val (siteAt0 (T := T) hell hM w hw 1).val = 0 := by
    have h1 : (siteAt0 (T := T) hell hM v hv 1).val = 0 := by simp [siteAt0]
    have h2 : (siteAt0 (T := T) hell hM w hw 1).val = 0 := by simp [siteAt0]
    rw [h1, h2]; exact pcd_self' _ _
  have e2 : pcd (scaleUp ell 2 (nvcLu M T) 2 + 1) (siteAt0 (T := T) hell hM v hv 2).val (siteAt0 (T := T) hell hM w hw 2).val = 0 := by
    have h1 : (siteAt0 (T := T) hell hM v hv 2).val = 0 := by simp [siteAt0]
    have h2 : (siteAt0 (T := T) hell hM w hw 2).val = 0 := by simp [siteAt0]
    rw [h1, h2]; exact pcd_self' _ _
  rw [e0, e1, e2]; simp

theorem pdist_ge0' {L : PeriodicLatticeExtent} (x y : PeriodicLatticeSite L) :
    pcd (L 0 + 1) (x 0).val (y 0).val ≤ pdist x y :=
  Finset.single_le_sum (f := fun μ : Fin 3 => pcd (L μ + 1) (x μ).val (y μ).val) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ 0)

theorem pdist_ge0N {L : PeriodicLatticeExtent} {N : ℕ} (hN : L 0 + 1 = N) (x y : PeriodicLatticeSite L) :
    pcd N (x 0).val (y 0).val ≤ pdist x y := by
  rw [← hN]; exact pdist_ge0' x y

/-- the asymmetric slab tower satisfies the tower hypotheses without base law: level-0 collar `R` (the smaller layer), levels `>= 1` collar `Rb`. -/
theorem asym_admSplitNB_slab {ell M R Rb T : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hdvd : ell ∣ M) (hR : 1 ≤ R) (hRb : R < Rb)
    (hRbT : Rb ≤ T) (hRT : R ≤ T) (hT : 1 ≤ T) {L : PeriodicLatticeExtent} (hN : ∀ μ, L μ + 1 = nvcN ell M T) :
    AdmSplitNB ell M R (fun _ => Rb) 2
      (slab3 L (nvcP0 ell M R T) (nvcQ0 ell M Rb T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T)) := by
  have G := slabGeo_inst hell hM hdvd hRT hT
  have Gb := slabGeo_inst (R := Rb) hell hM hdvd hRbT hT
  have hAdmA := slab3_admissible G hN
  have hAdmB := slab3_admissible Gb hN
  have GW : SlabGeoW M ell (nvcN ell M T) (nvcP0 ell M R T) (nvcQ0 ell M Rb T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T)
      (nvcQ2 ell M T) :=
    ⟨G.hM, G.hell, G.nest01, G.nest12, G.nestw, G.nest21, Gb.nest10, Gb.QN, G.d0, G.d1, G.d2, G.b0P, Gb.b0Q, G.b1P, G.b1Q, G.b2P, G.b2Q⟩
  have hQmono : nvcQ0 ell M R T ≤ nvcQ0 ell M Rb T := by
    simp only [nvcQ0]; exact Nat.add_le_add_left (Nat.mul_le_mul_right M hRb.le) _
  have hPmono : nvcP0 ell M Rb T ≤ nvcP0 ell M R T := by
    simp only [nvcP0]; exact Nat.mul_le_mul_left M (by omega)
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hAdmA
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hAdmB
  have hs0 : bigSide M ell 0 = M := by simp [bigSide]
  refine ⟨slab3_nest_W GW, ?_, a3, ?_, ?_, ?_⟩
  · intro j hj
    have h0 : j ≠ 0 := by omega
    have h1 : j ≠ 1 := by omega
    have h2 : j ≠ 2 := by omega
    ext x; simp [slab3, h0, h1, h2]
  · intro j hj
    have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases this with rfl | rfl | rfl
    · intro x hx y hy
      rw [hs0] at hy
      rw [om0_mem] at hx ⊢
      have h0 := hy 0
      exact iv_block G.hM G.b0P Gb.b0Q h0 hx
    · exact a4 1 hj
    · exact a4 2 hj
  · intro x hx y hy
    rw [om0_mem] at hx
    by_cases hl : (x 0).val < nvcP0 ell M R T
    · have hx' : x ∉ (slab3 L (nvcP0 ell M R T) (nvcQ0 ell M R T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T)).Om 0 := by
        rw [om0_mem]; omega
      exact a5 0 (Nat.zero_le _) x hx' y hy
    · have hx' : x ∉ (slab3 L (nvcP0 ell M Rb T) (nvcQ0 ell M Rb T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T)).Om 0 := by
        rw [om0_mem]; omega
      have := b5 0 (Nat.zero_le _) x hx' y hy
      exact lt_of_le_of_lt (Nat.mul_le_mul_right _ hRb.le) this
  · intro j hj1 hj2 x hx y hy
    have h0 : j ≠ 0 := by omega
    exact b5 j hj2 x (by simpa [slab3, h0] using hx) y (by
      have h1 : j + 1 ≠ 0 := by omega
      simpa [slab3, h1] using hy)

/-- the layer is not radial: no `R0`, no `Rs` makes the asymmetric slab an `AdmSplit` tower. -/
theorem asym_not_admSplit_slab {ell M R Rb T : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hdvd : ell ∣ M) (hR : 1 ≤ R) (hRb : R < Rb)
    (hRbT : Rb ≤ T) (hT : 1 ≤ T) {R0 : ℕ} {Rs : ℕ → ℕ}
    (hN : ∀ μ, scaleUp ell 2 (nvcLu M T) μ + 1 = nvcN ell M T) :
    ¬ AdalyFormal.ThinLayer.AdmSplit ell M R0 Rs 2
      (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M Rb T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T)) := by
  intro hA
  obtain ⟨-, -, -, -, -, -, h6⟩ := hA
  have hell0 : 0 < ell := by omega
  have hRT : R ≤ T := by omega
  have G := slabGeo_inst hell hM hdvd hRT hT
  have Gb := slabGeo_inst (R := Rb) hell hM hdvd hRbT hT
  obtain ⟨-, -, -, -, hQN, -, -, -⟩ := nvc_widths (c := 0) (R := Rb) hell hM (by omega) hRbT hT (by omega)
  have g1 := G.nest01; have g2 := G.nest12; have g3 := G.nestw; have g4 := G.nest21; have g5 := Gb.nest10
  have g6 := Gb.QN; have g7 := G.c0P; have g8 := Gb.c0Q; have g9 := Gb.c0D
  by_cases hcase : R0 < Rb
  · -- the last site of `Omega_0` forces `R0 >= Rb`
    have hvN : nvcQ0 ell M Rb T - 1 < nvcN ell M T := by omega
    set x := siteAt0 (T := T) hell0 hM (nvcQ0 ell M Rb T - 1) hvN with hx
    have hxv : (x 0).val = nvcQ0 ell M Rb T - 1 := siteAt0_val hell0 hM _ hvN
    have hxm : x ∈ (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M Rb T) (nvcP1 ell M T) (nvcQ1 ell M T)
        (nvcP2 ell M T) (nvcQ2 ell M T)).Om 0 := by
      rw [om0_mem, hxv]; omega
    obtain ⟨y, hy, z, hz, hd⟩ := (h6 x).1 hxm
    rw [om1_mem] at hy
    have hz0 : (z 0).val / M = (x 0).val / M := hz 0
    obtain ⟨q, hq⟩ := Gb.b0Q
    obtain ⟨s, rfl⟩ : ∃ s, q = s + 1 := ⟨q - 1, by
      have : 0 < nvcQ0 ell M Rb T := by omega
      rcases q with _ | q
      · simp at hq; omega
      · simp⟩
    have hq' : nvcQ0 ell M Rb T = M * s + M := by rw [hq]; ring
    have hms : M * s = s * M := Nat.mul_comm _ _
    have hdiv : (x 0).val / M = s := by
      rw [hxv]
      apply Nat.div_eq_of_lt_le
      · omega
      · rw [Nat.add_mul, one_mul]; omega
    have hzge : s * M ≤ (z 0).val := by
      have := Nat.div_mul_le_self (z 0).val M
      rw [hz0, hdiv] at this; exact this
    have hc := le_trans (pdist_ge0N (hN 0) z y) hd
    have hzl : (z 0).val < nvcN ell M T := by have := (z 0).isLt; have := hN 0; omega
    have hmul : (R0 + 1) * M ≤ Rb * M := Nat.mul_le_mul_right M hcase
    rw [Nat.add_mul, one_mul] at hmul
    have hBM : M ≤ Rb * M := Nat.le_mul_of_pos_left M (by omega)
    unfold pcd at hc
    split_ifs at hc <;> omega
  · -- the site just outside the left edge is in the radial neighbourhood of radius `R0 >= Rb > R`
    have hR0 : Rb ≤ R0 := by omega
    have hP0pos : 1 ≤ nvcP0 ell M R T := by
      have h4 : 4 ≤ ell ^ 2 := by nlinarith
      have h5 := Nat.mul_le_mul_right T h4
      simp only [nvcP0]
      exact Nat.mul_pos hM (by omega)
    have hvN : nvcP0 ell M R T - 1 < nvcN ell M T := by omega
    have hvP : nvcP1 ell M T < nvcN ell M T := by omega
    set x := siteAt0 (T := T) hell0 hM (nvcP0 ell M R T - 1) hvN with hx
    set y := siteAt0 (T := T) hell0 hM (nvcP1 ell M T) hvP with hy
    have hxv : (x 0).val = nvcP0 ell M R T - 1 := siteAt0_val hell0 hM _ hvN
    have hyv : (y 0).val = nvcP1 ell M T := siteAt0_val hell0 hM _ hvP
    have hxn : x ∉ (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M Rb T) (nvcP1 ell M T) (nvcQ1 ell M T)
        (nvcP2 ell M T) (nvcQ2 ell M T)).Om 0 := by
      rw [om0_mem, hxv]; omega
    have hym : y ∈ (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M Rb T) (nvcP1 ell M T) (nvcQ1 ell M T)
        (nvcP2 ell M T) (nvcQ2 ell M T)).Om 1 := by
      rw [om1_mem, hyv]; omega
    apply hxn
    refine (h6 x).2 ⟨y, hym, x, fun μ => rfl, ?_⟩
    rw [hx, hy, pdist_siteAt0 hell0 hM hvN hvP]
    have hmul : (R + 1) * M ≤ R0 * M := Nat.mul_le_mul_right M (by omega)
    rw [Nat.add_mul, one_mul] at hmul
    unfold pcd
    split_ifs <;> omega

theorem asym_nonvac_core {ell M R Rb T c : ℕ} (hell : 2 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (hRb : R < Rb) (hRbT : Rb ≤ T) (hRT : R ≤ T)
    (hT : 1 ≤ T) (hcT : c ≤ 2 * T + 1) (hcT' : c ≤ T) (hc10 : 10 ≤ c)
    {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ (k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
      (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ) (Bt : Bond Lu → SuTwo),
      2 ≤ k ∧ TorusOK ell M Lu ∧ AdmSplitNB ell M R (fun _ => Rb) k S ∧ (∀ (R0 : ℕ) (Rs : ℕ → ℕ), ¬ AdalyFormal.ThinLayer.AdmSplit ell M R0 Rs k S) ∧
      LambdaOK2 ell M Rb k S Lam ∧
      0 < α₀ ∧ ((c : ℕ) : ℝ) * (M : ℝ) * α₀ ≤ a₀ ∧
      ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
      (∃ p, p ∈ towerBj S 0) ∧ (∃ p, p ∈ towerBj S 1) ∧ (∃ p, p ∈ towerBj S 2) ∧
      (∃ p, p ∉ S.Om 0) ∧
      (∃ z, z ∈ S.Om 2 ∧ periodicLatticeShift z 0 ∈ S.Om 2 ∧ plaq U z ≠ 1) ∧
      (¬ ∃ g : PeriodicLatticeSite (scaleUp ell k Lu) → G2, periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
      Lam.Nonempty ∧ (LamPrime ell Lam).Nonempty ∧
      OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧ Bt ≠ 0 ∧
      (∀ j : ℕ, j ≤ k → ∀ μ : Fin 3, 6 * (c * bigSide M ell j) ≤ scaleUp ell k Lu μ + 1) ∧
      (∀ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ), IsClassCube ell M c k S sites j → ∃ x, x ∉ sites) := by
  have hell0 : 0 < ell := by omega
  have G := slabGeo_inst hell hM hdvd hRT hT
  have Gb := slabGeo_inst (R := Rb) hell hM hdvd hRbT hT
  obtain ⟨w0L, -, w1, w2, -, hP12, hQ21, -⟩ := nvc_widths hell hM hR hRT hT hcT
  obtain ⟨-, w0R, -, -, hQN, -, -, hQ10⟩ := nvc_widths (R := Rb) hell hM (by omega) hRbT hT hcT
  have hN : ∀ μ, scaleUp ell 2 (nvcLu M T) μ + 1 = nvcN ell M T := fun μ => scaleUp_nvc hell0 hM μ
  have hAdmA := slab3_admissible G hN
  have hAdmB := slab3_admissible Gb hN
  have GW : SlabGeoW M ell (nvcN ell M T) (nvcP0 ell M R T) (nvcQ0 ell M Rb T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T)
      (nvcQ2 ell M T) :=
    ⟨G.hM, G.hell, G.nest01, G.nest12, G.nestw, G.nest21, Gb.nest10, Gb.QN, G.d0, G.d1, G.d2, G.b0P, Gb.b0Q, G.b1P, G.b1Q, G.b2P, G.b2Q⟩
  have hcov := slab3_coverspW (by omega) GW w0L w0R w1 w2 hQN hP12 hQ21 hQ10 hN
  have hSplit := asym_admSplitNB_slab hell hM hdvd hR hRb hRbT hRT hT hN
  have hnot : ∀ (R0 : ℕ) (Rs : ℕ → ℕ), ¬ AdalyFormal.ThinLayer.AdmSplit ell M R0 Rs 2
      (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M Rb T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T)) :=
    fun R0 Rs => asym_not_admSplit_slab hell hM hdvd hR hRb hRbT hT hN
  have hAdm : AdalyFormal.ThinLayer.AdmSplitNB ell M R (fun _ => Rb) 2
      (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M Rb T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T)) := hSplit
  have hAdmT : ThinReplay.AdmT ell M R 2
      (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M Rb T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T)) :=
    AdalyFormal.ThinLayer.admT_of_splitNB (fun _ _ => hRb.le) hAdm
  have hNpos : 2 ≤ nvcN ell M T := by
    have := G.nest21; have := Gb.nest10; have := G.nestw; have := Gb.QN; omega
  have hL0 : 1 ≤ scaleUp ell 2 (nvcLu M T) 0 := by have := hN 0; omega
  have g1 := G.nest01; have g2 := G.nest12; have g3 := G.nestw; have g4 := G.nest21; have g5 := Gb.nest10
  have g6 := Gb.QN; have g7 := G.c0P; have g8 := Gb.c0Q
  have hRM : 0 < R * M := Nat.mul_pos (by omega) hM
  have hcR : (0 : ℝ) < c := by exact_mod_cast (show 0 < c by omega)
  -- the small parameter
  obtain ⟨α₀, hα0def⟩ : ∃ α₀ : ℝ, α₀ = min (a₀ / (c * M)) 1 / 2 := ⟨_, rfl⟩
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hα0 : 0 < α₀ := by
    rw [hα0def]
    have : 0 < a₀ / ((c : ℝ) * (M : ℝ)) := by positivity
    have := lt_min this one_pos; positivity
  have hα1 : α₀ ≤ 1 / 2 := by rw [hα0def]; have := min_le_right (a₀ / ((c : ℝ) * (M : ℝ))) 1; linarith
  have hαS : (c : ℝ) * M * α₀ ≤ a₀ := by
    rw [hα0def]
    have h := min_le_left (a₀ / ((c : ℝ) * (M : ℝ))) 1
    have h2 : (c : ℝ) * M * (a₀ / (c * M)) = a₀ := by field_simp
    have h3 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ c * M)
    have h0 : 0 ≤ min (a₀ / ((c : ℝ) * (M : ℝ))) 1 := le_min (by positivity) zero_le_one
    nlinarith
  -- the spike
  have hell' : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hη : (((ell : ℝ) ^ 2)⁻¹) ≤ 1 / 4 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]; nlinarith
  have hη0 : 0 < ((ell : ℝ) ^ 2)⁻¹ := by positivity
  have hc0 : 0 < α₀ * (((ell : ℝ) ^ 2)⁻¹) ^ 2 / 10 := by positivity
  have hηc0 : 0 < ((ell : ℝ) ^ 2)⁻¹ * (α₀ * (((ell : ℝ) ^ 2)⁻¹) ^ 2 / 10) := by positivity
  have hηc1 : ((ell : ℝ) ^ 2)⁻¹ * (α₀ * (((ell : ℝ) ^ 2)⁻¹) ^ 2 / 10) < 1 := by
    have h1 : (((ell : ℝ) ^ 2)⁻¹) ^ 2 ≤ 1 := by nlinarith
    nlinarith
  obtain ⟨v, hvdef⟩ : ∃ v, v = M * ell ^ 2 * (3 * T) := ⟨_, rfl⟩
  have hME : 0 < M * ell ^ 2 := Nat.mul_pos hM (pow_pos hell0 2)
  have hvP : nvcP2 ell M T ≤ v := by
    simp only [nvcP2]; rw [hvdef]; exact Nat.mul_le_mul_left _ (by omega)
  have hvQ : v + 1 < nvcQ2 ell M T := by
    simp only [nvcQ2]; rw [hvdef]
    have : M * ell ^ 2 * (4 * T + 1) = M * ell ^ 2 * (3 * T) + M * ell ^ 2 * (T + 1) := by ring
    have : 2 ≤ M * ell ^ 2 * (T + 1) := by nlinarith
    omega
  let z0 : PeriodicLatticeSite (scaleUp ell 2 (nvcLu M T)) := siteAt0 (T := T) hell0 hM v (by omega)
  have hz0v : (z0 0).val = v := siteAt0_val hell0 hM v (by omega)
  have hN1 : 1 < nvcN ell M T := by omega
  have hsh : ((periodicLatticeShift z0 0) 0).val = v + 1 := by
    rw [shift_val_N hN hN1, if_pos rfl, hz0v, Nat.mod_eq_of_lt (by omega)]
  have hUreg := AdalyFormal.M1.ufield_M1Regular (ell := ell) (M := M) (f := c) (k := 2) (by omega) hM hc10
    (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M Rb T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T))
    hα0 (spike (periodicLatticeShift z0 0, 1) (α₀ * (((ell : ℝ) ^ 2)⁻¹) ^ 2 / 10)) (by
      intro e
      unfold spike
      split_ifs
      · rw [abs_of_pos hc0]
      · simp only [abs_zero]; positivity)
  have hLam : LambdaOK2 ell M Rb 2
      (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M Rb T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T)) (LamN M T) :=
    lambdaOK2_congr (by simp [slab3]) (lambdaOK2_nv hell hdvd hM hRbT hT)
  refine ⟨2, nvcLu M T, slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M Rb T) (nvcP1 ell M T) (nvcQ1 ell M T)
    (nvcP2 ell M T) (nvcQ2 ell M T), LamN M T,
    Ufield (((ell : ℝ) ^ 2)⁻¹) (spike (periodicLatticeShift z0 0, 1) (α₀ * (((ell : ℝ) ^ 2)⁻¹) ^ 2 / 10)),
    α₀, BseedNv ell hM, le_rfl, torusOK_nv hell hdvd hM, hAdm, hnot, hLam, hα0, hαS,
    ⟨hcov, ThinScan.AdalyFormal.M1.perCube_of_M1 hAdmT hUreg⟩, ?_, ?_, ?_, ?_, ?_, ?_, lam_nonempty hM, ?_,
    (BseedNv_props hell hdvd hM).1, (BseedNv_props hell hdvd hM).2.1, (BseedNv_props hell hdvd hM).2.2.1,
    (BseedNv_props hell hdvd hM).2.2.2, ?_, ?_⟩
  · refine ⟨siteAt0 (T := T) hell0 hM (nvcP0 ell M R T) (by omega), ?_⟩
    rw [bj0, siteAt0_val]; omega
  · refine ⟨siteAt0 (T := T) hell0 hM (nvcP1 ell M T) (by omega), ?_⟩
    rw [bj1, siteAt0_val]; omega
  · refine ⟨siteAt0 (T := T) hell0 hM (nvcP2 ell M T) (by omega), ?_⟩
    rw [bj2, siteAt0_val]; omega
  · refine ⟨siteAt0 (T := T) hell0 hM (nvcQ0 ell M Rb T) (by omega), ?_⟩
    rw [om0_mem, siteAt0_val]; omega
  · refine ⟨z0, ?_, ?_, ?_⟩
    · rw [om2_mem, hz0v]; omega
    · rw [om2_mem, hsh]; omega
    · rw [plaq_spike _ _ z0 (shift_ne_self z0 0 hL0)]
      exact Ug_ne_one hηc0 hηc1
  · exact spike_not_pure_gauge hL0 _ _ z0 hηc0 hηc1
  · exact (lamBlockSum_nv hell0 hdvd hM).lamPrime_nonempty (lam_nonempty hM)
  · intro j hj μ
    rw [hN μ]
    exact nvc_period (by omega) hM hj hcT'
  · intro sites j hq
    obtain ⟨hj, ⟨z, -, rfl⟩, -⟩ := hq.1
    refine box_not_univ hN z ?_
    have := nvc_period (ell := ell) (M := M) (T := T) (c := c) (j := j) (by omega) hM hj hcT'
    have h2 : 0 < c * bigSide M ell j := Nat.mul_pos (by omega) (Nat.mul_pos hM (pow_pos hell0 j))
    omega


/-- the non-radial thin-layer witness at `M = ell^m`, left layer radius `R`, right layer / levels `>= 1` / `Lambda` radius `Rb > R`, layout scale `T = max Rb c`. -/
theorem asym_headline_regime_nonvacuous {ell m R Rb c : ℕ} (hell : 2 ≤ ell) (hm : 1 ≤ m) (hc : 10 ≤ c) (hR : 1 ≤ R) (hRb : R < Rb)
    {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ (k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
      (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ) (Bt : Bond Lu → SuTwo),
      2 ≤ k ∧ TorusOK ell (ell ^ m) Lu ∧ AdmSplitNB ell (ell ^ m) R (fun _ => Rb) k S ∧
      (∀ (R0 : ℕ) (Rs : ℕ → ℕ), ¬ AdalyFormal.ThinLayer.AdmSplit ell (ell ^ m) R0 Rs k S) ∧
      LambdaOK2 ell (ell ^ m) Rb k S Lam ∧
      0 < α₀ ∧ ((c : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ ∧
      ClassCoupled ell (ell ^ m) c k S α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
      (∃ p, p ∈ towerBj S 0) ∧ (∃ p, p ∈ towerBj S 1) ∧ (∃ p, p ∈ towerBj S 2) ∧
      (∃ p, p ∉ S.Om 0) ∧
      (∃ z, z ∈ S.Om 2 ∧ periodicLatticeShift z 0 ∈ S.Om 2 ∧ plaq U z ≠ 1) ∧
      (¬ ∃ g : PeriodicLatticeSite (scaleUp ell k Lu) → G2, periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
      Lam.Nonempty ∧ (LamPrime ell Lam).Nonempty ∧
      OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧ Bt ≠ 0 ∧
      (∀ j : ℕ, j ≤ k → ∀ μ : Fin 3, 6 * (c * bigSide (ell ^ m) ell j) ≤ scaleUp ell k Lu μ + 1) ∧
      (∀ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ), IsClassCube ell (ell ^ m) c k S sites j → ∃ x, x ∉ sites) :=
  asym_nonvac_core (T := max Rb c) hell (dvd_pow_self ell (by omega)) (pow_pos (by omega) m) hR hRb (le_max_left _ _)
    (by have := le_max_left Rb c; omega) (by have := le_max_left Rb c; omega)
    (by have := le_max_right Rb c; omega) (le_max_right Rb c) hc ha₀

/-- **the arbitrary-layer headline instantiated at the non-radial witness** (`totalLayer`): constants `m₁, R₁, a₀, γ₀` before `c, m, R, Rb`; for `R >= max R₁ 1` the witness list holds
and the conclusion (`WellDefG` and `γ₀ ‖B~‖² ≤ genForm (C B~)`) holds at it. -/
theorem asym_instance_inequality (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ (a₀ γ₀ : ℝ), 0 < a₀ ∧ 0 < γ₀ ∧ ∀ c : ℕ, 10 ≤ c → ∀ m : ℕ, m₁ ≤ m →
      ∀ R : ℕ, max R₁ 1 ≤ R → ∀ Rb : ℕ, R < Rb →
      ∃ (k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
        (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ) (Bt : Bond Lu → SuTwo),
        2 ≤ k ∧ TorusOK ell (ell ^ m) Lu ∧ AdmSplitNB ell (ell ^ m) R (fun _ => Rb) k S ∧
        (∀ (R0 : ℕ) (Rs : ℕ → ℕ), ¬ AdalyFormal.ThinLayer.AdmSplit ell (ell ^ m) R0 Rs k S) ∧
        LambdaOK2 ell (ell ^ m) Rb k S Lam ∧
        0 < α₀ ∧ ((c : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ ∧
        ClassCoupled ell (ell ^ m) c k S α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
        (∃ p, p ∈ towerBj S 0) ∧ (∃ p, p ∈ towerBj S 1) ∧ (∃ p, p ∈ towerBj S 2) ∧ (∃ p, p ∉ S.Om 0) ∧
        (∃ z, z ∈ S.Om 2 ∧ periodicLatticeShift z 0 ∈ S.Om 2 ∧ plaq U z ≠ 1) ∧
        (¬ ∃ g : PeriodicLatticeSite (scaleUp ell k Lu) → G2, periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
        Lam.Nonempty ∧ (LamPrime ell Lam).Nonempty ∧
        OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧ Bt ≠ 0 ∧
        (∀ j : ℕ, j ≤ k → ∀ μ : Fin 3, 6 * (c * bigSide (ell ^ m) ell j) ≤ scaleUp ell k Lu μ + 1) ∧
        (∀ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ),
          IsClassCube ell (ell ^ m) c k S sites j → ∃ x, x ∉ sites) ∧
        GenP.WellDefG (gparams ell k Lu (by omega) S U a Lam) ∧
        γ₀ * bondEnergy Bt ≤
          GenP.genForm (gparams ell k Lu (by omega) S U a Lam)
            (WithLp.toLp 2 (GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt)) := by
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ₀, hT⟩ := AdalyFormal.ThinLayer.totalLayer ell hell a ha
  refine ⟨m₁, hm₁, R₁, a₀, γ₀, ha₀, hγ₀, fun c hc m hm R hR Rb hRb => ?_⟩
  obtain ⟨k, Lu, S, Lam, U, α₀, Bt, hk, hTor, hSp, hn, hL, hα, hαS, hCC, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ :=
    asym_headline_regime_nonvacuous (ell := ell) (m := m) (R := R) (Rb := Rb) (c := c) hell (le_trans hm₁ hm) hc
      (le_trans (le_max_right _ _) hR) hRb ha₀
  have hmain := hT c hc m hm R (le_trans (le_max_left _ _) hR) (fun _ => Rb) (fun _ _ => hRb.le) Rb hRb.le k (by omega) Lu α₀ hα hαS
    hTor S hSp Lam hL U hCC
  exact ⟨k, Lu, S, Lam, U, α₀, Bt, hk, hTor, hSp, hn, hL, hα, hαS, hCC, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    hmain.1, hmain.2 Bt h8 h9⟩

end AdalyFormal.NonVacC

#print axioms AdalyFormal.NonVacC.slab3_coverspW
#print axioms AdalyFormal.NonVacC.asym_admSplitNB_slab
#print axioms AdalyFormal.NonVacC.asym_not_admSplit_slab
#print axioms AdalyFormal.NonVacC.asym_nonvac_core
#print axioms AdalyFormal.NonVacC.asym_headline_regime_nonvacuous
#print axioms AdalyFormal.NonVacC.asym_instance_inequality
