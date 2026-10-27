import NVC7
import L0C3

/-!
# L0C4 -- CURVED non-vacuity for the altered class (lane level0_class_20261019)

`nonvac_core_L0` is `M12NV.nonvac_core_Phi` (lanes nonvac_c_20261017, mixed12_20261019: slab tower, a single tiny spike `Ufield`, `Lambda`, `B~`) with the class hypothesis
`ClassCoupledP level0ClassW` / `ClassCoupledCap` for the family `famL Phi` (ALL triples with factor in `Phi`) in place of `ClassCoupledPhi`, and one more conjunct:
for every `f ∈ Phi` there is a `DescribedAt0` box `C` of factor `f` (a member of the family) which leaves `Omega_0`, meets `Omega_0`, and is a cube of NO original class (index, factor).
The regularity of such a `C` on the whole box (index 0) is `regBody_zero_of_M1`: the M1 regime bounds hold at the stratum `0 <= bstrat` on every bond.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 64000000

namespace AdalyFormal.L0NV

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.NonVacC
open AdalyFormal.P409L (DescribedAt0)
open AdalyFormal.L0C
open UNI.AllC UNI.Total

/-- the slab tower of the witness. -/
def towerW (ell M R T : ℕ) : Tower (scaleUp ell 2 (nvcLu M T)) :=
  slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M R T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T)

/-- the family of ALL triples with factor in `Φ`. -/
def famL (Φ : Set ℕ) (L : PeriodicLatticeExtent) : CubeFam L := {t | t.2.2 ∈ Φ}

/-- the M1 regime gives regularity at index `0` on EVERY set of sites (the stratum of any bond is `≥ 0`). -/
theorem regBody_zero_of_M1 {L : PeriodicLatticeExtent} {ell M f k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (h : AdalyFormal.M1.M1Regular ell M f k S α₀ η U) (sites : Set (PeriodicLatticeSite L)) :
    RegBodyH ell M f sites 0 α₀ η U := by
  obtain ⟨g, A, hU, hHT, h1, h2, h3⟩ := h
  refine ⟨g, A, fun e _ => ⟨hHT e, hU e, h1 e 0 (Nat.zero_le _)⟩,
    fun μ ν x _ _ => h2 μ ν x 0 (Nat.zero_le _) (Nat.zero_le _), ?_⟩
  intro μ x _
  exact h3 μ x 0 (fun ν _ => ⟨⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩,
    ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩⟩)

/-- the altered class hypotheses (wide and cap forms) from the M1 regime at every factor of `Φ` and an original coverage at one factor. -/
theorem altCoupled_of_M1 {L : PeriodicLatticeExtent} {ell M R k f0 : ℕ} {S : Tower L} (hA : Admissible ell M R k S)
    {Φ : Set ℕ} (hf0 : f0 ∈ Φ) (hcov : CoversOm0p ell M f0 k S) {α₀ η : ℝ} {U : LinkCfg L}
    (hreg : ∀ f ∈ Φ, AdalyFormal.M1.M1Regular ell M f k S α₀ η U) :
    ClassCoupledP level0ClassW ell M (famL Φ L) k S α₀ η U ∧ ClassCoupledCap ell M (famL Φ L) k S α₀ η U := by
  have hW : ∀ (f : ℕ) (sites : Set (PeriodicLatticeSite L)) (j : ℕ), (sites, j, f) ∈ famL Φ L →
      DescribedAtAlt ell M f k S sites j → RegBodyH ell M f sites j α₀ η U := by
    intro f sites j hmem hd
    have hfΦ : f ∈ Φ := hmem
    rcases hd with ⟨hj0, hd0⟩ | ⟨hj1, hd⟩
    · subst hj0; exact regBody_zero_of_M1 (hreg f hfΦ) sites
    · exact AdalyFormal.M1.perCube_of_M1 hA (hreg f hfΦ) sites j (AdalyFormal.Thin.isClassCube_of_described hA.1 hd)
  obtain ⟨hs, hp⟩ := hcov
  have c1 : ∀ x ∈ S.Om 0, ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ),
      (∃ f, (sites, j, f) ∈ famL Φ L ∧ DescribedAtAlt ell M f k S sites j) ∧ x ∈ sites := by
    intro x hx
    obtain ⟨sites, j, hq, hxs⟩ := hs x hx
    exact ⟨sites, j, ⟨f0, hf0, descAlt_of_desc hq.1⟩, hxs⟩
  have c2 : ∀ p : PeriodicLatticePlaquette L, (∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond (S.Om 0) e) →
      ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), (∃ f, (sites, j, f) ∈ famL Φ L ∧ DescribedAtAlt ell M f k S sites j) ∧
        ∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond sites e := by
    intro p hp'
    obtain ⟨sites, j, hq, hb⟩ := hp p hp'
    exact ⟨sites, j, ⟨f0, hf0, descAlt_of_desc hq.1⟩, hb⟩
  exact ⟨⟨c1, c2, hW⟩, ⟨c1, c2, fun f sites j hmem hd =>
    UNI.Joint.regBody_mono_sites Set.inter_subset_left (hW f sites j hmem hd)⟩⟩

/-- a site with first coordinate `v` and the others `0`. -/
def siteV {L : PeriodicLatticeExtent} {N : ℕ} (hN : ∀ μ, L μ + 1 = N) (v : ℕ) (hv : v < N) : PeriodicLatticeSite L :=
  fun μ => ⟨if μ = 0 then v else 0, by have := hN μ; split_ifs <;> omega⟩

theorem siteV_val0 {L : PeriodicLatticeExtent} {N : ℕ} (hN : ∀ μ, L μ + 1 = N) (v : ℕ) (hv : v < N) :
    ((siteV hN v hv) 0).val = v := by simp [siteV]

theorem siteV_valne {L : PeriodicLatticeExtent} {N : ℕ} (hN : ∀ μ, L μ + 1 = N) (v : ℕ) (hv : v < N) {μ : Fin 3} (h : μ ≠ 0) :
    ((siteV hN v hv) μ).val = 0 := by simp [siteV, h]

/-- **a `DescribedAt0` box that leaves `Omega_0`** (slab geometry): the box of side `f M` with corner `P0 - M` on the `M`-grid; it meets `Omega_0` (at `x_0 = P0`) and leaves it (at `x_0 = P0 - M`),
stays in `(Omega_1)^c ∪ B^1` because it stops before `Omega_2`. -/
theorem leaving_cube {L : PeriodicLatticeExtent} {ell M f N P0 Q0 P1 Q1 P2 Q2 : ℕ} (hN : ∀ μ, L μ + 1 = N)
    (hM : 0 < M) (hf : 10 ≤ f) (hMP0 : M ≤ P0) (hdvd : M ∣ P0) (hP01 : P0 < P1) (hw : P0 + f * M ≤ P2)
    (hP2N : P2 < N) (hP0Q0 : P0 < Q0) :
    ∃ C : Set (PeriodicLatticeSite L), DescribedAt0 ell M f (slab3 L P0 Q0 P1 Q1 P2 Q2) C ∧
      (∃ x ∈ C, x ∉ (slab3 L P0 Q0 P1 Q1 P2 Q2).Om 0) ∧ (∃ x ∈ C, x ∈ (slab3 L P0 Q0 P1 Q1 P2 Q2).Om 0) := by
  have hfM : 10 * M ≤ f * M := Nat.mul_le_mul_right M hf
  have hv1 : P0 - M < N := by omega
  have hv2 : P0 < N := by omega
  let z : PeriodicLatticeSite L := siteV hN (P0 - M) hv1
  let xr : PeriodicLatticeSite L := siteV hN P0 hv2
  have hz0 : (z 0).val = P0 - M := siteV_val0 hN _ _
  have hxr0 : (xr 0).val = P0 := siteV_val0 hN _ _
  have hb0 : bigSide M ell 0 = M := by simp [bigSide]
  have hmemC : ∀ x : PeriodicLatticeSite L, x ∈ siteBox z (f * bigSide M ell 0) → P0 - M ≤ (x 0).val ∧ (x 0).val < P2 := by
    intro x hx
    have h0 := hx 0
    have hn := hN 0
    rw [rel_eq (z 0).isLt (x 0).isLt, hz0, hb0] at h0
    split_ifs at h0 <;> omega
  have hrelz : ∀ μ : Fin 3, ((z μ).val + (L μ + 1) - (z μ).val) % (L μ + 1) < f * bigSide M ell 0 := by
    intro μ
    rw [rel_eq (z μ).isLt (z μ).isLt, if_pos le_rfl, Nat.sub_self, hb0]
    omega
  refine ⟨siteBox z (f * bigSide M ell 0), ⟨⟨z, ?_, rfl⟩, ?_, ?_⟩, ?_, ?_⟩
  · intro μ
    rw [hb0]
    by_cases hμ : μ = 0
    · subst hμ
      rw [hz0]
      exact Nat.mod_eq_zero_of_dvd (Nat.dvd_sub hdvd (dvd_refl M))
    · rw [siteV_valne hN _ _ hμ]; simp
  · intro x hx
    obtain ⟨h1, h2⟩ := hmemC x hx
    by_cases hx1 : x ∈ (slab3 L P0 Q0 P1 Q1 P2 Q2).Om 1
    · right
      refine ⟨hx1, ?_⟩
      rw [om2_mem]; omega
    · left; exact hx1
  · refine ⟨z, hrelz, ?_⟩
    intro h
    rw [om1_mem] at h
    rw [hz0] at h
    omega
  · refine ⟨z, hrelz, ?_⟩
    rw [om0_mem, hz0]; omega
  · refine ⟨xr, ?_, ?_⟩
    · intro μ
      have hn := hN μ
      rw [rel_eq (z μ).isLt (xr μ).isLt]
      by_cases hμ : μ = 0
      · subst hμ
        rw [hz0, hxr0, hb0]
        split_ifs <;> omega
      · rw [siteV_valne hN _ _ hμ, siteV_valne hN _ _ hμ, hb0]
        have hfM0 : 0 < f * M := Nat.mul_pos (by omega) hM
        split_ifs <;> omega
    · rw [om0_mem, hxr0]; omega

/-- a cube with a site outside `Omega_0` belongs to no original class. -/
theorem no_class_cube_of_leaves {L : PeriodicLatticeExtent} {ell M R k : ℕ} {S : Tower L} (hA : Admissible ell M R k S)
    {C : Set (PeriodicLatticeSite L)} (hx : ∃ x ∈ C, x ∉ S.Om 0) (f j : ℕ) : ¬ IsClassCube ell M f k S C j := by
  intro hq
  obtain ⟨x, hxC, hx0⟩ := hx
  have hanti : Antitone S.Om := antitone_nat_of_succ_le hA.1
  exact hx0 (hanti (Nat.zero_le j) (AdalyFormal.M1.classCube_sub hA hq hxC))

theorem nonvac_core_L0 {ell M R T : ℕ} (Φ : Set ℕ) (hne : Φ.Nonempty) (hΦ : ∀ f ∈ Φ, 10 ≤ f ∧ f ≤ T)
    (hell : 2 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (hRT : R ≤ T) (hT : 1 ≤ T)
    {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ (k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
      (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ) (Bt : Bond Lu → SuTwo),
      2 ≤ k ∧ TorusOK ell M Lu ∧ Admissible ell M R k S ∧ LambdaOK2 ell M R k S Lam ∧
      0 < α₀ ∧ (∀ f ∈ Φ, (f : ℝ) * (M : ℝ) * α₀ ≤ a₀) ∧
      ClassCoupledP level0ClassW ell M (famL Φ (scaleUp ell k Lu)) k S α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
      ClassCoupledCap ell M (famL Φ (scaleUp ell k Lu)) k S α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
      (∃ p, p ∈ towerBj S 0) ∧ (∃ p, p ∈ towerBj S 1) ∧ (∃ p, p ∈ towerBj S 2) ∧
      (∃ p, p ∉ S.Om 0) ∧
      (∃ z, z ∈ S.Om 2 ∧ periodicLatticeShift z 0 ∈ S.Om 2 ∧ plaq U z ≠ 1) ∧
      (¬ ∃ g : PeriodicLatticeSite (scaleUp ell k Lu) → G2, periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
      Lam.Nonempty ∧ (LamPrime ell Lam).Nonempty ∧
      OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧ Bt ≠ 0 ∧
      (∀ μ : Fin 3, M < Lu μ + 1) ∧
      (∀ f ∈ Φ, ∃ C : Set (PeriodicLatticeSite (scaleUp ell k Lu)), (C, 0, f) ∈ famL Φ (scaleUp ell k Lu) ∧
        DescribedAt0 ell M f S C ∧ (∃ x ∈ C, x ∉ S.Om 0) ∧ (∃ x ∈ C, x ∈ S.Om 0) ∧
        ∀ (f' j : ℕ), ¬ IsClassCube ell M f' k S C j) := by
  have hell0 : 0 < ell := by omega
  have G := slabGeo_inst hell hM hdvd hRT hT
  have hN : ∀ μ, scaleUp ell 2 (nvcLu M T) μ + 1 = nvcN ell M T := fun μ => scaleUp_nvc hell0 hM μ
  have hcovF : ∀ f ∈ Φ, CoversOm0p ell M f 2 (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M R T)
      (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T)) := by
    intro f hf
    have hf' := hΦ f hf
    obtain ⟨w0L, w0R, w1, w2, hQN, hP12, hQ21, hQ10⟩ := nvc_widths (c := f) hell hM hR hRT hT (by omega)
    exact slab3_coversp (by omega) G w0L w0R w1 w2 hQN hP12 hQ21 hQ10 hN
  obtain ⟨w0L, w0R, w1, w2, hQN, hP12, hQ21, hQ10⟩ := nvc_widths (c := 0) hell hM hR hRT hT (by omega)
  have hAdm := slab3_admissible G hN
  have hNpos : 2 ≤ nvcN ell M T := by
    have := G.nest21; have := G.nest10; have := G.nestw; have := G.QN; omega
  have hL0 : 1 ≤ scaleUp ell 2 (nvcLu M T) 0 := by have := hN 0; omega
  have g1 := G.nest01; have g2 := G.nest12; have g3 := G.nestw; have g4 := G.nest21; have g5 := G.nest10
  have g6 := G.QN; have g7 := G.c0P; have g8 := G.c0Q
  have hRM : 0 < R * M := Nat.mul_pos (by omega) hM
  have hTr : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  obtain ⟨α₀, hα0def⟩ : ∃ α₀ : ℝ, α₀ = min (a₀ / (T * M)) 1 / 2 := ⟨_, rfl⟩
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hα0 : 0 < α₀ := by
    rw [hα0def]
    have : 0 < a₀ / ((T : ℝ) * (M : ℝ)) := by positivity
    have := lt_min this one_pos; positivity
  have hα1 : α₀ ≤ 1 / 2 := by rw [hα0def]; have := min_le_right (a₀ / ((T : ℝ) * (M : ℝ))) 1; linarith
  have hαT : (T : ℝ) * M * α₀ ≤ a₀ := by
    rw [hα0def]
    have h := min_le_left (a₀ / ((T : ℝ) * (M : ℝ))) 1
    have h2 : (T : ℝ) * M * (a₀ / (T * M)) = a₀ := by field_simp
    have h3 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ T * M)
    have h0 : 0 ≤ min (a₀ / ((T : ℝ) * (M : ℝ))) 1 := le_min (by positivity) zero_le_one
    nlinarith
  have hαS : ∀ f ∈ Φ, (f : ℝ) * M * α₀ ≤ a₀ := by
    intro f hf
    have hfT : (f : ℝ) ≤ T := by exact_mod_cast (hΦ f hf).2
    have hMα : 0 ≤ (M : ℝ) * α₀ := by positivity
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
  have hUregF : ∀ f ∈ Φ, AdalyFormal.M1.M1Regular ell M f 2
      (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M R T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T))
      α₀ (((ell : ℝ) ^ 2)⁻¹)
      (Ufield (((ell : ℝ) ^ 2)⁻¹) (spike (periodicLatticeShift z0 0, 1) (α₀ * (((ell : ℝ) ^ 2)⁻¹) ^ 2 / 10))) := by
    intro f hf
    exact AdalyFormal.M1.ufield_M1Regular (ell := ell) (M := M) (f := f) (k := 2) (by omega) hM (hΦ f hf).1
      (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M R T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T))
      hα0 (spike (periodicLatticeShift z0 0, 1) (α₀ * (((ell : ℝ) ^ 2)⁻¹) ^ 2 / 10)) (by
        intro e
        unfold spike
        split_ifs
        · rw [abs_of_pos hc0]
        · simp only [abs_zero]; positivity)
  have hper : ∀ f ∈ Φ, ∀ j : ℕ, j ≤ 2 → ∀ μ : Fin 3, 6 * (f * bigSide M ell j) ≤ scaleUp ell 2 (nvcLu M T) μ + 1 := by
    intro f hf j hj μ
    rw [hN μ]
    exact nvc_period (by omega) hM hj (hΦ f hf).2

  obtain ⟨f0, hf0⟩ := hne
  have hAC := altCoupled_of_M1 hAdm hf0 (hcovF f0 hf0) hUregF
  have hleave : ∀ f ∈ Φ, ∃ C : Set (PeriodicLatticeSite (scaleUp ell 2 (nvcLu M T))),
      (C, 0, f) ∈ famL Φ (scaleUp ell 2 (nvcLu M T)) ∧ DescribedAt0 ell M f (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M R T)
        (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T)) C ∧
      (∃ x ∈ C, x ∉ (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M R T)
        (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T)).Om 0) ∧
      (∃ x ∈ C, x ∈ (slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M R T)
        (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T)).Om 0) := by
    intro f hf
    have hf' := hΦ f hf
    obtain ⟨v0L, v0R, v1, v2, vQN, vP12, vQ21, vQ10⟩ := nvc_widths (c := f) hell hM hR hRT hT (by omega)
    have hfM : 0 < f * (M * ell ^ 2) := Nat.mul_pos (by omega) (Nat.mul_pos hM (pow_pos hell0 2))
    have hMP0 : M ≤ nvcP0 ell M R T := by
      simp only [nvcP0]
      apply Nat.le_mul_of_pos_right
      have h4 : 4 ≤ ell ^ 2 := by nlinarith
      have : 4 * T ≤ ell ^ 2 * T := Nat.mul_le_mul_right T h4
      omega
    have hP01 : nvcP0 ell M R T < nvcP1 ell M T := by
      simp only [nvcP0, nvcP1]
      have h4 : 4 ≤ ell ^ 2 := by nlinarith
      have : 4 * T ≤ ell ^ 2 * T := Nat.mul_le_mul_right T h4
      have h5 : ell ^ 2 * T - R < ell ^ 2 * T := by omega
      calc M * (ell ^ 2 * T - R) < M * (ell ^ 2 * T) := Nat.mul_lt_mul_of_pos_left h5 hM
        _ = M * ell ^ 2 * T := by ring
    have hP2Q2 : nvcP2 ell M T < nvcQ2 ell M T := by omega
    obtain ⟨C, hC1, hC2, hC3⟩ := leaving_cube (L := scaleUp ell 2 (nvcLu M T)) (ell := ell) (f := f) (N := nvcN ell M T)
      (Q0 := nvcQ0 ell M R T) (P1 := nvcP1 ell M T) (Q1 := nvcQ1 ell M T) (Q2 := nvcQ2 ell M T) hN hM hf'.1 hMP0
      (by simp only [nvcP0]; exact Dvd.intro _ rfl) hP01 v0L (by omega) (by omega)
    exact ⟨C, hf, hC1, hC2, hC3⟩
  refine ⟨2, nvcLu M T, slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M R T) (nvcP1 ell M T) (nvcQ1 ell M T)
    (nvcP2 ell M T) (nvcQ2 ell M T), LamN M T,
    Ufield (((ell : ℝ) ^ 2)⁻¹) (spike (periodicLatticeShift z0 0, 1) (α₀ * (((ell : ℝ) ^ 2)⁻¹) ^ 2 / 10)),
    α₀, BseedNv ell hM, le_rfl, torusOK_nv hell hdvd hM, hAdm, lambdaOK2_nv hell hdvd hM hRT hT, hα0, hαS,
    hAC.1, hAC.2, ?_, ?_, ?_, ?_, ?_, ?_, lam_nonempty hM, ?_,
    (BseedNv_props hell hdvd hM).1, (BseedNv_props hell hdvd hM).2.1, (BseedNv_props hell hdvd hM).2.2.1,
    (BseedNv_props hell hdvd hM).2.2.2, ?_, ?_⟩
  · refine ⟨siteAt0 (T := T) hell0 hM (nvcP0 ell M R T) (by omega), ?_⟩
    rw [bj0, siteAt0_val]; omega
  · refine ⟨siteAt0 (T := T) hell0 hM (nvcP1 ell M T) (by omega), ?_⟩
    rw [bj1, siteAt0_val]; omega
  · refine ⟨siteAt0 (T := T) hell0 hM (nvcP2 ell M T) (by omega), ?_⟩
    rw [bj2, siteAt0_val]; omega
  · refine ⟨siteAt0 (T := T) hell0 hM (nvcQ0 ell M R T) (by omega), ?_⟩
    rw [om0_mem, siteAt0_val]; omega
  · refine ⟨z0, ?_, ?_, ?_⟩
    · rw [om2_mem, hz0v]; omega
    · rw [om2_mem, hsh]; omega
    · rw [plaq_spike _ _ z0 (shift_ne_self z0 0 hL0)]
      exact Ug_ne_one hηc0 hηc1
  · exact spike_not_pure_gauge hL0 _ _ z0 hηc0 hηc1
  · exact (lamBlockSum_nv hell0 hdvd hM).lamPrime_nonempty (lam_nonempty hM)
  · intro μ
    rw [nvcLu_succ hM]
    nlinarith
  · intro f hf
    obtain ⟨C, hCF, hC1, hC2, hC3⟩ := hleave f hf
    exact ⟨C, hCF, hC1, hC2, hC3, no_class_cube_of_leaves hAdm hC2⟩

end AdalyFormal.L0NV

#print axioms AdalyFormal.L0NV.regBody_zero_of_M1
#print axioms AdalyFormal.L0NV.altCoupled_of_M1
#print axioms AdalyFormal.L0NV.leaving_cube
#print axioms AdalyFormal.L0NV.no_class_cube_of_leaves
#print axioms AdalyFormal.L0NV.nonvac_core_L0
