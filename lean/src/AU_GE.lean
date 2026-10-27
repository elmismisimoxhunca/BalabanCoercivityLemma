import AC_GE7
import AC_CF
import AC_Base

/-!
# AU_GE -- c-FREE slab / vertex charts (lane allc_20261016, uniform-in-c route)

Text copies of `AC_GE4.slab_cube_auxAC`, `AC_GE5.slab_cubeAC`, `AC_GE7.vertex_chart_of_towerAC` with the hypotheses `x0 in Omega_{m+1}` and
`2 pdist + 3 fc b_m <= 2 R b_m` replaced by `hY` : every point of the vertex box lies in `Omega_0`, and (unless `m = 0`) in `Omega_{m+1}`.
The index of the covering cube is then `>= m` by `cubeIndex_ge_pred` (c-free); for `m = 0` it is trivial.  `cube_scaleAC` is not used.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M2GlueGeo

open AdalyFormal.AllC
variable {fc : ℕ} [CubeFactor fc]

open AdalyFormal.Target.ClayStatement AdalyFormal.M2Glue3 AdalyFormal.M2Glue2
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (pdist_comm pdist_triangle Ball)
open AdalyFormal.M1 (om_anti)
open AdalyFormal.M2Bridge (pdist_lt_three_s')
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 coe_mul coe_inv)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)

variable {L : PeriodicLatticeExtent}

theorem slab_cube_auxU {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S)
    (hcov : CoversOm0p ell M fc k S) (hell : 2 ≤ ell) (hM : 0 < M) {m : ℕ} (hmk : m ≤ k)
    {v : PeriodicLatticeSite L}
    (hv : ∀ μ, (v μ).val % bigSide M ell m = 0)
    (hY : ∀ p ∈ BoxS (bigSide M ell m), iota v p ∈ S.Om 0 ∧ (m = 0 ∨ iota v p ∈ S.Om (m + 1)))
    {μ ν σ : Fin 3} (hμν : μ < ν) (hσμ : σ ≠ μ) (hσν : σ ≠ ν) {cσ : ℤ} (hcσ : cσ = 0 ∨ cσ = -1) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube ell M fc k S sites j ∧ m ≤ j ∧
      ∀ p : Z3, (-(bigSide M ell m : ℤ) ≤ p μ ∧ p μ < bigSide M ell m) →
        (-(bigSide M ell m : ℤ) ≤ p ν ∧ p ν < bigSide M ell m) →
        p σ / (bigSide M ell m : ℤ) = cσ → iota v p ∈ sites := by
  set s := bigSide M ell m with hsdef
  have hs : 0 < s := bigSide_pos (by omega) hM m
  have hs1 : (1 : ℤ) ≤ s := by exact_mod_cast hs
  have hμν' : μ ≠ ν := ne_of_lt hμν
  let q0 : Z3 := fun i => if i = μ ∨ i = ν then -1 else cσ
  have hq0μ : q0 μ = -1 := by simp [q0]
  have hq0ν : q0 ν = -1 := by simp [q0, hμν'.symm]
  have hq0σ : q0 σ = cσ := by simp [q0, hσμ, hσν]
  have hbox : ∀ a b : ℤ, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → (q0 + a • ev μ + b • ev ν) ∈ BoxS s := by
    intro a b ha ha1 hb hb1 i
    have h1 : -(s : ℤ) ≤ -1 := by linarith
    by_cases hi : i = μ
    · subst hi
      have : i ≠ ν := hμν'
      simp [q0, ev, this]
      constructor <;> omega
    · by_cases hj : i = ν
      · subst hj
        simp [q0, ev, hi]
        constructor <;> omega
      · simp [q0, ev, hi, hj]
        rcases hcσ with h | h <;> rw [h] <;> constructor <;> omega
  have hΩ : ∀ p ∈ BoxS s, iota v p ∈ S.Om 0 := fun p hp => (hY p hp).1
  have hb00 := hbox 0 0 le_rfl (by norm_num) le_rfl (by norm_num)
  have hb10 := hbox 1 0 (by norm_num) le_rfl le_rfl (by norm_num)
  have hb01 := hbox 0 1 le_rfl (by norm_num) (by norm_num) le_rfl
  have hb11 := hbox 1 1 (by norm_num) le_rfl (by norm_num) le_rfl
  simp only [zero_smul, add_zero, one_smul] at hb00 hb10 hb01 hb11
  have hall : ∀ e ∈ periodicPlaquetteBoundaryEdges ((iota v q0, ⟨(μ, ν), hμν⟩) : PeriodicLatticePlaquette L),
      CubeBond (S.Om 0) e := by
    intro e he
    unfold periodicPlaquetteBoundaryEdges at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    · refine ⟨hΩ _ hb00, ?_⟩
      show periodicLatticeShift (iota v q0) μ ∈ S.Om 0
      rw [iota_shift]; exact hΩ _ hb10
    · refine ⟨?_, ?_⟩
      · show periodicLatticeShift (iota v q0) μ ∈ S.Om 0
        rw [iota_shift]; exact hΩ _ hb10
      · show periodicLatticeShift (periodicLatticeShift (iota v q0) μ) ν ∈ S.Om 0
        rw [iota_shift2]; exact hΩ _ hb11
    · refine ⟨?_, ?_⟩
      · show periodicLatticeShift (iota v q0) ν ∈ S.Om 0
        rw [iota_shift]; exact hΩ _ hb01
      · show periodicLatticeShift (periodicLatticeShift (iota v q0) ν) μ ∈ S.Om 0
        rw [iota_shift2, add_right_comm]; exact hΩ _ hb11
    · refine ⟨hΩ _ hb00, ?_⟩
      show periodicLatticeShift (iota v q0) ν ∈ S.Om 0
      rw [iota_shift]; exact hΩ _ hb01
  obtain ⟨sites, j, hq, hbonds⟩ := hcov.2 _ hall
  have e1 := hbonds (iota v q0, μ) (by unfold periodicPlaquetteBoundaryEdges; simp)
  have e2 := hbonds (periodicLatticeShift (iota v q0) μ, ν) (by unfold periodicPlaquetteBoundaryEdges; simp)
  have e3 := hbonds (periodicLatticeShift (iota v q0) ν, μ) (by unfold periodicPlaquetteBoundaryEdges; simp)
  have e4 := hbonds (iota v q0, ν) (by unfold periodicPlaquetteBoundaryEdges; simp)
  obtain ⟨h00, h10⟩ := e1
  obtain ⟨-, h11⟩ := e2
  obtain ⟨-, -⟩ := e3
  obtain ⟨-, h01⟩ := e4
  simp only [iota_shift] at h10 h01
  have h11' : iota v (q0 + ev μ + ev ν) ∈ sites := by
    have := h11
    simp only [iota_shift2] at this
    exact this
  have hjm : m ≤ j := by
    rcases (hY q0 hb00).2 with h0 | hmem
    · omega
    · have := cubeIndex_ge_pred hS hq h00 hmem
      omega
  have hC := cube_blockClosedAC hS hell hM hmk hq hjm
  refine ⟨sites, j, hq, hjm, fun p hpμ hpν hpσ => ?_⟩
  exact slab_sub hs hC hv (fun μ' => hS.2.2.1 m hmk μ') hσμ hσν hμν' hq0μ hq0ν
    (by rw [hq0σ]; exact hcσ) h00 h10 h01 h11' hpμ hpν (by
      have hc : cσ / (s : ℤ) = cσ := by
        rcases hcσ with h | h
        · rw [h]; simp
        · rw [h]; exact blk_m1 hs
      rw [hq0σ, hc]; exact hpσ)

theorem slab_cubeU {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S)
    (hcov : CoversOm0p ell M fc k S) (hell : 2 ≤ ell) (hM : 0 < M) {m : ℕ} (hmk : m ≤ k)
    {v : PeriodicLatticeSite L}
    (hv : ∀ μ, (v μ).val % bigSide M ell m = 0)
    (hY : ∀ p ∈ BoxS (bigSide M ell m), iota v p ∈ S.Om 0 ∧ (m = 0 ∨ iota v p ∈ S.Om (m + 1))) :
    VertexCubesAC fc ell M k S m v := by
  intro σ b
  have hs : 0 < bigSide M ell m := bigSide_pos (by omega) hM m
  have key : ∀ (μ ν : Fin 3), μ < ν → σ ≠ μ → σ ≠ ν → ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ),
      IsClassCube ell M fc k S sites j ∧ m ≤ j ∧ ∀ p ∈ HSlab (bigSide M ell m) σ b, iota v p ∈ sites := by
    intro μ ν hμν h1 h2
    obtain ⟨sites, j, hq, hjm, hall⟩ := slab_cube_auxU hS hcov hell hM hmk hv hY hμν h1 h2
      (cσ := if b then 0 else -1) (by cases b <;> simp)
    refine ⟨sites, j, hq, hjm, fun p hp => hall p (hp.1 μ) (hp.1 ν) ?_⟩
    rcases hp with ⟨hb, hsp⟩
    cases b
    · have h' : p σ ≤ -1 := by
        rcases hsp with ⟨h, -⟩ | ⟨-, h⟩
        · exact absurd h (by simp)
        · exact h
      simp only [Bool.false_eq_true, if_false]
      exact blk_idx_neg hs (hb σ).1 (by omega)
    · have h' : 0 ≤ p σ := by
        rcases hsp with ⟨-, h⟩ | ⟨h, -⟩
        · exact h
        · exact absurd h (by simp)
      simp only [if_true]
      exact blk_idx_nonneg hs h' (hb σ).2
  fin_cases σ
  · exact key 1 2 (by decide) (by decide) (by decide)
  · exact key 0 2 (by decide) (by decide) (by decide)
  · exact key 0 1 (by decide) (by decide) (by decide)

theorem vertex_chart_of_towerU {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S)
    (hcov : CoversOm0p ell M fc k S) (hell : 2 ≤ ell) (hM : 0 < M) {m : ℕ} (hmk : m ≤ k)
    {v : PeriodicLatticeSite L}
    (hv : ∀ μ, (v μ).val % bigSide M ell m = 0)
    (hY : ∀ p ∈ BoxS (bigSide M ell m), iota v p ∈ S.Om 0 ∧ (m = 0 ∨ iota v p ∈ S.Om (m + 1)))
    {α₀ η : ℝ} (hη : 0 < η) (hα : 0 ≤ α₀) {U : LinkCfg L} (hP : PerCubeRegular2H ell M fc 12 k S α₀ η U)
    (hsm : (12 : ℝ) * M * α₀ * ((ell : ℝ) ^ m)⁻¹ + 12 * M * α₀ * (((ell : ℝ) ^ m)⁻¹) ^ 2 ≤ 1)
    {R' : ℕ} (hR' : 1 ≤ R') (hRs : R' + 3 ≤ bigSide M ell m) (hinj : Set.InjOn (iota v) (Box (R' + 3)))
    (ht12 : (12 : ℝ) * M * α₀ * ((ell : ℝ) ^ m)⁻¹ ≤ 2)
    (hsmall : (4 * cB 1152 5 + 1) * (3 * (R' : ℝ) + 2) ^ 2 *
      ((1 + 4 * ((12 : ℝ) * M * α₀ * ((ell : ℝ) ^ m)⁻¹)) * ((12 : ℝ) * M * α₀ * (((ell : ℝ) ^ m)⁻¹) ^ 2)
        + 43 * ((12 : ℝ) * M * α₀ * ((ell : ℝ) ^ m)⁻¹) ^ 2) ≤ 1) :
    ∃ gv : PeriodicLatticeSite L → SU2,
      GChart U gv (lift v (Box R'))
        (KT1 4 1152 * (3 * R' + 2) * ((1 + 4 * ((12 : ℝ) * M * α₀ * ((ell : ℝ) ^ m)⁻¹)) *
          ((12 : ℝ) * M * α₀ * (((ell : ℝ) ^ m)⁻¹) ^ 2) + 43 * ((12 : ℝ) * M * α₀ * ((ell : ℝ) ^ m)⁻¹) ^ 2))
        (KT2 4 1152 * ((1 + 4 * ((12 : ℝ) * M * α₀ * ((ell : ℝ) ^ m)⁻¹)) *
          ((12 : ℝ) * M * α₀ * (((ell : ℝ) ^ m)⁻¹) ^ 2) + 43 * ((12 : ℝ) * M * α₀ * ((ell : ℝ) ^ m)⁻¹) ^ 2)) := by
  have hell0 : 0 < ell := by omega
  have hc : (0 : ℝ) ≤ 12 * M * α₀ := by positivity
  have hcubes := slab_cubeU hS hcov hell hM hmk hv hY
  have h : ∀ (σ : Fin 3) (b : Bool), ∃ g : PeriodicLatticeSite L → SU2,
      GChart U g (lift v (Hraw R' σ b)) ((12 : ℝ) * M * α₀ * ((ell : ℝ) ^ m)⁻¹)
        ((1 + 4 * ((12 : ℝ) * M * α₀ * ((ell : ℝ) ^ m)⁻¹)) * ((12 : ℝ) * M * α₀ * (((ell : ℝ) ^ m)⁻¹) ^ 2)) := by
    intro σ b
    obtain ⟨sites, j, hq, hjm, hall⟩ := hcubes σ b
    have hinv : (((ell : ℝ) ^ j)⁻¹) ≤ ((ell : ℝ) ^ m)⁻¹ := by
      have h1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell0
      exact inv_anti₀ (by positivity) (pow_le_pow_right₀ h1 hjm)
    obtain ⟨hs1, ht1, ht2⟩ := cube_consts hc (by positivity) hinv hsm
    obtain ⟨g, hg⟩ := gchart_of_cubeH hη hP hq (by simpa [mul_assoc] using hs1) hell0 CubeFactor.pos
    refine ⟨g, hg.mono ?_ (by simpa [mul_assoc] using ht1) (by simpa [mul_assoc, pow_two] using ht2)⟩
    rintro _ ⟨p, hp, rfl⟩
    exact hall p (Hraw_sub_HSlab hRs σ b hp)
  choose g hg using h
  have ht1 : (0 : ℝ) ≤ (12 : ℝ) * M * α₀ * ((ell : ℝ) ^ m)⁻¹ := by positivity
  have ht2 : (0 : ℝ) ≤ (1 + 4 * ((12 : ℝ) * M * α₀ * ((ell : ℝ) ^ m)⁻¹)) * ((12 : ℝ) * M * α₀ * (((ell : ℝ) ^ m)⁻¹) ^ 2) := by
    positivity
  obtain ⟨gv, hgv, -⟩ := gchart_at_bad_vertex v hR' hinj g ht1 ht12 ht2 hg hsmall
  exact ⟨gv, hgv⟩

end AdalyFormal.M2GlueGeo

#print axioms AdalyFormal.M2GlueGeo.slab_cube_auxU
#print axioms AdalyFormal.M2GlueGeo.slab_cubeU
#print axioms AdalyFormal.M2GlueGeo.vertex_chart_of_towerU
