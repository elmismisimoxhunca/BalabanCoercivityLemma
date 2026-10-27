import GE3

/-!
# GE4 -- `slab_cube`: the six half-slab cubes at a grid vertex (m2_gluegeo, 2026-10-15)

Hypotheses: `Admissible ell M R k S`, `CoversOm0p ell M 12 k S`, `2 <= ell`, `0 < M`, `m <= k`, `s = M ell^m`, a grid vertex `v`
(`(v mu).val % s = 0`), an anchor `x0 in Omega_{m+1}` with `pdist (iota v p) x0 + 18 s <= R s` for every `p` in the box `[-s, s)^3`.
Conclusion, for every direction `sigma` and side `b`: a class cube containing `iota v '' HSlab s sigma b`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M2GlueGeo

open AdalyFormal.Target.ClayStatement AdalyFormal.M2Glue3
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (pdist_comm pdist_triangle)
open AdalyFormal.M1 (om_anti)

variable {L : PeriodicLatticeExtent}

theorem slab_cube_aux {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S)
    (hcov : CoversOm0p ell M 12 k S) (hell : 2 ≤ ell) (hM : 0 < M) {m : ℕ} (hmk : m ≤ k)
    {x0 : PeriodicLatticeSite L} (hx0 : x0 ∈ S.Om (m + 1)) {v : PeriodicLatticeSite L}
    (hv : ∀ μ, (v μ).val % bigSide M ell m = 0)
    (hnear : ∀ p ∈ BoxS (bigSide M ell m), pdist (iota v p) x0 + 18 * bigSide M ell m ≤ R * bigSide M ell m)
    {μ ν σ : Fin 3} (hμν : μ < ν) (hσμ : σ ≠ μ) (hσν : σ ≠ ν) {cσ : ℤ} (hcσ : cσ = 0 ∨ cσ = -1) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube ell M 12 k S sites j ∧ m ≤ j ∧
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
  have hΩ : ∀ p ∈ BoxS s, iota v p ∈ S.Om 0 := by
    intro p hp
    have h : pdist (iota v p) x0 + 18 * s ≤ R * s := hnear p hp
    refine om_le_zero hS m (mem_om_of_near hS hmk hx0 ?_)
    show pdist (iota v p) x0 < R * s
    have : 0 < s := hs
    omega
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
  have hjm : m ≤ j := cube_scale hS hell hM hmk hq h00 hx0 (hnear q0 hb00)
  have hC := cube_blockClosed hS hell hM hmk hq hjm
  refine ⟨sites, j, hq, hjm, fun p hpμ hpν hpσ => ?_⟩
  exact slab_sub hs hC hv (fun μ' => hS.2.2.1 m hmk μ') hσμ hσν hμν' hq0μ hq0ν
    (by rw [hq0σ]; exact hcσ) h00 h10 h01 h11' hpμ hpν (by
      have hc : cσ / (s : ℤ) = cσ := by
        rcases hcσ with h | h
        · rw [h]; simp
        · rw [h]; exact blk_m1 hs
      rw [hq0σ, hc]; exact hpσ)

end AdalyFormal.M2GlueGeo
