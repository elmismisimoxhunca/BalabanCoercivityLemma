import CovC

/-!
# CovD -- the corner tower with a NONEMPTY `Λ` (`LambdaOK2`), for every `R ≥ 18` and every even `M`
(m2_coverage, 2026-10-14)

Unit torus `n·M` per direction, `n = 2q + 2`, `q = R + 12`; fine torus `2nM` (`ell = 2`, `k = 1`); tower `GT`;
`Λ` = the unit big block `{y | y_σ / M = q for all σ}`.  Then (`corner_nonempty`):
`TorusOK`, `Admissible 2 M R 1`, `CoversOm0p 2 M 12 1` (sites and plaquettes), `LambdaOK2 2 M R 1` with `Λ' ≠ ∅`,
and the twelve edges of the unit cell at `(M-1,M-1,M-1)` (a site of `Ω₀`) carry no clause-3 premise in any class cube.
`Ω₀` is the whole torus, so these bonds are in `BothIn Ω₀`, the set `genForm_congr_outside` (r8, ZR8Data:173) lets the
inequality read.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.M2Coverage

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)

theorem div_eq_of_bounds {v q M : ℕ} (hM : 0 < M) (h1 : q * M ≤ v) (h2 : v < q * M + M) : v / M = q := by
  have a := (Nat.le_div_iff_mul_le hM).2 h1
  have b : v / M < q + 1 := (Nat.div_lt_iff_lt_mul hM).2 (by rw [Nat.add_mul, one_mul]; exact h2)
  omega

theorem bounds_of_div {v q M : ℕ} (hM : 0 < M) (h : v / M = q) : q * M ≤ v ∧ v < q * M + M := by
  refine ⟨(Nat.le_div_iff_mul_le hM).1 (le_of_eq h.symm), ?_⟩
  have := (Nat.div_lt_iff_lt_mul hM).1 (show v / M < q + 1 by omega)
  rw [Nat.add_mul, one_mul] at this; exact this

theorem pcd_ge (T a b D : ℕ) (h1 : b + D ≤ a) (h3 : D + a ≤ T + b) : D ≤ pcd T a b := by
  unfold pcd
  rw [Nat.min_def]
  split_ifs <;> omega

def LuQ (n M : ℕ) : PeriodicLatticeExtent := fun _ => n * M - 1

def LamQ {Lu : PeriodicLatticeExtent} (M q : ℕ) : Set (PeriodicLatticeSite Lu) := {y | ∀ σ, (y σ).val / M = q}

/-- the embedding `y ↦ ell^k y = 2 y` (`k = 1`). -/
def embU {Lu : PeriodicLatticeExtent} (y : PeriodicLatticeSite Lu) : PeriodicLatticeSite (scaleUp 2 1 Lu) :=
  fun μ => ⟨2 * (y μ).val, by
    have h1 := (y μ).isLt
    unfold scaleUp; rw [pow_one]
    omega⟩

theorem embU_val {Lu : PeriodicLatticeExtent} (y : PeriodicLatticeSite Lu) (μ : Fin 3) : (embU y μ).val = 2 * (y μ).val := rfl

section lam
variable {n M q : ℕ} (hM : 0 < M) (hM2 : 2 ∣ M) (hq : 12 ≤ q) (hn : n = 2 * q + 2)
include hM hM2 hq hn

theorem luq_val (μ : Fin 3) : LuQ n M μ + 1 = n * M := by
  unfold LuQ
  have : 0 < n * M := Nat.mul_pos (by omega) hM
  omega

theorem fine_val (μ : Fin 3) : scaleUp 2 1 (LuQ n M) μ + 1 = 2 * n * M := by
  unfold scaleUp
  rw [luq_val hM hM2 hq hn μ]
  have : 0 < n * M := Nat.mul_pos (by omega) hM
  rw [show 2 * n * M = n * M * 2 ^ 1 by ring, pow_one]
  omega

theorem luq_torusOK : TorusOK 2 M (LuQ n M) := by
  refine ⟨fun μ => ?_, fun μ => ?_, fun μ => ?_⟩ <;> rw [luq_val hM hM2 hq hn μ]
  · exact Dvd.dvd.mul_left hM2 n
  · have : 26 ≤ n := by omega
    have : 26 * 1 ≤ n * M := Nat.mul_le_mul this hM
    omega
  · exact Dvd.intro_left n rfl

omit hM2 hq hn in
theorem col_emb (v : ℕ) : (2 * v) / (M * 2) = v / M := by
  rw [show M * 2 = 2 * M by ring, Nat.mul_div_mul_left v M (by norm_num)]

theorem lamQ_ok (R : ℕ) (hR : R + 2 ≤ 2 * q) :
    LambdaOK2 (Lu := LuQ n M) (Lf := scaleUp 2 1 (LuQ n M)) 2 M R 1 (GT (scaleUp 2 1 (LuQ n M)) n M) (LamQ M q) := by
  have hqM : q * M + M ≤ n * M := by
    have : (q + 1) * M ≤ n * M := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, one_mul] at this; exact this
  refine ⟨⟨?_, embU, fun y μ => by rw [embU_val, pow_one], ?_, ?_⟩, ?_⟩
  · -- BlockClosed M Λ
    intro x hx y hy σ
    rw [hy σ]; exact hx σ
  · -- Λ ⊆ Λ_k
    intro y hy
    rw [gt_om1]
    show ¬ holeQ n ((embU y 0).val / (M * 2)) ((embU y 1).val / (M * 2)) ((embU y 2).val / (M * 2))
    rw [embU_val, embU_val, embU_val, col_emb hM, col_emb hM, col_emb hM, hy 0, hy 1, hy 2]
    intro hc; unfold holeQ at hc; omega
  · -- the `R M` collar
    intro y hy y' hy'
    rw [gt_om1] at hy'
    simp only [Set.mem_setOf_eq, not_not] at hy'
    have hc : holeQ n ((y' 0).val / M) ((y' 1).val / M) ((y' 2).val / M) := by
      have := hy'
      unfold GH at this
      rw [embU_val, embU_val, embU_val, col_emb hM, col_emb hM, col_emb hM] at this
      exact this
    have hb : ∀ σ, q * M ≤ (y σ).val ∧ (y σ).val < q * M + M := fun σ => bounds_of_div hM (hy σ)
    have hsm : ∀ σ, (y' σ).val / M = 0 → (y' σ).val < M := fun σ h => by
      have := (bounds_of_div hM h).2; omega
    have hlt : ∀ σ, (y σ).val < n * M := fun σ => by
      have := (y σ).isLt; have := luq_val hM hM2 hq hn σ; omega
    have hRM : R * M + 2 * M ≤ 2 * (q * M) := by
      have := Nat.mul_le_mul_right M hR
      rw [Nat.add_mul, show 2 * q * M = 2 * (q * M) by ring] at this; exact this
    have hnM : n * M = 2 * (q * M) + 2 * M := by rw [hn]; ring
    have hp : ∀ σ, (y' σ).val / M = 0 → (q * M) - M + 1 ≤ pcd (LuQ n M σ + 1) (y σ).val (y' σ).val := by
      intro σ h0
      have h1 := hsm σ h0
      have h2 := hb σ
      have h3 := luq_val hM hM2 hq hn σ
      apply pcd_ge
      · omega
      · omega
    unfold pdist
    rw [Fin.sum_univ_three]
    have hqM1 : M ≤ q * M := by
      have := Nat.mul_le_mul_right M (show 1 ≤ q by omega); rw [one_mul] at this; exact this
    unfold holeQ at hc
    rcases hc with ⟨-, h1, h2⟩ | ⟨h0, -, h2⟩ | ⟨h0, h1, -⟩
    · have a := hp 1 h1; have b := hp 2 h2; omega
    · have a := hp 0 h0; have b := hp 2 h2; omega
    · have a := hp 0 h0; have b := hp 1 h1; omega
  · -- Λ = B(Λ')
    intro x hx
    obtain ⟨m, hm⟩ := hM2
    have hlt : ∀ σ, 2 * ((x σ).val / 2) < LuQ n M σ + 1 := fun σ => by
      have := (x σ).isLt; omega
    refine ⟨fun σ => ⟨2 * ((x σ).val / 2), hlt σ⟩, ⟨?_, ?_⟩, ?_⟩
    · rw [mem_CoarseLattice]; intro μ; show 2 * ((x μ).val / 2) % 2 = 0; omega
    · intro x' hx'
      rw [mem_blockOf] at hx'
      intro σ
      have h1 := hx' σ
      have h2 := bounds_of_div hM (hx σ)
      simp only at h1
      have hqm : q * M = 2 * (q * m) := by rw [hm]; ring
      apply div_eq_of_bounds hM <;> omega
    · rw [mem_blockOf]
      intro σ
      simp only
      omega

end lam

/-- **the corner with a nonempty `Λ`**: for every even `M ≥ 2` and every `R ≥ 18` there is a unit torus, an admissible
tower of height `1` with `ell = 2` satisfying the headline's coverage hypothesis at cube factor `12`, a `Λ` with
`LambdaOK2` and `Λ' ≠ ∅`, and a site `x` of `Ω₀` such that for each of the twelve edges `(x', μ)` of the unit cell at `x`
(`x'_μ = x_μ`, `x'_ν ∈ {x_ν, x_ν + 1}`) no class cube contains the `ddA` stencil of `(x', μ)`. -/
theorem corner_nonempty {M R : ℕ} (hM : 0 < M) (hM2 : 2 ∣ M) (hR : 18 ≤ R) :
    ∃ Lu : PeriodicLatticeExtent, TorusOK 2 M Lu ∧
    ∃ S : Tower (scaleUp 2 1 Lu), Admissible 2 M R 1 S ∧ CoversOm0p 2 M 12 1 S ∧
    ∃ Lam : Set (PeriodicLatticeSite Lu), LambdaOK2 (Lf := scaleUp 2 1 Lu) 2 M R 1 S Lam ∧
      (LamPrime 2 Lam).Nonempty ∧
    ∃ x : PeriodicLatticeSite (scaleUp 2 1 Lu), x ∈ S.Om 0 ∧
      ∀ (x' : PeriodicLatticeSite (scaleUp 2 1 Lu)) (μ : Fin 3), (x' μ).val = (x μ).val →
        (∀ ν, ν ≠ μ → (x' ν).val = (x ν).val ∨ (x' ν).val = (x ν).val + 1) →
        ¬ ∃ (sites : Set (PeriodicLatticeSite (scaleUp 2 1 Lu))) (i : ℕ), IsClassCube 2 M 12 1 S sites i ∧
          ∀ ν : Fin 3, ν ≠ μ → CurlReads sites (periodicLatticeShiftBack x' ν) ν μ ∧ CurlReads sites x' ν μ := by
  set q := R + 12 with hqdef
  set n := 2 * q + 2 with hndef
  have hq : 12 ≤ q := by omega
  have hn25 : 25 ≤ n := by omega
  have hL := fine_val (n := n) (q := q) hM hM2 hq hndef
  refine ⟨LuQ n M, luq_torusOK (n := n) hM hM2 hq hndef, GT _ n M, gt_admissible hM hn25 hL (by omega),
    gt_coversp hM hn25 hL hR, LamQ M q, lamQ_ok (n := n) hM hM2 hq hndef R (by omega), ?_, ?_⟩
  · apply LamBlockSum.lamPrime_nonempty (lamQ_ok (n := n) hM hM2 hq hndef R (by omega)).2
    have hqn : q * M + M ≤ n * M := by
      have : (q + 1) * M ≤ n * M := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, one_mul] at this; exact this
    refine ⟨fun σ => ⟨q * M, by have := luq_val (n := n) hM hM2 hq hndef σ; omega⟩, ?_⟩
    intro σ
    show q * M / M = q
    exact Nat.mul_div_cancel q hM
  · have hx : M - 1 < scaleUp 2 1 (LuQ n M) 0 + 1 := by
      rw [hL]; have : M ≤ 2 * n * M := Nat.le_mul_of_pos_left _ (by omega)
      omega
    refine ⟨fun σ => ⟨M - 1, by rw [hL σ]; rw [hL 0] at hx; exact hx⟩, by rw [gt_om0]; trivial, ?_⟩
    intro x' μ hμ hν
    refine gt_edge_no_cube hM hn25 hL x' μ hμ (fun ν hν' => ?_)
    rcases hν ν hν' with h | h
    · left; exact h
    · right; rw [h]; show M - 1 + 1 = M; omega

end AdalyFormal.M2Coverage
