import GE7
import CovD

/-!
# GE9 -- the third region type is REALISED (m2_gluegeo, 2026-10-15)

`corner_bad_vertex`: for every even `M` and every `R >= 24` there are a torus (`TorusOK`), an admissible tower of height `1`
(`ell = 2`) with `CoversOm0p 2 M 12 1`, a `Lambda` with `LambdaOK2` and `Lambda' != empty` (all as in `corner_nonempty`, CovD), and a grid
vertex `v` (on the `M`-grid) such that
* `BadVertex`: the box `iota v '' [-M, M)^3` lies in NO class cube (`gt_no_cube_of`, CovC);
* `VertexCubes`: all six half-slab cubes at `v` exist (`slab_cube`, anchor `v in Omega_1`).
Also: `good_overlap` (adjacent good vertices share the tube in both cubes).
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.M2GlueGeo

open AdalyFormal.Target.ClayStatement AdalyFormal.M2Glue3
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.M2Coverage AdalyFormal.StatementLaneG

/-- the overlap of the boxes of two adjacent good vertices is covered by both cubes (band of width `s`). -/
theorem good_overlap {L : PeriodicLatticeExtent} {ell M k : ℕ} {S : Tower L} {s : ℕ} {v v' : PeriodicLatticeSite L}
    {C C' : Set (PeriodicLatticeSite L)} (hC : ∀ p ∈ BoxS s, iota v p ∈ C) (hC' : ∀ p ∈ BoxS s, iota v' p ∈ C')
    {a : Z3} (ha : v' = iota v a) {q : Z3} (hq : q ∈ BoxS s) (hqa : a + q ∈ BoxS s) :
    iota v' q ∈ C ∧ iota v' q ∈ C' := by
  refine ⟨?_, hC' q hq⟩
  rw [ha, iota_iota]; exact hC _ hqa

theorem corner_bad_vertex {M R : ℕ} (hM : 0 < M) (hM2 : 2 ∣ M) (hR : 24 ≤ R) :
    ∃ Lu : PeriodicLatticeExtent, TorusOK 2 M Lu ∧
    ∃ S : Tower (scaleUp 2 1 Lu), Admissible 2 M R 1 S ∧ CoversOm0p 2 M 12 1 S ∧
    ∃ Lam : Set (PeriodicLatticeSite Lu), LambdaOK2 (Lf := scaleUp 2 1 Lu) 2 M R 1 S Lam ∧
      (LamPrime 2 Lam).Nonempty ∧
    ∃ v : PeriodicLatticeSite (scaleUp 2 1 Lu), (∀ μ, (v μ).val % bigSide M 2 0 = 0) ∧
      BadVertex 2 M 1 S (bigSide M 2 0) v ∧ VertexCubes 2 M 1 S 0 v := by
  set q := R + 12 with hqdef
  set n := 2 * q + 2 with hndef
  have hq : 12 ≤ q := by omega
  have hn25 : 25 ≤ n := by omega
  have hL := fine_val (n := n) (q := q) hM hM2 hq hndef
  have hadm := gt_admissible (L := scaleUp 2 1 (LuQ n M)) hM hn25 hL (by omega : 2 ≤ R)
  have hcov := gt_coversp (L := scaleUp 2 1 (LuQ n M)) hM hn25 hL (by omega : 18 ≤ R)
  have hLam := lamQ_ok (n := n) hM hM2 hq hndef R (by omega)
  refine ⟨LuQ n M, luq_torusOK (n := n) hM hM2 hq hndef, GT _ n M, hadm, hcov, LamQ M q, hLam, ?_, ?_⟩
  · apply LamBlockSum.lamPrime_nonempty hLam.2
    have hqn : q * M + M ≤ n * M := by
      have : (q + 1) * M ≤ n * M := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, one_mul] at this; exact this
    refine ⟨fun σ => ⟨q * M, by have := luq_val (n := n) hM hM2 hq hndef σ; omega⟩, ?_⟩
    intro σ
    show q * M / M = q
    exact Nat.mul_div_cancel q hM
  · have hMn : M < 2 * n * M := by nlinarith
    let v : PeriodicLatticeSite (scaleUp 2 1 (LuQ n M)) := fun μ => ⟨M, by rw [hL μ]; exact hMn⟩
    have hvval : ∀ μ, (v μ).val = M := fun μ => rfl
    have hvg : ∀ μ, (v μ).val % bigSide M 2 0 = 0 := by
      intro μ; rw [hvval, bs0]; exact Nat.mod_self M
    have hiota : ∀ (c : ℤ), -1 ≤ c → c ≤ 0 → ∀ μ, ((iota v (fun _ => c) μ).val : ℤ) = M + c := by
      intro c h1 h2 μ
      rw [iota_val_int, hvval, hL μ]
      have : ((2 * n * M : ℕ) : ℤ) = 2 * n * M := by push_cast; ring
      have hMz : (1 : ℤ) ≤ M := by exact_mod_cast hM
      have hbig : (M : ℤ) < 2 * n * M := by exact_mod_cast hMn
      rw [Int.emod_eq_of_lt (by omega) (by push_cast; omega)]
    have hbox : ∀ c : ℤ, -1 ≤ c → c ≤ 0 → (fun _ : Fin 3 => c) ∈ BoxS (bigSide M 2 0) := by
      intro c h1 h2 i
      rw [bs0]
      have hMz : (1 : ℤ) ≤ M := by exact_mod_cast hM
      constructor <;> (dsimp only; omega)
    refine ⟨v, hvg, ?_, ?_⟩
    · rintro ⟨sites, j, hq', hall⟩
      refine gt_no_cube_of hM hn25 hL sites j hq' (fun σ => iota v (fun _ => -1)) (fun σ => iota v (fun _ => 0))
        (fun σ => ⟨hall _ (hbox (-1) le_rfl (by norm_num)), ?_⟩)
        (fun σ => ⟨hall _ (hbox 0 (by norm_num) le_rfl), ?_⟩)
      · have h := hiota (-1) le_rfl (by norm_num) σ
        apply Nat.div_eq_of_lt
        have hMz : (1 : ℤ) ≤ M := by exact_mod_cast hM
        omega
      · have h := hiota 0 (by norm_num) le_rfl σ
        have : (iota v (fun _ => 0) σ).val = M := by omega
        rw [this]; exact Nat.div_self hM
    · have hx0 : v ∈ (GT (scaleUp 2 1 (LuQ n M)) n M).Om (0 + 1) := by
        rw [gt_om1]
        intro hc
        unfold GH holeQ at hc
        simp only [hvval] at hc
        have h0 : M / (M * 2) = 0 := Nat.div_eq_of_lt (by omega)
        rw [h0] at hc
        omega
      have hnear : ∀ p ∈ BoxS (bigSide M 2 0), pdist (iota v p) v + 18 * bigSide M 2 0 ≤ R * bigSide M 2 0 := by
        intro p hp
        have h6 := AdalyFormal.M2Bridge.pdist_lt_three_s' (iota_mem_box (v := v) hp)
          (iota_mem_box (v := v) (show (fun _ : Fin 3 => (0 : ℤ)) ∈ BoxS (bigSide M 2 0) from by
            intro i; rw [bs0]; have : (1 : ℤ) ≤ M := by exact_mod_cast hM
            constructor <;> (dsimp only; omega)))
        have h0 : iota v (fun _ => (0 : ℤ)) = v := by
          funext μ; apply Fin.ext
          have := hiota 0 (by norm_num) le_rfl μ
          have h2 : ((iota v (fun _ => (0 : ℤ)) μ).val : ℤ) = M := by simpa using this
          rw [hvval]; exact_mod_cast h2
        rw [h0] at h6
        rw [bs0] at h6 ⊢
        nlinarith
      exact slab_cube hadm hcov (by norm_num) hM (by norm_num) hx0 hvg hnear

end AdalyFormal.M2GlueGeo
