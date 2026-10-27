import GE6
import ZT5C

/-!
# GE8 -- item (e): what `Lambda != empty` does and does not give for non-wrapping (m2_gluegeo, 2026-10-15)

* `nonwrap_of_thick`: if every unit side satisfies `2 rho + 6 < Lu_mu + 1` then `iota v` is injective on `Box (rho ell^j + 3)` for all
  `j <= k` (fine side `(Lu_mu + 1) ell^k`).
* `lambda_ball_in_Omk` / `lambda_sum_sides`: `LambdaOK` puts the `R M` ball of `Lambda` (unit metric) in `Omega_k`; if `Omega_k` is not the
  whole torus this only gives `2 R M < sum_mu (Lu_mu + 1)` (the SUM of the sides -- one side may be small).
* `not_injOn_of_small`: `iota v` is not injective on `Box r` when `L_0 + 1 <= 2 r`.
* `thin_torus_counterexample`: for `ell | M`, `k >= 1`, `2 <= n <= 12` and EVERY `R`: the torus `Lu_mu + 1 = n M` is `TorusOK`; the full tower
  `Sk` (`Omega_j` = torus for `j <= k`) is `Admissible`, `CoversOm0p ell M 12 k`, `Lambda = univ` is `LambdaOK2` with `Lambda' != empty`; and
  `iota v` is injective on NO `Box r` with `n M ell^k <= 2 r` (e.g. `r = 7 M ell^k`).  So `Lambda != empty` does not give non-wrap.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M2GlueGeo

open AdalyFormal.Target.ClayStatement AdalyFormal.M2Glue3
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG
open AdalyFormal.StatementLaneR8 (pdist_comm pdist_triangle)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf)

theorem nonwrap_of_thick {Lu Lf : PeriodicLatticeExtent} {ell k j ρ : ℕ} (hell : 0 < ell) (hjk : j ≤ k)
    (hf : ∀ μ, Lf μ + 1 = (Lu μ + 1) * ell ^ k) (hthick : ∀ μ, 2 * ρ + 6 < Lu μ + 1)
    (v : PeriodicLatticeSite Lf) : Set.InjOn (iota v) (Box (ρ * ell ^ j + 3)) := by
  apply iota_injOn
  intro μ
  rw [hf μ]
  have h1 : ell ^ j ≤ ell ^ k := Nat.pow_le_pow_right hell hjk
  have h2 : 1 ≤ ell ^ k := Nat.one_le_pow _ _ hell
  have h3 := hthick μ
  have h4 : (2 * ρ + 7) * ell ^ k ≤ (Lu μ + 1) * ell ^ k := Nat.mul_le_mul_right _ (by omega)
  have h5 : ρ * ell ^ j ≤ ρ * ell ^ k := Nat.mul_le_mul_left _ h1
  nlinarith

theorem lambda_ball_in_Omk {Lu Lf : PeriodicLatticeExtent} {ell M R k : ℕ} {S : Tower Lf}
    {Lam : Set (PeriodicLatticeSite Lu)} (h : LambdaOK ell M R k S Lam) :
    ∃ emb : PeriodicLatticeSite Lu → PeriodicLatticeSite Lf, (∀ y μ, (emb y μ).val = ell ^ k * (y μ).val) ∧
      ∀ y ∈ Lam, ∀ y' : PeriodicLatticeSite Lu, pdist y y' ≤ R * M → emb y' ∈ S.Om k := by
  obtain ⟨-, emb, hemb, -, hcol⟩ := h
  refine ⟨emb, hemb, fun y hy y' hd => ?_⟩
  by_contra hc
  have := hcol y hy y' hc
  omega

theorem pcd_two_le (N a b : ℕ) : 2 * pcd N a b ≤ N := by
  unfold pcd
  split_ifs <;> omega

theorem pdist_two_le {L : PeriodicLatticeExtent} (x y : PeriodicLatticeSite L) :
    2 * pdist x y ≤ ∑ μ : Fin 3, (L μ + 1) := by
  unfold pdist
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun μ _ => pcd_two_le _ _ _)

/-- if `Omega_k` is not the whole torus (some embedded site is outside) and `Lambda != empty`, the SUM of the unit sides exceeds `2 R M`. -/
theorem lambda_sum_sides {Lu Lf : PeriodicLatticeExtent} {ell M R k : ℕ} {S : Tower Lf}
    {Lam : Set (PeriodicLatticeSite Lu)} (h : LambdaOK ell M R k S Lam) {y : PeriodicLatticeSite Lu} (hy : y ∈ Lam)
    (hout : ∃ (emb : PeriodicLatticeSite Lu → PeriodicLatticeSite Lf), (∀ y μ, (emb y μ).val = ell ^ k * (y μ).val) ∧
      ∃ y', emb y' ∉ S.Om k) :
    2 * (R * M) < ∑ μ : Fin 3, (Lu μ + 1) := by
  obtain ⟨-, emb, hemb, -, hcol⟩ := h
  obtain ⟨emb', hemb', y', hy'⟩ := hout
  have hE : emb' = emb := by
    funext z μ; apply Fin.ext; rw [hemb' z μ, hemb z μ]
  subst hE
  have := hcol y hy y' hy'
  have h2 := pdist_two_le y y'
  omega

theorem not_injOn_of_small {L : PeriodicLatticeExtent} (v : PeriodicLatticeSite L) {r : ℕ} (hr : L 0 + 1 ≤ 2 * r) :
    ¬ Set.InjOn (iota v) (Box r) := by
  intro hinj
  set N := L 0 + 1 with hN
  let p : Z3 := fun i => if i = 0 then ((N - N / 2 : ℕ) : ℤ) else 0
  let p' : Z3 := fun i => if i = 0 then -((N / 2 : ℕ) : ℤ) else 0
  have hp : p ∈ Box r := by
    intro i
    by_cases hi : i = 0
    · simp only [p, hi, if_true]; rw [abs_of_nonneg (by positivity)]; exact_mod_cast (by omega : N - N / 2 ≤ r)
    · simp [p, hi]
  have hp' : p' ∈ Box r := by
    intro i
    by_cases hi : i = 0
    · simp only [p', hi, if_true]; rw [abs_neg, abs_of_nonneg (by positivity)]; exact_mod_cast (by omega : N / 2 ≤ r)
    · simp [p', hi]
  have heq : iota v p = iota v p' := by
    funext μ
    by_cases hμ : μ = 0
    · subst hμ
      unfold iota
      congr 1
      have h3 : (((p 0 : ℤ)) : ZMod (L 0 + 1)) = (((p' 0 : ℤ)) : ZMod (L 0 + 1)) := by
        rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
        refine ⟨-1, ?_⟩
        simp only [p, p', if_true]
        have : (N - N / 2 : ℕ) + N / 2 = N := by omega
        have h' : (((N - N / 2 : ℕ) : ℤ)) + ((N / 2 : ℕ) : ℤ) = (N : ℤ) := by exact_mod_cast this
        have hNc : ((L 0 + 1 : ℕ) : ℤ) = (N : ℤ) := by rw [hN]
        rw [hNc]
        linarith
      exact h3
    · simp [iota, p, p', hμ]
  have := hinj hp hp' heq
  have h0 := congrFun this 0
  simp only [p, p', if_true] at h0
  have : (0 : ℤ) < N := by positivity
  have h1 : (0 : ℤ) ≤ ((N - N / 2 : ℕ) : ℤ) := by positivity
  have h2 : (0 : ℤ) ≤ ((N / 2 : ℕ) : ℤ) := by positivity
  have h4 : ((N - N / 2 : ℕ) : ℤ) + ((N / 2 : ℕ) : ℤ) = N := by
    have : (N - N / 2 : ℕ) + N / 2 = N := by omega
    exact_mod_cast this
  have h5 : (0 : ℤ) < N := by exact_mod_cast (by omega : 0 < N)
  linarith

theorem thin_torus_counterexample {ell M k n : ℕ} (hell : 2 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hk : 1 ≤ k)
    (hn2 : 2 ≤ n) (hn12 : n ≤ 12) (R : ℕ) :
    ∃ Lu : PeriodicLatticeExtent, TorusOK ell M Lu ∧
      Admissible ell M R k (Sk (scaleUp ell k Lu) k) ∧ CoversOm0p ell M 12 k (Sk (scaleUp ell k Lu) k) ∧
      LambdaOK2 (Lu := Lu) (Lf := scaleUp ell k Lu) ell M R k (Sk (scaleUp ell k Lu) k) Set.univ ∧
      (LamPrime ell (Set.univ : Set (PeriodicLatticeSite Lu))).Nonempty ∧
      (∀ μ, Lu μ + 1 = n * M) ∧
      ∀ (v : PeriodicLatticeSite (scaleUp ell k Lu)) (r : ℕ), n * M * ell ^ k ≤ 2 * r → ¬ Set.InjOn (iota v) (Box r) := by
  obtain ⟨c, hc⟩ := hdvd
  have hnM : 0 < n * M := Nat.mul_pos (by omega) hM
  have hLu : ∀ μ : Fin 3, ((fun _ : Fin 3 => n * M - 1) μ) + 1 = n * M := fun μ => by simp only; omega
  have hf : ∀ μ, scaleUp ell k (fun _ : Fin 3 => n * M - 1) μ + 1 = (n * M) * ell ^ k := by
    intro μ
    have : 0 < n * M * ell ^ k := Nat.mul_pos hnM (pow_pos (by omega) k)
    unfold scaleUp
    simp only
    rw [show n * M - 1 + 1 = n * M by omega]
    omega
  have hf' : ∀ μ, scaleUp ell k (fun _ : Fin 3 => n * M - 1) μ + 1 = ((fun _ : Fin 3 => n * M - 1) μ + 1) * ell ^ k := by
    intro μ; rw [hf μ, hLu μ]
  have hdiv : ∀ j : ℕ, j ≤ k → ∀ μ : Fin 3, M * ell ^ j ∣ scaleUp ell k (fun _ : Fin 3 => n * M - 1) μ + 1 := by
    intro j hj μ
    rw [hf μ]
    obtain ⟨d, hd⟩ : ell ^ j ∣ ell ^ k := pow_dvd_pow ell hj
    exact ⟨n * d, by rw [hd]; ring⟩
  have hLambda := SkG_lambdaOK (Lu := fun _ : Fin 3 => n * M - 1) (Lf := scaleUp ell k (fun _ : Fin 3 => n * M - 1))
    ell M R k hf' (by omega)
  refine ⟨fun _ => n * M - 1, ⟨fun μ => ?_, fun μ => ?_, fun μ => ?_⟩, SkG_admissible ell M R k hk hdiv,
    SkG_coversp ell M k 12 (by omega) hM (by norm_num) (fun μ => ?_), ⟨hLambda, lamBlockSum_univ ell (by omega)⟩, ?_, hLu, ?_⟩
  · rw [hLu μ, hc]; exact ⟨n * c, by ring⟩
  · rw [hLu μ]
    have hcpos : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · rw [h0] at hc; omega
      · exact h0
    have hle : ell ≤ M := by rw [hc]; exact Nat.le_mul_of_pos_right ell hcpos
    nlinarith
  · rw [hLu μ]; exact Dvd.intro_left n rfl
  · rw [hf μ]
    have h1 : n * M * ell ^ k ≤ 12 * (M * ell ^ k) := by
      have : n * (M * ell ^ k) ≤ 12 * (M * ell ^ k) := Nat.mul_le_mul_right _ hn12
      linarith [mul_assoc n M (ell ^ k)]
    exact h1
  · exact (lamBlockSum_univ ell (by omega)).lamPrime_nonempty ⟨fun _ => ⟨0, Nat.succ_pos _⟩, Set.mem_univ _⟩
  · intro v r hr
    apply not_injOn_of_small v
    rw [hf 0]; exact hr

end AdalyFormal.M2GlueGeo
