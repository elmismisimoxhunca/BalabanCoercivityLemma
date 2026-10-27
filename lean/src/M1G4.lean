import M1G3

/-!
# M1G4 -- G4 `patch_partition`: a multi-piece normalised bump partition subordinate to the G3 patches (M1 lane B, 2026-10-13)

For a patch `(j, w)` (`IsPatch`, coarse spacing `G_j = κ M ell^j`) the tent `bump = clamp₀¹((c G_j − |w − y|)/((c − 4) G_j))` is `1` on the
core (`|w−y| ≤ 4 G_j`), `0` off the patch, Lipschitz `1/((c−4) G_j)` in `ℓ¹`.  `psi p y` = the bump of `p` if `p` is a patch index, else `0`;
`hpart p y = psi p y / √(Σ_q psi q y²)`.
* `hpart_nonneg`, `hpart_supp` (support inside the patch), `sum_hpart_sq` (`Σ_p hpart p y² = 1` on `Ω₀`, from `patch_cover`);
* `hpart_grad_sq` (the IMS input): for a bond `y, y + e_μ` of `Ω₀`,
  `Σ_p (hpart p y − hpart p (y+e_μ))² ≤ 4 m δ²`,  `m = 6 (3(2c+1))³`,  `δ = ell² / ((c − 4) κ M ell^{strat y})`;
* `hpart_lip`: `|hpart p y − hpart p (y+e_μ)| ≤ 2 √m δ`  (Lipschitz `≤ C(c, ell) / (κ M ell^{strat})`, free of `k` and `κ`).
Hypotheses: `Admissible`, `0 < κ`, `0 < M`, `1 ≤ ell`, `1 ≤ R`, `(c+3) κ ell ≤ R`, `5 ≤ c`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M1

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneR8 (pdist_comm pdist_shift_le pdist_triangle pdist_self)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

variable {L : PeriodicLatticeExtent}

open Classical

theorem clamp_lip (u v : ℝ) : |max 0 (min 1 u) - max 0 (min 1 v)| ≤ |u - v| := by
  have h1 : |max 0 (min 1 u) - max 0 (min 1 v)| ≤ |min 1 u - min 1 v| := by
    rw [max_comm 0 (min 1 u), max_comm 0 (min 1 v)]
    exact abs_max_sub_max_le_abs _ _ _
  have h2 : |min 1 u - min 1 v| ≤ |u - v| := by
    have := abs_min_sub_min_le_max (1 : ℝ) u 1 v
    rw [sub_self, abs_zero] at this
    exact this.trans (max_le (abs_nonneg _) le_rfl)
  exact h1.trans h2

/-- the tent of a patch. -/
noncomputable def bump (ell M κ c j : ℕ) (w y : PeriodicLatticeSite L) : ℝ :=
  max 0 (min 1 (((c : ℝ) * gsp ell M κ j - pdist w y) / (((c : ℝ) - 4) * gsp ell M κ j)))

theorem bump_nonneg (ell M κ c j : ℕ) (w y : PeriodicLatticeSite L) : 0 ≤ bump ell M κ c j w y := le_max_left _ _

theorem bump_le_one (ell M κ c j : ℕ) (w y : PeriodicLatticeSite L) : bump ell M κ c j w y ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem bump_core {ell M κ c j : ℕ} (hc : 5 ≤ c) (hG : 0 < gsp ell M κ j) {w y : PeriodicLatticeSite L}
    (hy : y ∈ pcore ell M κ j w) : bump ell M κ c j w y = 1 := by
  have hy' : pdist w y ≤ 4 * gsp ell M κ j := hy
  have hGr : (0 : ℝ) < gsp ell M κ j := by exact_mod_cast hG
  have hcr : (5 : ℝ) ≤ c := by exact_mod_cast hc
  have hd : ((pdist w y : ℕ) : ℝ) ≤ 4 * gsp ell M κ j := by exact_mod_cast hy'
  have hden : 0 < ((c : ℝ) - 4) * gsp ell M κ j := mul_pos (by linarith) hGr
  have hr : 1 ≤ ((c : ℝ) * gsp ell M κ j - pdist w y) / (((c : ℝ) - 4) * gsp ell M κ j) := by
    rw [le_div_iff₀ hden]; nlinarith
  unfold bump
  rw [min_eq_left hr, max_eq_right zero_le_one]

theorem bump_supp {ell M κ c j : ℕ} (hc : 5 ≤ c) (hG : 0 < gsp ell M κ j) {w y : PeriodicLatticeSite L}
    (h : bump ell M κ c j w y ≠ 0) : y ∈ patch ell M κ c j w := by
  by_contra hn
  have hn' : c * gsp ell M κ j < pdist w y := by
    have : ¬ pdist w y ≤ c * gsp ell M κ j := hn
    omega
  have hGr : (0 : ℝ) < gsp ell M κ j := by exact_mod_cast hG
  have hcr : (5 : ℝ) ≤ c := by exact_mod_cast hc
  have hd : (c : ℝ) * gsp ell M κ j < pdist w y := by exact_mod_cast hn'
  have hden : 0 < ((c : ℝ) - 4) * gsp ell M κ j := mul_pos (by linarith) hGr
  have hr : ((c : ℝ) * gsp ell M κ j - pdist w y) / (((c : ℝ) - 4) * gsp ell M κ j) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le
  apply h
  unfold bump
  exact max_eq_left (le_trans (min_le_right _ _) hr)

theorem bump_lip {ell M κ c j : ℕ} (hc : 5 ≤ c) (hG : 0 < gsp ell M κ j) (w y y' : PeriodicLatticeSite L) :
    |bump ell M κ c j w y - bump ell M κ c j w y'| ≤ (pdist y y' : ℝ) / (((c : ℝ) - 4) * gsp ell M κ j) := by
  have hGr : (0 : ℝ) < gsp ell M κ j := by exact_mod_cast hG
  have hcr : (5 : ℝ) ≤ c := by exact_mod_cast hc
  have hden : 0 < ((c : ℝ) - 4) * gsp ell M κ j := mul_pos (by linarith) hGr
  refine (clamp_lip _ _).trans ?_
  rw [← sub_div, abs_div, abs_of_pos hden]
  apply div_le_div_of_nonneg_right _ hden.le
  have t1 := pdist_triangle w y y'
  have t2 := pdist_triangle w y' y
  have t3 := pdist_comm y' y
  have r1 : (pdist w y' : ℝ) ≤ pdist w y + pdist y y' := by exact_mod_cast t1
  have r2 : (pdist w y : ℝ) ≤ pdist w y' + pdist y y' := by
    have : pdist w y ≤ pdist w y' + pdist y y' := by omega
    exact_mod_cast this
  rw [abs_le]; constructor <;> linarith

/-- the bump of a patch index (`0` if not a patch). -/
noncomputable def psi (ell M k κ c : ℕ) (S : Tower L) (p : Fin (k + 1) × PeriodicLatticeSite L)
    (y : PeriodicLatticeSite L) : ℝ :=
  if IsPatch ell M k κ S p.1.val p.2 then bump ell M κ c p.1.val p.2 y else 0

/-- `Σ_q psi_q(y)²`. -/
noncomputable def psiSq (ell M k κ c : ℕ) (S : Tower L) (y : PeriodicLatticeSite L) : ℝ :=
  ∑ p, psi ell M k κ c S p y ^ 2

/-- the normalised partition. -/
noncomputable def hpart (ell M k κ c : ℕ) (S : Tower L) (p : Fin (k + 1) × PeriodicLatticeSite L)
    (y : PeriodicLatticeSite L) : ℝ :=
  psi ell M k κ c S p y / Real.sqrt (psiSq ell M k κ c S y)

theorem psi_nonneg {ell M k κ c : ℕ} {S : Tower L} (p : Fin (k + 1) × PeriodicLatticeSite L) (y : PeriodicLatticeSite L) :
    0 ≤ psi ell M k κ c S p y := by
  unfold psi; split_ifs
  · exact bump_nonneg _ _ _ _ _ _ _
  · exact le_rfl

theorem psi_supp {ell M k κ c : ℕ} {S : Tower L} (hc : 5 ≤ c) (hκ : 0 < κ) (hM : 0 < M) (hell : 0 < ell)
    {p : Fin (k + 1) × PeriodicLatticeSite L} {y : PeriodicLatticeSite L} (h : psi ell M k κ c S p y ≠ 0) :
    p ∈ patchesAt ell M k κ c S y := by
  unfold psi at h
  split_ifs at h with hp
  · simp only [patchesAt, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hp, bump_supp hc (gsp_pos hκ hM hell _) h⟩
  · exact absurd rfl h

theorem psiSq_nonneg {ell M k κ c : ℕ} {S : Tower L} (y : PeriodicLatticeSite L) : 0 ≤ psiSq ell M k κ c S y :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- on `Ω₀` some bump equals `1`, so `Σ psi² ≥ 1`. -/
theorem psiSq_ge_one {ell M k κ c : ℕ} {S : Tower L} (hc : 5 ≤ c) (hκ : 0 < κ) (hM : 0 < M) (hell : 0 < ell)
    {y : PeriodicLatticeSite L} (hy : y ∈ S.Om 0) : 1 ≤ psiSq ell M k κ c S y := by
  obtain ⟨j, w, hp, hcore, -⟩ := patch_cover (ell := ell) (k := k) hκ hM hell hy 0
  set q : Fin (k + 1) × PeriodicLatticeSite L := (⟨j, Nat.lt_succ_of_le hp.1⟩, w)
  have hq : psi ell M k κ c S q y = 1 := by
    unfold psi; rw [if_pos hp]; exact bump_core hc (gsp_pos hκ hM hell _) hcore
  have := Finset.single_le_sum (f := fun p => psi ell M k κ c S p y ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ q)
  simp only [hq, one_pow] at this
  exact this

theorem hpart_nonneg {ell M k κ c : ℕ} {S : Tower L} (p : Fin (k + 1) × PeriodicLatticeSite L)
    (y : PeriodicLatticeSite L) : 0 ≤ hpart ell M k κ c S p y :=
  div_nonneg (psi_nonneg p y) (Real.sqrt_nonneg _)

/-- support: a nonzero partition function lives on its patch. -/
theorem hpart_supp {ell M k κ c : ℕ} {S : Tower L} (hc : 5 ≤ c) (hκ : 0 < κ) (hM : 0 < M) (hell : 0 < ell)
    {p : Fin (k + 1) × PeriodicLatticeSite L} {y : PeriodicLatticeSite L} (h : hpart ell M k κ c S p y ≠ 0) :
    p ∈ patchesAt ell M k κ c S y := by
  apply psi_supp hc hκ hM hell
  intro h0; apply h; unfold hpart; rw [h0, zero_div]

/-- **`Σ_p h_p(y)² = 1` on `Ω₀`.** -/
theorem sum_hpart_sq {ell M k κ c : ℕ} {S : Tower L} (hc : 5 ≤ c) (hκ : 0 < κ) (hM : 0 < M) (hell : 0 < ell)
    {y : PeriodicLatticeSite L} (hy : y ∈ S.Om 0) : ∑ p, hpart ell M k κ c S p y ^ 2 = 1 := by
  have hS := psiSq_ge_one (k := k) hc hκ hM hell (c := c) (S := S) hy
  have hS0 : 0 < psiSq ell M k κ c S y := by linarith
  unfold hpart
  simp only [div_pow, Real.sq_sqrt hS0.le]
  rw [← Finset.sum_div]
  exact div_self hS0.ne'

/-- the per-index difference is at most `δ = ell²/((c−4) κ M ell^{strat y})` for a bond of `Ω₀`. -/
theorem psi_diff_le {ell M R k κ c : ℕ} {S : Tower L} (hA : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M)
    (hell : 1 ≤ ell) (hR1 : 1 ≤ R) (hR : (c + 3) * κ * ell ≤ R) (hc : 5 ≤ c) (y : PeriodicLatticeSite L) (μ : Fin 3)
    (p : Fin (k + 1) × PeriodicLatticeSite L)
    (hp : p ∈ patchesAt ell M k κ c S y ∪ patchesAt ell M k κ c S (periodicLatticeShift y μ)) :
    |psi ell M k κ c S p y - psi ell M k κ c S p (periodicLatticeShift y μ)|
      ≤ (ell : ℝ) ^ 2 / (((c : ℝ) - 4) * κ * M * (ell : ℝ) ^ strat S k y) := by
  have hpat : IsPatch ell M k κ S p.1.val p.2 := by
    rcases Finset.mem_union.mp hp with h | h <;>
      · simp only [patchesAt, Finset.mem_filter, Finset.mem_univ, true_and] at h; exact h.1
  have hs : strat S k y ≤ p.1.val + 2 := by
    rcases Finset.mem_union.mp hp with h | h
    · simp only [patchesAt, Finset.mem_filter, Finset.mem_univ, true_and] at h
      have := patch_strat_bounds hA hκ hM hell hR hpat h.2
      omega
    · simp only [patchesAt, Finset.mem_filter, Finset.mem_univ, true_and] at h
      have := patch_strat_bounds hA hκ hM hell hR hpat h.2
      have := (strat_adj hA hR1 hM hell y μ).2
      omega
  have hG := gsp_pos hκ hM (by omega : 0 < ell) (ell := ell) p.1.val
  unfold psi; rw [if_pos hpat, if_pos hpat]
  refine (bump_lip hc hG _ _ _).trans ?_
  have hcr : (5 : ℝ) ≤ c := by exact_mod_cast hc
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hκr : (0 : ℝ) < κ := by exact_mod_cast hκ
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hd1 : (pdist y (periodicLatticeShift y μ) : ℝ) ≤ 1 := by exact_mod_cast pdist_shift_le y μ
  have hGr : ((gsp ell M κ p.1.val : ℕ) : ℝ) = κ * (M * (ell : ℝ) ^ p.1.val) := by
    unfold gsp bigSide; push_cast; ring
  rw [hGr]
  have hpos1 : 0 < ((c : ℝ) - 4) * (κ * (M * (ell : ℝ) ^ p.1.val)) := by
    have : (0 : ℝ) < (ell : ℝ) ^ p.1.val := by positivity
    have : (0 : ℝ) < (c : ℝ) - 4 := by linarith
    positivity
  have hpos2 : 0 < ((c : ℝ) - 4) * κ * M * (ell : ℝ) ^ strat S k y := by
    have : (0 : ℝ) < (ell : ℝ) ^ strat S k y := by positivity
    have : (0 : ℝ) < (c : ℝ) - 4 := by linarith
    positivity
  rw [div_le_div_iff₀ hpos1 hpos2]
  have hpow : (ell : ℝ) ^ strat S k y ≤ (ell : ℝ) ^ 2 * (ell : ℝ) ^ p.1.val := by
    rw [← pow_add]; exact pow_le_pow_right₀ hellr (by omega)
  have h0 : (0 : ℝ) ≤ ((c : ℝ) - 4) * κ * M := by
    have : (0 : ℝ) < (c : ℝ) - 4 := by linarith
    positivity
  have hpd : (0 : ℝ) ≤ (pdist y (periodicLatticeShift y μ) : ℝ) := Nat.cast_nonneg _
  calc (pdist y (periodicLatticeShift y μ) : ℝ) * (((c : ℝ) - 4) * κ * M * (ell : ℝ) ^ strat S k y)
      ≤ 1 * (((c : ℝ) - 4) * κ * M * (ell : ℝ) ^ strat S k y) :=
        mul_le_mul_of_nonneg_right hd1 hpos2.le
    _ ≤ 1 * (((c : ℝ) - 4) * κ * M * ((ell : ℝ) ^ 2 * (ell : ℝ) ^ p.1.val)) := by
        have := mul_le_mul_of_nonneg_left hpow h0
        linarith
    _ = (ell : ℝ) ^ 2 * (((c : ℝ) - 4) * (κ * (M * (ell : ℝ) ^ p.1.val))) := by ring

/-- Cauchy–Schwarz form of the reverse triangle inequality in `ℓ²`: `(A − B)² ≤ Σ (a − b)²`. -/
theorem sqrt_sub_sq_le {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    (Real.sqrt (∑ i, a i ^ 2) - Real.sqrt (∑ i, b i ^ 2)) ^ 2 ≤ ∑ i, (a i - b i) ^ 2 := by
  have hA := Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (a i)) : (0 : ℝ) ≤ ∑ i, a i ^ 2)
  have hB := Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (b i)) : (0 : ℝ) ≤ ∑ i, b i ^ 2)
  have hcs : ∑ i, a i * b i ≤ Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2) := by
    rw [← Real.sqrt_mul (Finset.sum_nonneg (fun i _ => sq_nonneg (a i)))]
    refine le_trans (le_abs_self _) ?_
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
  have hexp : ∑ i, (a i - b i) ^ 2 = ∑ i, a i ^ 2 + ∑ i, b i ^ 2 - 2 * ∑ i, a i * b i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hexp]
  nlinarith [hA, hB, hcs]

/-- **G4, the IMS input (`hpart_grad_sq`)**: for a bond `y, y+e_μ` with both ends in `Ω₀`,
`Σ_p (h_p(y) − h_p(y+e_μ))² ≤ 4 · 6 (3(2c+1))³ · δ²`, `δ = ell² / ((c − 4) κ M ell^{strat y})`. -/
theorem hpart_grad_sq {ell M R k κ c : ℕ} {S : Tower L} (hA : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M)
    (hell : 1 ≤ ell) (hR1 : 1 ≤ R) (hR : (c + 3) * κ * ell ≤ R) (hc : 5 ≤ c) {y : PeriodicLatticeSite L}
    (hy : y ∈ S.Om 0) (μ : Fin 3) (hy' : periodicLatticeShift y μ ∈ S.Om 0) :
    ∑ p, (hpart ell M k κ c S p y - hpart ell M k κ c S p (periodicLatticeShift y μ)) ^ 2
      ≤ 4 * (6 * (3 * (2 * c + 1)) ^ 3 : ℕ) *
        ((ell : ℝ) ^ 2 / (((c : ℝ) - 4) * κ * M * (ell : ℝ) ^ strat S k y)) ^ 2 := by
  set y' := periodicLatticeShift y μ with hy'def
  set a : Fin (k + 1) × PeriodicLatticeSite L → ℝ := fun p => psi ell M k κ c S p y with ha
  set b : Fin (k + 1) × PeriodicLatticeSite L → ℝ := fun p => psi ell M k κ c S p y' with hb
  set A := Real.sqrt (∑ p, a p ^ 2) with hAdef
  set B := Real.sqrt (∑ p, b p ^ 2) with hBdef
  set δ : ℝ := (ell : ℝ) ^ 2 / (((c : ℝ) - 4) * κ * M * (ell : ℝ) ^ strat S k y) with hδ
  have hell0 : 0 < ell := by omega
  have hA1 : 1 ≤ A := by
    rw [hAdef, ← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (psiSq_ge_one (k := k) hc hκ hM hell0 (c := c) (S := S) hy)
  have hB1 : 1 ≤ B := by
    rw [hBdef, ← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (psiSq_ge_one (k := k) hc hκ hM hell0 (c := c) (S := S) hy')
  have hBsq : B ^ 2 = ∑ p, b p ^ 2 := Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  set D := ∑ p, (a p - b p) ^ 2 with hD
  -- pointwise split and sum
  have hsplit : ∀ p, (a p / A - b p / B) ^ 2 ≤ 2 * ((a p - b p) ^ 2) + 2 * (b p ^ 2 * (1 / A - 1 / B) ^ 2) := by
    intro p
    have e : a p / A - b p / B = (a p - b p) / A + b p * (1 / A - 1 / B) := by field_simp; ring
    rw [e]
    have hA0 : 0 < A := by linarith
    have h1 : ((a p - b p) / A) ^ 2 ≤ (a p - b p) ^ 2 := by
      rw [div_pow]
      exact div_le_self (sq_nonneg _) (by nlinarith)
    nlinarith [sq_nonneg ((a p - b p) / A - b p * (1 / A - 1 / B)), sq_nonneg (b p * (1 / A - 1 / B))]
  have hsum1 : ∑ p, (a p / A - b p / B) ^ 2 ≤ 2 * D + 2 * ((∑ p, b p ^ 2) * (1 / A - 1 / B) ^ 2) := by
    calc ∑ p, (a p / A - b p / B) ^ 2 ≤ ∑ p, (2 * ((a p - b p) ^ 2) + 2 * (b p ^ 2 * (1 / A - 1 / B) ^ 2)) :=
          Finset.sum_le_sum (fun p _ => hsplit p)
      _ = 2 * D + 2 * ((∑ p, b p ^ 2) * (1 / A - 1 / B) ^ 2) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul]
  have hAB : (∑ p, b p ^ 2) * (1 / A - 1 / B) ^ 2 ≤ (A - B) ^ 2 := by
    rw [← hBsq]
    have hA0 : 0 < A := by linarith
    have hB0 : 0 < B := by linarith
    have e : B ^ 2 * (1 / A - 1 / B) ^ 2 = (A - B) ^ 2 / A ^ 2 := by field_simp; ring
    rw [e]
    exact div_le_self (sq_nonneg _) (by nlinarith)
  have hAB2 : (A - B) ^ 2 ≤ D := sqrt_sub_sq_le a b
  have hmain : ∑ p, (a p / A - b p / B) ^ 2 ≤ 4 * D := by linarith
  -- D ≤ m δ²
  set U := patchesAt ell M k κ c S y ∪ patchesAt ell M k κ c S y' with hU
  have hzero : ∀ p ∉ U, a p - b p = 0 := by
    intro p hp
    have h1 : a p = 0 := by
      by_contra h
      exact hp (Finset.mem_union_left _ (psi_supp hc hκ hM hell0 h))
    have h2 : b p = 0 := by
      by_contra h
      exact hp (Finset.mem_union_right _ (psi_supp hc hκ hM hell0 h))
    rw [h1, h2, sub_zero]
  have hDU : D = ∑ p ∈ U, (a p - b p) ^ 2 := by
    rw [hD]
    refine (Finset.sum_subset (Finset.subset_univ U) (fun p _ hp => ?_)).symm
    rw [hzero p hp]; ring
  have hcardU : (U.card : ℝ) ≤ (6 * (3 * (2 * c + 1)) ^ 3 : ℕ) := by
    have h1 := patch_mult hA hκ hM hell hR y
    have h2 := patch_mult hA hκ hM hell hR y'
    have h3 := Finset.card_union_le (patchesAt ell M k κ c S y) (patchesAt ell M k κ c S y')
    exact_mod_cast (show U.card ≤ 6 * (3 * (2 * c + 1)) ^ 3 by rw [hU]; omega)
  have hDle : D ≤ (6 * (3 * (2 * c + 1)) ^ 3 : ℕ) * δ ^ 2 := by
    rw [hDU]
    calc ∑ p ∈ U, (a p - b p) ^ 2 ≤ ∑ _p ∈ U, δ ^ 2 := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          have := psi_diff_le hA hκ hM hell hR1 hR hc y μ p hp
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = (U.card : ℝ) * δ ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcardU (sq_nonneg _)
  have hfin : ∑ p, (hpart ell M k κ c S p y - hpart ell M k κ c S p y') ^ 2 = ∑ p, (a p / A - b p / B) ^ 2 := rfl
  rw [hfin]
  calc _ ≤ 4 * D := hmain
    _ ≤ 4 * ((6 * (3 * (2 * c + 1)) ^ 3 : ℕ) * δ ^ 2) := by linarith
    _ = _ := by ring

/-- **G4 Lipschitz (`hpart_lip`)**: `|h_p(y) − h_p(y+e_μ)| ≤ 2 √m δ`, `m = 6 (3(2c+1))³`, on bonds of `Ω₀`. -/
theorem hpart_lip {ell M R k κ c : ℕ} {S : Tower L} (hA : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M)
    (hell : 1 ≤ ell) (hR1 : 1 ≤ R) (hR : (c + 3) * κ * ell ≤ R) (hc : 5 ≤ c) {y : PeriodicLatticeSite L}
    (hy : y ∈ S.Om 0) (μ : Fin 3) (hy' : periodicLatticeShift y μ ∈ S.Om 0) (p : Fin (k + 1) × PeriodicLatticeSite L) :
    |hpart ell M k κ c S p y - hpart ell M k κ c S p (periodicLatticeShift y μ)|
      ≤ 2 * Real.sqrt ((6 * (3 * (2 * c + 1)) ^ 3 : ℕ)) *
        ((ell : ℝ) ^ 2 / (((c : ℝ) - 4) * κ * M * (ell : ℝ) ^ strat S k y)) := by
  set δ : ℝ := (ell : ℝ) ^ 2 / (((c : ℝ) - 4) * κ * M * (ell : ℝ) ^ strat S k y)
  have hcr : (5 : ℝ) ≤ c := by exact_mod_cast hc
  have hδ : 0 ≤ δ := by
    have : (0 : ℝ) < (c : ℝ) - 4 := by linarith
    positivity
  have h1 := Finset.single_le_sum
    (f := fun q => (hpart ell M k κ c S q y - hpart ell M k κ c S q (periodicLatticeShift y μ)) ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ p)
  have h2 := hpart_grad_sq hA hκ hM hell hR1 hR hc hy μ hy'
  have h3 : (hpart ell M k κ c S p y - hpart ell M k κ c S p (periodicLatticeShift y μ)) ^ 2
      ≤ (2 * Real.sqrt ((6 * (3 * (2 * c + 1)) ^ 3 : ℕ)) * δ) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    have := h1.trans h2
    linarith
  have h4 : 0 ≤ 2 * Real.sqrt ((6 * (3 * (2 * c + 1)) ^ 3 : ℕ)) * δ := by positivity
  exact abs_le_of_sq_le_sq' h3 h4 |>.elim (fun h h' => abs_le.mpr ⟨h, h'⟩)

#print axioms clamp_lip
#print axioms bump_core
#print axioms bump_supp
#print axioms bump_lip
#print axioms psi_supp
#print axioms psiSq_ge_one
#print axioms hpart_nonneg
#print axioms hpart_supp
#print axioms sum_hpart_sq
#print axioms psi_diff_le
#print axioms sqrt_sub_sq_le
#print axioms hpart_grad_sq
#print axioms hpart_lip

end AdalyFormal.M1
