import ZR8Geo

/-!
# M1A -- strata of an admissible tower; G1 `strat_adj` / `strat_close`, G1' `lam_deep`  (M1 lane B, 2026-10-13)

`strat S k x` = the largest `j ≤ k` with `x ∈ Ω_j` (`Nat.findGreatest`; `0` if there is none, in particular off `Ω₀`).
`bstrat S k b` = the both-endpoint (`j_min`) stratum of a bond (plan D4; plan = `compute/plan_m1m2_20261012/PLAN.md`).
G1: two sites at `ℓ¹` distance `≤ R M ell^{strat x + 1}` have strata differing by at most one (`strat_close`); adjacent sites
(`strat_adj`) are the case of distance `≤ 1`.  The collar `x ∉ Ω_j, y ∈ Ω_{j+1} ⇒ R M ell^j < |x-y|` is clause 5 of `Admissible` (`collar`).
G1': a unit site within unit distance `R M` of `Λ` (`LambdaOK`) has its whole fine `ell^k`-block in `Ω_k` (`lam_deep`), so its fine sites
have stratum `k` (`lam_deep_strat`).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M1

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneR8 (pdist_comm pdist_shift_le pdist_triangle)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

variable {L : PeriodicLatticeExtent}

open Classical

open Classical in
/-- stratum of a site: the largest `j ≤ k` with `x ∈ Ω_j`; `0` if none. -/
noncomputable def strat (S : Tower L) (k : ℕ) (x : PeriodicLatticeSite L) : ℕ :=
  Nat.findGreatest (fun j => x ∈ S.Om j) k

/-- stratum of a bond: both-endpoint (`j_min`) convention. -/
noncomputable def bstrat (S : Tower L) (k : ℕ) (b : Bond L) : ℕ :=
  min (strat S k b.1) (strat S k (periodicLatticeShift b.1 b.2))

theorem strat_le (S : Tower L) (k : ℕ) (x : PeriodicLatticeSite L) : strat S k x ≤ k := by
  classical
  unfold strat; exact Nat.findGreatest_le k

theorem bstrat_le (S : Tower L) (k : ℕ) (b : Bond L) : bstrat S k b ≤ k :=
  le_trans (min_le_left _ _) (strat_le S k b.1)

/-- the tower is antitone (clause 1 of `Admissible`). -/
theorem om_anti {ell M R k : ℕ} {S : Tower L} (h : Admissible ell M R k S) {a b : ℕ} (hab : a ≤ b) :
    S.Om b ⊆ S.Om a := by
  induction hab with
  | refl => exact le_rfl
  | step _ ih => exact (h.1 _).trans ih

theorem le_strat_of_mem {S : Tower L} {k j : ℕ} {x : PeriodicLatticeSite L} (hj : j ≤ k) (hx : x ∈ S.Om j) :
    j ≤ strat S k x := by
  classical
  unfold strat; exact Nat.le_findGreatest hj hx

/-- if the stratum is `≥ 1` the site lies in `Ω_{strat}`. -/
theorem mem_strat_of_pos {S : Tower L} {k : ℕ} {x : PeriodicLatticeSite L} (h : 1 ≤ strat S k x) :
    x ∈ S.Om (strat S k x) := by
  unfold strat at h ⊢
  exact Nat.findGreatest_of_ne_zero rfl (Nat.one_le_iff_ne_zero.mp h)

/-- on `Ω₀` the site lies in `Ω_{strat}`. -/
theorem mem_strat_of_mem0 {S : Tower L} {k : ℕ} {x : PeriodicLatticeSite L} (hx : x ∈ S.Om 0) :
    x ∈ S.Om (strat S k x) := by
  classical
  unfold strat
  exact Nat.findGreatest_spec (P := fun j => x ∈ S.Om j) (Nat.zero_le k) hx

/-- `1 ≤ j ≤ k`: `j ≤ strat x ↔ x ∈ Ω_j`. -/
theorem le_strat_iff {ell M R k : ℕ} {S : Tower L} (h : Admissible ell M R k S) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (x : PeriodicLatticeSite L) : j ≤ strat S k x ↔ x ∈ S.Om j := by
  constructor
  · intro hle
    exact om_anti h hle (mem_strat_of_pos (le_trans hj1 hle))
  · exact le_strat_of_mem hjk

/-- `x ∈ Ω_j` for every `j ≤ strat x`, if `x ∈ Ω₀`. -/
theorem mem_of_le_strat {ell M R k : ℕ} {S : Tower L} (h : Admissible ell M R k S) {x : PeriodicLatticeSite L}
    (hx : x ∈ S.Om 0) {j : ℕ} (hj : j ≤ strat S k x) : x ∈ S.Om j :=
  om_anti h hj (mem_strat_of_mem0 hx)

/-- the site is NOT in the next level. -/
theorem not_mem_strat_succ {ell M R k : ℕ} {S : Tower L} (h : Admissible ell M R k S) (x : PeriodicLatticeSite L) :
    x ∉ S.Om (strat S k x + 1) := by
  classical
  by_cases hk : strat S k x + 1 ≤ k
  · unfold strat at hk ⊢
    exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hk
  · have hs : strat S k x = k := by have := strat_le S k x; omega
    rw [hs, h.2.1 (k + 1) (Nat.lt_succ_self k)]
    exact fun h' => h'

/-- `B^j(Λ_j) = Ω_j \ Ω_{j+1}` is exactly the stratum-`j` part of `Ω₀` (`j ≤ k`). -/
theorem strat_eq_iff {ell M R k : ℕ} {S : Tower L} (h : Admissible ell M R k S) {j : ℕ} (hjk : j ≤ k)
    (x : PeriodicLatticeSite L) : (x ∈ towerBj S j) ↔ (x ∈ S.Om 0 ∧ strat S k x = j) := by
  constructor
  · rintro ⟨hj, hj1⟩
    have hx0 : x ∈ S.Om 0 := om_anti h (Nat.zero_le j) hj
    refine ⟨hx0, le_antisymm ?_ (le_strat_of_mem hjk hj)⟩
    by_contra hlt
    push Not at hlt
    exact hj1 (mem_of_le_strat h hx0 (show j + 1 ≤ strat S k x by omega))
  · rintro ⟨hx0, rfl⟩
    exact ⟨mem_strat_of_mem0 hx0, not_mem_strat_succ h x⟩

/-- clause 5 of `Admissible`, as a named collar fact. -/
theorem collar {ell M R k : ℕ} {S : Tower L} (h : Admissible ell M R k S) {j : ℕ} (hjk : j ≤ k)
    {x y : PeriodicLatticeSite L} (hx : x ∉ S.Om j) (hy : y ∈ S.Om (j + 1)) :
    R * bigSide M ell j < pdist x y :=
  h.2.2.2.2.1 j hjk x hx y hy

/-- **G1 (general form, `strat_close`).**  If `|x - y| ≤ R M ell^{strat x + 1}` then `strat y ≤ strat x + 1`. -/
theorem strat_close {ell M R k : ℕ} {S : Tower L} (h : Admissible ell M R k S) {x y : PeriodicLatticeSite L}
    (hd : pdist x y ≤ R * bigSide M ell (strat S k x + 1)) : strat S k y ≤ strat S k x + 1 := by
  by_contra hlt
  push Not at hlt
  have hyk : strat S k y ≤ k := strat_le S k y
  have hy : y ∈ S.Om (strat S k x + 2) :=
    (le_strat_iff h (by omega) (by omega) y).mp (by omega)
  have hx : x ∉ S.Om (strat S k x + 1) := not_mem_strat_succ h x
  have := collar h (j := strat S k x + 1) (by omega) hx hy
  omega

/-- **G1 (`strat_adj`).**  Adjacent sites: strata differ by at most one (needs `R M ell ≥ 1`, i.e. `R, M, ell ≥ 1`). -/
theorem strat_adj {ell M R k : ℕ} {S : Tower L} (h : Admissible ell M R k S) (hR : 1 ≤ R) (hM : 1 ≤ M) (hell : 1 ≤ ell)
    (x : PeriodicLatticeSite L) (μ : Fin 3) :
    strat S k (periodicLatticeShift x μ) ≤ strat S k x + 1 ∧ strat S k x ≤ strat S k (periodicLatticeShift x μ) + 1 := by
  have hpos : ∀ j : ℕ, 1 ≤ R * bigSide M ell j := fun j => by
    unfold bigSide
    have : 1 ≤ ell ^ j := Nat.one_le_pow _ _ hell
    have : 1 ≤ M * ell ^ j := Nat.one_le_iff_ne_zero.mpr (by positivity)
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h1 := pdist_shift_le x μ
  refine ⟨strat_close h (le_trans h1 (hpos _)), strat_close h ?_⟩
  rw [pdist_comm]; exact le_trans h1 (hpos _)

/-- the both-endpoint stratum is `≥ j` iff both endpoints lie in `Ω_j` (`1 ≤ j ≤ k`). -/
theorem le_bstrat_iff {ell M R k : ℕ} {S : Tower L} (h : Admissible ell M R k S) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (b : Bond L) : j ≤ bstrat S k b ↔ (b.1 ∈ S.Om j ∧ periodicLatticeShift b.1 b.2 ∈ S.Om j) := by
  unfold bstrat
  rw [le_min_iff, le_strat_iff h hj1 hjk, le_strat_iff h hj1 hjk]

/-- a bond with both endpoints in `Ω_j` (`j ≤ k`) has `bstrat ≥ j`. -/
theorem le_bstrat_of_mem {S : Tower L} {k j : ℕ} (hjk : j ≤ k) (b : Bond L) (h1 : b.1 ∈ S.Om j)
    (h2 : periodicLatticeShift b.1 b.2 ∈ S.Om j) : j ≤ bstrat S k b :=
  le_min (le_strat_of_mem hjk h1) (le_strat_of_mem hjk h2)

/-- the two endpoint strata of a bond differ by at most one, so `bstrat ≥ strat (either end) - 1`. -/
theorem bstrat_ge {ell M R k : ℕ} {S : Tower L} (h : Admissible ell M R k S) (hR : 1 ≤ R) (hM : 1 ≤ M) (hell : 1 ≤ ell)
    (b : Bond L) : strat S k b.1 ≤ bstrat S k b + 1 := by
  unfold bstrat
  have := (strat_adj h hR hM hell b.1 b.2).2
  omega

/-- **G1' (`lam_deep`).**  `LambdaOK`: if `y ∈ Λ` and the unit site `y'` is within unit distance `R M` of `y`, then every fine site
`x` of the fine `ell^k`-block of `y'` (i.e. `x_μ / ell^k = y'_μ`) lies in `Ω_k`. -/
theorem lam_deep {Lu Lf : PeriodicLatticeExtent} {ell M R k : ℕ} {S : Tower Lf} {Lam : Set (PeriodicLatticeSite Lu)}
    (hA : Admissible ell M R k S) (hL : LambdaOK ell M R k S Lam) (hell : 0 < ell)
    {y y' : PeriodicLatticeSite Lu} (hy : y ∈ Lam) (hd : pdist y y' ≤ R * M)
    {x : PeriodicLatticeSite Lf} (hx : ∀ μ, (x μ).val / ell ^ k = (y' μ).val) : x ∈ S.Om k := by
  obtain ⟨-, emb, hemb, -, hfar⟩ := hL
  have hin : emb y' ∈ S.Om k := by
    by_contra hn
    have := hfar y hy y' hn
    omega
  have hpk : 0 < ell ^ k := pow_pos hell k
  refine hA.2.2.2.1 k le_rfl (emb y') hin x (fun μ => ?_)
  unfold bigSide
  rw [hemb y' μ, Nat.mul_comm M (ell ^ k), ← Nat.div_div_eq_div_mul, hx μ, Nat.mul_div_mul_left _ _ hpk]

/-- G1' corollary: such fine sites have stratum `k`. -/
theorem lam_deep_strat {Lu Lf : PeriodicLatticeExtent} {ell M R k : ℕ} {S : Tower Lf} {Lam : Set (PeriodicLatticeSite Lu)}
    (hA : Admissible ell M R k S) (hL : LambdaOK ell M R k S Lam) (hell : 0 < ell)
    {y y' : PeriodicLatticeSite Lu} (hy : y ∈ Lam) (hd : pdist y y' ≤ R * M)
    {x : PeriodicLatticeSite Lf} (hx : ∀ μ, (x μ).val / ell ^ k = (y' μ).val) : strat S k x = k :=
  le_antisymm (strat_le S k x) (le_strat_of_mem le_rfl (lam_deep hA hL hell hy hd hx))

#print axioms strat_le
#print axioms bstrat_le
#print axioms om_anti
#print axioms le_strat_iff
#print axioms mem_of_le_strat
#print axioms not_mem_strat_succ
#print axioms strat_eq_iff
#print axioms collar
#print axioms strat_close
#print axioms strat_adj
#print axioms le_bstrat_iff
#print axioms le_bstrat_of_mem
#print axioms bstrat_ge
#print axioms lam_deep
#print axioms lam_deep_strat

end AdalyFormal.M1
