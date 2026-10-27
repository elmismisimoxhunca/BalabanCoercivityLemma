import THL6

/-!
# TD1 -- geometry and regularity gluing for the two-domain transfer (lane two_domain_20261019)

* `regBody_mono_b`  : regularity with bound factor `b` gives regularity with every larger factor `b'`.
* `regBody_glue`    : two regular pieces `D`, `E` of `l^1`-distance `>= 4` form a regular union (single gauge, single `A`).
* `far_block_exists`: if `Om1 != empty`, some site `w` lies outside `Om0`, and the level-0 strict collar `R0 * M < pdist x y` holds with `4 <= R0`,
  then some site `v ∈ Om0` has `pdist v y >= 3 M + 1` for every `y ∈ Om1`.
-/
set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 8000

namespace AdalyFormal.TwoDom

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open UNI.AllC

variable {L : PeriodicLatticeExtent}

theorem pd_comm (x y : PeriodicLatticeSite L) : pdist x y = pdist y x := AdalyFormal.StatementLaneR8.pdist_comm x y
theorem pd_tri (x y z : PeriodicLatticeSite L) : pdist x z ≤ pdist x y + pdist y z := AdalyFormal.StatementLaneR8.pdist_triangle x y z
theorem pd_self (x : PeriodicLatticeSite L) : pdist x x = 0 := AdalyFormal.StatementLaneR8.pdist_self x
theorem pd_shift (x : PeriodicLatticeSite L) (μ : Fin 3) : pdist x (periodicLatticeShift x μ) ≤ 1 := AdalyFormal.StatementLaneR8.pdist_shift_le x μ

theorem regBody_mono_b {ell M b b' : ℕ} {sites : Set (PeriodicLatticeSite L)} {j : ℕ} {α₀ η : ℝ} {U : LinkCfg L}
    (hb : b ≤ b') (hα : 0 ≤ α₀) (hη : 0 ≤ η) (h : RegBodyH ell M b sites j α₀ η U) : RegBodyH ell M b' sites j α₀ η U := by
  obtain ⟨g, A, hc1, hc2, hc3⟩ := h
  have hb' : (b : ℝ) ≤ b' := by exact_mod_cast hb
  have key : ∀ p : ℕ, (b : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ p) ≤ (b' : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ p) := by
    intro p
    have hX : (0 : ℝ) ≤ ((ell : ℝ) ^ j * η)⁻¹ ^ p := by
      apply pow_nonneg
      apply inv_nonneg.2
      positivity
    have h0 : (0 : ℝ) ≤ (M : ℝ) * α₀ := by positivity
    apply mul_le_mul_of_nonneg_right _ hX
    have := mul_le_mul_of_nonneg_right hb' h0
    nlinarith
  exact ⟨g, A, fun e he => ⟨(hc1 e he).1, (hc1 e he).2.1, lt_of_lt_of_le (hc1 e he).2.2 (key 1)⟩,
    fun μ ν x h1 h2 => lt_of_lt_of_le (hc2 μ ν x h1 h2) (key 2),
    fun μ x h1 => lt_of_lt_of_le (hc3 μ x h1) (key 3)⟩

/-- adjacency facts -/
theorem pdist_shift_back (x : PeriodicLatticeSite L) (ν : Fin 3) : pdist x (periodicLatticeShiftBack x ν) ≤ 1 := by
  rw [pd_comm]
  have := pd_shift (periodicLatticeShiftBack x ν) ν
  rwa [AdalyFormal.Balaban.CovariantHjMinimizer.periodicLatticeShift_shiftBack] at this

/-- the agreement lemma for one side of the glued pair. `hP`: sites of `W` within `l^1`-distance `3` of a site of `P` are in `P`.
`A` agrees with `A'` on bonds starting in `P`. -/
theorem glue_side {P W : Set (PeriodicLatticeSite L)}
    (hP : ∀ s ∈ P, ∀ t ∈ W, pdist s t ≤ 3 → t ∈ P)
    {A A' : Bond L → Matrix (Fin 2) (Fin 2) ℂ} (hA : ∀ e : Bond L, e.1 ∈ P → A e = A' e) (η : ℝ) :
    (∀ (μ ν : Fin 3) (x : PeriodicLatticeSite L), x ∈ P → CubeBond W ((x, ν) : Bond L) →
        CubeBond W ((periodicLatticeShift x μ, ν) : Bond L) →
        CubeBond P ((x, ν) : Bond L) ∧ CubeBond P ((periodicLatticeShift x μ, ν) : Bond L) ∧
        A (periodicLatticeShift x μ, ν) = A' (periodicLatticeShift x μ, ν) ∧ A (x, ν) = A' (x, ν)) ∧
    (∀ (μ : Fin 3) (x : PeriodicLatticeSite L), x ∈ P →
        (∀ ν : Fin 3, ν ≠ μ → CurlReads W (periodicLatticeShiftBack x ν) ν μ ∧ CurlReads W x ν μ) →
        (∀ ν : Fin 3, ν ≠ μ → CurlReads P (periodicLatticeShiftBack x ν) ν μ ∧ CurlReads P x ν μ) ∧
        ddA η A x μ = ddA η A' x μ) := by
  have hsh : ∀ (y : PeriodicLatticeSite L) (a : Fin 3), pdist y (periodicLatticeShift y a) ≤ 3 := fun y a => le_trans (pd_shift y a) (by norm_num)
  -- curl reads from a base site in P stay in P
  have curl : ∀ (y : PeriodicLatticeSite L), y ∈ P → ∀ a b : Fin 3, CurlReads W y a b → CurlReads P y a b := by
    intro y hy a b ⟨c1, c2, c3, c4⟩
    have s1 : periodicLatticeShift y a ∈ P := hP y hy _ c4.2 (hsh y a)
    have s3 : periodicLatticeShift y b ∈ P := hP y hy _ c2.2 (hsh y b)
    have t1 : periodicLatticeShift (periodicLatticeShift y a) b ∈ P :=
      hP _ s1 _ c1.2 (hsh _ b)
    have t3 : periodicLatticeShift (periodicLatticeShift y b) a ∈ P :=
      hP _ s3 _ c3.2 (hsh _ a)
    exact ⟨⟨s1, t1⟩, ⟨hy, s3⟩, ⟨s3, t3⟩, ⟨hy, s1⟩⟩
  have curlEq : ∀ (y : PeriodicLatticeSite L) (a b : Fin 3), CurlReads P y a b → curlA η A y a b = curlA η A' y a b := by
    intro y a b ⟨c1, c2, c3, c4⟩
    unfold curlA
    rw [hA (periodicLatticeShift y a, b) c1.1, hA (y, b) c2.1, hA (periodicLatticeShift y b, a) c3.1, hA (y, a) c4.1]
  refine ⟨?_, ?_⟩
  · intro μ ν x hx b1 b2
    have s1 : periodicLatticeShift x ν ∈ P := hP x hx _ b1.2 (hsh x ν)
    have s2 : periodicLatticeShift x μ ∈ P := hP x hx _ b2.1 (hsh x μ)
    have s3 : periodicLatticeShift (periodicLatticeShift x μ) ν ∈ P := hP _ s2 _ b2.2 (hsh _ ν)
    exact ⟨⟨hx, s1⟩, ⟨s2, s3⟩, hA _ s2, hA _ hx⟩
  · intro μ x hx hcr
    have hbk : ∀ ν : Fin 3, ν ≠ μ → periodicLatticeShiftBack x ν ∈ P := by
      intro ν hν
      exact hP x hx _ ((hcr ν hν).1.2.1.1) (le_trans (pdist_shift_back x ν) (by norm_num))
    have hP' : ∀ ν : Fin 3, ν ≠ μ → CurlReads P (periodicLatticeShiftBack x ν) ν μ ∧ CurlReads P x ν μ :=
      fun ν hν => ⟨curl _ (hbk ν hν) ν μ (hcr ν hν).1, curl x hx ν μ (hcr ν hν).2⟩
    refine ⟨hP', ?_⟩
    unfold ddA
    congr 1
    apply Finset.sum_congr rfl
    intro ν hν
    have hν' : ν ≠ μ := (Finset.mem_filter.1 hν).2
    rw [curlEq _ ν μ (hP' ν hν').1, curlEq _ ν μ (hP' ν hν').2]

theorem regBody_glue {ell M b : ℕ} {D E : Set (PeriodicLatticeSite L)} {j : ℕ} {α₀ η : ℝ} {U : LinkCfg L}
    (hsep : ∀ s ∈ D, ∀ t ∈ E, 4 ≤ pdist s t)
    (hD : RegBodyH ell M b D j α₀ η U) (hE : RegBodyH ell M b E j α₀ η U) :
    RegBodyH ell M b (D ∪ E) j α₀ η U := by
  classical
  obtain ⟨g1, A1, d1, d2, d3⟩ := hD
  obtain ⟨g2, A2, e1, e2, e3⟩ := hE
  have hdisj : ∀ s, s ∈ D → s ∈ E → False := by
    intro s hD' hE'
    have := hsep s hD' s hE'
    rw [pd_self] at this; omega
  have hnearD : ∀ s ∈ D, ∀ t ∈ D ∪ E, pdist s t ≤ 3 → t ∈ D := by
    intro s hs t ht h3
    rcases ht with ht | ht
    · exact ht
    · have := hsep s hs t ht; omega
  have hnearE : ∀ s ∈ E, ∀ t ∈ D ∪ E, pdist s t ≤ 3 → t ∈ E := by
    intro s hs t ht h3
    rcases ht with ht | ht
    · have := hsep t ht s hs; rw [pd_comm] at this; omega
    · exact ht
  let g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ := fun x => if x ∈ D then g1 x else g2 x
  let A : Bond L → Matrix (Fin 2) (Fin 2) ℂ := fun e => if e.1 ∈ D then A1 e else A2 e
  have hAD : ∀ e : Bond L, e.1 ∈ D → A e = A1 e := fun e he => if_pos he
  have hAE : ∀ e : Bond L, e.1 ∈ E → A e = A2 e := fun e he => if_neg (fun h => hdisj _ h he)
  have gD : ∀ x ∈ D, g x = g1 x := fun x hx => if_pos hx
  have gE : ∀ x ∈ E, g x = g2 x := fun x hx => if_neg (fun h => hdisj _ h hx)
  obtain ⟨hs1, hs2⟩ := glue_side (P := D) (W := D ∪ E) hnearD hAD η
  obtain ⟨ht1, ht2⟩ := glue_side (P := E) (W := D ∪ E) hnearE hAE η
  refine ⟨g, A, ?_, ?_, ?_⟩
  · intro e he
    rcases he.1 with h1 | h1
    · have h2 : periodicLatticeShift e.1 e.2 ∈ D := hnearD _ h1 _ he.2 (le_trans (pd_shift e.1 e.2) (by norm_num))
      have key := d1 e ⟨h1, h2⟩
      have hg : periodicGaugeTransform g U e = periodicGaugeTransform g1 U e := by
        unfold periodicGaugeTransform; rw [gD _ h1, gD _ h2]
      rw [hg, hAD e h1]
      exact key
    · have h2 : periodicLatticeShift e.1 e.2 ∈ E := hnearE _ h1 _ he.2 (le_trans (pd_shift e.1 e.2) (by norm_num))
      have key := e1 e ⟨h1, h2⟩
      have hg : periodicGaugeTransform g U e = periodicGaugeTransform g2 U e := by
        unfold periodicGaugeTransform; rw [gE _ h1, gE _ h2]
      rw [hg, hAE e h1]
      exact key
  · intro μ ν x b1 b2
    rcases b1.1 with hx | hx
    · obtain ⟨c1, c2, c3, c4⟩ := hs1 μ ν x hx b1 b2
      rw [c3, c4]
      exact d2 μ ν x c1 c2
    · obtain ⟨c1, c2, c3, c4⟩ := ht1 μ ν x hx b1 b2
      rw [c3, c4]
      exact e2 μ ν x c1 c2
  · intro μ x hcr
    obtain ⟨ν0, hν0⟩ : ∃ ν : Fin 3, ν ≠ μ := by
      fin_cases μ
      · exact ⟨1, by decide⟩
      · exact ⟨0, by decide⟩
      · exact ⟨0, by decide⟩
    rcases (hcr ν0 hν0).2.2.1.1 with hx | hx
    · obtain ⟨c1, c2⟩ := hs2 μ x hx hcr
      rw [c2]
      exact d3 μ x c1
    · obtain ⟨c1, c2⟩ := ht2 μ x hx hcr
      rw [c2]
      exact e3 μ x c1


/-- every site is in the box of side `L 0 + L 1 + L 2 + 3` -/
theorem mem_bigBox (z v : PeriodicLatticeSite L) : v ∈ siteBox z (L 0 + L 1 + L 2 + 3) := by
  intro μ
  have h := Nat.mod_lt ((v μ).val + (L μ + 1) - (z μ).val) (show 0 < L μ + 1 by omega)
  have hL : L μ ≤ L 0 + L 1 + L 2 := by fin_cases μ <;> simp <;> omega
  show ((v μ).val + (L μ + 1) - (z μ).val) % (L μ + 1) < L 0 + L 1 + L 2 + 3
  omega

/-- **a far block**: if `Om1` contains `y0`, a site `w` lies outside `Om0`, and the strict level-0 collar `R0 * M < pdist x y` holds
(`x ∉ Om0`, `y ∈ Om1`) with `4 <= R0`, then some `v ∈ Om0` has `pdist v y >= 3 M + 1` for every `y ∈ Om1`.  (Discrete intermediate-value argument along unit steps.) -/
theorem far_block_exists {Om0 Om1 : Set (PeriodicLatticeSite L)} {M R0 : ℕ} (hM : 0 < M) (hR : 4 ≤ R0)
    (hcol : ∀ x : PeriodicLatticeSite L, x ∉ Om0 → ∀ y ∈ Om1, R0 * M < pdist x y)
    {y0 : PeriodicLatticeSite L} (hy0 : y0 ∈ Om1) {w : PeriodicLatticeSite L} (hw : w ∉ Om0) :
    ∃ v ∈ Om0, ∀ y ∈ Om1, 3 * M + 1 ≤ pdist v y := by
  by_contra hno
  push Not at hno
  have hRM : 3 * M + 1 ≤ R0 * M := by nlinarith
  have H : ∀ v : PeriodicLatticeSite L, (∃ y1 ∈ Om1, pdist v y1 ≤ 3 * M + 1) → ∃ y ∈ Om1, pdist v y < 3 * M + 1 := by
    rintro v ⟨y1, hy1, h1⟩
    have hv : v ∈ Om0 := by
      by_contra hv
      have := hcol v hv y1 hy1
      omega
    exact hno v hv
  have claim : ∀ n : ℕ, ∀ v : PeriodicLatticeSite L, AdalyFormal.L0C.bd y0 y0 v = n → ∃ y ∈ Om1, pdist v y < 3 * M + 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro v hn
      by_cases hv : v = y0
      · subst hv
        exact ⟨v, hy0, by rw [pd_self]; omega⟩
      · obtain ⟨v', -, hpd, hlt⟩ := AdalyFormal.L0C.exists_step (mem_bigBox y0 y0) (mem_bigBox y0 v) hv
        obtain ⟨y, hy, hyd⟩ := ih (AdalyFormal.L0C.bd y0 y0 v') (by omega) v' rfl
        apply H v
        refine ⟨y, hy, ?_⟩
        have := pd_tri v v' y
        omega
  obtain ⟨y, hy, hyd⟩ := claim _ w rfl
  have := hcol w hw y hy
  omega

/-- the aligned `M`-block of `v` -/
def blockOf (M : ℕ) (v : PeriodicLatticeSite L) : Set (PeriodicLatticeSite L) :=
  {u | ∀ μ : Fin 3, (u μ).val / M = (v μ).val / M}

theorem pcd_le_absdiff (N a b : ℕ) : pcd N a b ≤ (if a ≤ b then b - a else a - b) := by
  unfold pcd; exact min_le_left _ _

/-- sites of one aligned `M`-block are within `l^1`-distance `3 (M-1)` -/
theorem pdist_block_le {M : ℕ} (hM : 0 < M) {u v : PeriodicLatticeSite L} (h : u ∈ blockOf M v) : pdist u v + 3 ≤ 3 * M := by
  unfold pdist
  have hc : ∀ μ : Fin 3, pcd (L μ + 1) (u μ).val (v μ).val + 1 ≤ M := by
    intro μ
    have h1 := pcd_le_absdiff (L μ + 1) (u μ).val (v μ).val
    have h2 := h μ
    have h3 := Nat.div_add_mod (u μ).val M
    have h4 := Nat.div_add_mod (v μ).val M
    have h5 := Nat.mod_lt (u μ).val hM
    have h6 := Nat.mod_lt (v μ).val hM
    rw [h2] at h3
    generalize M * ((v μ).val / M) = X at h3 h4
    split_ifs at h1 <;> omega
  have := hc 0; have := hc 1; have := hc 2
  rw [Fin.sum_univ_three]
  omega

theorem blockOf_blockClosed {M : ℕ} (v : PeriodicLatticeSite L) : BlockClosed M (blockOf M v) := by
  intro x hx y hxy μ
  rw [hxy μ]; exact hx μ

theorem mem_blockOf_self (M : ℕ) (v : PeriodicLatticeSite L) : v ∈ blockOf M v := fun _ => rfl

end AdalyFormal.TwoDom

#print axioms AdalyFormal.TwoDom.regBody_mono_b
#print axioms AdalyFormal.TwoDom.glue_side
#print axioms AdalyFormal.TwoDom.regBody_glue
#print axioms AdalyFormal.TwoDom.far_block_exists
#print axioms AdalyFormal.TwoDom.pdist_block_le
