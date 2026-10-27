import MZ1
import DW1

/-!
# MZ2 -- a codimension-2 set costs only a k-free factor in the column geometric sum (m2_dlayer, 2026-10-15)

`b(x) = ℓ^{strat x − 1}`.  Blocks of side `b(x)` (cut at multiples of `b(x)`) lie in one stratum (`blk_strat`) and in one
`phiC`-oscillation window (`phiC_block`, 6θ).  A site set `P` all of whose points have stratum `≥ 2` and two coordinates next to
`b`-grid planes meets every such block in at most `12 b` points (`count_le`), while the block has at least `b³` points
(`blk_card_ge`).  Averaging over the block (`unc_sum`):
  `Σ_{x ∈ P} ℓ^{-2 strat x} e^{-2 φ x}  ≤  12 ℓ² e^{12θ} · Σ_x ℓ^{-4 strat x} e^{-2 φ x}`
for EVERY centre `c` of the Combes–Thomas weight `φ = phiC θ c` (DW1).  No `k`, torus, or tower constant.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M2DLayer

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.M1 (strat strat_le strat_eq_iff le_strat_of_mem not_mem_strat_succ mem_strat_of_pos om_anti)
open AdalyFormal.M1DStrat (phiC phiC_block)

variable {L : PeriodicLatticeExtent}

/-- `y` lies in the `b`-block of `x` -/
def SameBlk (b : ℕ) (x y : PeriodicLatticeSite L) : Prop := ∀ μ : Fin 3, (y μ).val / b = (x μ).val / b

theorem NP_of_dvd {b g t : ℕ} (hb : 1 ≤ b) (hbg : b ∣ g) (hg : 1 ≤ g) (h : NP g t) : NP b t := by
  rcases h with h | h
  · left; rw [← Nat.mod_mod_of_dvd t hbg, h, Nat.zero_mod]
  · right
    rw [← Nat.mod_mod_of_dvd t hbg, h]
    obtain ⟨c, rfl⟩ := hbg
    have hc : 1 ≤ c := by rcases Nat.eq_zero_or_pos c with h0 | h0 <;> [simp [h0] at hg; exact h0]
    rw [show b * c - 1 = (b - 1) + b * (c - 1) by
      cases c with
      | zero => omega
      | succ c => rw [Nat.mul_succ]; simp only [Nat.add_sub_cancel]; omega]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-! ## 1. block facts -/

theorem div_eq_of_div_eq {b m u v : ℕ} (h : u / b = v / b) : u / (b * m) = v / (b * m) := by
  rw [← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, h]

theorem blk_strat {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) {x y : PeriodicLatticeSite L}
    (hs : 1 ≤ strat S k x) (hxy : SameBlk (ell ^ (strat S k x - 1)) x y) :
    strat S k y = strat S k x ∧ y ∈ S.Om 0 := by
  set s := strat S k x with hsdef
  have hsk : s ≤ k := strat_le S k x
  have hxs : x ∈ S.Om s := mem_strat_of_pos hs
  -- `y` in the level-`s` block of `x`
  have hblk : ∀ m : ℕ, s ≤ m → m ≤ k → ∀ μ : Fin 3, (y μ).val / bigSide M ell m = (x μ).val / bigSide M ell m := by
    intro m hm _ μ
    have e : bigSide M ell m = ell ^ (s - 1) * (M * ell ^ (m - s + 1)) := by
      have hm' : m = (s - 1) + (m - s + 1) := by omega
      unfold bigSide
      conv_lhs => rw [hm', pow_add]
      ring
    rw [e]; exact div_eq_of_div_eq (hxy μ)
  have hys : y ∈ S.Om s := hS.2.2.2.1 s hsk x hxs y (fun μ => hblk s le_rfl hsk μ)
  have hyn : y ∉ S.Om (s + 1) := by
    intro hy1
    by_cases hk : s + 1 ≤ k
    · exact not_mem_strat_succ hS x
        (hS.2.2.2.1 (s + 1) hk y hy1 x (fun μ => (hblk (s + 1) (by omega) hk μ).symm))
    · rw [hS.2.1 (s + 1) (by omega)] at hy1; exact hy1
  have hy0 : y ∈ S.Om 0 := om_anti hS (Nat.zero_le _) hys
  exact ⟨((strat_eq_iff hS hsk y).1 ⟨hys, hyn⟩).2, hy0⟩

theorem diff_le_of_div {u v b : ℕ} (hb : 0 < b) (h : u / b = v / b) :
    (if u ≤ v then v - u else u - v) ≤ b - 1 := by
  have hu := Nat.div_add_mod u b
  have hv := Nat.div_add_mod v b
  have h1 := Nat.mod_lt u hb
  have h2 := Nat.mod_lt v hb
  rw [h] at hu
  generalize b * (v / b) = Q at hu hv
  split_ifs <;> omega

theorem pdist_blk {b : ℕ} (hb : 0 < b) {x y : PeriodicLatticeSite L} (hxy : SameBlk b x y) :
    pdist x y ≤ 3 * (b - 1) := by
  unfold pdist
  have hc : ∀ μ : Fin 3, pcd (L μ + 1) (x μ).val (y μ).val ≤ b - 1 := by
    intro μ
    unfold pcd
    exact (min_le_left _ _).trans (diff_le_of_div hb (hxy μ).symm)
  rw [Fin.sum_univ_three]
  have := hc 0; have := hc 1; have := hc 2
  omega

/-- the CT weight oscillates by at most `6θ` on a block -/
theorem phiC_blk {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hR : 1 ≤ R) (hM : 1 ≤ M)
    (hell : 2 ≤ ell) {θ : ℝ} (hθ : 0 ≤ θ) (c : PeriodicLatticeSite L) {x y : PeriodicLatticeSite L}
    (hs : 1 ≤ strat S k x) (hxy : SameBlk (ell ^ (strat S k x - 1)) x y) :
    |phiC S ell M R k θ c x - phiC S ell M R k θ c y| ≤ 6 * θ := by
  obtain ⟨hst, hy0⟩ := blk_strat hS hs hxy
  have hx0 : x ∈ S.Om 0 := AdalyFormal.M1DStrat.mem_om0_of_strat hS hs
  have hb : 0 < ell ^ (strat S k x - 1) := pow_pos (by omega) _
  have hpd := pdist_blk hb hxy
  have hpow : ell ^ (strat S k x - 1) ≤ ell ^ strat S k x := Nat.pow_le_pow_right (by omega) (by omega)
  have hpd' : pdist x y ≤ 3 * ell ^ strat S k x := by omega
  refine phiC_block hS hR hM hell hθ c hx0 hy0 rfl hst ?_
  exact_mod_cast hpd'

/-! ## 2. counting -/

theorem lt_of_blk {x N b r : ℕ} (hx : x < N) (hbN : b ∣ N) (hb : 0 < b) (hr : r < b) : x / b * b + r < N := by
  obtain ⟨m, rfl⟩ := hbN
  have h1 : x / b < m := (Nat.div_lt_iff_lt_mul hb).2 (by linarith [mul_comm b m])
  have h2 : (x / b + 1) * b ≤ m * b := Nat.mul_le_mul_right b h1
  rw [Nat.succ_mul] at h2
  linarith [mul_comm b m]

open Classical in
theorem blk_card_ge {b : ℕ} (hb : 0 < b) (hbN : ∀ μ, b ∣ L μ + 1) (x : PeriodicLatticeSite L) :
    b ^ 3 ≤ (Finset.univ.filter (fun y : PeriodicLatticeSite L => SameBlk b x y)).card := by
  let F : (Fin 3 → Fin b) → PeriodicLatticeSite L := fun r μ =>
    ⟨(x μ).val / b * b + (r μ).val, lt_of_blk (x μ).isLt (hbN μ) hb (r μ).isLt⟩
  have hcard : (Finset.univ : Finset (Fin 3 → Fin b)).card = b ^ 3 := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn F (fun r _ => ?_) (fun r _ r' _ h => ?_)
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    intro μ
    show ((x μ).val / b * b + (r μ).val) / b = (x μ).val / b
    rw [mul_comm, Nat.mul_add_div hb, Nat.div_eq_of_lt (r μ).isLt, add_zero]
  · funext μ
    have := congrArg (fun y : PeriodicLatticeSite L => (y μ).val) h
    simp only [F] at this
    exact Fin.ext (by omega)

/-- the `NP` pattern on `Fin b`-valued residues -/
def NPf {b : ℕ} (t : Fin b) : Prop := t.val = 0 ∨ t.val = b - 1

open Classical in
theorem card_S2 {b : ℕ} (hb : 0 < b) : (Finset.univ.filter (fun t : Fin b => NPf t)).card ≤ 2 := by
  have hsub : Finset.univ.filter (fun t : Fin b => NPf t) ⊆ {⟨0, hb⟩, ⟨b - 1, by omega⟩} := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, NPf] at ht
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases ht with h | h
    · left; exact Fin.ext h
    · right; exact Fin.ext h
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_insert_le _ _).trans ?_
  simp

open Classical in
theorem card_U {b : ℕ} (hb : 0 < b) (a c : Fin 3) (hac : a ≠ c) :
    (Finset.univ.filter (fun r : Fin 3 → Fin b => NPf (r a) ∧ NPf (r c))).card ≤ 4 * b := by
  have h2 := card_S2 hb
  let t : Fin 3 → Finset (Fin b) := fun μ =>
    if μ = a ∨ μ = c then Finset.univ.filter (fun t : Fin b => NPf t) else Finset.univ
  have hsub : Finset.univ.filter (fun r : Fin 3 → Fin b => NPf (r a) ∧ NPf (r c)) ⊆ Fintype.piFinset t := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    rw [Fintype.mem_piFinset]
    intro μ
    simp only [t]
    split_ifs with hμ
    · rcases hμ with rfl | rfl
      · simp [hr.1]
      · simp [hr.2]
    · exact Finset.mem_univ _
  have key : ∀ μ, (t μ).card ≤ if μ = a ∨ μ = c then 2 else b := by
    intro μ
    simp only [t]
    split_ifs
    · exact h2
    · rw [Finset.card_univ, Fintype.card_fin]
  refine (Finset.card_le_card hsub).trans ?_
  rw [Fintype.card_piFinset]
  refine (Finset.prod_le_prod' (fun μ _ => key μ)).trans ?_
  rw [Fin.prod_univ_three]
  fin_cases a <;> fin_cases c <;> simp at hac ⊢ <;> omega

open Classical in
theorem card_T {b : ℕ} (hb : 0 < b) :
    (Finset.univ.filter (fun r : Fin 3 → Fin b => ∃ a c : Fin 3, a ≠ c ∧ NPf (r a) ∧ NPf (r c))).card ≤ 12 * b := by
  have hsub : Finset.univ.filter (fun r : Fin 3 → Fin b => ∃ a c : Fin 3, a ≠ c ∧ NPf (r a) ∧ NPf (r c)) ⊆
      (Finset.univ.filter (fun r : Fin 3 → Fin b => NPf (r 0) ∧ NPf (r 1))) ∪
      (Finset.univ.filter (fun r : Fin 3 → Fin b => NPf (r 0) ∧ NPf (r 2))) ∪
      (Finset.univ.filter (fun r : Fin 3 → Fin b => NPf (r 1) ∧ NPf (r 2))) := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    obtain ⟨a, c, hac, ha, hc⟩ := hr
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    fin_cases a <;> fin_cases c <;> simp at hac <;> tauto
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_union_le _ _).trans ?_
  have h1 := card_U hb 0 1 (by decide)
  have h2 := card_U hb 0 2 (by decide)
  have h3 := card_U hb 1 2 (by decide)
  have h4 := Finset.card_union_le (Finset.univ.filter (fun r : Fin 3 → Fin b => NPf (r 0) ∧ NPf (r 1)))
    (Finset.univ.filter (fun r : Fin 3 → Fin b => NPf (r 0) ∧ NPf (r 2)))
  omega

open Classical in
/-- a `b`-block meets the two-plane set in at most `12 b` sites -/
theorem count_le {b : ℕ} (hb : 0 < b) (y : PeriodicLatticeSite L) (Q : PeriodicLatticeSite L → Prop)
    (hQ : ∀ x, Q x → SameBlk b y x → ∃ a c : Fin 3, a ≠ c ∧ NP b (x a).val ∧ NP b (x c).val) :
    (Finset.univ.filter (fun x : PeriodicLatticeSite L => Q x ∧ SameBlk b y x)).card ≤ 12 * b := by
  let G : PeriodicLatticeSite L → (Fin 3 → Fin b) := fun x μ => ⟨(x μ).val % b, Nat.mod_lt _ hb⟩
  refine le_trans ?_ (card_T hb)
  refine Finset.card_le_card_of_injOn G (fun x hx => ?_) (fun x hx x' hx' h => ?_)
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢
    obtain ⟨a, c, hac, ha, hc⟩ := hQ x hx.1 hx.2
    exact ⟨a, c, hac, ha, hc⟩
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx hx'
    funext μ
    have h1 := congrArg (fun r : Fin 3 → Fin b => (r μ).val) h
    simp only [G] at h1
    have e1 := Nat.div_add_mod (x μ).val b
    have e2 := Nat.div_add_mod (x' μ).val b
    have hq : (x μ).val / b = (x' μ).val / b := (hx.2 μ).trans (hx'.2 μ).symm
    rw [hq, h1] at e1
    exact Fin.ext (by omega)

/-! ## 3. the averaging -/

theorem NP_one (t : ℕ) : NP 1 t := Or.inl (Nat.mod_one t)

open Classical in
/-- **the codimension-2 averaging**: the two-plane set costs `12 ℓ² e^{12θ}` times the bulk column sum. -/
theorem unc_sum {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hR : 1 ≤ R) (hM : 1 ≤ M)
    (hell : 2 ≤ ell) {θ : ℝ} (hθ : 0 ≤ θ) (c : PeriodicLatticeSite L) (P : PeriodicLatticeSite L → Prop)
    (hP : ∀ x, P x → 1 ≤ strat S k x ∧ ∃ a a' : Fin 3, a ≠ a' ∧ NP (ell ^ (strat S k x - 1)) (x a).val ∧
      NP (ell ^ (strat S k x - 1)) (x a').val) :
    ∑ x ∈ Finset.univ.filter P, (((ell : ℝ) ^ strat S k x)⁻¹) ^ 2 * Real.exp (-(2 * phiC S ell M R k θ c x))
      ≤ 12 * (ell : ℝ) ^ 2 * Real.exp (12 * θ) *
        ∑ x : PeriodicLatticeSite L, (((ell : ℝ) ^ strat S k x)⁻¹) ^ 4 * Real.exp (-(2 * phiC S ell M R k θ c x)) := by
  set φ := phiC S ell M R k θ c with hφ
  set bb : PeriodicLatticeSite L → ℕ := fun x => ell ^ (strat S k x - 1) with hbb
  set f : PeriodicLatticeSite L → ℝ := fun x => (((ell : ℝ) ^ strat S k x)⁻¹) ^ 2 * Real.exp (-(2 * φ x)) with hf
  set h : PeriodicLatticeSite L → ℝ := fun x => (((ell : ℝ) ^ strat S k x)⁻¹) ^ 4 * Real.exp (-(2 * φ x)) with hh
  set w : PeriodicLatticeSite L → ℝ := fun x =>
    (ell : ℝ) ^ (2 * strat S k x) * Real.exp (12 * θ) / ((bb x : ℕ) : ℝ) ^ 3 with hw
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast (show 1 ≤ ell by omega)
  have hl0 : (0 : ℝ) < ell := by linarith
  have hbpos : ∀ x, 0 < bb x := fun x => pow_pos (by omega) _
  have hbposr : ∀ x, (0 : ℝ) < ((bb x : ℕ) : ℝ) := fun x => by exact_mod_cast hbpos x
  have hh0 : ∀ x, 0 ≤ h x := fun x => by simp only [hh]; positivity
  have hf0 : ∀ x, 0 ≤ f x := fun x => by simp only [hf]; positivity
  have hw0 : ∀ x, 0 ≤ w x := fun x => by simp only [hw]; have := hbposr x; positivity
  have hbN : ∀ x, ∀ μ, bb x ∣ L μ + 1 := by
    intro x μ
    have h1 := hS.2.2.1 (strat S k x - 1) (by have := strat_le S k x; omega) μ
    exact (Dvd.intro_left M rfl).trans h1
  -- step 1: one point against its block
  have step1 : ∀ x, P x → f x ≤ w x * ∑ y ∈ Finset.univ.filter (fun y => SameBlk (bb x) x y), h y := by
    intro x hx
    have hs := (hP x hx).1
    set B := Finset.univ.filter (fun y => SameBlk (bb x) x y) with hB
    have hcard : bb x ^ 3 ≤ B.card := blk_card_ge (hbpos x) (hbN x) x
    have hpt : ∀ y ∈ B, f x ≤ (ell : ℝ) ^ (2 * strat S k x) * Real.exp (12 * θ) * h y := by
      intro y hy
      have hy' : SameBlk (bb x) x y := (Finset.mem_filter.1 hy).2
      obtain ⟨hst, -⟩ := blk_strat hS hs hy'
      have hosc := phiC_blk hS hR hM hell hθ c hs hy'
      have hab := abs_le.1 hosc
      have hex : Real.exp (-(2 * φ x)) ≤ Real.exp (12 * θ) * Real.exp (-(2 * φ y)) := by
        rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by rw [hφ]; linarith)
      simp only [hf, hh, hst]
      have hp : (0 : ℝ) < (ell : ℝ) ^ strat S k x := by positivity
      have e1 : (ell : ℝ) ^ (2 * strat S k x) * ((((ell : ℝ) ^ strat S k x)⁻¹) ^ 4)
          = (((ell : ℝ) ^ strat S k x)⁻¹) ^ 2 := by
        rw [pow_mul']; field_simp
      calc (((ell : ℝ) ^ strat S k x)⁻¹) ^ 2 * Real.exp (-(2 * φ x))
          ≤ (((ell : ℝ) ^ strat S k x)⁻¹) ^ 2 * (Real.exp (12 * θ) * Real.exp (-(2 * φ y))) :=
            mul_le_mul_of_nonneg_left hex (by positivity)
        _ = (ell : ℝ) ^ (2 * strat S k x) * Real.exp (12 * θ)
              * ((((ell : ℝ) ^ strat S k x)⁻¹) ^ 4 * Real.exp (-(2 * φ y))) := by rw [← e1]; ring
    have hsum : (B.card : ℝ) * f x ≤ (ell : ℝ) ^ (2 * strat S k x) * Real.exp (12 * θ) * ∑ y ∈ B, h y := by
      rw [← nsmul_eq_mul, ← Finset.sum_const, Finset.mul_sum]
      exact Finset.sum_le_sum hpt
    have hc3 : ((bb x : ℕ) : ℝ) ^ 3 ≤ (B.card : ℝ) := by exact_mod_cast hcard
    have h3 : ((bb x : ℕ) : ℝ) ^ 3 * f x ≤ (ell : ℝ) ^ (2 * strat S k x) * Real.exp (12 * θ) * ∑ y ∈ B, h y :=
      (mul_le_mul_of_nonneg_right hc3 (hf0 x)).trans hsum
    have hb3 : (0 : ℝ) < ((bb x : ℕ) : ℝ) ^ 3 := by have := hbposr x; positivity
    simp only [hw]
    rw [div_mul_eq_mul_div, le_div_iff₀ hb3]
    linarith
  -- step 2: as a double sum
  have step2 : ∑ x ∈ Finset.univ.filter P, f x
      ≤ ∑ x : PeriodicLatticeSite L, ∑ y : PeriodicLatticeSite L,
          (if P x ∧ SameBlk (bb x) x y then w x * h y else 0) := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum (fun x _ => ?_)
    by_cases hx : P x
    · rw [if_pos hx]
      refine (step1 x hx).trans (le_of_eq ?_)
      rw [Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      by_cases hy : SameBlk (bb x) x y
      · rw [if_pos hy, if_pos ⟨hx, hy⟩]
      · simp [hy]
    · rw [if_neg hx]
      refine le_of_eq (Finset.sum_eq_zero (fun y _ => ?_)).symm
      rw [if_neg (fun h' => hx h'.1)]
  -- step 3: each `y` is counted at most `12 b` times
  have step3 : ∀ y : PeriodicLatticeSite L, ∑ x : PeriodicLatticeSite L,
      (if P x ∧ SameBlk (bb x) x y then w x * h y else 0) ≤ 12 * (ell : ℝ) ^ 2 * Real.exp (12 * θ) * h y := by
    intro y
    have hle : ∀ x, (if P x ∧ SameBlk (bb x) x y then w x * h y else 0)
        ≤ (if P x ∧ SameBlk (bb y) y x then w y * h y else 0) := by
      intro x
      by_cases hc : P x ∧ SameBlk (bb x) x y
      · obtain ⟨hst, -⟩ := blk_strat hS (hP x hc.1).1 hc.2
        have hb : bb y = bb x := by simp only [hbb, hst]
        have hwy : w y = w x := by simp only [hw, hbb, hst]
        have hsb : SameBlk (bb y) y x := fun μ => by rw [hb]; exact (hc.2 μ).symm
        rw [if_pos hc, if_pos ⟨hc.1, hsb⟩, hwy]
      · rw [if_neg hc]
        split_ifs
        · exact mul_nonneg (hw0 y) (hh0 y)
        · exact le_rfl
    have hcnt : (Finset.univ.filter (fun x => P x ∧ SameBlk (bb y) y x)).card ≤ 12 * bb y := by
      refine count_le (hbpos y) y P (fun x hx hxy => ?_)
      by_cases hsy : 1 ≤ strat S k y
      · have hxy' : SameBlk (ell ^ (strat S k y - 1)) y x := hxy
        obtain ⟨hst, -⟩ := blk_strat hS hsy hxy'
        obtain ⟨-, a, a', haa, ha, ha'⟩ := hP x hx
        refine ⟨a, a', haa, ?_, ?_⟩
        · show NP (ell ^ (strat S k y - 1)) _; rw [← hst]; exact ha
        · show NP (ell ^ (strat S k y - 1)) _; rw [← hst]; exact ha'
      · have h1 : bb y = 1 := by simp only [hbb]; rw [show strat S k y - 1 = 0 by omega, pow_zero]
        rw [h1]
        exact ⟨0, 1, by decide, NP_one _, NP_one _⟩
    have hkey : (ell : ℝ) ^ (2 * strat S k y) ≤ (ell : ℝ) ^ 2 * ((bb y : ℕ) : ℝ) ^ 2 := by
      simp only [hbb]; push_cast
      rw [← pow_mul, ← pow_add]
      exact pow_le_pow_right₀ hellr (by omega)
    calc ∑ x : PeriodicLatticeSite L, (if P x ∧ SameBlk (bb x) x y then w x * h y else 0)
        ≤ ∑ x : PeriodicLatticeSite L, (if P x ∧ SameBlk (bb y) y x then w y * h y else 0) :=
          Finset.sum_le_sum (fun x _ => hle x)
      _ = w y * h y * ((Finset.univ.filter (fun x => P x ∧ SameBlk (bb y) y x)).card : ℝ) := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ w y * h y * (12 * ((bb y : ℕ) : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hw0 y) (hh0 y))
          exact_mod_cast hcnt
      _ = 12 * Real.exp (12 * θ) * h y * ((ell : ℝ) ^ (2 * strat S k y) / ((bb y : ℕ) : ℝ) ^ 2) := by
          simp only [hw]; have := hbposr y; field_simp
      _ ≤ 12 * Real.exp (12 * θ) * h y * (ell : ℝ) ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (by have := hh0 y; positivity)
          rw [div_le_iff₀ (by have := hbposr y; positivity)]; exact hkey
      _ = 12 * (ell : ℝ) ^ 2 * Real.exp (12 * θ) * h y := by ring
  calc ∑ x ∈ Finset.univ.filter P, f x
      ≤ ∑ x : PeriodicLatticeSite L, ∑ y : PeriodicLatticeSite L,
          (if P x ∧ SameBlk (bb x) x y then w x * h y else 0) := step2
    _ = ∑ y : PeriodicLatticeSite L, ∑ x : PeriodicLatticeSite L,
          (if P x ∧ SameBlk (bb x) x y then w x * h y else 0) := Finset.sum_comm
    _ ≤ ∑ y : PeriodicLatticeSite L, 12 * (ell : ℝ) ^ 2 * Real.exp (12 * θ) * h y :=
        Finset.sum_le_sum (fun y _ => step3 y)
    _ = 12 * (ell : ℝ) ^ 2 * Real.exp (12 * θ) * ∑ y : PeriodicLatticeSite L, h y := by rw [Finset.mul_sum]

#print axioms SameBlk
#print axioms NP_of_dvd
#print axioms div_eq_of_div_eq
#print axioms blk_strat
#print axioms diff_le_of_div
#print axioms pdist_blk
#print axioms phiC_blk
#print axioms lt_of_blk
#print axioms blk_card_ge
#print axioms NPf
#print axioms card_S2
#print axioms card_U
#print axioms card_T
#print axioms count_le
#print axioms NP_one
#print axioms unc_sum

end AdalyFormal.M2DLayer
