import MR7

/-!
# GL1 -- the WRAP tower: a printed-admissible, covered tower whose class cubes are all short in direction 0
(m2_glue, 2026-10-15)

Fine torus of side `N = 7 T` in every direction, `T = M ℓ^{n+1}` (`n ≥ 1`, height `k = n + 1`):
`Ω_j = torus` for `j ≤ n`, `Ω_{n+1} = Blk` (the single level-`(n+1)` block `[0,T)³`), `Ω_j = ∅` above.
* `wt_admissible` : `Admissible ell M R (n+1) (WT …)` for EVERY `R` (the base law and collars are vacuous/trivial).
* `wt_class_index` : every class cube (factor 12) has index `n` (side `12 M ℓ^n < N`, so it never wraps).
* `uw_trivial_on_box` : the configuration `Uw` (`-1` on the bonds `(x, 0)` with `x₀ = N-1`, `1` elsewhere) is gauge
  trivial (`U^g = 1`) on the bonds of every box of side `< N`.
* `wt_perCube` : `PerCubeRegular2 ell M 12 (n+1) (WT …) α₀ η Uw` for EVERY `α₀ > 0`, `η > 0` (`A = 0` in every cube).
* `wt_coversp` : `CoversOm0p ell M 12 (n+1) (WT …)` (sites and plaquettes) for `2 ≤ ℓ ≤ 11`, `36 ≤ R ℓ`.
* `wt_classCoupled` : `ClassCoupled ell M 12 (n+1) (WT …) α₀ η Uw`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.M2Glue

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (Ball)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobNorm_zero)
open AdalyFormal.Balaban.SuTwoLogExp (M2 su2NegOne coe_su2NegOne)
open AdalyFormal.M1NonFlat (SU2)
open AdalyFormal.M2Bridge (cube_isClass)
open AdalyFormal.M2Route (shift_comm HT_zero)

variable {L : PeriodicLatticeExtent}

/-- the single top block `[0,T)³`. -/
def Blk (T : ℕ) : Set (PeriodicLatticeSite L) := {x | ∀ σ, (x σ).val < T}

/-- the wrap tower of height `n + 1`. -/
def WT (L : PeriodicLatticeExtent) (M ell n : ℕ) : Tower L :=
  ⟨fun j => if j ≤ n then Set.univ else if j = n + 1 then Blk (M * ell ^ (n + 1)) else ∅⟩

theorem wt_le {M ell n j : ℕ} (h : j ≤ n) : (WT L M ell n).Om j = Set.univ := by
  simp only [WT]; rw [if_pos h]

theorem wt_top {M ell n : ℕ} : (WT L M ell n).Om (n + 1) = Blk (M * ell ^ (n + 1)) := by
  simp [WT]

theorem wt_gt {M ell n j : ℕ} (h : n + 1 < j) : (WT L M ell n).Om j = ∅ := by
  simp only [WT]; rw [if_neg (by omega), if_neg (by omega)]

theorem pdist_self' (x : PeriodicLatticeSite L) : pdist x x = 0 := by
  unfold pdist pcd; simp

/-- the forward shift, coordinatewise, without `%`. -/
theorem shift_val' (x : PeriodicLatticeSite L) (μ σ : Fin 3) :
    (periodicLatticeShift x μ σ).val =
      if σ = μ then (if (x σ).val = L σ then 0 else (x σ).val + 1) else (x σ).val := by
  unfold periodicLatticeShift
  by_cases h : σ = μ
  · subst h
    rw [Function.update_self, if_pos rfl, Fin.val_add_one]
    by_cases h1 : x σ = Fin.last (L σ)
    · rw [if_pos h1, if_pos (by rw [h1, Fin.val_last])]
    · rw [if_neg h1, if_neg (fun h2 => h1 (Fin.ext (by rw [h2, Fin.val_last])))]
  · rw [Function.update_of_ne h, if_neg h]

/-- a site from coordinates. -/
def mkN {M ell n : ℕ} (hL : ∀ μ, L μ + 1 = 7 * (M * ell ^ (n + 1))) (f : Fin 3 → ℕ)
    (hf : ∀ σ, f σ < 7 * (M * ell ^ (n + 1))) : PeriodicLatticeSite L :=
  fun σ => ⟨f σ, by have := hL σ; have := hf σ; omega⟩

theorem mkN_val {M ell n : ℕ} (hL : ∀ μ, L μ + 1 = 7 * (M * ell ^ (n + 1))) (f : Fin 3 → ℕ)
    (hf : ∀ σ, f σ < 7 * (M * ell ^ (n + 1))) (σ : Fin 3) : ((mkN hL f hf) σ).val = f σ := rfl

/-- the point `(T, 0, 0)` (outside the top block). -/
def pT {M ell n : ℕ} (hM : 0 < M) (hell : 0 < ell) (hL : ∀ μ, L μ + 1 = 7 * (M * ell ^ (n + 1))) :
    PeriodicLatticeSite L :=
  mkN hL (fun σ => if σ = 0 then M * ell ^ (n + 1) else 0)
    (fun σ => by have : 0 < M * ell ^ (n + 1) := Nat.mul_pos hM (pow_pos hell _); split_ifs <;> omega)

/-- the block corner of `x` at level `n`. -/
def zc {M ell n : ℕ} (hL : ∀ μ, L μ + 1 = 7 * (M * ell ^ (n + 1))) (x : PeriodicLatticeSite L) :
    PeriodicLatticeSite L :=
  mkN hL (fun σ => (M * ell ^ n) * ((x σ).val / (M * ell ^ n)))
    (fun σ => by
      have := Nat.mul_div_le (x σ).val (M * ell ^ n)
      have := (x σ).isLt; have := hL σ
      omega)

theorem zc_val {M ell n : ℕ} (hL : ∀ μ, L μ + 1 = 7 * (M * ell ^ (n + 1))) (x : PeriodicLatticeSite L)
    (σ : Fin 3) : ((zc hL x) σ).val = (M * ell ^ n) * ((x σ).val / (M * ell ^ n)) := rfl

section tower
variable {M ell n : ℕ} (hM : 0 < M) (hell : 0 < ell) (hn : 1 ≤ n)
  (hL : ∀ μ, L μ + 1 = 7 * (M * ell ^ (n + 1)))
include hM hell hn hL

theorem wt_admissible (R : ℕ) : Admissible ell M R (n + 1) (WT L M ell n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j x hx
    by_cases h : j ≤ n
    · rw [wt_le h]; trivial
    · rw [wt_gt (show n + 1 < j + 1 by omega)] at hx; exact hx.elim
  · intro j hj; exact wt_gt hj
  · intro j hj μ
    rw [hL μ]; unfold bigSide
    exact Dvd.dvd.mul_left (mul_dvd_mul_left M (pow_dvd_pow ell hj)) 7
  · intro j hj x hx y hy
    by_cases h : j ≤ n
    · rw [wt_le h]; trivial
    · have hj' : j = n + 1 := by omega
      subst hj'
      rw [wt_top] at hx ⊢
      intro σ
      have hx' := hx σ
      have hT : 0 < M * ell ^ (n + 1) := by positivity
      have h1 := hy σ
      unfold bigSide at h1
      have h2 : (x σ).val / (M * ell ^ (n + 1)) = 0 := Nat.div_eq_of_lt hx'
      rw [h2] at h1
      by_contra hc
      push_neg at hc
      have := Nat.div_pos hc hT
      omega
  · intro j hj x hx y hy
    by_cases h : j ≤ n
    · rw [wt_le h] at hx; exact (hx trivial).elim
    · rw [wt_gt (show n + 1 < j + 1 by omega)] at hy; exact hy.elim
  · intro x
    constructor
    · intro _
      refine ⟨x, ?_, x, fun _ => rfl, ?_⟩
      · rw [wt_le hn]; trivial
      · rw [pdist_self']; exact Nat.zero_le _
    · intro _; rw [wt_le (Nat.zero_le n)]; trivial

theorem T_pos : 0 < M * ell ^ (n + 1) := by positivity

theorem T_eq : M * ell ^ (n + 1) = ell * (M * ell ^ n) := by ring

theorem pT_not_blk : pT hM hell hL ∉ (Blk (M * ell ^ (n + 1)) : Set (PeriodicLatticeSite L)) := by
  intro h
  have := h 0
  simp [pT, mkN_val] at this

/-- **every class cube has index `n`**. -/
theorem wt_class_index {sites : Set (PeriodicLatticeSite L)} {j : ℕ}
    (hq : IsClassCube ell M 12 (n + 1) (WT L M ell n) sites j) : j = n := by
  obtain ⟨⟨hjk, ⟨z, -, hsz⟩, hsub, ⟨p, -, hpB⟩⟩, -⟩ := hq
  by_contra hne
  rcases Nat.lt_or_ge j n with hlt | hge
  · exact hpB.2 (by rw [wt_le (show j + 1 ≤ n by omega)]; trivial)
  · have hj : j = n + 1 := by omega
    subst hj
    have hin : pT hM hell hL ∈ sites := by
      rw [hsz]
      intro σ
      have hl := hL σ
      have hT := T_pos hM hell hn hL
      refine lt_of_lt_of_le (Nat.mod_lt _ (by omega)) ?_
      unfold bigSide; omega
    rcases hsub hin with h1 | h1
    · exact pT_not_blk hM hell hn hL (by have := h1.1; rwa [wt_top] at this)
    · have := h1.1; rw [wt_gt (by omega)] at this; exact this
end tower

/-! ## the configuration and its triviality on short boxes -/

/-- `Uw` : `-1` on the bonds `(x, 0)` with `x₀ = L 0` (the last slice), `1` elsewhere. -/
noncomputable def Uw : LinkCfg L := fun e => if e.2 = 0 ∧ (e.1 0).val = L 0 then su2NegOne else 1

/-- the cube gauge: `-1` before the window start `z0` in direction 0, `1` from it on. -/
noncomputable def gz (z0 : ℕ) : PeriodicLatticeSite L → SU2 := fun x => if (x 0).val < z0 then su2NegOne else 1

theorem negOne_mul_negOne : (su2NegOne : SU2) * su2NegOne = 1 := by
  apply Subtype.ext
  show ((su2NegOne : SU2) : M2) * ((su2NegOne : SU2) : M2) = 1
  rw [coe_su2NegOne]; simp

theorem negOne_inv : (su2NegOne : SU2)⁻¹ = su2NegOne := by
  rw [inv_eq_iff_mul_eq_one]; exact negOne_mul_negOne

theorem uw_trivial_on_box (z : PeriodicLatticeSite L) (s : ℕ) (hs : s < L 0 + 1) (e : Bond L)
    (he : CubeBond (siteBox z s) e) : periodicGaugeTransform (gz (z 0).val) Uw e = 1 := by
  obtain ⟨x, μ⟩ := e
  obtain ⟨hx, hy⟩ := he
  have hx0 := hx 0
  have hy0 := hy 0
  have hxl := (x 0).isLt
  have hzl := (z 0).isLt
  unfold periodicGaugeTransform Uw gz
  by_cases hμ : μ = 0
  · subst hμ
    have hs0 := shift_val' x 0 0
    rw [if_pos rfl] at hs0
    by_cases ht : (x 0).val = L 0
    · rw [if_pos ht] at hs0
      have hz : 0 < (z 0).val := by
        by_contra hz0
        have hz0' : (z 0).val = 0 := by omega
        have : ((x 0).val + (L 0 + 1) - (z 0).val) % (L 0 + 1) = L 0 := by
          rw [hz0', Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega), ht]
        rw [this] at hx0; omega
      simp only [hs0, ht, and_self, if_true]
      rw [if_neg (by omega), if_pos hz, one_mul, negOne_inv, negOne_mul_negOne]
    · rw [if_neg ht] at hs0
      have hne : (x 0).val + 1 ≠ (z 0).val := by
        intro h1
        have : ((x 0).val + (L 0 + 1) - (z 0).val) % (L 0 + 1) = L 0 := by
          rw [show (x 0).val + (L 0 + 1) - (z 0).val = L 0 by omega]; exact Nat.mod_eq_of_lt (by omega)
        rw [this] at hx0; omega
      simp only [hs0, ht, and_false, if_false, mul_one]
      by_cases h1 : (x 0).val < (z 0).val
      · rw [if_pos h1, if_pos (by omega), mul_inv_cancel]
      · rw [if_neg h1, if_neg (by omega), mul_inv_cancel]
  · have hs0 := shift_val' x μ 0
    rw [if_neg (fun h => hμ h.symm)] at hs0
    simp only [hs0, hμ, false_and, if_false, mul_one, mul_inv_cancel]

/-- the window estimate: a coordinate `v ∈ {x, x+1}` sits at offset `≤ b` from the block corner of `x`. -/
theorem win_le (N x b : ℕ) (hx : x < N) (hb : 0 < b) (v : ℕ)
    (hv : v = x ∨ v = (if x = N - 1 then 0 else x + 1)) :
    (v + N - b * (x / b)) % N ≤ b := by
  have hd := Nat.div_add_mod x b
  have hm := Nat.mod_lt x hb
  rcases hv with h | h <;> rw [h]
  · rw [show x + N - b * (x / b) = (x - b * (x / b)) + N by omega, Nat.add_mod_right]
    exact (Nat.mod_le _ _).trans (by omega)
  · split_ifs with h
    · exact (Nat.mod_le _ _).trans (by omega)
    · rw [show x + 1 + N - b * (x / b) = (x + 1 - b * (x / b)) + N by omega, Nat.add_mod_right]
      exact (Nat.mod_le _ _).trans (by omega)

section cubes
variable {M ell n : ℕ} (hM : 0 < M) (hell : 0 < ell) (hn : 1 ≤ n)
  (hL : ∀ μ, L μ + 1 = 7 * (M * ell ^ (n + 1)))
include hM hell hn hL

theorem side_lt (hell2 : 2 ≤ ell) : 12 * bigSide M ell n < L 0 + 1 := by
  rw [hL 0, T_eq hM hell hn hL]
  unfold bigSide
  have hb : 0 < M * ell ^ n := by positivity
  nlinarith

/-- **the class at every `α₀ > 0`**: `A = 0` in every class cube. -/
theorem wt_perCube (hell2 : 2 ≤ ell) (α₀ η : ℝ) (hα : 0 < α₀) (hη : 0 < η) :
    PerCubeRegular2 ell M 12 (n + 1) (WT L M ell n) α₀ η Uw := by
  intro sites j hq
  have hj := wt_class_index hM hell hn hL hq
  obtain ⟨⟨-, ⟨z, -, hsz⟩, -, -⟩, -⟩ := hq
  subst hj
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hlr : (0 : ℝ) < ell := by exact_mod_cast hell
  refine ⟨gz (z 0).val, fun _ => 0, fun e he => ⟨HT_zero, ?_, ?_⟩, fun μ ν x _ _ => ?_, fun μ x _ => ?_⟩
  · rw [hsz] at he
    rw [uw_trivial_on_box z _ (side_lt hM hell hn hL hell2) e he]
    simp [NormedSpace.exp_zero]
  · rw [frobNorm_zero]; positivity
  · simp only [sub_self, smul_zero, frobNorm_zero]; positivity
  · have h0 : ddA η (fun _ => (0 : M2)) x μ = 0 := by
      unfold ddA curlA; simp
    rw [h0, frobNorm_zero]; positivity

theorem in_zc_box (x y : PeriodicLatticeSite L)
    (hy : ∀ σ, (y σ).val = (x σ).val ∨ (y σ).val = (if (x σ).val = L σ then 0 else (x σ).val + 1)) :
    y ∈ siteBox (zc hL x) (12 * bigSide M ell n) := by
  intro σ
  have hb : 0 < M * ell ^ n := by positivity
  have hxl := (x σ).isLt
  have h := win_le (L σ + 1) (x σ).val (M * ell ^ n) hxl hb (y σ).val
    (by rcases hy σ with h1 | h1
        · exact Or.inl h1
        · right; rw [h1]; simp only [Nat.add_sub_cancel])
  show ((y σ).val + (L σ + 1) - ((zc hL x) σ).val) % (L σ + 1) < 12 * bigSide M ell n
  rw [zc_val]
  unfold bigSide; omega

/-- a site of the `zc`-box outside the top block. -/
theorem zc_witness (hell11 : ell ≤ 11) (x : PeriodicLatticeSite L) :
    ∃ y ∈ siteBox (zc hL x) (12 * bigSide M ell n), y ∈ towerBj (WT L M ell n) n := by
  have hb : 0 < M * ell ^ n := by positivity
  have hT := T_eq hM hell hn hL
  set z := zc hL x with hz
  by_cases hz0 : M * ell ^ (n + 1) ≤ (z 0).val
  · refine ⟨z, fun σ => ?_, ?_, ?_⟩
    · show ((z σ).val + (L σ + 1) - (z σ).val) % (L σ + 1) < 12 * bigSide M ell n
      rw [Nat.add_sub_cancel_left, Nat.mod_self]; unfold bigSide; omega
    · rw [wt_le le_rfl]; trivial
    · rw [wt_top]; intro h; have := h 0; omega
  · push_neg at hz0
    have hzl : ∀ σ, (z σ).val < 7 * (M * ell ^ (n + 1)) := fun σ => by have := (z σ).isLt; have := hL σ; omega
    let y := mkN hL (fun σ => if σ = 0 then M * ell ^ (n + 1) else (z σ).val)
      (fun σ => by have := hzl σ; split_ifs <;> omega)
    refine ⟨y, fun σ => ?_, ?_, ?_⟩
    · show ((y σ).val + (L σ + 1) - (z σ).val) % (L σ + 1) < 12 * bigSide M ell n
      rw [mkN_val]
      have hl := hL σ
      by_cases hσ : σ = 0
      · subst hσ
        rw [if_pos rfl, show M * ell ^ (n + 1) + (L 0 + 1) - (z 0).val = (M * ell ^ (n + 1) - (z 0).val) + (L 0 + 1)
          by omega, Nat.add_mod_right]
        refine lt_of_le_of_lt (Nat.mod_le _ _) ?_
        unfold bigSide
        have : ell * (M * ell ^ n) ≤ 11 * (M * ell ^ n) := Nat.mul_le_mul_right _ hell11
        omega
      · rw [if_neg hσ, Nat.add_sub_cancel_left, Nat.mod_self]; unfold bigSide; omega
    · rw [wt_le le_rfl]; trivial
    · rw [wt_top]; intro h; have := h 0; simp [y, mkN_val] at this

theorem zc_class (hell2 : 2 ≤ ell) (hell11 : ell ≤ 11) {R : ℕ} (hR : 3 * 12 ≤ R * ell) (x : PeriodicLatticeSite L) :
    IsClassCube ell M 12 (n + 1) (WT L M ell n) (siteBox (zc hL x) (12 * bigSide M ell n)) n := by
  obtain ⟨y, hyQ, hy⟩ := zc_witness hM hell hn hL hell11 x
  refine cube_isClass (wt_admissible hM hell hn hL R) (by omega) ?_ (by rw [wt_le le_rfl]; exact Set.subset_univ _) hyQ hy hR
  intro σ
  show (M * ell ^ n) * ((x σ).val / (M * ell ^ n)) % bigSide M ell n = 0
  unfold bigSide; exact Nat.mul_mod_right _ _

theorem wt_plaq_cover (hell2 : 2 ≤ ell) (hell11 : ell ≤ 11) {R : ℕ} (hR : 3 * 12 ≤ R * ell)
    (x : PeriodicLatticeSite L) {μ ν : Fin 3} (hμν : μ ≠ ν) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube ell M 12 (n + 1) (WT L M ell n) sites j ∧
      x ∈ sites ∧ periodicLatticeShift x μ ∈ sites ∧ periodicLatticeShift x ν ∈ sites ∧
      periodicLatticeShift (periodicLatticeShift x μ) ν ∈ sites := by
  refine ⟨_, n, zc_class hM hell hn hL hell2 hell11 hR x, ?_, ?_, ?_, ?_⟩
  · exact in_zc_box hM hell hn hL x x (fun _ => Or.inl rfl)
  · refine in_zc_box hM hell hn hL x _ (fun σ => ?_)
    rw [shift_val']; split_ifs <;> simp_all
  · refine in_zc_box hM hell hn hL x _ (fun σ => ?_)
    rw [shift_val']; split_ifs <;> simp_all
  · refine in_zc_box hM hell hn hL x _ (fun σ => ?_)
    rw [shift_val', shift_val']
    by_cases h1 : σ = ν
    · have h2 : σ ≠ μ := fun h2 => hμν (h2.symm.trans h1)
      rw [if_pos h1, if_neg h2]; right; rfl
    · rw [if_neg h1]
      split_ifs <;> simp_all

theorem wt_coversp (hell2 : 2 ≤ ell) (hell11 : ell ≤ 11) {R : ℕ} (hR : 3 * 12 ≤ R * ell) :
    CoversOm0p ell M 12 (n + 1) (WT L M ell n) := by
  refine ⟨fun x _ => ?_, fun p _ => ?_⟩
  · obtain ⟨sites, j, hq, hx, -⟩ := wt_plaq_cover hM hell hn hL hell2 hell11 hR x (μ := 0) (ν := 1) (by decide)
    exact ⟨sites, j, hq, hx⟩
  · obtain ⟨x, ⟨⟨μ, ν⟩, hμν⟩⟩ := p
    obtain ⟨sites, j, hq, h1, h2, h3, h4⟩ :=
      wt_plaq_cover hM hell hn hL hell2 hell11 hR x (μ := μ) (ν := ν) (ne_of_lt hμν)
    refine ⟨sites, j, hq, fun e he => ?_⟩
    simp only [periodicPlaquetteBoundaryEdges, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact ⟨h1, h2⟩
    · exact ⟨h2, h4⟩
    · exact ⟨h3, by rw [shift_comm]; exact h4⟩
    · exact ⟨h1, h3⟩

theorem wt_classCoupled (hell2 : 2 ≤ ell) (hell11 : ell ≤ 11) {R : ℕ} (hR : 3 * 12 ≤ R * ell)
    (α₀ η : ℝ) (hα : 0 < α₀) (hη : 0 < η) :
    ClassCoupled ell M 12 (n + 1) (WT L M ell n) α₀ η Uw :=
  ⟨wt_coversp hM hell hn hL hell2 hell11 hR, wt_perCube hM hell hn hL hell2 α₀ η hα hη⟩

end cubes

end AdalyFormal.M2Glue
