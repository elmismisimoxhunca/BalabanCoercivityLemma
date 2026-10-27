import GenCl3

/-!
# GenCl4 -- the tip of `Ω₀` (box reading, ANY factor) and the nocover site under the general reading (lane general_class_20261015)

1. `gc_tip_uncovered`: on the isolated-block tower (GenCl2), if `2 ≤ ell ≤ 7` (`R ≥ 1`), the tip site
   `x_t = (P1' + M ell + RM - M, M ell, M ell)` of `Ω₀` lies in NO general class cube, of ANY factor `f ≥ 10` (no upper bound).
   Index 1: `x_t ∉ Ω₁`.  Index 0: an `f M`-window (`f ≥ 10`) through `x_t₁ ∈ [M ell, 2 M ell)` contains the `M`-block starting at
   `2 M ell + M` or the one starting at `M ell - 2 M`; those sites are at `ℓ¹`-distance `> RM` from `Ω₁`, so the cube leaves `Ω₀`.
   `gc_tip_gap`: in the headline regime (`3 ≤ ell ≤ 7`, every `m ≥ 1`, `R ≥ 1`), for EVERY `F` the general class
   `PerCubeRegularG .. F ..` leaves `b_t = (x_t, 1)` free and `p_t = (x_t; 0, 1) ∈ plaqIn Ω₀`.
   `gc_tip_forces_unit`: `P428Target8G F` (`F ≥ 1`) forces `Ginv` invertible at every `1[b_t ↦ v]` there.
2. `nc_site_coveredG`: on the nocover tower (`ncS`, NC4/NC5), the site `x*` that escapes every factor-12 cube lies in a general
   class cube of factor 10 (index 1), whose bonds include the four boundary bonds of `p* = (x*; 0, 1)`; more generally every site
   of the thin component `[P1', Q1')` lies in a factor-10 general cube.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000

namespace AdalyFormal.GeneralClass

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.NoCover
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.NonVac (pcd_self' iv_iff mem_box_N shift_val_N)

/-! ## 1. distance and window arithmetic -/

theorem pcd_ge (N a b D : ℕ) (h1 : D ≤ (if a ≤ b then b - a else a - b)) (h2 : D ≤ N - (if a ≤ b then b - a else a - b)) :
    D ≤ pcd N a b := by
  unfold pcd; exact le_min h1 h2

theorem pcd_le_diff (N a b : ℕ) : pcd N a b ≤ (if a ≤ b then b - a else a - b) := by
  unfold pcd; exact min_le_left _ _

theorem pdist_three {L : PeriodicLatticeExtent} (x y : PeriodicLatticeSite L) :
    pdist x y = pcd (L 0 + 1) (x 0).val (y 0).val + pcd (L 1 + 1) (x 1).val (y 1).val + pcd (L 2 + 1) (x 2).val (y 2).val := by
  unfold pdist; rw [Fin.sum_univ_three]

theorem blk_of_div {M x y : ℕ} (hM : 0 < M) (hx : M ∣ x) (h : y / M = x / M) : x ≤ y ∧ y < x + M := by
  obtain ⟨q, rfl⟩ := hx
  rw [Nat.mul_div_cancel_left q hM] at h
  have := (iv_iff (s := M) (t := q) (u := q + 1) (x := y) hM).2 ⟨h.ge, by omega⟩
  rw [mul_add, mul_one] at this
  exact this

/-- an `A`-window (`A ≥ 10 M`) through a point of `[lo, lo+W)` (`W ≤ 7 M`) contains `lo + W + M` or `lo - 2M`. -/
theorem winTip (N x z A lo W M : ℕ) (hxN : x < N) (hzN : z < N) (hx : lo ≤ x ∧ x < lo + W)
    (h1 : (x + N - z) % N < A) (hA : 10 * M ≤ A) (hW : W ≤ 7 * M) (hlo : 2 * M ≤ lo) (hN : lo + W + M < N) :
    (lo + W + M + N - z) % N < A ∨ (lo - 2 * M + N - z) % N < A := by
  rw [off_cases N _ _ hxN hzN] at h1
  rw [off_cases N _ _ hN hzN, off_cases N _ _ (by omega) hzN]
  split_ifs at h1 ⊢ <;> omega

/-! ## 2. the tip -/

/-- the tip `x_t = (P1' + M ell + RM - M, M ell, M ell)`. -/
def xtG (ell M R : ℕ) (hell : 0 < ell) (hM : 0 < M) : GSite ell M R :=
  fun μ => ⟨if μ = 0 then ncP1' ell M R + M * ell + R * M - M else M * ell, by
    have h := nc_scaleUp (ell := ell) (R := R) hell hM μ
    obtain ⟨-, -, e3, -, e5⟩ := nc_expand ell M R
    have hme : M * ell = ell * M := Nat.mul_comm _ _
    have hRM : R * M ≤ ell * (R * M) := Nat.le_mul_of_pos_left _ hell
    split_ifs <;> omega⟩

theorem xtG_val {ell M R : ℕ} (hell : 0 < ell) (hM : 0 < M) :
    ((xtG ell M R hell hM) 0).val = ncP1' ell M R + M * ell + R * M - M ∧
    ((xtG ell M R hell hM) 1).val = M * ell ∧ ((xtG ell M R hell hM) 2).val = M * ell := by
  simp [xtG]

/-- sites near the tip (first coordinate in the tip `M`-block, the other two in the block's range) are in `Ω₀`. -/
theorem tip_mem {ell M R : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) (p : GSite ell M R)
    (h0 : (p 0).val / M = (ncP1' ell M R + M * ell + R * M - M) / M)
    (h1 : M * ell ≤ (p 1).val ∧ (p 1).val < 2 * (M * ell)) (h2 : M * ell ≤ (p 2).val ∧ (p 2).val < 2 * (M * ell)) :
    p ∈ (gcS ell M R).Om 0 := by
  have hell0 : 0 < ell := by omega
  have hN := nc_scaleUp (ell := ell) (R := R) hell0 hM
  obtain ⟨-, -, e3, -, e5⟩ := nc_expand ell M R
  have hme : M * ell = ell * M := Nat.mul_comm _ _
  have hRM : M ≤ R * M := Nat.le_mul_of_pos_left M (by omega)
  have hRMl : R * M ≤ ell * (R * M) := Nat.le_mul_of_pos_left _ hell0
  have hMl : 2 * M ≤ M * ell := by rw [mul_comm 2 M]; exact Nat.mul_le_mul_left M hell
  set t := ncP1' ell M R + M * ell + R * M - M with ht
  have htN : t < ncN ell M R := by rw [ht, e3, e5]; omega
  have ytN : ncP1' ell M R + M * ell - 1 < scaleUp ell 1 (ncLu M R) 0 + 1 := by rw [hN 0, e3, e5]; omega
  let y : GSite ell M R := fun μ => if μ = 0 then ⟨ncP1' ell M R + M * ell - 1, ytN⟩ else p μ
  let z : GSite ell M R := fun μ => if μ = 0 then ⟨t, by rw [hN μ]; exact htN⟩ else p μ
  rw [gcS_om0]
  refine ⟨y, ?_, z, ?_, ?_⟩
  · right
    simp only [y, if_pos rfl, if_neg (by decide : (1 : Fin 3) ≠ 0), if_neg (by decide : (2 : Fin 3) ≠ 0)]
    refine ⟨?_, h1, h2⟩; omega
  · intro μ
    by_cases hμ : μ = 0
    · subst hμ; simp only [z, if_pos rfl]; exact h0.symm
    · simp only [z, if_neg hμ]
  · rw [pdist_three]
    simp only [y, z, if_pos rfl, if_neg (by decide : (1 : Fin 3) ≠ 0), if_neg (by decide : (2 : Fin 3) ≠ 0), pcd_self',
      add_zero]
    refine le_trans (pcd_le_diff _ _ _) ?_
    split_ifs <;> omega

theorem xtG_om0 {ell M R : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) :
    xtG ell M R (by omega) hM ∈ (gcS ell M R).Om 0 := by
  obtain ⟨h0, h1, h2⟩ := xtG_val (R := R) (by omega : 0 < ell) hM
  have hMl : M ≤ M * ell := Nat.le_mul_of_pos_right M (by omega)
  exact tip_mem hell hM hR _ (by rw [h0]) (by rw [h1]; omega) (by rw [h2]; omega)

/-- the two far `M`-blocks: sites with the tip's first coordinate and second coordinate in `[2M ell + M, 2M ell + 2M)` or in
`[M ell - 2M, M ell - M)` are NOT in `Ω₀`. -/
theorem tip_far {ell M R : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) (w : GSite ell M R)
    (h0 : (w 0).val = ncP1' ell M R + M * ell + R * M - M)
    (h1 : (w 1).val = 2 * (M * ell) + M ∨ (w 1).val = M * ell - 2 * M) : w ∉ (gcS ell M R).Om 0 := by
  have hell0 : 0 < ell := by omega
  have hN := nc_scaleUp (ell := ell) (R := R) hell0 hM
  obtain ⟨e1, e2, e3, -, e5⟩ := nc_expand ell M R
  have hme : M * ell = ell * M := Nat.mul_comm _ _
  have hRM : M ≤ R * M := Nat.le_mul_of_pos_left M (by omega)
  have hRMl : R * M ≤ ell * (R * M) := Nat.le_mul_of_pos_left _ hell0
  have hMl : 2 * M ≤ M * ell := by rw [mul_comm 2 M]; exact Nat.mul_le_mul_left M hell
  have hlt : ∀ y : GSite ell M R, ∀ ν, (y ν).val < ncN ell M R := fun y ν => by
    have := (y ν).isLt; have := hN ν; omega
  have dX : M ∣ ell * (R * M) := Dvd.dvd.mul_left (Dvd.intro_left R rfl) ell
  have dY : M ∣ ell * M := Dvd.intro_left ell rfl
  have d0 : M ∣ ncP1' ell M R + M * ell + R * M - M := by
    rw [e3]
    refine Nat.dvd_sub (Nat.dvd_add (Nat.dvd_add (Nat.dvd_add (Dvd.dvd.mul_left dX 4) (Dvd.dvd.mul_left dY 5))
      (Dvd.intro ell rfl)) (Dvd.intro_left R rfl)) (dvd_refl M)
  have d1 : M ∣ (w 1).val := by
    rcases h1 with h | h <;> rw [h]
    · exact Nat.dvd_add (Dvd.dvd.mul_left (Dvd.intro ell rfl) 2) (dvd_refl M)
    · exact Nat.dvd_sub (Dvd.intro ell rfl) (Dvd.intro_left 2 rfl)
  rw [gcS_om0]
  rintro ⟨y, hy, z, hz, hd⟩
  have bz0 := blk_of_div hM (h0 ▸ d0) (hz 0)
  have bz1 := blk_of_div hM d1 (hz 1)
  rw [h0] at bz0
  rw [pdist_three] at hd
  simp only [hN] at hd
  have hz0N := hlt z 0
  have hz1N := hlt z 1
  have hy0N := hlt y 0
  have hy1N := hlt y 1
  rcases hy with hy | ⟨hy0, hy1, -⟩
  · -- `y` in the thick slab: the first coordinate alone is farther than `RM`
    rw [e1] at hy; rw [e2] at hy
    have : R * M + 1 ≤ pcd (ncN ell M R) (z 0).val (y 0).val := by
      apply pcd_ge <;> split_ifs <;> rw [e3, e5] at * <;> omega
    omega
  · -- `y` in the isolated block: `RM - M + 1` in the first coordinate and `M + 1` in the second
    have c0 : R * M - M + 1 ≤ pcd (ncN ell M R) (z 0).val (y 0).val := by
      apply pcd_ge <;> split_ifs <;> rw [e3, e5] at * <;> omega
    have c1 : M + 1 ≤ pcd (ncN ell M R) (z 1).val (y 1).val := by
      rcases h1 with h | h <;> rw [h] at bz1 <;> apply pcd_ge <;> split_ifs <;> rw [e5] at * <;> omega
    omega

/-- **the tip lies in no general class cube of ANY factor** (`2 ≤ ell ≤ 7`, `R ≥ 1`). -/
theorem gc_tip_uncovered {ell M R : ℕ} (hell : 2 ≤ ell) (hell7 : ell ≤ 7) (hM : 0 < M) (hR : 1 ≤ R)
    (f : ℕ) (sites : Set (GSite ell M R)) (j : ℕ) (hq : IsClassCubeG ell M f 1 (gcS ell M R) sites j) :
    xtG ell M R (by omega) hM ∉ sites := by
  have hell0 : 0 < ell := by omega
  obtain ⟨hf, ⟨hj, ⟨z, -, rfl⟩, hsub, -⟩, -⟩ := hq
  intro hx
  have hN := nc_scaleUp (ell := ell) (R := R) hell0 hM
  obtain ⟨e1, e2, e3, -, e5⟩ := nc_expand ell M R
  have hme : M * ell = ell * M := Nat.mul_comm _ _
  have hRM : M ≤ R * M := Nat.le_mul_of_pos_left M (by omega)
  have hRMl : R * M ≤ ell * (R * M) := Nat.le_mul_of_pos_left _ hell0
  have hMl : 2 * M ≤ M * ell := by rw [mul_comm 2 M]; exact Nat.mul_le_mul_left M hell
  have hM7 : M * ell ≤ 7 * M := by rw [mul_comm 7 M]; exact Nat.mul_le_mul_left M hell7
  have hlt : ∀ y : GSite ell M R, ∀ ν, (y ν).val < ncN ell M R := fun y ν => by
    have := (y ν).isLt; have := hN ν; omega
  obtain ⟨hx0, hx1, hx2⟩ := xtG_val (R := R) hell0 hM
  have hj' : j = 0 ∨ j = 1 := by omega
  rcases hj' with rfl | rfl
  · have bx := (mem_box_N hN z _ _).1 hx
    simp only [bigSide, pow_zero, mul_one] at bx
    have hfM : 10 * M ≤ f * M := Nat.mul_le_mul_right M hf
    have wt := winTip (ncN ell M R) _ _ (f * M) (M * ell) (M * ell) M (hlt _ 1) (hlt z 1)
      (by rw [hx1]; omega) bx.2.1 hfM hM7 hMl (by rw [e5]; omega)
    -- the far site
    have hfar : ∃ v : ℕ, (v = 2 * (M * ell) + M ∨ v = M * ell - 2 * M) ∧ v < ncN ell M R ∧
        (v + ncN ell M R - (z 1).val) % ncN ell M R < f * M := by
      rcases wt with h | h
      · exact ⟨M * ell + M * ell + M, Or.inl (by ring), by rw [e5]; omega, h⟩
      · exact ⟨_, Or.inr rfl, by rw [e5]; omega, h⟩
    obtain ⟨v, hv, hvN, hvw⟩ := hfar
    have hv' : v < scaleUp ell 1 (ncLu M R) 1 + 1 := by rw [hN 1]; exact hvN
    let w : GSite ell M R := Function.update (xtG ell M R hell0 hM) 1 ⟨v, hv'⟩
    have hw0 : (w 0).val = ncP1' ell M R + M * ell + R * M - M := by simp [w, hx0]
    have hw1 : (w 1).val = v := by simp [w]
    have hw2 : w 2 = xtG ell M R hell0 hM 2 := by simp [w]
    have hwbox : w ∈ siteBox z (f * bigSide M ell 0) := by
      rw [mem_box_N hN]
      simp only [bigSide, pow_zero, mul_one]
      refine ⟨by rw [hw0, ← hx0]; exact bx.1, by rw [hw1]; exact hvw, by rw [hw2]; exact bx.2.2⟩
    have hwO : w ∈ (gcS ell M R).Om 0 := by
      rcases hsub hwbox with h | h
      · exact h.1
      · have h1 := h.1
        rw [gcS_om1] at h1
        rw [gcS_om0]
        exact gcOm1_sub ell M R h1
    exact tip_far hell hM hR w hw0 (hw1 ▸ hv) hwO
  · rcases hsub hx with h | h
    · have h1 := h.1
      rw [gcS_om1] at h1
      rcases h1 with h1 | ⟨h1, -, -⟩ <;> rw [hx0] at h1 <;> rw [e2, e3] at * <;> omega
    · have h1 := h.1; rw [gcS_omHi ell M R 2 le_rfl] at h1; exact h1

#print axioms winTip
#print axioms tip_mem
#print axioms xtG_om0
#print axioms tip_far
#print axioms gc_tip_uncovered

/-! ## 3. the tip in the headline regime -/

theorem pStar_plaqIn_tip {ell M R : ℕ} (hell : 2 ≤ ell) (hM2 : 2 ≤ M) (hR : 1 ≤ R) :
    pStar (xtG ell M R (by omega) (by omega)) ∈ plaqIn ((gcS ell M R).Om 0) := by
  have hell0 : 0 < ell := by omega
  have hM : 0 < M := by omega
  have hN := nc_scaleUp (ell := ell) (R := R) hell0 hM
  obtain ⟨-, -, e3, -, e5⟩ := nc_expand ell M R
  have hme : M * ell = ell * M := Nat.mul_comm _ _
  have hRM : M ≤ R * M := Nat.le_mul_of_pos_left M (by omega)
  have hRMl : R * M ≤ ell * (R * M) := Nat.le_mul_of_pos_left _ hell0
  have hMl : 2 * M ≤ M * ell := by rw [mul_comm 2 M]; exact Nat.mul_le_mul_left M hell
  have hN1 : 1 < ncN ell M R := by rw [e5]; omega
  obtain ⟨hx0, hx1, hx2⟩ := xtG_val (R := R) hell0 hM
  set x := xtG ell M R hell0 hM
  have dX : M ∣ ell * (R * M) := Dvd.dvd.mul_left (Dvd.intro_left R rfl) ell
  have dY : M ∣ ell * M := Dvd.intro_left ell rfl
  have d0 : M ∣ ncP1' ell M R + M * ell + R * M - M := by
    rw [e3]
    refine Nat.dvd_sub (Nat.dvd_add (Nat.dvd_add (Nat.dvd_add (Dvd.dvd.mul_left dX 4) (Dvd.dvd.mul_left dY 5))
      (Dvd.intro ell rfl)) (Dvd.intro_left R rfl)) (dvd_refl M)
  have memB : ∀ y : GSite ell M R, ((y 0).val = (x 0).val ∨ (y 0).val = (x 0).val + 1) →
      ((y 1).val = (x 1).val ∨ (y 1).val = (x 1).val + 1) → (y 2).val = (x 2).val → y ∈ (gcS ell M R).Om 0 := by
    intro y h0 h1 h2
    rw [hx0] at h0; rw [hx1] at h1; rw [hx2] at h2
    refine tip_mem hell hM hR y ?_ (by omega) (by omega)
    rcases h0 with h | h <;> rw [h]
    · exact blk_div hM d0 (by omega)
  have v0 : (x 0).val + 1 < ncN ell M R := by rw [hx0, e3, e5]; omega
  have v1 : (x 1).val + 1 < ncN ell M R := by rw [hx1, e5]; omega
  have m0 : ((x 0).val + 1) % ncN ell M R = (x 0).val + 1 := Nat.mod_eq_of_lt v0
  have m1 : ((x 1).val + 1) % ncN ell M R = (x 1).val + 1 := Nat.mod_eq_of_lt v1
  have sv := shift_val_N hN hN1
  intro e he
  simp only [periodicPlaquetteBoundaryEdges, pStar, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · refine ⟨memB _ (Or.inl rfl) (Or.inl rfl) rfl, memB _ ?_ ?_ ?_⟩ <;> simp [sv, m0]
  · refine ⟨memB _ ?_ ?_ ?_, memB _ ?_ ?_ ?_⟩ <;> simp [sv, m0, m1]
  · refine ⟨memB _ ?_ ?_ ?_, memB _ ?_ ?_ ?_⟩ <;> simp [sv, m0, m1]
  · refine ⟨memB _ (Or.inl rfl) (Or.inl rfl) rfl, memB _ ?_ ?_ ?_⟩ <;> simp [sv, m1]

/-- **the tip gap in the headline regime, for EVERY bound `F`** (`3 ≤ ell ≤ 7`). -/
theorem gc_tip_gap {ell m R : ℕ} (hell : 3 ≤ ell) (hell7 : ell ≤ 7) (hm : 1 ≤ m) (hR : 1 ≤ R) :
    ∃ (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell 1 Lu)) (Lam : Set (PeriodicLatticeSite Lu))
      (Bt : Bond Lu → SuTwo) (x : PeriodicLatticeSite (scaleUp ell 1 Lu)),
      TorusOK ell (ell ^ m) Lu ∧ Admissible ell (ell ^ m) R 1 S ∧ LambdaOK2 ell (ell ^ m) R 1 S Lam ∧ Lam.Nonempty ∧
      OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧
      x ∈ S.Om 0 ∧
      (∀ (f : ℕ) (sites : Set (PeriodicLatticeSite (scaleUp ell 1 Lu))) (j : ℕ),
        IsClassCubeG ell (ell ^ m) f 1 S sites j → x ∉ sites) ∧
      (∀ F : ℕ, ¬ CoversOm0G ell (ell ^ m) F 1 S) ∧
      (∀ (F : ℕ) (α₀ : ℝ), 0 < α₀ → ∀ v : Matrix.specialUnitaryGroup (Fin 2) ℂ,
        PerCubeRegularG ell (ell ^ m) F 1 S α₀ ((ell : ℝ) ^ 1)⁻¹ (Function.update (fun _ => 1) ((x, 1) : Bond _) v)) ∧
      (∀ (F : ℕ) (α₀ η : ℝ) (U : LinkCfg (scaleUp ell 1 Lu)), PerCubeRegularG ell (ell ^ m) F 1 S α₀ η U →
        ∀ v : Matrix.specialUnitaryGroup (Fin 2) ℂ,
          PerCubeRegularG ell (ell ^ m) F 1 S α₀ η (Function.update U ((x, 1) : Bond _) v)) ∧
      pStar x ∈ plaqIn (S.Om 0) ∧ ((x, 1) : Bond _) ∈ periodicPlaquetteBoundaryEdges (pStar x) ∧
      periodicPlaquetteHolonomy (Function.update (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) ((x, 1) : Bond _) negOne)
        (pStar x) = negOne := by
  have hell0 : 0 < ell := by omega
  have hM : 0 < ell ^ m := pow_pos hell0 m
  have hM2 : 2 ≤ ell ^ m := le_trans (by omega) (Nat.le_self_pow (by omega) ell)
  have hdvd : ell ∣ ell ^ m := dvd_pow_self ell (by omega)
  obtain ⟨Bp1, Bp2, Bp3, -⟩ := BseedNc_props (R := R) hell hdvd hM
  have hunc := gc_tip_uncovered (R := R) (by omega) hell7 hM hR
  have hN := nc_scaleUp (ell := ell) (R := R) hell0 hM
  have hN1 : 1 < ncN ell (ell ^ m) R := by
    obtain ⟨-, -, -, -, e5⟩ := nc_expand ell (ell ^ m) R
    have : 0 < ell * ell ^ m := Nat.mul_pos hell0 hM
    rw [e5]; omega
  have hx0 := xtG_om0 (ell := ell) (R := R) (by omega) hM hR
  refine ⟨ncLu (ell ^ m) R, gcS ell (ell ^ m) R, ncLam (ell ^ m) R, BseedNc (R := R) ell hM, xtG ell (ell ^ m) R hell0 hM,
    torusOK_nc hell hdvd hM, gc_admissible hell0 hM, lambdaOK2_gc hell hdvd hM hR, ncLam_nonempty hM, Bp1, Bp2, Bp3,
    hx0, hunc, ?_, ?_, ?_, pStar_plaqIn_tip (by omega) hM2 hR, bStar_mem _, hol_update_negOne hN hN1 _⟩
  · intro F h
    obtain ⟨f, sites, j, -, hq, hx⟩ := h _ hx0
    exact hunc f sites j hq hx
  · intro F α₀ hα v
    have hη : (0 : ℝ) < ((ell : ℝ) ^ 1)⁻¹ := by positivity
    exact perCubeG_update (perCubeG_one hell0 hM hα hη) _ (fun f sites j _ hq => hunc f sites j hq) v
  · intro F α₀ η U hU v
    exact perCubeG_update hU _ (fun f sites j _ hq => hunc f sites j hq) v

/-- **`P428Target8G F` forces `Ginv` (3.122) invertible at every `1[b_t ↦ v]` on the tip instances** (`3 ≤ ell ≤ 7`, any `F ≥ 1`). -/
theorem gc_tip_forces_unit {F : ℕ} (hF : 1 ≤ F) (h : P428Target8G F) :
    ∀ (ell : ℕ) (hell : 3 ≤ ell), ell ≤ 7 → ∀ (a : ℝ), 0 < a →
      ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 1 ≤ R →
        ∀ v : Matrix.specialUnitaryGroup (Fin 2) ℂ,
        IsUnit (gparams ell 1 (ncLu (ell ^ m) R) (by omega) (gcS ell (ell ^ m) R)
          (Function.update (fun _ => 1) ((xtG ell (ell ^ m) R (by omega) (pow_pos (by omega) m), 1) : Bond _) v) a
          (ncLam (ell ^ m) R)).data.Ginv := by
  intro ell hell hell7 a ha
  obtain ⟨m₀, hm₀, hm⟩ := h ell (by omega) a ha
  refine ⟨m₀, hm₀, fun m hm' => ?_⟩
  obtain ⟨R₀, hR⟩ := hm m hm'
  refine ⟨R₀, fun R hR' hR1 v => ?_⟩
  obtain ⟨-, a₀, ha₀, γ₀, hγ, hcore⟩ := hR R hR'
  have hell0 : 0 < ell := by omega
  have hM : 0 < ell ^ m := pow_pos hell0 m
  have hdvd : ell ∣ ell ^ m := dvd_pow_self ell (by omega)
  have hMr : (0 : ℝ) < ((ell ^ m : ℕ) : ℝ) := by exact_mod_cast hM
  have hFr : (0 : ℝ) < (F : ℝ) := by exact_mod_cast hF
  set α₀ : ℝ := a₀ / ((F : ℝ) * ((ell ^ m : ℕ) : ℝ)) with hα
  have hα0 : 0 < α₀ := by rw [hα]; positivity
  have hαS : (F : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ := by
    rw [hα]; field_simp; exact le_rfl
  have hη : (0 : ℝ) < ((ell : ℝ) ^ 1)⁻¹ := by
    have : (0 : ℝ) < ell := by exact_mod_cast hell0
    positivity
  have hcls : PerCubeRegularG ell (ell ^ m) F 1 (gcS ell (ell ^ m) R) α₀ ((ell : ℝ) ^ 1)⁻¹
      (Function.update (fun _ => 1) ((xtG ell (ell ^ m) R hell0 hM, 1) : Bond _) v) :=
    perCubeG_update (perCubeG_one hell0 hM hα0 hη) _
      (fun f sites j _ hq => gc_tip_uncovered (by omega) hell7 hM hR1 f sites j hq) v
  have hI := hcore 1 le_rfl (ncLu (ell ^ m) R) α₀ hα0 hαS (torusOK_nc hell hdvd hM) (gcS ell (ell ^ m) R)
    (gc_admissible hell0 hM) (ncLam (ell ^ m) R) (lambdaOK2_gc hell hdvd hM hR1) _ hcls
  by_contra hn
  exact instIneq_fails_of_not_unit_gc hell hdvd hM ha hγ.le _ hn hI

#print axioms pStar_plaqIn_tip
#print axioms gc_tip_gap
#print axioms gc_tip_forces_unit

end AdalyFormal.GeneralClass
