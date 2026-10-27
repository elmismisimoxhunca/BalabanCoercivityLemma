import SH4

/-!
# SH5 -- the concrete lone-block tower on the torus, its `D_j` cube, and the facts used by both threshold directions.

`g = M ell^j`, `q = R + 11`, `X = loneBlock g q` (the level-`j` block `[q g, (q+1) g)^3`), `c = (R+12) g` (a `D_j` cube centre: `dCube = [(R+11) g, (R+13) g)^3 contains X`),
`tilde-square^5 = [(R+6) g, (R+18) g)^3`.  Torus hypothesis `(3R+30) g <= N` (no wrap).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.P409S

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG AdalyFormal.M2Bridge
open AdalyFormal.GeneralClass
open AdalyFormal.P409
open AdalyFormal.P409W
open AdalyFormal.P409C5
open AdalyFormal.StatementLaneR8 (pdist_comm pdist_triangle)

variable {L : PeriodicLatticeExtent}

/-- the site all of whose coordinates are `v` (mod the side). -/
def sitePt (L : PeriodicLatticeExtent) (v : ℕ) : PeriodicLatticeSite L := fun μ => ⟨v % (L μ + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

/-- the site with coordinates `x, y, z` (mod the sides). -/
def pt3 (L : PeriodicLatticeExtent) (x y z : ℕ) : PeriodicLatticeSite L := fun μ =>
  ⟨(if μ = 0 then x else if μ = 1 then y else z) % (L μ + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

theorem sitePt_val (v : ℕ) (μ : Fin 3) (h : v < L μ + 1) : ((sitePt L v) μ).val = v := by
  simp [sitePt, Nat.mod_eq_of_lt h]

theorem pt3_val0 (x y z : ℕ) (h : x < L 0 + 1) : ((pt3 L x y z) 0).val = x := by
  simp [pt3, Nat.mod_eq_of_lt h]

theorem pt3_val1 (x y z : ℕ) (h : y < L 1 + 1) : ((pt3 L x y z) 1).val = y := by
  simp [pt3, Nat.mod_eq_of_lt h]

theorem pt3_val2 (x y z : ℕ) (h : z < L 2 + 1) : ((pt3 L x y z) 2).val = z := by
  simp [pt3, Nat.mod_eq_of_lt h]

/-- the level-`g` block with index `q` in every coordinate. -/
def loneBlock (g q : ℕ) : Set (PeriodicLatticeSite L) := {x | ∀ μ : Fin 3, (x μ).val / g = q}

theorem loneBlock_closed (g q : ℕ) : BlockClosed g (loneBlock (L := L) g q) := by
  intro x hx y hxy μ
  exact (hxy μ).trans (hx μ)

/-- natural-number coordinates inside the window give membership in `cubeR` (no wrap). -/
theorem mem_cubeR_of_nat (c y : PeriodicLatticeSite L) (r : ℕ)
    (h : ∀ μ : Fin 3, (c μ).val ≤ (y μ).val + r ∧ (y μ).val < (c μ).val + r) : y ∈ cubeR c r := by
  intro μ
  refine ⟨((y μ).val : ℤ) - ((c μ).val : ℤ), by have := (h μ).1; omega, by have := (h μ).2; omega, ?_⟩
  have e : ((c μ).val : ℤ) + (((y μ).val : ℤ) - ((c μ).val : ℤ)) = ((y μ).val : ℤ) := by ring
  rw [e]

theorem blk_bounds (n h a : ℕ) (hh : 0 < h) (hd : a / h = n) : h * n ≤ a ∧ a < h * n + h := by
  have h1 := Nat.div_add_mod a h
  have h2 := Nat.mod_lt a hh
  rw [hd] at h1
  omega

/-- the concrete tower. -/
def loneT (ell M R j : ℕ) : Tower L := loneTower ell M R j (loneBlock (bigSide M ell j) (R + 11))

theorem loneT_Om_top (ell M R j : ℕ) : (loneT (L := L) ell M R j).Om j = loneBlock (bigSide M ell j) (R + 11) :=
  loneOm_top ell M R j _

theorem loneT_Om_above (ell M R j i : ℕ) (h : j < i) : (loneT (L := L) ell M R j).Om i = ∅ :=
  loneOm_above ell M R j _ h

theorem loneT_Om_below (ell M R j' : ℕ) :
    (loneT (L := L) ell M R (j' + 1)).Om j' =
      nbhdOp (bigSide M ell j') (R * bigSide M ell j') (loneBlock (bigSide M ell (j' + 1)) (R + 11)) := by
  show loneOm ell M R (j' + 1) _ j' = _
  rw [loneOm_below ell M R (j' + 1) _ (by omega)]
  show nbhdOp _ _ (loneOm ell M R (j' + 1) _ (j' + 1)) = _
  rw [loneOm_top]

theorem loneT_admissible {ell M R k j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k)
    (hdiv : ∀ μ : Fin 3, bigSide M ell k ∣ L μ + 1) : Admissible ell M R k (loneT (L := L) ell M R j) :=
  lone_admissible hj hjk (loneBlock_closed _ _) hdiv

/-- the centre. -/
def loneC (L : PeriodicLatticeExtent) (ell M R j : ℕ) : PeriodicLatticeSite L := sitePt L ((R + 12) * bigSide M ell j)

theorem loneT_dcube {ell M R k j : ℕ} (hM : 0 < M) (hell : 0 < ell) (hjk : j ≤ k)
    (hbig : ∀ μ : Fin 3, (3 * R + 30) * bigSide M ell j ≤ L μ + 1) :
    IsDCube ell M k (loneT ell M R j) j (loneC L ell M R j) := by
  have hg : 0 < bigSide M ell j := bigSide_pos' hM hell j
  refine ⟨hjk, ?_, sitePt L ((R + 11) * bigSide M ell j), ?_, ?_⟩
  · intro μ
    have h1 : (R + 12) * bigSide M ell j < L μ + 1 := by have := hbig μ; nlinarith
    show ((sitePt L ((R + 12) * bigSide M ell j)) μ).val % bigSide M ell j = 0
    rw [sitePt_val _ μ h1]
    exact Nat.mul_mod_left _ _
  · have h1 : ∀ μ : Fin 3, (R + 11) * bigSide M ell j < L μ + 1 := fun μ => by have := hbig μ; nlinarith
    refine ⟨?_, ?_⟩
    · rw [loneT_Om_top]
      intro μ
      rw [sitePt_val _ μ (h1 μ)]
      exact Nat.mul_div_cancel _ hg
    · rw [loneT_Om_above ell M R j (j + 1) (by omega)]
      exact Set.notMem_empty _
  · rw [dCube_eq]
    apply mem_cubeR_of_nat
    intro μ
    have h1 : (R + 11) * bigSide M ell j < L μ + 1 := by have := hbig μ; nlinarith
    have h2 : (R + 12) * bigSide M ell j < L μ + 1 := by have := hbig μ; nlinarith
    show ((loneC L ell M R j) μ).val ≤ ((sitePt L ((R + 11) * bigSide M ell j)) μ).val + bigSide M ell j ∧ _
    unfold loneC
    rw [sitePt_val _ μ h1, sitePt_val _ μ h2]
    constructor <;> nlinarith

end AdalyFormal.P409S
