import AB1
import AdalyFormal.Balaban.AbelianBlockingRate
/-!
# AB2 -- the abelian identity CMP98 (48) for the tree's blocking map (real angle fields)

For a real bond field `F` (angles of a diagonal `SU(2)` configuration), `blkAngle s ell F` is the
tree's blocked angle (`AbelianBlockingRate.blkAngle`, exactly the angle of `ubarSU2` on `torusCfg F`
on the principal branch).  At a coarse-aligned base point `y` (`y ∈ CoarseLattice L (s·ell)`,
`s·ell ∣ L ν + 1`):

  `curlS (s·ell) (blkAngle s ell F) y ν μ = Σ_{x ∈ B_s(y)} ell⁻³ · ladA s F x (ell·ν) μ ell`

(`curl_blk_identity`): the staircase terms cancel around the coarse plaquette (block translation,
AB1), and what is left is the block average of the `ell × ell` translated fine squares (CMP98 (48)).
`ladA_le`: `|ladA| ≤ |p|·n·Q` when the enclosed stride-`s` curls are `≤ Q` (abelian Stokes).

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath coarsePathEndpoint)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (cPlusS cPlusS_eq)
open AdalyFormal.Balaban.AbelianBlockingRate (pathAngle pathAngle_cons pathAngle_nil bondAngle
  loopAngle blkAngle)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice mem_CoarseLattice coarseLattice_mem_fits)

variable {L : PeriodicLatticeExtent}

/-- Stride-`s` curl (same orientation as `pw`). -/
def curlS (s : ℕ) (F : PeriodicLatticeEdge L → ℝ) (y : PeriodicLatticeSite L) (ν μ : Fin 3) : ℝ :=
  F (y, ν) + F (coarseShift y s ν, μ) - F (coarseShift y s μ, ν) - F (y, μ)

/-- Abelian ladder. -/
def ladA (s : ℕ) (F : PeriodicLatticeEdge L → ℝ) (y : PeriodicLatticeSite L) (p : List (Fin 3))
    (μ : Fin 3) (n : ℕ) : ℝ :=
  pathAngle s F y p + pathAngle s F (coarsePathEndpoint s y p) (List.replicate n μ)
    - pathAngle s F (coarseShift y (s * n) μ) p - pathAngle s F y (List.replicate n μ)

theorem ladA_cons (s : ℕ) (F : PeriodicLatticeEdge L → ℝ) (y : PeriodicLatticeSite L)
    (ν : Fin 3) (p : List (Fin 3)) (μ : Fin 3) (n : ℕ) :
    ladA s F y (ν :: p) μ n = ladA s F (coarseShift y s ν) p μ n + ladA s F y [ν] μ n := by
  have hc := AdalyFormal.Balaban.U1AnchorPoincare.coarseShift_comm_gen y (s * n) s μ ν
  have e1 : coarsePathEndpoint s y (ν :: p) = coarsePathEndpoint s (coarseShift y s ν) p := rfl
  have e2 : coarsePathEndpoint s y [ν] = coarseShift y s ν := rfl
  unfold ladA
  rw [e1, e2]
  simp only [pathAngle_cons, pathAngle_nil]
  rw [hc]
  ring

theorem ladA_rung (s : ℕ) (F : PeriodicLatticeEdge L → ℝ) (y : PeriodicLatticeSite L)
    (ν μ : Fin 3) (n : ℕ) :
    ladA s F y [ν] μ (n + 1) = curlS s F y ν μ + ladA s F (coarseShift y s μ) [ν] μ n := by
  have hc := AdalyFormal.Balaban.U1AnchorPoincare.coarseShift_comm_gen y s s ν μ
  have ha : coarseShift y (s * (n + 1)) μ = coarseShift (coarseShift y s μ) (s * n) μ := by
    rw [Nat.mul_succ, shift_add]
  have e2 : coarsePathEndpoint s y [ν] = coarseShift y s ν := rfl
  have e3 : coarsePathEndpoint s (coarseShift y s μ) [ν] = coarseShift (coarseShift y s μ) s ν := rfl
  unfold ladA curlS
  rw [ha, e2, e3]
  simp only [pathAngle_cons, pathAngle_nil, List.replicate_succ]
  rw [hc]
  ring

theorem rungA_le (s : ℕ) (F : PeriodicLatticeEdge L → ℝ) (ν μ : Fin 3) (Q : ℝ) :
    ∀ (n : ℕ) (y : PeriodicLatticeSite L),
      (∀ t ∈ rungPlaqs s ν μ y n, |curlS s F t.1 t.2.1 t.2.2| ≤ Q) →
      |ladA s F y [ν] μ n| ≤ (n : ℝ) * Q := by
  intro n
  induction n with
  | zero =>
      intro y _
      have : ladA s F y [ν] μ 0 = 0 := by
        unfold ladA
        rw [Nat.mul_zero, show coarseShift y 0 μ = y from rfl]
        simp only [List.replicate_zero, pathAngle_nil]
        ring
      rw [this]; simp
  | succ k ih =>
      intro y h
      rw [ladA_rung]
      have h0 := h (y, ν, μ) (List.mem_cons_self ..)
      have h1 := ih (coarseShift y s μ) (fun t ht => h t (List.mem_cons_of_mem _ ht))
      push_cast
      calc |curlS s F y ν μ + ladA s F (coarseShift y s μ) [ν] μ k|
          ≤ |curlS s F y ν μ| + |ladA s F (coarseShift y s μ) [ν] μ k| := abs_add_le _ _
        _ ≤ ((k : ℝ) + 1) * Q := by linarith

theorem ladA_le (s : ℕ) (F : PeriodicLatticeEdge L → ℝ) (μ : Fin 3) (n : ℕ) (Q : ℝ) :
    ∀ (p : List (Fin 3)) (y : PeriodicLatticeSite L),
      (∀ t ∈ ladPlaqs s μ n y p, |curlS s F t.1 t.2.1 t.2.2| ≤ Q) →
      |ladA s F y p μ n| ≤ (p.length : ℝ) * ((n : ℝ) * Q) := by
  intro p
  induction p with
  | nil =>
      intro y _
      have : ladA s F y [] μ n = 0 := by
        unfold ladA
        rw [show coarsePathEndpoint s y [] = y from rfl]
        simp only [pathAngle_nil]
        ring
      rw [this]; simp
  | cons ν rest ih =>
      intro y h
      rw [ladA_cons]
      have h1 := ih (coarseShift y s ν) (fun t ht => h t (List.mem_append_right _ ht))
      have h2 := rungA_le s F ν μ Q n y (fun t ht => h t (List.mem_append_left _ ht))
      simp only [List.length_cons]; push_cast
      calc |ladA s F (coarseShift y s ν) rest μ n + ladA s F y [ν] μ n|
          ≤ |ladA s F (coarseShift y s ν) rest μ n| + |ladA s F y [ν] μ n| := abs_add_le _ _
        _ ≤ ((rest.length : ℝ) + 1) * ((n : ℝ) * Q) := by nlinarith

/-- `blkAngle` at a full block: `φ(c₋) − (translated φ)(c₊) + average straight transport`. -/
theorem blk_split (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell) (F : PeriodicLatticeEdge L → ℝ)
    (c : PeriodicLatticeEdge L) (hfit : ∀ ν, (c.1 ν).val + s * ell ≤ L ν + 1) :
    blkAngle s ell F c
      = ∑ x ∈ stepBlockOf c.1 s ell, ((ell : ℝ) ^ 3)⁻¹ *
          (pathAngle s F c.1 (coarseGammaPath s c.1 x)
            - pathAngle s F (cPlusS s ell c) (coarseGammaPath s c.1 x)
            + pathAngle s F x (List.replicate ell c.2)) := by
  have hcard := AdalyFormal.Balaban.QjComposite.card_stepBlockOf c.1 s ell hs hfit
  have hw : ∑ _x ∈ stepBlockOf c.1 s ell, ((ell : ℝ) ^ 3)⁻¹ = 1 := by
    rw [Finset.sum_const, hcard, nsmul_eq_mul]; push_cast
    have : (0 : ℝ) < (ell : ℝ) ^ 3 := by positivity
    field_simp
  unfold blkAngle loopAngle
  have hb : ∑ x ∈ stepBlockOf c.1 s ell, ((ell : ℝ) ^ 3)⁻¹ * bondAngle s ell F c
      = bondAngle s ell F c := by rw [← Finset.sum_mul, hw, one_mul]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, hb]
  ring

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.ladA_le
#print axioms AdalyFormal.CurvBlock.blk_split
