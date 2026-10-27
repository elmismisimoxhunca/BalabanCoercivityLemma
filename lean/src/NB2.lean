import AB4
import CB8
/-!
# NB2 -- the identity CMP98 (48) for MATRIX-valued (𝔰𝔲(2)) fields (piece N3)

Real coordinates `coord i j b X` (real / imaginary part of entry `(i,j)`) are ℝ-linear; every linear
object of AB2/AB3 (path sum, block loop sum, blocked field, curl, ladder) commutes with them, so the
identity and the ladder recursion transfer verbatim from AB3/AB2 to `M2`-valued fields:

* `curlM_blk_identity`: `curlM (s·ell) (blkM s ell A) y ν μ = Σ_{x ∈ B_s(y)} ell⁻³ • ladAM s A x (ell·ν) μ ell`
  at aligned `y`;
* `ladAM_le`: `‖ladAM s A y p μ n‖_F ≤ |p|·n·Q` when the enclosed `‖curlM s A ·‖_F ≤ Q`.

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath coarsePathEndpoint)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (cPlusS)
open AdalyFormal.Balaban.AbelianBlockingRate (pathAngle pathAngle_cons pathAngle_nil bondAngle
  loopAngle blkAngle)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)

variable {L : PeriodicLatticeExtent}

/-- Real coordinate of a 2×2 complex matrix. -/
def coord (i j : Fin 2) (b : Bool) (X : M2) : ℝ := if b then (X i j).re else (X i j).im

theorem coord_add (i j : Fin 2) (b : Bool) (X Y : M2) :
    coord i j b (X + Y) = coord i j b X + coord i j b Y := by
  cases b <;> simp [coord]

theorem coord_sub (i j : Fin 2) (b : Bool) (X Y : M2) :
    coord i j b (X - Y) = coord i j b X - coord i j b Y := by
  cases b <;> simp [coord]

theorem coord_zero (i j : Fin 2) (b : Bool) : coord i j b (0 : M2) = 0 := by
  cases b <;> simp [coord]

theorem coord_smul (i j : Fin 2) (b : Bool) (r : ℝ) (X : M2) :
    coord i j b (r • X) = r * coord i j b X := by
  cases b <;> simp [coord, Matrix.smul_apply]

theorem coord_sum {ι : Type*} (S : Finset ι) (i j : Fin 2) (b : Bool) (f : ι → M2) :
    coord i j b (∑ x ∈ S, f x) = ∑ x ∈ S, coord i j b (f x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [coord_zero]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, coord_add, ih]

theorem ext_coord {X Y : M2} (h : ∀ i j b, coord i j b X = coord i j b Y) : X = Y := by
  ext i j
  apply Complex.ext
  · exact h i j true
  · exact h i j false

def pathM (s : ℕ) (A : PeriodicLatticeEdge L → M2) : PeriodicLatticeSite L → List (Fin 3) → M2
  | _, [] => 0
  | y, μ :: rest => A (y, μ) + pathM s A (coarseShift y s μ) rest

def cf (i j : Fin 2) (b : Bool) (A : PeriodicLatticeEdge L → M2) : PeriodicLatticeEdge L → ℝ :=
  fun e => coord i j b (A e)

theorem coord_pathM (s : ℕ) (A : PeriodicLatticeEdge L → M2) (i j : Fin 2) (b : Bool) :
    ∀ (p : List (Fin 3)) (y : PeriodicLatticeSite L),
      coord i j b (pathM s A y p) = pathAngle s (cf i j b A) y p := by
  intro p
  induction p with
  | nil => intro y; simp [pathM, coord_zero]
  | cons μ rest ih => intro y; simp only [pathM, pathAngle_cons, coord_add, ih]; rfl

def bondM (s ell : ℕ) (A : PeriodicLatticeEdge L → M2) (c : PeriodicLatticeEdge L) : M2 :=
  pathM s A c.1 (List.replicate ell c.2)

def loopM (s ell : ℕ) (A : PeriodicLatticeEdge L → M2) (c : PeriodicLatticeEdge L)
    (x : PeriodicLatticeSite L) : M2 :=
  pathM s A c.1 (coarseGammaPath s c.1 x) + pathM s A x (List.replicate ell c.2)
    - pathM s A (cPlusS s ell c) (coarseGammaPath s c.1 x) - bondM s ell A c

/-- The linear (Lie-algebra) blocking. -/
def blkM (s ell : ℕ) (A : PeriodicLatticeEdge L → M2) (c : PeriodicLatticeEdge L) : M2 :=
  (∑ x ∈ stepBlockOf c.1 s ell, ((ell : ℝ) ^ 3)⁻¹ • loopM s ell A c x) + bondM s ell A c

def curlM (s : ℕ) (A : PeriodicLatticeEdge L → M2) (y : PeriodicLatticeSite L) (ν μ : Fin 3) : M2 :=
  A (y, ν) + A (coarseShift y s ν, μ) - A (coarseShift y s μ, ν) - A (y, μ)

def ladAM (s : ℕ) (A : PeriodicLatticeEdge L → M2) (y : PeriodicLatticeSite L) (p : List (Fin 3))
    (μ : Fin 3) (n : ℕ) : M2 :=
  pathM s A y p + pathM s A (coarsePathEndpoint s y p) (List.replicate n μ)
    - pathM s A (coarseShift y (s * n) μ) p - pathM s A y (List.replicate n μ)

theorem coord_blkM (s ell : ℕ) (A : PeriodicLatticeEdge L → M2) (i j : Fin 2) (b : Bool)
    (c : PeriodicLatticeEdge L) : coord i j b (blkM s ell A c) = blkAngle s ell (cf i j b A) c := by
  unfold blkM blkAngle loopM loopAngle bondM bondAngle
  rw [coord_add, coord_sum]
  simp only [coord_smul, coord_add, coord_sub, coord_pathM]

theorem cf_blkM (s ell : ℕ) (A : PeriodicLatticeEdge L → M2) (i j : Fin 2) (b : Bool) :
    cf i j b (blkM s ell A) = blkAngle s ell (cf i j b A) := by
  funext c; exact coord_blkM s ell A i j b c

theorem coord_curlM (s : ℕ) (A : PeriodicLatticeEdge L → M2) (i j : Fin 2) (b : Bool)
    (y : PeriodicLatticeSite L) (ν μ : Fin 3) :
    coord i j b (curlM s A y ν μ) = curlS s (cf i j b A) y ν μ := by
  unfold curlM curlS; simp only [coord_add, coord_sub]; rfl

theorem coord_ladAM (s : ℕ) (A : PeriodicLatticeEdge L → M2) (i j : Fin 2) (b : Bool)
    (y : PeriodicLatticeSite L) (p : List (Fin 3)) (μ : Fin 3) (n : ℕ) :
    coord i j b (ladAM s A y p μ n) = ladA s (cf i j b A) y p μ n := by
  unfold ladAM ladA; simp only [coord_add, coord_sub, coord_pathM]

/-- **CMP98 (48), matrix-valued.** -/
theorem curlM_blk_identity (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell)
    (A : PeriodicLatticeEdge L → M2) (y : PeriodicLatticeSite L) (ν μ : Fin 3)
    (hdvd : ∀ ρ, s * ell ∣ L ρ + 1) (hy : y ∈ CoarseLattice L (s * ell)) :
    curlM (s * ell) (blkM s ell A) y ν μ
      = ∑ x ∈ stepBlockOf y s ell, ((ell : ℝ) ^ 3)⁻¹ • ladAM s A x (List.replicate ell ν) μ ell := by
  apply ext_coord
  intro i j b
  rw [coord_curlM, cf_blkM, curl_blk_identity s ell hs hell _ y ν μ hdvd hy, coord_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [coord_smul, coord_ladAM]

theorem ladAM_cons (s : ℕ) (A : PeriodicLatticeEdge L → M2) (y : PeriodicLatticeSite L)
    (ν : Fin 3) (p : List (Fin 3)) (μ : Fin 3) (n : ℕ) :
    ladAM s A y (ν :: p) μ n = ladAM s A (coarseShift y s ν) p μ n + ladAM s A y [ν] μ n := by
  apply ext_coord; intro i j b
  rw [coord_add, coord_ladAM, coord_ladAM, coord_ladAM, ladA_cons]

theorem ladAM_rung (s : ℕ) (A : PeriodicLatticeEdge L → M2) (y : PeriodicLatticeSite L)
    (ν μ : Fin 3) (n : ℕ) :
    ladAM s A y [ν] μ (n + 1) = curlM s A y ν μ + ladAM s A (coarseShift y s μ) [ν] μ n := by
  apply ext_coord; intro i j b
  rw [coord_add, coord_ladAM, coord_ladAM, coord_curlM, ladA_rung]

theorem ladAM_zero (s : ℕ) (A : PeriodicLatticeEdge L → M2) (y : PeriodicLatticeSite L)
    (ν μ : Fin 3) : ladAM s A y [ν] μ 0 = 0 := by
  apply ext_coord; intro i j b
  rw [coord_ladAM, coord_zero]
  unfold ladA
  rw [Nat.mul_zero, show coarseShift y 0 μ = y from rfl]
  simp only [List.replicate_zero, pathAngle_nil]
  ring

theorem ladAM_nil (s : ℕ) (A : PeriodicLatticeEdge L → M2) (y : PeriodicLatticeSite L)
    (μ : Fin 3) (n : ℕ) : ladAM s A y [] μ n = 0 := by
  apply ext_coord; intro i j b
  rw [coord_ladAM, coord_zero]
  unfold ladA
  rw [show coarsePathEndpoint s y [] = y from rfl]
  simp only [pathAngle_nil]
  ring

theorem ladAM_le (s : ℕ) (A : PeriodicLatticeEdge L → M2) (μ : Fin 3) (n : ℕ) (Q : ℝ) :
    ∀ (p : List (Fin 3)) (y : PeriodicLatticeSite L),
      (∀ t ∈ ladPlaqs s μ n y p, frobNorm (curlM s A t.1 t.2.1 t.2.2) ≤ Q) →
      frobNorm (ladAM s A y p μ n) ≤ (p.length : ℝ) * ((n : ℝ) * Q) := by
  have hr : ∀ (ν : Fin 3) (k : ℕ) (y : PeriodicLatticeSite L),
      (∀ t ∈ rungPlaqs s ν μ y k, frobNorm (curlM s A t.1 t.2.1 t.2.2) ≤ Q) →
      frobNorm (ladAM s A y [ν] μ k) ≤ (k : ℝ) * Q := by
    intro ν k
    induction k with
    | zero => intro y _; rw [ladAM_zero s A y ν μ]; simp
    | succ k ih =>
        intro y h
        rw [ladAM_rung]
        have h0 := h (y, ν, μ) (List.mem_cons_self ..)
        have h1 := ih (coarseShift y s μ) (fun t ht => h t (List.mem_cons_of_mem _ ht))
        have := AdalyFormal.Balaban.Bch2.frobNorm_add_le (curlM s A y ν μ)
          (ladAM s A (coarseShift y s μ) [ν] μ k)
        push_cast; linarith
  intro p
  induction p with
  | nil => intro y _; rw [ladAM_nil]; simp
  | cons ν rest ih =>
      intro y h
      rw [ladAM_cons]
      have h1 := ih (coarseShift y s ν) (fun t ht => h t (List.mem_append_right _ ht))
      have h2 := hr ν n y (fun t ht => h t (List.mem_append_left _ ht))
      have := AdalyFormal.Balaban.Bch2.frobNorm_add_le (ladAM s A (coarseShift y s ν) rest μ n)
        (ladAM s A y [ν] μ n)
      simp only [List.length_cons]; push_cast
      nlinarith

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.curlM_blk_identity
#print axioms AdalyFormal.CurvBlock.ladAM_le
