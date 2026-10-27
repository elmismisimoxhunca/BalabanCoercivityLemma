import AdalyFormal.Balaban.ClassPropagationUbar
import AdalyFormal.Balaban.U1AnchorPoincare
/-!
# CB1 -- the defect functional `dv g = ‖g - 1‖_F` and path comparison

`dv` is subadditive, inverse- and conjugation-invariant (tree lemmas, reused).  `path_cmp`: if two
configurations differ bond-by-bond by at most `d` (in the sense `dv (V b * (T b)⁻¹) ≤ d`), their
holonomies along any strided path differ by at most `|p| * d`.  `four_cmp`: the same for the
four-factor word `A B C⁻¹ E⁻¹` (block loop `W_x` and plaquette word share this shape).

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)

variable {L : PeriodicLatticeExtent}

/-- The defect of a group element: `‖g − 1‖_F`. -/
def dv (g : SU2) : ℝ := frobNorm ((g : M2) - 1)

theorem dv_mul (a b : SU2) : dv (a * b) ≤ dv a + dv b :=
  AdalyFormal.Balaban.RegularUQChain.frobNorm_su_mul_sub_one_le a b

theorem dv_inv (a : SU2) : dv a⁻¹ = dv a :=
  AdalyFormal.Balaban.RegularUQChain.frobNorm_su_inv_sub_one a

theorem dv_conj (g a : SU2) : dv (g * a * g⁻¹) = dv a :=
  AdalyFormal.Balaban.BlockingLinkEstimate.frobNorm_conj_sub_one g a

theorem dv_one : dv (1 : SU2) = 0 := by
  unfold dv; simp [AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero]

theorem dv_nonneg (a : SU2) : 0 ≤ dv a := AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _

/-- The bonds visited by a strided path (same recursion as `coarsePathHolonomy`). -/
def pathBonds (s : ℕ) : PeriodicLatticeSite L → List (Fin 3) → List (PeriodicLatticeEdge L)
  | _, [] => []
  | y, μ :: rest => (y, μ) :: pathBonds s (coarseShift y s μ) rest

/-- **Path comparison.** Local form: only the bonds the path visits enter. -/
theorem path_cmp (s : ℕ) (V T : PeriodicLinkConfiguration SU2 L) (d : ℝ) :
    ∀ (p : List (Fin 3)) (y : PeriodicLatticeSite L),
      (∀ b ∈ pathBonds s y p, dv (V b * (T b)⁻¹) ≤ d) →
      dv (coarsePathHolonomy s V y p * (coarsePathHolonomy s T y p)⁻¹) ≤ (p.length : ℝ) * d := by
  intro p
  induction p with
  | nil =>
      intro y _
      show dv ((1 : SU2) * (1 : SU2)⁻¹) ≤ _
      rw [mul_inv_cancel, dv_one]; simp
  | cons μ rest ih =>
      intro y h
      have h0 : dv (V (y, μ) * (T (y, μ))⁻¹) ≤ d := h _ (List.mem_cons_self ..)
      have h1 := ih (coarseShift y s μ) (fun b hb => h b (List.mem_cons_of_mem _ hb))
      set X := coarsePathHolonomy s V (coarseShift y s μ) rest
      set Y := coarsePathHolonomy s T (coarseShift y s μ) rest
      have hid : coarsePathHolonomy s V y (μ :: rest) * (coarsePathHolonomy s T y (μ :: rest))⁻¹
          = (V (y, μ) * (T (y, μ))⁻¹) * (T (y, μ) * (X * Y⁻¹) * (T (y, μ))⁻¹) := by
        show V (y, μ) * X * (T (y, μ) * Y)⁻¹ = _
        group
      rw [hid]
      refine le_trans (dv_mul _ _) ?_
      rw [dv_conj]
      simp only [List.length_cons]; push_cast
      linarith

/-- **Four-factor comparison.** `dv (A B C⁻¹ E⁻¹) ≤ Σ dv(Xᵢ) + dv(a b c⁻¹ e⁻¹)` where
`A = X₁ a`, `B = X₂ b`, `C = X₃ c`, `E = X₄ e`.  Exact group identity + conjugation invariance. -/
theorem four_cmp (X1 X2 X3 X4 a b c e : SU2) :
    dv ((X1 * a) * (X2 * b) * (X3 * c)⁻¹ * (X4 * e)⁻¹)
      ≤ dv X1 + dv X2 + dv X3 + dv X4 + dv (a * b * c⁻¹ * e⁻¹) := by
  set W := a * b * c⁻¹ * e⁻¹
  have hid : (X1 * a) * (X2 * b) * (X3 * c)⁻¹ * (X4 * e)⁻¹
      = X1 * (a * X2 * a⁻¹) * ((a * b * c⁻¹) * X3⁻¹ * (a * b * c⁻¹)⁻¹)
          * (W * X4⁻¹ * W⁻¹) * W := by
    simp only [W]; group
  rw [hid]
  have t1 := dv_mul (X1 * (a * X2 * a⁻¹) * ((a * b * c⁻¹) * X3⁻¹ * (a * b * c⁻¹)⁻¹)
    * (W * X4⁻¹ * W⁻¹)) W
  have t2 := dv_mul (X1 * (a * X2 * a⁻¹) * ((a * b * c⁻¹) * X3⁻¹ * (a * b * c⁻¹)⁻¹))
    (W * X4⁻¹ * W⁻¹)
  have t3 := dv_mul (X1 * (a * X2 * a⁻¹)) ((a * b * c⁻¹) * X3⁻¹ * (a * b * c⁻¹)⁻¹)
  have t4 := dv_mul X1 (a * X2 * a⁻¹)
  have c2 : dv (W * X4⁻¹ * W⁻¹) = dv X4 := by rw [dv_conj, dv_inv]
  have c3 : dv ((a * b * c⁻¹) * X3⁻¹ * (a * b * c⁻¹)⁻¹) = dv X3 := by rw [dv_conj, dv_inv]
  have c4 : dv (a * X2 * a⁻¹) = dv X2 := dv_conj a X2
  linarith

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.path_cmp
#print axioms AdalyFormal.CurvBlock.four_cmp
