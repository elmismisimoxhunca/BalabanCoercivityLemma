import AB2
/-!
# AB3 -- CMP98 (48) for the tree's blocked angle, and level-uniform abelian curvature blocking

* `curl_blk_identity`: at a coarse-aligned `y` (`y ∈ CoarseLattice L (s·ell)`, `s·ell ∣ L ν + 1`):
  `curlS (s·ell) (blkAngle s ell F) y ν μ = Σ_{x ∈ B_s(y)} ell⁻³ · ladA s F x (ell·ν) μ ell`.
* `linT ell f`: the iterated blocked angle field (`linT 0 = f`, `linT (l+1) = blkAngle (ell^l) ell (linT l)`).
* `linT_curl`: if every fine curl is `≤ q0` in absolute value and `ell^n ∣ L ν + 1`, then for every
  `l ≤ n` and every `y ∈ CoarseLattice L (ell^l)`: `|curlS (ell^l) (linT l) y ν μ| ≤ (ell²)^l · q0`.
  Coefficient exactly `ell²` per level, constant 1, every `ell ≥ 1` (dyadic included).

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_mem_coarseLattice)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath coarsePathEndpoint)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (cPlusS cPlusS_eq)
open AdalyFormal.Balaban.AbelianBlockingRate (pathAngle blkAngle)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice mem_CoarseLattice coarseLattice_mem_fits)

variable {L : PeriodicLatticeExtent}

/-- Translated block potential. -/
def phiB (s ell : ℕ) (F : PeriodicLatticeEdge L → ℝ) (z w : PeriodicLatticeSite L) : ℝ :=
  ∑ x ∈ stepBlockOf z s ell, ((ell : ℝ) ^ 3)⁻¹ * pathAngle s F w (coarseGammaPath s z x)

/-- Block-averaged straight transport. -/
def strB (s ell : ℕ) (F : PeriodicLatticeEdge L → ℝ) (z : PeriodicLatticeSite L) (ρ : Fin 3) : ℝ :=
  ∑ x ∈ stepBlockOf z s ell, ((ell : ℝ) ^ 3)⁻¹ * pathAngle s F x (List.replicate ell ρ)

theorem blk_split3 (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell) (F : PeriodicLatticeEdge L → ℝ)
    (c : PeriodicLatticeEdge L) (hfit : ∀ ν, (c.1 ν).val + s * ell ≤ L ν + 1) :
    blkAngle s ell F c = phiB s ell F c.1 c.1 - phiB s ell F c.1 (cPlusS s ell c)
      + strB s ell F c.1 c.2 := by
  rw [blk_split s ell hs hell F c hfit]
  unfold phiB strB
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  ring

theorem phiB_shift (s ell n : ℕ) (μ : Fin 3) (F : PeriodicLatticeEdge L → ℝ)
    {z : PeriodicLatticeSite L} (hfit : ∀ ν, (z ν).val + s * ell ≤ L ν + 1)
    (hfit' : ∀ ν, ((coarseShift z n μ) ν).val + s * ell ≤ L ν + 1) :
    phiB s ell F z (coarseShift z n μ) = phiB s ell F (coarseShift z n μ) (coarseShift z n μ) := by
  unfold phiB
  have h := block_sum_shift s ell n μ hfit hfit'
    (fun x' => ((ell : ℝ) ^ 3)⁻¹ * pathAngle s F (coarseShift z n μ)
      (coarseGammaPath s (coarseShift z n μ) x'))
  rw [← h]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [gamma_shift]

theorem strB_shift (s ell n : ℕ) (μ ρ : Fin 3) (F : PeriodicLatticeEdge L → ℝ)
    {z : PeriodicLatticeSite L} (hfit : ∀ ν, (z ν).val + s * ell ≤ L ν + 1)
    (hfit' : ∀ ν, ((coarseShift z n μ) ν).val + s * ell ≤ L ν + 1) :
    strB s ell F (coarseShift z n μ) ρ
      = ∑ x ∈ stepBlockOf z s ell, ((ell : ℝ) ^ 3)⁻¹
          * pathAngle s F (coarseShift x n μ) (List.replicate ell ρ) := by
  unfold strB
  exact (block_sum_shift s ell n μ hfit hfit'
    (fun x' => ((ell : ℝ) ^ 3)⁻¹ * pathAngle s F x' (List.replicate ell ρ))).symm

/-- **CMP98 (48) for the tree's blocked angle.** -/
theorem curl_blk_identity (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell)
    (F : PeriodicLatticeEdge L → ℝ) (y : PeriodicLatticeSite L) (ν μ : Fin 3)
    (hdvd : ∀ ρ, s * ell ∣ L ρ + 1) (hy : y ∈ CoarseLattice L (s * ell)) :
    curlS (s * ell) (blkAngle s ell F) y ν μ
      = ∑ x ∈ stepBlockOf y s ell, ((ell : ℝ) ^ 3)⁻¹
          * ladA s F x (List.replicate ell ν) μ ell := by
  have hy1 := coarseShift_mem_coarseLattice hdvd hy ν
  have hy2 := coarseShift_mem_coarseLattice hdvd hy μ
  have hy12 := coarseShift_mem_coarseLattice hdvd hy1 μ
  have f0 := coarseLattice_mem_fits hdvd hy
  have f1 := coarseLattice_mem_fits hdvd hy1
  have f2 := coarseLattice_mem_fits hdvd hy2
  have f12 := coarseLattice_mem_fits hdvd hy12
  have hc : coarseShift (coarseShift y (s * ell) μ) (s * ell) ν
      = coarseShift (coarseShift y (s * ell) ν) (s * ell) μ :=
    AdalyFormal.Balaban.U1AnchorPoincare.coarseShift_comm_gen y (s * ell) (s * ell) μ ν
  have f21 : ∀ ρ, ((coarseShift (coarseShift y (s * ell) μ) (s * ell) ν) ρ).val + s * ell
      ≤ L ρ + 1 := by rw [hc]; exact f12
  have cp : ∀ (z : PeriodicLatticeSite L) (ρ : Fin 3),
      cPlusS s ell (z, ρ) = coarseShift z (s * ell) ρ := fun z ρ => cPlusS_eq s ell (z, ρ)
  have e : ∀ x : PeriodicLatticeSite L,
      coarsePathEndpoint s x (List.replicate ell ν) = coarseShift x (s * ell) ν := fun x => cp x ν
  unfold curlS
  rw [blk_split3 s ell hs hell F (y, ν) f0,
    blk_split3 s ell hs hell F (coarseShift y (s * ell) ν, μ) f1,
    blk_split3 s ell hs hell F (coarseShift y (s * ell) μ, ν) f2,
    blk_split3 s ell hs hell F (y, μ) f0]
  simp only [cp]
  rw [phiB_shift s ell (s * ell) ν F f0 f1, phiB_shift s ell (s * ell) μ F f0 f2,
    phiB_shift s ell (s * ell) μ F f1 f12, phiB_shift s ell (s * ell) ν F f2 f21, hc,
    strB_shift s ell (s * ell) ν μ F f0 f1, strB_shift s ell (s * ell) μ ν F f0 f2]
  unfold strB ladA
  simp only [e, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.curl_blk_identity
