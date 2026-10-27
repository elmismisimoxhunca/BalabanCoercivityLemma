import NB5
/-!
# NB6 -- `log_ubar_lin`: linearisation of one blocked link

`‖log (ubarSU2 s ell W c) − blkM s ell A c‖_F ≤ 200 π ell² k²` and `exp ∘ log = id` there, when all bonds
read carry `W = exp A`, `A ∈ 𝔰𝔲(2)`, `‖A‖ ≤ k`, `8 ell k ≤ 1/(8π)`.

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Log su2Exp)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobNorm_nonneg)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (cPlusS coarseBondVar gammaVarStrided loopVar)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2 ubarSU2_eq_blockedLink)
open AdalyFormal.Balaban.BlockingLinkEstimate (blockExponent)
open AdalyFormal.Balaban.Bch2 (IsSu2)

variable {L : PeriodicLatticeExtent}

/-- The exponent list of the block loop `W_x`. -/
def loopList (s ell : ℕ) (A : PeriodicLatticeEdge L → M2) (c : PeriodicLatticeEdge L)
    (x : PeriodicLatticeSite L) : List M2 :=
  pl s A c.1 (coarseGammaPath s c.1 x) ++ pl s A x (List.replicate ell c.2)
    ++ plInv s A (cPlusS s ell c) (coarseGammaPath s c.1 x)
    ++ plInv s A c.1 (List.replicate ell c.2)

theorem loopList_facts (s ell : ℕ) (hs : 0 < s) (W : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2) (k : ℝ) (hk : 0 ≤ k) (c : PeriodicLatticeEdge L)
    (x : PeriodicLatticeSite L) (hx : x ∈ stepBlockOf c.1 s ell)
    (h : ∀ b ∈ loopBonds s ell c x, Chart W A k b) :
    loopVar s ell W c x = ((loopList s ell A c x).map su2Exp).prod ∧
    (loopList s ell A c x).sum = loopM s ell A c x ∧
    (∀ a ∈ loopList s ell A c x, IsSu2 a) ∧
    ((loopList s ell A c x).map frobNorm).sum ≤ 8 * ell * k := by
  have hell := AdalyFormal.Balaban.ClassPropagationUbar.ell_pos_of_mem hs hx
  have hg := AdalyFormal.Balaban.ClassPropagationUbar.gammaPath_length_le c.1 x hs hx
  have hgR : ((coarseGammaPath s c.1 x).length : ℝ) ≤ 3 * (ell : ℝ) := by
    have h1 : ((coarseGammaPath s c.1 x).length : ℝ) ≤ ((3 * (ell - 1) : ℕ) : ℝ) := by
      exact_mod_cast hg
    rw [Nat.cast_mul, Nat.cast_sub hell] at h1; push_cast at h1; linarith
  have m1 : ∀ b ∈ pathBonds s c.1 (coarseGammaPath s c.1 x), Chart W A k b := fun b hb =>
    h b (by unfold loopBonds; simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl hb)))
  have m2 : ∀ b ∈ pathBonds s x (List.replicate ell c.2), Chart W A k b := fun b hb =>
    h b (by unfold loopBonds; simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inr hb)))
  have m3 : ∀ b ∈ pathBonds s (cPlusS s ell c) (coarseGammaPath s c.1 x), Chart W A k b :=
    fun b hb => h b (by unfold loopBonds; simp only [List.mem_append]; exact Or.inl (Or.inr hb))
  have m4 : ∀ b ∈ pathBonds s c.1 (List.replicate ell c.2), Chart W A k b := fun b hb =>
    h b (by unfold loopBonds; simp only [List.mem_append]; exact Or.inr hb)
  obtain ⟨p1, -, s1, -, u1, -, n1, -⟩ := pl_facts s W A k _ _ m1
  obtain ⟨p2, -, s2, -, u2, -, n2, -⟩ := pl_facts s W A k _ _ m2
  obtain ⟨-, q3, -, t3, -, v3, -, o3⟩ := pl_facts s W A k _ _ m3
  obtain ⟨-, q4, -, t4, -, v4, -, o4⟩ := pl_facts s W A k _ _ m4
  refine ⟨?_, ?_, ?_, ?_⟩
  · show gammaVarStrided s ell W c x * (coarseBondVar s ell W c)⁻¹ = _
    unfold gammaVarStrided coarseBondVar
    rw [q4, q3, p2, p1]
    unfold loopList
    simp only [List.map_append, List.prod_append]
  · unfold loopList loopM bondM
    simp only [List.sum_append, s1, s2, t3, t4]
    abel
  · intro a ha
    unfold loopList at ha
    simp only [List.mem_append] at ha
    rcases ha with ((ha | ha) | ha) | ha
    · exact u1 a ha
    · exact u2 a ha
    · exact v3 a ha
    · exact v4 a ha
  · unfold loopList
    simp only [List.map_append, List.sum_append]
    rw [List.length_replicate] at n2 o4
    have : (0 : ℝ) ≤ k := hk
    nlinarith

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.loopList_facts
