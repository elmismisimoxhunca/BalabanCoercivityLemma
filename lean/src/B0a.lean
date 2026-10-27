import R2Raw1

/-!
# B0a -- the raw averaging maps a PURE-GAUGE fluctuation to a pure-gauge fluctuation (exact, nonlinear)

`pgV s V γ e = γ(e₋) V(e) γ(e₋ + s e_μ)⁻¹ V(e)⁻¹` is the fluctuation `V₁` with `V₁ V = V^γ` (gauge transform at
stride `s`).  `nextG s ell V γ y = exp(S(y))⁻¹ γ(y)`, `S = sBlock s ell V (pgV s V γ)` (R2Raw1, CMP98 (63)).

`rawStep_pgV`: `rawStep s ell V (pgV s V γ) c = pgV (s·ell) (Ū(V)) (nextG s ell V γ) c` for EVERY `c`, every `γ`,
every `V`; `Ū(V) = stridedBlockedGauge su2LogExp s ell V`.  No smallness, no regularity.  This is the nonlinear form
of the print's (3.113)-(3.115) (CMP99b p.418): a gauge fluctuation at level `j` is a gauge fluctuation at level `j+1`
for the coarse gauge `exp(-S) γ`.  Ingredients: `stridedBlockedGauge_gauge` (tree, exact), `rawStep_simp` (R2Raw1),
and `su2Exp (-A) = (su2Exp A)⁻¹`.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace AdalyFormal.SliceCoerc

open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp su2Log su2Exp M2 SU2 su2Exp_of_mem su2Exp_of_not_mem)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge cPlusS cPlusS_eq stridedBlockedGauge_gauge)

variable {L : PeriodicLatticeExtent}

/-- the pure-gauge fluctuation at stride `s`: `V₁ V = V^γ`. -/
def pgV (s : ℕ) (V : PeriodicLinkConfiguration SU2 L) (γ : PeriodicLatticeSite L → SU2) :
    PeriodicLinkConfiguration SU2 L :=
  fun e => γ e.1 * V e * (γ (coarseShift e.1 s e.2))⁻¹ * (V e)⁻¹

theorem pgV_mul (s : ℕ) (V : PeriodicLinkConfiguration SU2 L) (γ : PeriodicLatticeSite L → SU2) :
    (fun b => pgV s V γ b * V b) = AdalyFormal.Balaban.QjComposite.coarseGaugeTransform s γ V := by
  funext b
  simp only [pgV, AdalyFormal.Balaban.QjComposite.coarseGaugeTransform]
  group

theorem inv_mem_SU2 {M : M2} (h : M ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    M⁻¹ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  have h1 := ((⟨M, h⟩ : SU2)⁻¹).2
  rw [AdalyFormal.Balaban.SuTwoLogExp.coe_inv,
    ← AdalyFormal.Balaban.SuTwoLogExp.coe_matrix_inv] at h1
  simpa using h1

theorem su2Exp_neg (A : M2) : su2Exp (-A) = (su2Exp A)⁻¹ := by
  classical
  have hinv : NormedSpace.exp (-A) = (NormedSpace.exp A)⁻¹ := Matrix.exp_neg A
  by_cases hA : NormedSpace.exp A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ
  · have hA' : NormedSpace.exp (-A) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
      rw [hinv]; exact inv_mem_SU2 hA
    apply Subtype.ext
    rw [su2Exp_of_mem hA', hinv, AdalyFormal.Balaban.SuTwoLogExp.coe_inv, su2Exp_of_mem hA]
    have := AdalyFormal.Balaban.SuTwoLogExp.coe_matrix_inv ⟨NormedSpace.exp A, hA⟩
    simpa using this
  · have hA' : NormedSpace.exp (-A) ∉ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
      intro h
      apply hA
      have h2 : NormedSpace.exp A = (NormedSpace.exp (-A))⁻¹ := by
        rw [← Matrix.exp_neg, neg_neg]
      rw [h2]; exact inv_mem_SU2 h
    rw [su2Exp_of_not_mem hA', su2Exp_of_not_mem hA, inv_one]

/-- the coarse gauge of the next level: `exp(S(y))⁻¹ γ(y)`. -/
noncomputable def nextG (s ell : ℕ) (V : PeriodicLinkConfiguration SU2 L)
    (γ : PeriodicLatticeSite L → SU2) : PeriodicLatticeSite L → SU2 :=
  fun y => (su2Exp (sBlock s ell V (pgV s V γ) y))⁻¹ * γ y

/-- **Pure gauge in, pure gauge out (exact, nonlinear).** -/
theorem rawStep_pgV (s ell : ℕ) (V : PeriodicLinkConfiguration SU2 L)
    (γ : PeriodicLatticeSite L → SU2) (c : PeriodicLatticeEdge L) :
    rawStep s ell V (pgV s V γ) c
      = pgV (s * ell) (stridedBlockedGauge su2LogExp s ell V) (nextG s ell V γ) c := by
  rw [rawStep_simp, pgV_mul, stridedBlockedGauge_gauge]
  simp only [pgV, nextG, AdalyFormal.Balaban.QjComposite.coarseGaugeTransform, su2Exp_neg]
  rw [cPlusS_eq]
  group

#print axioms pgV_mul
#print axioms inv_mem_SU2
#print axioms su2Exp_neg
#print axioms rawStep_pgV

end AdalyFormal.SliceCoerc
