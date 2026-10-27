import GFC16
import ZGU1N

/-!
# GFC17 -- repo bridge, part 1: su(2) coordinates, norms and the curl term.  Standard axioms only.
-/
set_option autoImplicit false
open scoped BigOperators ComplexInnerProductSpace RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

namespace AdalyFormal.FlatCoercivity

variable {L : PeriodicLatticeExtent} {n : ℕ}

abbrev JJ := Fin (Module.finrank ℝ SuTwo)

noncomputable def eb : OrthonormalBasis JJ ℝ SuTwo := stdOrthonormalBasis ℝ SuTwo

noncomputable def crd (v : SuTwo) (j : JJ) : ℝ := eb.repr v j

theorem crd_add (v w : SuTwo) (j : JJ) : crd (v + w) j = crd v j + crd w j := by simp [crd]
theorem crd_sub (v w : SuTwo) (j : JJ) : crd (v - w) j = crd v j - crd w j := by simp [crd]
theorem crd_smul (c : ℝ) (v : SuTwo) (j : JJ) : crd (c • v) j = c * crd v j := by simp [crd]

theorem norm_sq_crd (v : SuTwo) : ‖v‖ ^ 2 = ∑ j, (crd v j) ^ 2 := by
  have h := eb.repr.norm_map v
  rw [← h, EuclideanSpace.norm_sq_eq]
  simp [crd]

/-- coordinate `j` of a bond field, as a complex torus field -/
noncomputable def coordB (A : Bond L → SuTwo) (j : JJ) : TB L :=
  WithLp.toLp 2 (fun p : Site L × Fin 3 => ((crd (A p) j : ℝ) : ℂ))

theorem coordB_apply (A : Bond L → SuTwo) (j : JJ) (p : Site L × Fin 3) :
    coordB A j p = ((crd (A p) j : ℝ) : ℂ) := rfl

theorem norm_bond (A : BondFnL2 L) : ‖A‖ ^ 2 = ∑ j, ‖coordB (WithLp.ofLp A) j‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [norm_sq_crd, EuclideanSpace.norm_sq_eq, coordB_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [Finset.sum_comm]


theorem fin3_sym (G : Fin 3 → Fin 3 → ℝ) (hs : ∀ μ ν, G ν μ = G μ ν) (hd : ∀ μ, G μ μ = 0) :
    ∑ μ, ∑ ν, G μ ν = 2 * (G 0 1 + G 0 2 + G 1 2) := by
  simp only [Fin.sum_univ_three, hd, hs 1 0, hs 2 0, hs 2 1]
  ring

theorem subtype_pairs (F : Fin 3 × Fin 3 → ℝ) :
    ∑ d : PeriodicPlaquetteDirections, F d.1 = F (0, 1) + F (0, 2) + F (1, 2) := by
  have : (Finset.univ : Finset PeriodicPlaquetteDirections).map ⟨Subtype.val, Subtype.val_injective⟩
      = {((0 : Fin 3), (1 : Fin 3)), (0, 2), (1, 2)} := by
    ext ⟨a, b⟩
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨a', b'⟩, h⟩, hab⟩
      simp only [Prod.mk.injEq] at hab
      obtain ⟨rfl, rfl⟩ := hab
      revert h; revert a' b'; decide
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨⟨(0, 1), by decide⟩, rfl⟩
      · exact ⟨⟨(0, 2), by decide⟩, rfl⟩
      · exact ⟨⟨(1, 2), by decide⟩, rfl⟩
  have h2 := Finset.sum_map (Finset.univ : Finset PeriodicPlaquetteDirections) ⟨Subtype.val, Subtype.val_injective⟩ F
  rw [this] at h2
  simp only [Function.Embedding.coeFn_mk] at h2
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton] at h2
  rw [← h2]; ring


open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue)
open AdalyFormal.GenuineU1 (curlnorm_eq)
open AdalyFormal.IngredientFamilyR2 (flatCfg)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)

/-- real curl coordinate -/
noncomputable def crl (a : Site L × Fin 3 → ℝ) (x : Site L) (μ ν : Fin 3) : ℝ :=
  a (x + eU L μ, ν) - a (x, ν) - a (x + eU L ν, μ) + a (x, μ)

theorem crl_anti (a : Site L × Fin 3 → ℝ) (x : Site L) (μ ν : Fin 3) : crl a x ν μ = - crl a x μ ν := by
  unfold crl; ring

theorem crl_diag (a : Site L × Fin 3 → ℝ) (x : Site L) (μ : Fin 3) : crl a x μ μ = 0 := by
  unfold crl; ring

theorem crd_flatCurl (A : Bond L → SuTwo) (x : Site L) (d : PeriodicPlaquetteDirections) (j : JJ) :
    crd (flatCurlValue A (x, d)) j = crl (fun p => crd (A p) j) x d.1.1 d.1.2 := by
  unfold flatCurlValue crl
  simp only [crd_add, crd_sub, shift_eq]
  ring

theorem L1_coord_norm (A : Bond L → SuTwo) (j : JJ) :
    ‖L1 L (coordB A j)‖ ^ 2 = ∑ x : Site L, ∑ μ : Fin 3, ∑ ν : Fin 3,
      (1 / 2 : ℝ) * (crl (fun p => crd (A p) j) x μ ν) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun μ _ => Finset.sum_congr rfl (fun ν _ => ?_))
  rw [L1_apply]
  simp only [coordB_apply]
  have : (((1 / Real.sqrt 2 : ℝ) : ℂ) * (((crd (A (x + eU L μ, ν)) j : ℝ) : ℂ) - ((crd (A (x, ν)) j : ℝ) : ℂ)
      - ((crd (A (x + eU L ν, μ)) j : ℝ) : ℂ) + ((crd (A (x, μ)) j : ℝ) : ℂ)))
      = (((1 / Real.sqrt 2 * crl (fun p => crd (A p) j) x μ ν : ℝ)) : ℂ) := by
    unfold crl; push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, div_pow, Real.sq_sqrt (by norm_num)]
  ring

theorem curl_energy (A : BondFnL2 L) :
    ‖curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) A‖ ^ 2
      = ∑ j, ‖L1 L (coordB (WithLp.ofLp A) j)‖ ^ 2 := by
  rw [curlnorm_eq, Fintype.sum_prod_type]
  have key : ∀ (x : Site L) (j : JJ), ∑ d : PeriodicPlaquetteDirections,
      (crl (fun p => crd ((WithLp.ofLp A) p) j) x d.1.1 d.1.2) ^ 2
      = ∑ μ : Fin 3, ∑ ν : Fin 3, (1 / 2 : ℝ) * (crl (fun p => crd ((WithLp.ofLp A) p) j) x μ ν) ^ 2 := by
    intro x j
    set a : Site L × Fin 3 → ℝ := fun p => crd ((WithLp.ofLp A) p) j with ha
    have h1 := subtype_pairs (fun q => (crl a x q.1 q.2) ^ 2)
    have h2 := fin3_sym (fun μ ν => (1 / 2 : ℝ) * (crl a x μ ν) ^ 2)
      (fun μ ν => by simp only [crl_anti a x μ ν]; ring) (fun μ => by simp [crl_diag])
    simp only at h1 h2
    rw [h1, h2]; ring
  have hL : ∀ x : Site L, ∑ d : PeriodicPlaquetteDirections, ‖flatCurlValue (WithLp.ofLp A) (x, d)‖ ^ 2
      = ∑ j, ∑ d : PeriodicPlaquetteDirections, (crl (fun p => crd ((WithLp.ofLp A) p) j) x d.1.1 d.1.2) ^ 2 := by
    intro x
    simp only [norm_sq_crd, crd_flatCurl]
    rw [Finset.sum_comm]
  simp only [hL, key, L1_coord_norm]
  rw [Finset.sum_comm]

end AdalyFormal.FlatCoercivity
