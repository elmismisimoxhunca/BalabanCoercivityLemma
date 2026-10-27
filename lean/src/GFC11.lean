import GFC10
import GFC3

/-!
# GFC11 -- eigen-field sums: for chi-eigen fields, torus sums are `∏ M_μ` times cell sums.  Standard axioms only.
-/
set_option autoImplicit false
open scoped BigOperators ComplexInnerProductSpace
open AdalyFormal.Target.ClayStatement

namespace AdalyFormal.FlatCoercivity

variable {L : PeriodicLatticeExtent} {n : ℕ}

/-- `∏ M_μ` as a real number -/
noncomputable def Mnum (L : PeriodicLatticeExtent) (n : ℕ) : ℝ := ((∏ μ, Mc L n μ : ℕ) : ℝ)

theorem Mnum_pos (hn : 0 < n) (hdvd : ∀ μ, n ∣ L μ + 1) : 0 < Mnum L n := by
  unfold Mnum
  have : 0 < ∏ μ, Mc L n μ := Finset.prod_pos (fun μ _ => Mc_pos hn hdvd μ)
  exact_mod_cast this

/-- eigen-fields on the torus (site fields) -/
def IsEigS (n : ℕ) (χ : AddChar (Site L) ℂ) (φ : TS L) : Prop := ∀ (g x : Site L), φ (x + n • g) = χ g * φ x

/-- eigen-fields (indexed by `Site × β`) -/
def IsEig {β : Type*} [Fintype β] (n : ℕ) (χ : AddChar (Site L) ℂ) (F : EuclideanSpace ℂ (Site L × β)) : Prop :=
  ∀ (g x : Site L) (b : β), F (x + n • g, b) = χ g * F (x, b)

theorem sum_site_eq_real (hn : 0 < n) (hdvd : ∀ μ, n ∣ L μ + 1) (f : Site L → ℝ)
    (hf : ∀ (g x : Site L), f (x + n • g) = f x) :
    ∑ x, f x = Mnum L n * ∑ t : Cell n, f (ιc hdvd t) := by
  have h := sum_site_eq hn hdvd (fun x => (f x : ℂ)) (fun g x => by rw [hf])
  unfold Mnum
  exact_mod_cast h

theorem normS_eig (hn : 0 < n) (hdvd : ∀ μ, n ∣ L μ + 1) (χ : AddChar (Site L) ℂ) (φ : TS L)
    (hφ : IsEigS n χ φ) : ‖φ‖ ^ 2 = Mnum L n * ∑ t : Cell n, ‖φ (ιc hdvd t)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine sum_site_eq_real hn hdvd (fun x => ‖φ x‖ ^ 2) (fun g x => ?_)
  simp only [hφ g x, norm_mul, AddChar.norm_apply, one_mul]

theorem innerS_eig (hn : 0 < n) (hdvd : ∀ μ, n ∣ L μ + 1) (χ : AddChar (Site L) ℂ) (φ ψ : TS L)
    (hφ : IsEigS n χ φ) (hψ : IsEigS n χ ψ) :
    ⟪φ, ψ⟫ = (Mnum L n : ℂ) * ∑ t : Cell n, (starRingEnd ℂ) (φ (ιc hdvd t)) * ψ (ιc hdvd t) := by
  have h := sum_site_eq hn hdvd (fun x => (starRingEnd ℂ) (φ x) * ψ x) (fun g x => by
    rw [hφ g x, hψ g x, map_mul]
    have : (starRingEnd ℂ) (χ g) * χ g = 1 := by
      rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]; simp
    calc _ = ((starRingEnd ℂ) (χ g) * χ g) * ((starRingEnd ℂ) (φ x) * ψ x) := by ring
      _ = _ := by rw [this, one_mul])
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply]
  have hM : (Mnum L n : ℂ) = ((∏ μ, Mc L n μ : ℕ) : ℂ) := by
    unfold Mnum; exact Complex.ofReal_natCast _
  rw [hM, ← h]
  exact Finset.sum_congr rfl (fun x _ => mul_comm _ _)

/-- slice of a `Site × β` field -/
noncomputable def sliceB {β : Type*} [Fintype β] (F : EuclideanSpace ℂ (Site L × β)) (b : β) : TS L :=
  WithLp.toLp 2 (fun x => F (x, b))

theorem normB_eig {β : Type*} [Fintype β] (hn : 0 < n) (hdvd : ∀ μ, n ∣ L μ + 1) (χ : AddChar (Site L) ℂ)
    (F : EuclideanSpace ℂ (Site L × β)) (hF : IsEig n χ F) :
    ‖F‖ ^ 2 = Mnum L n * ∑ b : β, ∑ t : Cell n, ‖F (ιc hdvd t, b)‖ ^ 2 := by
  have h1 : ‖F‖ ^ 2 = ∑ b : β, ‖sliceB F b‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  rw [h1, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  exact normS_eig hn hdvd χ (sliceB F b) (fun g x => hF g x b)

theorem eig_of_equiv {β κ : Type*} [Fintype β] [Fintype κ] (χ : AddChar (Site L) ℂ)
    (A : EuclideanSpace ℂ (Site L × β)) (hA : IsEig n χ A) (Lm : EuclideanSpace ℂ (Site L × β) →ₗ[ℂ] EuclideanSpace ℂ (Site L × κ))
    (hL : ∀ (g : Site L) (A : EuclideanSpace ℂ (Site L × β)), Lm (shiftE n g β A) = shiftE n g κ (Lm A)) :
    IsEig n χ (Lm A) := by
  intro g x b
  have h1 : shiftE n g β A = χ g • A := by
    ext ⟨y, c⟩
    rw [shiftE_apply]
    exact hA g y c
  have h2 := hL g A
  rw [h1, map_smul] at h2
  have h3 := congrArg (fun F => F (x, b)) h2
  simp only [shiftE_apply] at h3
  simpa using h3.symm

end AdalyFormal.FlatCoercivity
