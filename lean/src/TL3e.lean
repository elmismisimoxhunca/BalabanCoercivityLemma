import TL3d

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace

section proj
variable {D X Xt : Type} [Fintype D] [Fintype X] [Fintype Xt] [DecidableEq X] [DecidableEq Xt]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem adjoint_starProj {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (K : Submodule ℝ F) : ContinuousLinearMap.adjoint K.starProjection = K.starProjection := by
  rw [← ContinuousLinearMap.star_eq_adjoint]
  exact (isSelfAdjoint_starProjection K).star_eq

theorem adjoint_mem_of_invariant {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (ρ : F →L[ℝ] F) (hρ : (ContinuousLinearMap.adjoint ρ).comp ρ = ContinuousLinearMap.id ℝ F)
    (N : Submodule ℝ F) (hN : ∀ n ∈ N, ρ n ∈ N) : ∀ n ∈ N, ContinuousLinearMap.adjoint ρ n ∈ N := by
  intro n hn
  let r : N →ₗ[ℝ] N := (ρ : F →ₗ[ℝ] F).restrict hN
  have hinj : Function.Injective r := by
    intro x y hxy
    have h1 : ρ x.1 = ρ y.1 := congrArg Subtype.val hxy
    have h2 := congrArg (ContinuousLinearMap.adjoint ρ) h1
    have e : ∀ z : F, ContinuousLinearMap.adjoint ρ (ρ z) = z := fun z => congrArg (fun T => T z) hρ
    rw [e, e] at h2
    exact Subtype.ext h2
  obtain ⟨m, hm⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨n, hn⟩
  have : ρ m.1 = n := congrArg Subtype.val hm
  have e : ContinuousLinearMap.adjoint ρ (ρ m.1) = m.1 := congrArg (fun T => T m.1) hρ
  rw [← this, e]
  exact m.2

theorem comm_adjoint_unitary {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (ρ Φ : F →L[ℝ] F) (h1 : ρ.comp (ContinuousLinearMap.adjoint ρ) = ContinuousLinearMap.id ℝ F)
    (h2 : (ContinuousLinearMap.adjoint ρ).comp ρ = ContinuousLinearMap.id ℝ F)
    (hc : ∀ g, Φ (ρ g) = ρ (Φ g)) (m : F) : Φ (ContinuousLinearMap.adjoint ρ m) = ContinuousLinearMap.adjoint ρ (Φ m) := by
  have e1 : ∀ z, ρ (ContinuousLinearMap.adjoint ρ z) = z := fun z => congrArg (fun T => T z) h1
  have e2 : ∀ z, ContinuousLinearMap.adjoint ρ (ρ z) = z := fun z => congrArg (fun T => T z) h2
  have := congrArg (ContinuousLinearMap.adjoint ρ) (hc (ContinuousLinearMap.adjoint ρ m))
  rw [e1, e2] at this
  exact this.symm

theorem Kt_adjoint_mem {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (ρ Φ : F →L[ℝ] F) (h1 : ρ.comp (ContinuousLinearMap.adjoint ρ) = ContinuousLinearMap.id ℝ F)
    (h2 : (ContinuousLinearMap.adjoint ρ).comp ρ = ContinuousLinearMap.id ℝ F)
    (hc : ∀ g, Φ (ρ g) = ρ (Φ g)) (Nt Kt : Submodule ℝ F) (hNtadj : ∀ n ∈ Nt, ContinuousLinearMap.adjoint ρ n ∈ Nt)
    (memKt : ∀ w, w ∈ Kt ↔ ∃ m ∈ Nt, Φ m = w) : ∀ w ∈ Kt, ContinuousLinearMap.adjoint ρ w ∈ Kt := by
  intro w hw
  obtain ⟨m, hm, rfl⟩ := (memKt _).mp hw
  exact (memKt _).mpr ⟨ContinuousLinearMap.adjoint ρ m, hNtadj m hm, comm_adjoint_unitary ρ Φ h1 h2 hc m⟩

/-- the orthogonal projection onto `Φ N` descends when `ℓ N ⊂ Ñ` and `σ Ñ ⊂ N` and `Φ` descends. -/
theorem desc_starProjection [Nonempty D] (cX : Cov D Xt X)
    (Φ : PiLp 2 (fun _ : X => E) →L[ℝ] PiLp 2 (fun _ : X => E))
    (Φt : PiLp 2 (fun _ : Xt => E) →L[ℝ] PiLp 2 (fun _ : Xt => E)) (hΦ : Desc cX cX Φ Φt)
    (N : Submodule ℝ (PiLp 2 (fun _ : X => E))) (Nt : Submodule ℝ (PiLp 2 (fun _ : Xt => E)))
    (ha : ∀ f ∈ N, cX.ell f ∈ Nt) (hb : ∀ f ∈ Nt, cX.sig f ∈ N)
    (hNt : ∀ d, ∀ f ∈ Nt, cX.pull d f ∈ Nt)
    (K : Submodule ℝ (PiLp 2 (fun _ : X => E))) (Kt : Submodule ℝ (PiLp 2 (fun _ : Xt => E)))
    (memK : ∀ w, w ∈ K ↔ ∃ m ∈ N, Φ m = w) (memKt : ∀ w, w ∈ Kt ↔ ∃ m ∈ Nt, Φt m = w) :
    Desc (E := E) cX cX K.starProjection Kt.starProjection := by
  have e1 : E1 (E := E) cX cX K.starProjection Kt.starProjection := by
    ext1 x
    simp only [ContinuousLinearMap.comp_apply]
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
    · have hmem := Submodule.starProjection_apply_mem K x
      obtain ⟨n, hn, hnx⟩ := (memK _).mp hmem
      refine (memKt _).mpr ⟨cX.ell n, ha n hn, ?_⟩
      rw [← hnx]
      exact (congrArg (fun T => T n) hΦ.e1)
    · intro w hw
      obtain ⟨m, hm, rfl⟩ := (memKt _).mp hw
      rw [← map_sub, cX.inner_ell_left]
      have h2 : cX.sig (Φt m) = Φ (cX.sig m) := congrArg (fun T => T m) hΦ.e2
      rw [h2]
      have hmem : Φ (cX.sig m) ∈ K := (memK _).mpr ⟨cX.sig m, hb m hm, rfl⟩
      exact Submodule.sub_starProjection_mem_orthogonal x _ hmem |> fun h => by
        rw [real_inner_comm]; exact h
  refine ⟨e1, ?_, ?_⟩
  · have := congrArg ContinuousLinearMap.adjoint e1
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, adjoint_starProj, adjoint_starProj, ← cX.sig_eq_adjoint_ell] at this
    unfold E2
    exact this
  · intro d
    ext1 x
    simp only [ContinuousLinearMap.comp_apply]
    obtain ⟨hPY, hPYs⟩ := cX.pull_orth (E := E) d
    have hKt : ∀ w ∈ Kt, cX.pull d w ∈ Kt := by
      intro w hw
      obtain ⟨m, hm, rfl⟩ := (memKt _).mp hw
      refine (memKt _).mpr ⟨cX.pull d m, hNt d m hm, ?_⟩
      exact congrArg (fun T => T m) (hΦ.equi d)
    have hNtadj : ∀ n ∈ Nt, ContinuousLinearMap.adjoint (cX.pull d) n ∈ Nt :=
      adjoint_mem_of_invariant (F := PiLp 2 fun _ : Xt => E) (cX.pull d) hPYs Nt (hNt d)
    have hKtadj : ∀ w ∈ Kt, ContinuousLinearMap.adjoint (cX.pull d) w ∈ Kt :=
      Kt_adjoint_mem (F := PiLp 2 fun _ : Xt => E) (cX.pull d) Φt hPY hPYs
        (fun g => congrArg (fun T => T g) (hΦ.equi d)) Nt Kt hNtadj memKt
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
    · exact hKt _ (Submodule.starProjection_apply_mem Kt x)
    · intro w hw
      have hw' := hKtadj w hw
      have h0 := Submodule.sub_starProjection_mem_orthogonal (K := Kt) x _ hw'
      rw [← map_sub, ← ContinuousLinearMap.adjoint_inner_right]
      rw [real_inner_comm]; exact h0

end proj

end AdalyFormal.Thin
