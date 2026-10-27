import UA7

/-!
# UA8 -- U3 `lemma24_cov_C`: the covariant floor for `B = C B̃` of the statement, with the explicit partition (lane m2_unit_20261014)

Unit torus `L` (`ℓ ≥ 2`, `ℓ < L_μ+1`, `ℓ ∣ L_μ+1`), partition cells of side `M` (`PartOK L M`), region `Λ = B(Λ')`,
unit background `W` with `H₀(Q1jet ℓ W)` bijective, `B̃ ∈ Λ̃` on the touching set, `B = Cop Λ (Q1jet ℓ W) B̃` (= `genC` when
`W = unitBgU`, `Q₁ = Q1jet ℓ W`).  Charts: an index set `I` containing every cell active at the base point of a bond touching `Λ`,
and for each `m ∈ I` a gauge `u m` with `‖W^{u m} − 1‖_F ≤ κ` on `Ball(x, 4ℓ)` for every `x` in the support of cell `m`.
Conclusion: `(1/54)ℓ⁻⁵ ‖B‖² ≤ (1+ε) Σ_p ‖curl_W B p‖² + Eims ℓ (π/2M) (4ℓπ/2M) κ ε ‖B‖²` and `‖B̃‖² ≤ ‖B‖²`.
No global gauge: one gauge per cell of side `2M`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
namespace AdalyFormal.M2Unit

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.StatementLane2 (OnLambdaT)
open AdalyFormal.IngredientFamilyR2 (Q1jet H0 Cop)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice staircasePath)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo curlValueCovariant)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.StatementLaneR8 (Ball)
open AdalyFormal.NonflatJet (rhoOf r0)
open SmallnessBridge.Assemble (loopFactorBound)

variable {L : PeriodicLatticeExtent}

/-- `x` in the block of `c₀`, then `j < ℓ` steps along `c`: reached from `c₀` in at most `4ℓ` forward steps. -/
theorem reach_path {ell : ℕ} (hell : 0 < ell) (c : CoarseBond L ell) {x : PeriodicLatticeSite L}
    (hx : x ∈ blockOf c.1.1 ell) {j : ℕ} (hj : j ∈ Finset.range ell) :
    AdalyFormal.DLayer.Reach (4 * ell) c.1.1 (pathSite x c.2 j) := by
  have hx1 : x ∈ AdalyFormal.Balaban.QjComposite.stepBlockOf c.1.1 1 ell := by
    rw [AdalyFormal.Balaban.QjComposite.stepBlockOf_one]; exact hx
  have h1 := AdalyFormal.DLayer.block_reach 1 ell one_pos c.1.1 x hx1
  have h2 : AdalyFormal.DLayer.Reach j x (pathSite x c.2 j) :=
    ⟨List.replicate j c.2, by simp, AdalyFormal.DLayer.iterate_shift_foldl c.2 j x⟩
  have h3 := AdalyFormal.DLayer.Reach_trans h1 h2
  refine AdalyFormal.DLayer.Reach_mono ?_ h3
  have := Finset.mem_range.mp hj
  have : 3 * (ell - 1) * 1 ≤ 3 * ell := by omega
  omega

theorem Dq_part {ell M : ℕ} (hell : 0 < ell) (hP : PartOK L M) (I : Set ((μ : Fin 3) → Fin (Kc L M μ)))
    (c : CoarseBond L ell) (x : PeriodicLatticeSite L) (hx : x ∈ blockOf c.1.1 ell) (j : ℕ) (hj : j ∈ Finset.range ell) :
    ∑ m, (hres M I m (pathSite x c.2 j) - hres M I m c.1.1) ^ 2
      ≤ ((4 * ell : ℕ) * (Real.pi / (2 * M))) ^ 2 :=
  (hres_diff_le M I _ _).trans (hpart_reach hP (reach_path hell c hx hj))

/-- **U3 for the statement's `C`** (`lemma24_cov_C`). -/
theorem lemma24_cov_C {ell M : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ μ : Fin 3, ell < L μ + 1) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (hP : PartOK L M)
    {Lam : Set (PeriodicLatticeSite L)} (hLB : LamBlockSum ell Lam)
    (W : PeriodicLinkConfiguration SU2 L) (hb : Function.Bijective (H0 Lam (Q1jet ell W)))
    (Bt : Bond L → SuTwo) (hBt : OnLambdaTildeIn Lam ell Bt) (hBT : OnLambdaT Lam Bt)
    (I : Set ((μ : Fin 3) → Fin (Kc L M μ)))
    (hI : ∀ m (b : Bond L), (b.1 ∈ Lam ∨ periodicLatticeShift b.1 b.2 ∈ Lam) → hpart M m b.1 ≠ 0 → m ∈ I)
    (u : ((μ : Fin 3) → Fin (Kc L M μ)) → GaugeFn L) (κ ε : ℝ) (hκ : 0 ≤ κ) (hε : 0 < ε)
    (hρ : rhoOf ell κ < Real.pi / 2) (hrg : Real.pi / 2 * ((loopFactorBound ell : ℝ) * κ) < r0)
    (hS : ∀ m ∈ I, ∀ x, hpart M m x ≠ 0 → ∀ z ∈ Ball x (4 * (1 * ell)), ∀ μ : Fin 3,
      frobNorm (((periodicGaugeTransform (u m) W (z, μ) : SU2) : M2) - 1) ≤ κ) :
    (1 / 54 : ℝ) * (1 / (ell : ℝ) ^ 5) * ∑ b : Bond L, ‖Cop Lam (Q1jet ell W) Bt b‖ ^ 2
      ≤ (1 + ε) * ∑ p : PeriodicLatticePlaquette L, ‖curlValueCovariant W (Cop Lam (Q1jet ell W) Bt) p‖ ^ 2
        + Eims ell (Real.pi / (2 * M)) ((4 * ell : ℕ) * (Real.pi / (2 * M))) κ ε
          * ∑ b : Bond L, ‖Cop Lam (Q1jet ell W) Bt b‖ ^ 2
    ∧ bondEnergy Bt ≤ ∑ b : Bond L, ‖Cop Lam (Q1jet ell W) Bt b‖ ^ 2 := by
  have hell : 0 < ell := by omega
  have hu : ∀ μ, 1 ≤ L μ := fun μ => by have := hstrict μ; omega
  obtain ⟨hax, hrow, hen, hsup⟩ := Cop_props_Q hell hdvd hu hLB (Q1jet ell W) hb Bt hBt hBT
  refine ⟨?_, hen⟩
  refine cov_floor_ims hell2 hstrict hdvd W _ hax hrow (hres M I) u (Real.pi / (2 * M))
    ((4 * ell : ℕ) * (Real.pi / (2 * M))) κ ε hκ hε hρ hrg ?_ (hres_sq_le hP I) ?_ ?_ ?_
  · intro b hB
    exact hres_sq_eq hP I b.1 (fun m hm => hI m b (hsup b hB) hm)
  · intro x μ
    exact (hres_diff_le M I x _).trans (hpart_lip hP x μ)
  · intro c x hx j hj
    exact Dq_part hell hP I c x hx j hj
  · intro m x hx z hz μ
    unfold hres at hx
    by_cases hm : m ∈ I
    · rw [if_pos hm] at hx; exact hS m hm x hx z hz μ
    · rw [if_neg hm] at hx; exact absurd rfl hx

end AdalyFormal.M2Unit

#print axioms AdalyFormal.M2Unit.reach_path
#print axioms AdalyFormal.M2Unit.Dq_part
#print axioms AdalyFormal.M2Unit.lemma24_cov_C
