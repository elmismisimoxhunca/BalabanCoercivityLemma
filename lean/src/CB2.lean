import CB1
/-!
# CB2 -- the strided ladder (nonabelian Stokes estimate at stride `s`)

`ladS s V y p μ n` is the closed loop: path `p` from `y`, then `n` strided steps in direction `μ`,
back along the `n μ`-translate of `p`, back along the `n` strided `μ`-steps.  Two exact group
identities peel off one rung (`ladS_cons`) and one plaquette (`ladS_rung`); with conjugation
invariance and subadditivity of `dv` they give `dv (ladS) ≤ |p| · n · q` whenever every enclosed
stride-`s` plaquette word has defect `≤ q` (`ladS_le`, local: only the enclosed plaquettes enter).
This generalises `UniformFactor.lad`/`su2Angle_lad_le` (stride 1, angle) to stride `s` and `dv`.

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarsePathEndpoint)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)

variable {L : PeriodicLatticeExtent}

/-- The stride-`s` plaquette word in the `(ν, μ)` order. -/
def pw (s : ℕ) (V : PeriodicLinkConfiguration SU2 L) (y : PeriodicLatticeSite L) (ν μ : Fin 3) :
    SU2 :=
  V (y, ν) * V (coarseShift y s ν, μ) * (V (coarseShift y s μ, ν))⁻¹ * (V (y, μ))⁻¹

/-- The strided ladder loop. -/
def ladS (s : ℕ) (V : PeriodicLinkConfiguration SU2 L) (y : PeriodicLatticeSite L)
    (p : List (Fin 3)) (μ : Fin 3) (n : ℕ) : SU2 :=
  coarsePathHolonomy s V y p
      * coarsePathHolonomy s V (coarsePathEndpoint s y p) (List.replicate n μ)
      * (coarsePathHolonomy s V (coarseShift y (s * n) μ) p)⁻¹
    * (coarsePathHolonomy s V y (List.replicate n μ))⁻¹

/-- Plaquettes enclosed by one rung. -/
def rungPlaqs (s : ℕ) (ν μ : Fin 3) :
    PeriodicLatticeSite L → ℕ → List (PeriodicLatticeSite L × Fin 3 × Fin 3)
  | _, 0 => []
  | y, n + 1 => (y, ν, μ) :: rungPlaqs s ν μ (coarseShift y s μ) n

/-- Plaquettes enclosed by the ladder. -/
def ladPlaqs (s : ℕ) (μ : Fin 3) (n : ℕ) :
    PeriodicLatticeSite L → List (Fin 3) → List (PeriodicLatticeSite L × Fin 3 × Fin 3)
  | _, [] => []
  | y, ν :: rest => rungPlaqs s ν μ y n ++ ladPlaqs s μ n (coarseShift y s ν) rest

theorem shift_add (y : PeriodicLatticeSite L) (a b : ℕ) (μ : Fin 3) :
    coarseShift y (a + b) μ = coarseShift (coarseShift y b μ) a μ := by
  unfold coarseShift
  rw [Function.iterate_add_apply]

theorem ladS_cons (s : ℕ) (V : PeriodicLinkConfiguration SU2 L) (y : PeriodicLatticeSite L)
    (ν : Fin 3) (p : List (Fin 3)) (μ : Fin 3) (n : ℕ) :
    ladS s V y (ν :: p) μ n
      = (V (y, ν) * ladS s V (coarseShift y s ν) p μ n * (V (y, ν))⁻¹) * ladS s V y [ν] μ n := by
  have hc := AdalyFormal.Balaban.U1AnchorPoincare.coarseShift_comm_gen y (s * n) s μ ν
  unfold ladS
  show V (y, ν) * coarsePathHolonomy s V (coarseShift y s ν) p
      * coarsePathHolonomy s V (coarsePathEndpoint s (coarseShift y s ν) p) (List.replicate n μ)
      * (V (coarseShift y (s * n) μ, ν)
          * coarsePathHolonomy s V (coarseShift (coarseShift y (s * n) μ) s ν) p)⁻¹
      * (coarsePathHolonomy s V y (List.replicate n μ))⁻¹
    = (V (y, ν) * (coarsePathHolonomy s V (coarseShift y s ν) p
      * coarsePathHolonomy s V (coarsePathEndpoint s (coarseShift y s ν) p) (List.replicate n μ)
      * (coarsePathHolonomy s V (coarseShift (coarseShift y s ν) (s * n) μ) p)⁻¹
      * (coarsePathHolonomy s V (coarseShift y s ν) (List.replicate n μ))⁻¹) * (V (y, ν))⁻¹)
      * ((V (y, ν) * 1) * coarsePathHolonomy s V (coarseShift y s ν) (List.replicate n μ)
        * (V (coarseShift y (s * n) μ, ν) * 1)⁻¹ * (coarsePathHolonomy s V y (List.replicate n μ))⁻¹)
  rw [hc]
  group

theorem ladS_rung (s : ℕ) (V : PeriodicLinkConfiguration SU2 L) (y : PeriodicLatticeSite L)
    (ν μ : Fin 3) (n : ℕ) :
    ladS s V y [ν] μ (n + 1)
      = pw s V y ν μ * (V (y, μ) * ladS s V (coarseShift y s μ) [ν] μ n * (V (y, μ))⁻¹) := by
  have hc := AdalyFormal.Balaban.U1AnchorPoincare.coarseShift_comm_gen y s s ν μ
  have ha : coarseShift y (s * (n + 1)) μ = coarseShift (coarseShift y s μ) (s * n) μ := by
    rw [Nat.mul_succ, shift_add]
  unfold ladS pw
  rw [ha]
  show (V (y, ν) * 1)
      * (V (coarseShift y s ν, μ)
          * coarsePathHolonomy s V (coarseShift (coarseShift y s ν) s μ) (List.replicate n μ))
      * (V (coarseShift (coarseShift y s μ) (s * n) μ, ν) * 1)⁻¹
      * (V (y, μ) * coarsePathHolonomy s V (coarseShift y s μ) (List.replicate n μ))⁻¹
    = V (y, ν) * V (coarseShift y s ν, μ) * (V (coarseShift y s μ, ν))⁻¹ * (V (y, μ))⁻¹
      * (V (y, μ) * ((V (coarseShift y s μ, ν) * 1)
        * coarsePathHolonomy s V (coarseShift (coarseShift y s μ) s ν) (List.replicate n μ)
        * (V (coarseShift (coarseShift y s μ) (s * n) μ, ν) * 1)⁻¹
        * (coarsePathHolonomy s V (coarseShift y s μ) (List.replicate n μ))⁻¹) * (V (y, μ))⁻¹)
  rw [hc]
  group

theorem ladS_zero (s : ℕ) (V : PeriodicLinkConfiguration SU2 L) (y : PeriodicLatticeSite L)
    (p : List (Fin 3)) (μ : Fin 3) : ladS s V y p μ 0 = 1 := by
  unfold ladS
  rw [Nat.mul_zero]
  show coarsePathHolonomy s V y p * 1 * (coarsePathHolonomy s V y p)⁻¹ * (1 : SU2)⁻¹ = 1
  group

theorem ladS_nil (s : ℕ) (V : PeriodicLinkConfiguration SU2 L) (y : PeriodicLatticeSite L)
    (μ : Fin 3) (n : ℕ) : ladS s V y [] μ n = 1 := by
  unfold ladS
  show 1 * coarsePathHolonomy s V y (List.replicate n μ) * (1 : SU2)⁻¹
      * (coarsePathHolonomy s V y (List.replicate n μ))⁻¹ = 1
  group

/-- **Rung bound.** -/
theorem rung_le (s : ℕ) (V : PeriodicLinkConfiguration SU2 L) (ν μ : Fin 3) (q : ℝ) :
    ∀ (n : ℕ) (y : PeriodicLatticeSite L),
      (∀ t ∈ rungPlaqs s ν μ y n, dv (pw s V t.1 t.2.1 t.2.2) ≤ q) →
      dv (ladS s V y [ν] μ n) ≤ (n : ℝ) * q := by
  intro n
  induction n with
  | zero => intro y _; rw [ladS_zero, dv_one]; simp
  | succ k ih =>
      intro y h
      rw [ladS_rung]
      refine le_trans (dv_mul _ _) ?_
      rw [dv_conj]
      have h0 := h (y, ν, μ) (List.mem_cons_self ..)
      have h1 := ih (coarseShift y s μ) (fun t ht => h t (List.mem_cons_of_mem _ ht))
      push_cast
      linarith

/-- **Ladder bound (strided nonabelian Stokes).** -/
theorem ladS_le (s : ℕ) (V : PeriodicLinkConfiguration SU2 L) (μ : Fin 3) (n : ℕ) (q : ℝ) :
    ∀ (p : List (Fin 3)) (y : PeriodicLatticeSite L),
      (∀ t ∈ ladPlaqs s μ n y p, dv (pw s V t.1 t.2.1 t.2.2) ≤ q) →
      dv (ladS s V y p μ n) ≤ (p.length : ℝ) * ((n : ℝ) * q) := by
  intro p
  induction p with
  | nil => intro y _; rw [ladS_nil, dv_one]; simp
  | cons ν rest ih =>
      intro y h
      rw [ladS_cons]
      refine le_trans (dv_mul _ _) ?_
      rw [dv_conj]
      have h1 := ih (coarseShift y s ν)
        (fun t ht => h t (List.mem_append_right _ ht))
      have h2 := rung_le s V ν μ q n y (fun t ht => h t (List.mem_append_left _ ht))
      simp only [List.length_cons]; push_cast
      linarith

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.ladS_cons
#print axioms AdalyFormal.CurvBlock.ladS_rung
#print axioms AdalyFormal.CurvBlock.ladS_le
