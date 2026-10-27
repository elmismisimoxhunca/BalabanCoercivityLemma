import GdTheta

/-!
# GdGeo -- the source `J` of the boundary-twist family `Uth (Ω₀) θ` vanishes on every bond of `E₀` that is not a level-0 bond.
Reason: such a bond has an endpoint in `Ω₁`, all plaquettes involved in `J` there have their corner sites in `Ω₀` (collar `R M ≥ 5`), hence all their links
are `1` and `Im ∂U = 0`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.D1Guarded

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.IngredientFamily
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.SourceJ
open AdalyFormal.D1Literal
open AdalyFormal.StatementLaneR8
open AdalyFormal.Balaban.CoarseCurl (coarseShift)

variable {L : PeriodicLatticeExtent}

theorem coarseShift_one' (y : PeriodicLatticeSite L) (μ : Fin 3) : coarseShift y 1 μ = periodicLatticeShift y μ := rfl

/-- a bond of `E₀` which is not a level-0 bond has an endpoint in `Ω₁`. -/
theorem endpoint_om1 {ell M R k : ℕ} (hell : 0 < ell) {S : Tower L} (hS : Admissible ell M R k S) (b : Bond L)
    (h1 : b ∈ bondsOm0 (geomOf ell k S)) (h2 : b ∉ bondsLam (geomOf ell k S) 0) :
    b.1 ∈ S.Om 1 ∨ periodicLatticeShift b.1 b.2 ∈ S.Om 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨n1, n2⟩ := hcon
  apply h2
  have hge1 : ¬ OmGe (geomOf ell k S) 1 b.1 := fun h => n1 ((omGe_iff_om ell M R k hell S hS 1 _).mp h)
  have hge2 : ¬ OmGe (geomOf ell k S) 1 (coarseShift b.1 (ell ^ 0) b.2) := by
    intro h
    have := (omGe_iff_om ell M R k hell S hS 1 _).mp h
    rw [pow_zero, coarseShift_one'] at this
    exact n2 this
  refine ⟨?_, fun h => h.elim hge1 hge2⟩
  rcases h1 with h | h
  · exact Or.inl ⟨fun μ => by simp, h, n1⟩
  · refine Or.inr ⟨fun μ => by simp, ?_, ?_⟩
    · rw [pow_zero, coarseShift_one']; exact h
    · rw [pow_zero, coarseShift_one']; exact n2

/-- collar: every site within `ℓ¹`-distance `R M` of an `Ω₁`-site lies in `Ω₀`. -/
theorem near_om1 {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) {w z : PeriodicLatticeSite L}
    (hw : w ∈ S.Om 1) (hd : pdist z w ≤ R * M) (hk : 0 ≤ k) : z ∈ S.Om 0 := by
  by_contra hz
  have := hS.2.2.2.2.1 0 hk z hz w hw
  simp [bigSide] at this
  omega

theorem Uth_one_of_base (Om : Set (PeriodicLatticeSite L)) (θ : ℝ) (e : Bond L) (he : e.1 ∈ Om) :
    Uth Om θ e = 1 := by
  unfold Uth
  rw [if_neg]
  intro h; exact h.1 he

theorem imHolonomy_eq_zero_of_flat (U : PeriodicLinkConfiguration SU2m L) (p : PeriodicLatticePlaquette L)
    (h : ((holonomyElem U p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = 1) : imHolonomy U p = 0 := by
  have hinv : ((holonomyElemInv U p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    have : ((holonomyElemInv U p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = star ((holonomyElem U p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := rfl
    rw [this, h]; simp
  unfold imHolonomy; rw [h, hinv]; simp

theorem hol_eq_one (U : PeriodicLinkConfiguration SU2m L) (Om : Set (PeriodicLatticeSite L))
    (hU : ∀ e : Bond L, e.1 ∈ Om → U e = 1) (p : PeriodicLatticePlaquette L)
    (h0 : p.1 ∈ Om) (h1 : periodicLatticeShift p.1 p.2.1.1 ∈ Om) (h2 : periodicLatticeShift p.1 p.2.1.2 ∈ Om) :
    ((holonomyElem U p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  unfold holonomyElem periodicPlaquetteHolonomy
  simp [hU (p.1, p.2.1.1) h0, hU (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) h1,
    hU (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) h2, hU (p.1, p.2.1.2) h0]

theorem FnuMuLoc_zero_of_flat (P : Set (PeriodicLatticePlaquette L)) (U : PeriodicLinkConfiguration SU2m L)
    (Om : Set (PeriodicLatticeSite L)) (hU : ∀ e : Bond L, e.1 ∈ Om → U e = 1)
    (ν μ : Fin 3) (y : PeriodicLatticeSite L) (h0 : y ∈ Om) (h1 : periodicLatticeShift y ν ∈ Om)
    (h2 : periodicLatticeShift y μ ∈ Om) : FnuMuLoc P U ν μ y = 0 := by
  have hz : ∀ q : PeriodicLatticePlaquette L, q.1 = y →
      (q.2.1.1 = ν ∧ q.2.1.2 = μ ∨ q.2.1.1 = μ ∧ q.2.1.2 = ν) → imHolonomy U q = 0 := by
    intro q hq hdir
    apply imHolonomy_eq_zero_of_flat
    apply hol_eq_one U Om hU q
    · rw [hq]; exact h0
    · rcases hdir with ⟨a, b⟩ | ⟨a, b⟩ <;> rw [hq, a] <;> assumption
    · rcases hdir with ⟨a, b⟩ | ⟨a, b⟩ <;> rw [hq, b] <;> assumption
  unfold FnuMuLoc
  split_ifs with hlt hmem hgt hmem'
  · rw [hz (y, ⟨(ν, μ), hlt⟩) rfl (Or.inl ⟨rfl, rfl⟩)]; simp [piProj]
  · rfl
  · rw [hz (y, ⟨(μ, ν), hgt⟩) rfl (Or.inr ⟨rfl, rfl⟩)]; simp [piProj]
  · rfl
  · rfl

theorem JfieldLoc_zero_of_flat (P : Set (PeriodicLatticePlaquette L)) (U : PeriodicLinkConfiguration SU2m L)
    (Om : Set (PeriodicLatticeSite L)) (hU : ∀ e : Bond L, e.1 ∈ Om → U e = 1)
    (x : PeriodicLatticeSite L) (μ : Fin 3)
    (hcol : ∀ z : PeriodicLatticeSite L, pdist z x ≤ 2 → z ∈ Om) : JfieldLoc P U x μ = 0 := by
  unfold JfieldLoc
  refine Finset.sum_eq_zero (fun ν _ => ?_)
  by_cases hνμ : ν = μ
  · simp [hνμ]
  · simp only [hνμ, if_false]
    have hb := AdalyFormal.StatementLaneR8.pdist_shiftBack_le x ν
    have s1 := AdalyFormal.StatementLaneR8.pdist_shift_le x ν
    have s2 := AdalyFormal.StatementLaneR8.pdist_shift_le x μ
    have hF0 : FnuMuLoc P U ν μ x = 0 :=
      FnuMuLoc_zero_of_flat P U Om hU ν μ x (hcol x (by rw [AdalyFormal.StatementLaneR8.pdist_self]; omega))
        (hcol _ (by rw [AdalyFormal.StatementLaneR8.pdist_comm]; omega)) (hcol _ (by rw [AdalyFormal.StatementLaneR8.pdist_comm]; omega))
    set x' := AdalyFormal.Balaban.CovariantHjMinimizer.periodicLatticeShiftBack x ν with hx'
    have t1 := AdalyFormal.StatementLaneR8.pdist_shift_le x' ν
    have t2 := AdalyFormal.StatementLaneR8.pdist_shift_le x' μ
    have tri1 := AdalyFormal.StatementLaneR8.pdist_triangle x x' (periodicLatticeShift x' ν)
    have tri2 := AdalyFormal.StatementLaneR8.pdist_triangle x x' (periodicLatticeShift x' μ)
    have hF1 : FnuMuLoc P U ν μ x' = 0 :=
      FnuMuLoc_zero_of_flat P U Om hU ν μ x' (hcol x' (by rw [AdalyFormal.StatementLaneR8.pdist_comm]; omega))
        (hcol _ (by rw [AdalyFormal.StatementLaneR8.pdist_comm]; omega)) (hcol _ (by rw [AdalyFormal.StatementLaneR8.pdist_comm]; omega))
    unfold DstarDir
    simp only []
    rw [← hx', hF0, hF1]
    simp

section assembled
variable (sJ : PlaqSel) (P : IngrBParams)

theorem JfS_vanish {M R : ℕ} (hS : Admissible P.ell M R P.k P.S) (hell : 0 < P.ell) (h3 : 3 ≤ R * M) (θ : ℝ)
    (hU : P.U = Uth (P.S.Om 0) θ) (b : Bond P.Lf) (hb1 : b ∈ bondsOm0 P.G) (hb2 : b ∉ bondsLam P.G 0) :
    (WithLp.ofLp (JfS sJ P)) b = 0 := by
  have hU' : ∀ e : Bond P.Lf, e.1 ∈ P.S.Om 0 → P.U e = 1 := fun e he => by
    rw [hU]; exact Uth_one_of_base _ θ e he
  have hz : JfieldLoc (sJ _ P.G) P.U b.1 b.2 = 0 := by
    apply JfieldLoc_zero_of_flat _ _ (P.S.Om 0) hU'
    intro z hz
    rcases endpoint_om1 hell hS b hb1 hb2 with hw | hw
    · refine near_om1 hS hw ?_ (Nat.zero_le _)
      have := AdalyFormal.StatementLaneR8.pdist_triangle z b.1 b.1
      rw [AdalyFormal.StatementLaneR8.pdist_self] at this
      omega
    · refine near_om1 hS hw ?_ (Nat.zero_le _)
      have h1 := AdalyFormal.StatementLaneR8.pdist_triangle z b.1 (periodicLatticeShift b.1 b.2)
      have h2 := AdalyFormal.StatementLaneR8.pdist_shift_le b.1 b.2
      omega
  unfold JfS
  simp only [WithLp.ofLp_toLp]
  unfold AdalyFormal.IngredientFamily.JSU2Loc
  apply Subtype.ext
  simp [hz]

end assembled

#print axioms coarseShift_one'
#print axioms endpoint_om1
#print axioms near_om1
#print axioms Uth_one_of_base
#print axioms imHolonomy_eq_zero_of_flat
#print axioms hol_eq_one
#print axioms FnuMuLoc_zero_of_flat
#print axioms JfieldLoc_zero_of_flat
#print axioms JfS_vanish

end AdalyFormal.D1Guarded
