import NsCvO4

/-!
# CvO5 -- TEMPORAL configurations: all loops of the (43)-average are trivial, and blocking preserves the class (lane omega)

`IsTemporal s V a`: at every stride-`s` coarse site `y`, `V (y,0) = cartan (a y₀)` and `V (y,1) = V (y,2) = 1`.
* `loopVar_temporal`: every loop `W_x = V(Γ_{c,x}) V(c)⁻¹` of such a configuration is `1` (the angle sums telescope);
* `blocked_temporal`: `stridedBlockedGauge su2LogExp s ell V` is temporal at stride `s * ell` with `a'(v) = Σ_{j<ell} a((v + s j) mod N₀)`.
Used for the levels `≥ 1` of the tower of the staggered layer (CvO6): there `Ū^1` is temporal (numerics: only the `0`-direction links
at the layer carry angle `± t/2`), hence every loop of `Ū^1, Ū^2, ...` is `1` and `su2Log` is evaluated at the identity.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge loopVar coarseBondVar gammaVarStrided cPlusS cPlusS_eq)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarsePathEndpoint coarseGammaPath coarseCoordSteps coarseStraightSegment)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf coarsePathHolonomy_cons coarsePathHolonomy_nil coarsePathEndpoint_cons
  coarsePathEndpoint_append coarsePathHolonomy_append)

variable {L : PeriodicLatticeExtent}

/-- every coordinate of `y` is divisible by `s`. -/
def Crs (s : ℕ) (y : PeriodicLatticeSite L) : Prop := ∀ μ, s ∣ (y μ).val

theorem Crs_shift {s : ℕ} (hdiv : ∀ μ, s ∣ L μ + 1) {y : PeriodicLatticeSite L} (hy : Crs s y) (μ : Fin 3) (m : ℕ)
    (hm : s ∣ m) : Crs s (coarseShift y m μ) := by
  intro ν
  by_cases h : ν = μ
  · subst h
    rw [coarseShift_val_eq]
    exact (Nat.dvd_mod_iff (hdiv ν)).mpr (dvd_add (hy ν) hm)
  · rw [coarseShift_apply_ne y m μ ν h]; exact hy ν

theorem endpoint_rep_ne (s : ℕ) (μ ν : Fin 3) (hνμ : ν ≠ μ) (n : ℕ) :
    ∀ y : PeriodicLatticeSite L, (coarsePathEndpoint s y (List.replicate n μ)) ν = y ν := by
  induction n with
  | zero => intro y; rfl
  | succ n ih => intro y; rw [List.replicate_succ, coarsePathEndpoint_cons, ih, coarseShift_apply_ne y s μ ν hνμ]

theorem crs_endpoint_rep {s : ℕ} (hdiv : ∀ μ, s ∣ L μ + 1) (μ : Fin 3) (n : ℕ) :
    ∀ y : PeriodicLatticeSite L, Crs s y → Crs s (coarsePathEndpoint s y (List.replicate n μ)) := by
  induction n with
  | zero => intro y hy; exact hy
  | succ n ih => intro y hy; rw [List.replicate_succ, coarsePathEndpoint_cons]; exact ih _ (Crs_shift hdiv hy μ s dvd_rfl)

/-- temporal configuration at stride `s`. -/
def IsTemporal (s : ℕ) (V : PeriodicLinkConfiguration SU2 L) (a : ℕ → ℝ) : Prop :=
  ∀ y : PeriodicLatticeSite L, Crs s y → V (y, 0) = cartan (a (y 0).val) ∧ V (y, 1) = 1 ∧ V (y, 2) = 1

/-- angle along a stride-`s` path of a temporal configuration. -/
noncomputable def tAng (s : ℕ) (a : ℕ → ℝ) : PeriodicLatticeSite L → List (Fin 3) → ℝ
  | _, [] => 0
  | y, μ :: rest => (if μ = 0 then a (y 0).val else 0) + tAng s a (coarseShift y s μ) rest

theorem hol_temporal {s : ℕ} (hdiv : ∀ μ, s ∣ L μ + 1) {V : PeriodicLinkConfiguration SU2 L} {a : ℕ → ℝ}
    (hV : IsTemporal s V a) (p : List (Fin 3)) :
    ∀ y : PeriodicLatticeSite L, Crs s y → coarsePathHolonomy s V y p = cartan (tAng s a y p) := by
  induction p with
  | nil => intro y _; rw [coarsePathHolonomy_nil]; exact cartan_zero.symm
  | cons μ rest ih =>
    intro y hy
    rw [coarsePathHolonomy_cons, ih _ (Crs_shift hdiv hy μ s dvd_rfl)]
    obtain ⟨h0, h1, h2⟩ := hV y hy
    simp only [tAng]
    fin_cases μ
    · simp only [Fin.zero_eta, h0, if_true, cartan_mul]
    · simp only [Fin.mk_one, h1, one_mul]; simp
    · simp only [Fin.reduceFinMk, h2, one_mul]; simp

theorem tAng_append (s : ℕ) (a : ℕ → ℝ) (p q : List (Fin 3)) :
    ∀ y : PeriodicLatticeSite L, tAng s a y (p ++ q) = tAng s a y p + tAng s a (coarsePathEndpoint s y p) q := by
  induction p with
  | nil => intro y; simp [tAng, coarsePathEndpoint]
  | cons μ rest ih =>
    intro y
    simp only [List.cons_append, tAng, coarsePathEndpoint_cons, ih]
    ring

theorem tAng_rep_ne (s : ℕ) (a : ℕ → ℝ) (μ : Fin 3) (hμ : μ ≠ 0) (n : ℕ) :
    ∀ y : PeriodicLatticeSite L, tAng s a y (List.replicate n μ) = 0 := by
  induction n with
  | zero => intro y; rfl
  | succ n ih => intro y; simp [List.replicate_succ, tAng, hμ, ih]

/-- `n` steps in direction `0`: `Σ_{j<n} a((y₀ + s j) mod N₀)`. -/
theorem tAng_rep_zero (s : ℕ) (a : ℕ → ℝ) (n : ℕ) :
    ∀ y : PeriodicLatticeSite L, tAng s a y (List.replicate n 0) =
      ∑ j ∈ Finset.range n, a (((y 0).val + s * j) % (L 0 + 1)) := by
  induction n with
  | zero => intro y; simp [tAng]
  | succ n ih =>
    intro y
    rw [List.replicate_succ, tAng, ih, Finset.sum_range_succ' (fun j => a (((y 0).val + s * j) % (L 0 + 1)))]
    simp only [if_true, mul_zero, add_zero, Nat.mod_eq_of_lt (y 0).isLt]
    have h : ∀ j, a ((((coarseShift y s 0) 0).val + s * j) % (L 0 + 1)) = a (((y 0).val + s * (j + 1)) % (L 0 + 1)) := by
      intro j
      rw [coarseShift_val_eq, Nat.mod_add_mod]
      congr 2; ring
    simp only [h]
    ring

/-- the staircase (any base `z`) has only `0`-steps contributing, and they occur at `z₀`. -/
theorem tAng_gamma (s : ℕ) (a : ℕ → ℝ) (z y x : PeriodicLatticeSite L) :
    tAng s a z (coarseGammaPath s y x) =
      ∑ j ∈ Finset.range (((x 0 - (Function.update (Function.update y 2 (x 2)) 1 (x 1)) 0).val) / s),
        a (((z 0).val + s * j) % (L 0 + 1)) := by
  unfold coarseGammaPath coarseStraightSegment coarseCoordSteps
  rw [tAng_append, tAng_rep_ne s a 2 (by decide), tAng_append, tAng_rep_ne s a 1 (by decide)]
  simp only [zero_add]
  rw [tAng_rep_zero]
  have h1 : ∀ n1 n2 : ℕ, (coarsePathEndpoint s (coarsePathEndpoint s z (List.replicate n2 2)) (List.replicate n1 1)) 0 = z 0 := by
    intro n1 n2
    rw [endpoint_rep_ne s 1 0 (by decide), endpoint_rep_ne s 2 0 (by decide)]
  rw [h1]

theorem cartan_comb (a b c d : ℝ) (h : a + b - c - d = 0) :
    cartan a * cartan b * (cartan c)⁻¹ * (cartan d)⁻¹ = 1 := by
  rw [cartan_inv, cartan_inv, cartan_mul, cartan_mul, cartan_mul]
  have : a + b + -c + -d = 0 := by linarith
  rw [this, cartan_zero]

theorem crs_of_mem_block {s ell : ℕ} {y x : PeriodicLatticeSite L} (hy : Crs s y) (hx : x ∈ stepBlockOf y s ell) :
    Crs s x := by
  intro μ
  have h := mem_stepBlockOf.mp hx μ
  have hd : s ∣ (x μ).val - (y μ).val := h.2.2
  have : (x μ).val = (y μ).val + ((x μ).val - (y μ).val) := by have := h.1; omega
  rw [this]
  exact dvd_add (hy μ) hd

/-- the telescoping identity behind `loopVar_temporal` in direction `0`. -/
theorem telescope_loop (a : ℕ → ℝ) (s ell N y0 n0 : ℕ) :
    ∑ j ∈ Finset.range n0, a ((y0 + s * j) % N) + ∑ j ∈ Finset.range ell, a ((y0 + s * n0 + s * j) % N)
      - ∑ j ∈ Finset.range n0, a (((y0 + s * ell) % N + s * j) % N) - ∑ j ∈ Finset.range ell, a ((y0 + s * j) % N) = 0 := by
  have e1 := Finset.sum_range_add (fun i => a ((y0 + s * i) % N)) n0 ell
  have e2 := Finset.sum_range_add (fun i => a ((y0 + s * i) % N)) ell n0
  rw [Nat.add_comm n0 ell] at e1
  have h1 : ∀ j, a ((y0 + s * (n0 + j)) % N) = a ((y0 + s * n0 + s * j) % N) := by
    intro j; congr 2; ring
  have h2 : ∀ j, a ((y0 + s * (ell + j)) % N) = a (((y0 + s * ell) % N + s * j) % N) := by
    intro j; rw [Nat.mod_add_mod]; congr 2; ring
  simp only [h1, h2] at e1 e2
  linarith

theorem n0_eq {s ell : ℕ} {y x : PeriodicLatticeSite L} (hx : x ∈ stepBlockOf y s ell) :
    (x 0).val = (y 0).val + s * ((x 0 - (Function.update (Function.update y 2 (x 2)) 1 (x 1)) 0).val / s) := by
  have e0 : (Function.update (Function.update y 2 (x 2)) 1 (x 1)) 0 = y 0 := by simp [Function.update_of_ne]
  rw [e0]
  have h := mem_stepBlockOf.mp hx 0
  have hle : y 0 ≤ x 0 := by rw [Fin.le_def]; exact h.1
  have hsub : (x 0 - y 0).val = (x 0).val - (y 0).val := (Fin.coe_sub_iff_le.mpr hle)
  rw [hsub, Nat.mul_div_cancel' h.2.2]
  have := h.1; omega

/-- the unwrapped loop angle of a temporal configuration vanishes. -/
theorem tAng_loop_expr {s ell : ℕ} (a : ℕ → ℝ) {y : PeriodicLatticeSite L} (μ : Fin 3) {x : PeriodicLatticeSite L}
    (hx : x ∈ stepBlockOf y s ell) :
    tAng s a y (coarseGammaPath s y x) + tAng s a x (List.replicate ell μ)
      - tAng s a (cPlusS s ell (y, μ)) (coarseGammaPath s y x) - tAng s a y (List.replicate ell μ) = 0 := by
  have hx0 := n0_eq hx
  rw [tAng_gamma, tAng_gamma]
  have key : μ = 0 ∨ μ = 1 ∨ μ = 2 := by fin_cases μ <;> simp
  rcases key with rfl | rfl | rfl
  · rw [tAng_rep_zero, tAng_rep_zero, cPlusS_eq]
    simp only [coarseShift_val_eq]
    set n0 := (x 0 - (Function.update (Function.update y 2 (x 2)) 1 (x 1)) 0).val / s with hn0
    rw [hx0]
    exact telescope_loop a s ell (L 0 + 1) (y 0).val n0
  · rw [tAng_rep_ne s a 1 (by decide), tAng_rep_ne s a 1 (by decide), cPlusS_eq]
    simp only [coarseShift_apply_ne y (s * ell) 1 0 (by decide)]
    ring
  · rw [tAng_rep_ne s a 2 (by decide), tAng_rep_ne s a 2 (by decide), cPlusS_eq]
    simp only [coarseShift_apply_ne y (s * ell) 2 0 (by decide)]
    ring

/-- **every loop of a temporal configuration is trivial.** -/
theorem loopVar_temporal {s ell : ℕ} (hdiv : ∀ μ, s ∣ L μ + 1) {V : PeriodicLinkConfiguration SU2 L} {a : ℕ → ℝ}
    (hV : IsTemporal s V a) {y : PeriodicLatticeSite L} (hy : Crs s y) (μ : Fin 3) {x : PeriodicLatticeSite L}
    (hx : x ∈ stepBlockOf y s ell) : loopVar s ell V (y, μ) x = 1 := by
  have hxc : Crs s x := crs_of_mem_block hy hx
  have hcp : Crs s (cPlusS s ell (y, μ)) := by
    rw [cPlusS_eq]; exact Crs_shift hdiv hy μ _ (dvd_mul_right s ell)
  unfold loopVar gammaVarStrided coarseBondVar
  simp only []
  rw [hol_temporal hdiv hV _ y hy, hol_temporal hdiv hV _ x hxc, hol_temporal hdiv hV _ _ hcp, hol_temporal hdiv hV _ y hy]
  exact cartan_comb _ _ _ _ (tAng_loop_expr a μ hx)

/-- **blocking a temporal configuration gives a temporal configuration** at stride `s * ell`, with
`a'(v) = Σ_{j<ell} a((v + s j) mod N₀)`. -/
theorem blocked_temporal {s ell : ℕ} (hdiv : ∀ μ, s ∣ L μ + 1) {V : PeriodicLinkConfiguration SU2 L} {a : ℕ → ℝ}
    (hV : IsTemporal s V a) :
    IsTemporal (s * ell) (stridedBlockedGauge su2LogExp s ell V)
      (fun v => ∑ j ∈ Finset.range ell, a ((v + s * j) % (L 0 + 1))) := by
  intro y hy'
  have hy : Crs s y := fun μ => dvd_trans (dvd_mul_right s ell) (hy' μ)
  have hloop : ∀ μ : Fin 3, ∀ x ∈ stepBlockOf (y, μ).1 s ell, loopVar s ell V (y, μ) x = cartan 0 ∧ |(0 : ℝ)| < Real.pi := by
    intro μ x hx
    exact ⟨by rw [loopVar_temporal hdiv hV hy μ hx, cartan_zero], by rw [abs_zero]; exact Real.pi_pos⟩
  have hcb : ∀ μ : Fin 3, coarseBondVar s ell V (y, μ) = cartan (tAng s a y (List.replicate ell μ)) := by
    intro μ; unfold coarseBondVar; exact hol_temporal hdiv hV _ y hy
  have key : ∀ μ : Fin 3, stridedBlockedGauge su2LogExp s ell V (y, μ) = cartan (tAng s a y (List.replicate ell μ)) := by
    intro μ
    have := blocked_cartan s ell V (y, μ) (fun _ => 0) _ (hloop μ) (hcb μ)
    simpa using this
  refine ⟨?_, ?_, ?_⟩
  · rw [key 0, tAng_rep_zero]
  · rw [key 1, tAng_rep_ne s a 1 (by decide), cartan_zero]
  · rw [key 2, tAng_rep_ne s a 2 (by decide), cartan_zero]

#print axioms Crs_shift
#print axioms hol_temporal
#print axioms tAng_gamma
#print axioms tAng_loop_expr
#print axioms loopVar_temporal
#print axioms blocked_temporal

end AdalyFormal.CoverOmega
