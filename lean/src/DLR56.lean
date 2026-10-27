import DLR55
import GCb7

/-!
# DL56 -- the source `J` at a site from a LOCAL exponential representation `U = e^{iηA}` (the cube gauge of (3.35)-(3.36))

Given `V(e) = exp(iη A(e))` on a set `InC` of bonds containing the seven bonds per direction that `J(x,μ)` reads, with
`A(e)` Hermitian traceless, `‖A(e)‖ ≤ a₁` (clause 1), `‖η⁻¹(A(z+ν',d) − A(z,d))‖ ≤ a₂` for `(z,d),(z+ν',d) ∈ InC` (clause 2),
`‖∂^{η*}∂^η A(x,μ)‖ ≤ a₃` (clause 3, `ddA`), and `4ηa₁ ≤ 1`:
* `F_expand` : `F_{νμ}(y) = η² curlA(y;ν,μ) + Kpl(y) + R`, `‖R‖ ≤ 1024 η³a₁³` (`Kpl` = oriented commutator term);
* **`J_local_bound`** : `‖Jfield V x μ‖ ≤ η³ (a₃ + 40 a₁a₂ + 4144 a₁³ + 8192 η a₁⁴)`.
The leading term is exactly `η³ ∂^{η*}∂^η A` (the second difference of the plaquette curls); the commutator terms enter only
through their DIFFERENCES (gradient clause), the cubic remainders and the transport through `a₁`.
-/
set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 20000

namespace AdalyFormal.DLayer

open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.RMapLipschitz (frobSq frobNorm frobSq_nonneg frobNorm_nonneg frobNorm_sq)
open AdalyFormal.Balaban.SourceJ (piProj FnuMu DstarDir Jfield)
open AdalyFormal.Balaban.DeltaPrime (imHolonomy holonomyElem holonomyElemInv)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack)
open AdalyFormal.Balaban.CovariantOperators (conjByAmbient)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 coe_inv)
open AdalyFormal.StatementLane2 (curlA ddA)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

local notation "Mt" => Matrix (Fin 2) (Fin 2) ℂ

variable {L : PeriodicLatticeExtent}

/-! ## site and holonomy algebra -/

theorem shift_comm (y : PeriodicLatticeSite L) (a b : Fin 3) :
    periodicLatticeShift (periodicLatticeShift y a) b = periodicLatticeShift (periodicLatticeShift y b) a := by
  by_cases hab : a = b
  · subst hab; rfl
  · funext c
    unfold periodicLatticeShift
    by_cases hca : c = a
    · subst hca
      rw [Function.update_of_ne hab, Function.update_self, Function.update_self, Function.update_of_ne hab]
    · by_cases hcb : c = b
      · subst hcb
        rw [Function.update_self, Function.update_of_ne (Ne.symm hab), Function.update_of_ne (Ne.symm hab),
          Function.update_self]
      · rw [Function.update_of_ne hcb, Function.update_of_ne hca, Function.update_of_ne hca, Function.update_of_ne hcb]

theorem imHol_eq (U : PeriodicLinkConfiguration SU2 L) (p : PeriodicLatticePlaquette L) :
    imHolonomy U p = imP ((holonomyElem U p : SU2) : Mt) := by
  unfold imHolonomy imP holonomyElemInv
  rw [coe_inv]

theorem hol_coe (U : PeriodicLinkConfiguration SU2 L) (y : PeriodicLatticeSite L) (a b : Fin 3) (h : a < b) :
    ((holonomyElem U (y, ⟨(a, b), h⟩) : SU2) : Mt)
      = ((U (y, a) : SU2) : Mt) * ((U (periodicLatticeShift y a, b) : SU2) : Mt)
        * ((U (periodicLatticeShift y b, a) : SU2) : Mt)ᴴ * ((U (y, b) : SU2) : Mt)ᴴ := by
  unfold holonomyElem periodicPlaquetteHolonomy
  simp only [Submonoid.coe_mul, Subgroup.coe_toSubmonoid]
  rw [coe_inv, coe_inv]

theorem HT_AHT (η : ℝ) (A : Mt) (hA : Aᴴ = A ∧ Matrix.trace A = 0) : AHT (((η : ℂ) * Complex.I) • A) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_smul, hA.1]
    have : star ((η : ℂ) * Complex.I) = -((η : ℂ) * Complex.I) := by
      simp [Complex.conj_ofReal]
    rw [this, neg_smul]
  · rw [Matrix.trace_smul, hA.2, smul_zero]

theorem fN_H (η : ℝ) (hη : 0 ≤ η) (A : Mt) : frobNorm (((η : ℂ) * Complex.I) • A) = η * frobNorm A := by
  rw [fN_csmul]
  congr 1
  simp [abs_of_nonneg hη]

/-! ## commutator algebra -/

theorem comm_diff (a b a' b' : Mt) :
    frobNorm ((a' * b' - b' * a') - (a * b - b * a))
      ≤ 2 * frobNorm (a' - a) * frobNorm b' + 2 * frobNorm a * frobNorm (b' - b) := by
  have e : (a' * b' - b' * a') - (a * b - b * a)
      = ((a' - a) * b' - b' * (a' - a)) + (a * (b' - b) - (b' - b) * a) := by noncomm_ring
  rw [e]
  refine (fN_add _ _).trans ?_
  have h1 : frobNorm ((a' - a) * b' - b' * (a' - a)) ≤ 2 * frobNorm (a' - a) * frobNorm b' := by
    refine (fN_sub _ _).trans ?_
    have := fN_mul (a' - a) b'
    have := fN_mul b' (a' - a)
    linarith
  have h2 : frobNorm (a * (b' - b) - (b' - b) * a) ≤ 2 * frobNorm a * frobNorm (b' - b) := by
    refine (fN_sub _ _).trans ?_
    have := fN_mul a (b' - b)
    have := fN_mul (b' - b) a
    linarith
  linarith

theorem comm_le (a b : Mt) : frobNorm (a * b - b * a) ≤ 2 * frobNorm a * frobNorm b := by
  refine (fN_sub _ _).trans ?_
  have := fN_mul a b
  have := fN_mul b a
  linarith

theorem Kc_le (a1 a2 a3 a4 : Mt) (m : ℝ) (h1 : frobNorm a1 ≤ m) (h2 : frobNorm a2 ≤ m) (h3 : frobNorm a3 ≤ m)
    (h4 : frobNorm a4 ≤ m) : frobNorm (Kc a1 a2 a3 a4) ≤ 12 * m ^ 2 := by
  unfold Kc
  have hm : 0 ≤ m := le_trans (frobNorm_nonneg _) h1
  have c12 := comm_le a1 a2
  have c13 := comm_le a1 a3
  have c14 := comm_le a1 a4
  have c23 := comm_le a2 a3
  have c24 := comm_le a2 a4
  have c34 := comm_le a3 a4
  have p : ∀ x y : Mt, frobNorm x ≤ m → frobNorm y ≤ m → 2 * frobNorm x * frobNorm y ≤ 2 * m ^ 2 := by
    intro x y hx hy
    have := mul_le_mul hx hy (frobNorm_nonneg _) hm
    nlinarith
  refine (fN_add _ _).trans ?_
  refine (add_le_add (fN_add _ _) le_rfl).trans ?_
  refine (add_le_add (add_le_add (fN_add _ _) le_rfl) le_rfl).trans ?_
  refine (add_le_add (add_le_add (add_le_add (fN_add _ _) le_rfl) le_rfl) le_rfl).trans ?_
  refine (add_le_add (add_le_add (add_le_add (add_le_add (fN_add _ _) le_rfl) le_rfl) le_rfl) le_rfl).trans ?_
  linarith [c12.trans (p a1 a2 h1 h2), c13.trans (p a1 a3 h1 h3), c14.trans (p a1 a4 h1 h4),
    c23.trans (p a2 a3 h2 h3), c24.trans (p a2 a4 h2 h4), c34.trans (p a3 a4 h3 h4)]

theorem Kc_diff (a1 a2 a3 a4 b1 b2 b3 b4 : Mt) (m δ : ℝ)
    (ha1 : frobNorm a1 ≤ m) (ha2 : frobNorm a2 ≤ m) (ha3 : frobNorm a3 ≤ m) (ha4 : frobNorm a4 ≤ m)
    (hb1 : frobNorm b1 ≤ m) (hb2 : frobNorm b2 ≤ m) (hb3 : frobNorm b3 ≤ m) (hb4 : frobNorm b4 ≤ m)
    (d1 : frobNorm (a1 - b1) ≤ δ) (d2 : frobNorm (a2 - b2) ≤ δ) (d3 : frobNorm (a3 - b3) ≤ δ)
    (d4 : frobNorm (a4 - b4) ≤ δ) :
    frobNorm (Kc a1 a2 a3 a4 - Kc b1 b2 b3 b4) ≤ 24 * m * δ := by
  have hm : 0 ≤ m := le_trans (frobNorm_nonneg _) ha1
  have hδ : 0 ≤ δ := le_trans (frobNorm_nonneg _) d1
  have q : ∀ x y x' y' : Mt, frobNorm x' ≤ m → frobNorm y' ≤ m → frobNorm x ≤ m → frobNorm y ≤ m →
      frobNorm (x' - x) ≤ δ → frobNorm (y' - y) ≤ δ →
      frobNorm ((x' * y' - y' * x') - (x * y - y * x)) ≤ 4 * m * δ := by
    intro x y x' y' hx' hy' hx hy hdx hdy
    refine (comm_diff x y x' y').trans ?_
    have t1 := mul_le_mul hdx hy' (frobNorm_nonneg _) hδ
    have t2 := mul_le_mul hx hdy (frobNorm_nonneg _) hm
    nlinarith
  have e : Kc a1 a2 a3 a4 - Kc b1 b2 b3 b4
      = ((a1 * a2 - a2 * a1) - (b1 * b2 - b2 * b1)) + ((a1 * a3 - a3 * a1) - (b1 * b3 - b3 * b1))
        + ((a1 * a4 - a4 * a1) - (b1 * b4 - b4 * b1)) + ((a2 * a3 - a3 * a2) - (b2 * b3 - b3 * b2))
        + ((a2 * a4 - a4 * a2) - (b2 * b4 - b4 * b2)) + ((a3 * a4 - a4 * a3) - (b3 * b4 - b4 * b3)) := by
    unfold Kc; abel
  rw [e]
  have r12 := q b1 b2 a1 a2 ha1 ha2 hb1 hb2 d1 d2
  have r13 := q b1 b3 a1 a3 ha1 ha3 hb1 hb3 d1 d3
  have r14 := q b1 b4 a1 a4 ha1 ha4 hb1 hb4 d1 d4
  have r23 := q b2 b3 a2 a3 ha2 ha3 hb2 hb3 d2 d3
  have r24 := q b2 b4 a2 a4 ha2 ha4 hb2 hb4 d2 d4
  have r34 := q b3 b4 a3 a4 ha3 ha4 hb3 hb4 d3 d4
  refine (fN_add _ _).trans ?_
  refine (add_le_add (fN_add _ _) le_rfl).trans ?_
  refine (add_le_add (add_le_add (fN_add _ _) le_rfl) le_rfl).trans ?_
  refine (add_le_add (add_le_add (add_le_add (fN_add _ _) le_rfl) le_rfl) le_rfl).trans ?_
  refine (add_le_add (add_le_add (add_le_add (add_le_add (fN_add _ _) le_rfl) le_rfl) le_rfl) le_rfl).trans ?_
  linarith

/-! ## the plaquette function `F_{νμ}` -/

/-- the oriented second-order term of `F_{νμ}(y)` (`H e = iη A e`) -/
noncomputable def Kpl (H : Bond L → Mt) (ν μ : Fin 3) (y : PeriodicLatticeSite L) : Mt :=
  if ν < μ then (1 / (2 * Complex.I) : ℂ) • Kc (H (y, ν)) (H (periodicLatticeShift y ν, μ))
      (-H (periodicLatticeShift y μ, ν)) (-H (y, μ))
  else -((1 / (2 * Complex.I) : ℂ) • Kc (H (y, μ)) (H (periodicLatticeShift y μ, ν))
      (-H (periodicLatticeShift y ν, μ)) (-H (y, ν)))

section Local
variable (V : PeriodicLinkConfiguration SU2 L) (η : ℝ) (A : Bond L → Mt) (a1 a2 : ℝ) (InC : Bond L → Prop)

/-- the hypotheses of the local representation -/
structure LocRep : Prop where
  hη : 0 < η
  rep : ∀ e, InC e → ((V e : SU2) : Mt) = NormedSpace.exp (((η : ℂ) * Complex.I) • A e)
  ht : ∀ e, InC e → (A e)ᴴ = A e ∧ Matrix.trace (A e) = 0
  h1 : ∀ e, InC e → frobNorm (A e) ≤ a1
  h2 : ∀ z d d', InC (z, d) → InC (periodicLatticeShift z d', d) →
    frobNorm ((η⁻¹ : ℝ) • (A (periodicLatticeShift z d', d) - A (z, d))) ≤ a2
  small : 4 * η * a1 ≤ 1

variable {V η A a1 a2 InC}

theorem LocRep.a1_nonneg (h : LocRep V η A a1 a2 InC) (e : Bond L) (he : InC e) : 0 ≤ a1 :=
  le_trans (frobNorm_nonneg _) (h.h1 e he)

/-- the `H`-field `iηA` -/
noncomputable def Hof (η : ℝ) (A : Bond L → Mt) : Bond L → Mt := fun e => ((η : ℂ) * Complex.I) • A e

theorem LocRep.H_le (h : LocRep V η A a1 a2 InC) (e : Bond L) (he : InC e) : frobNorm (Hof η A e) ≤ η * a1 := by
  unfold Hof; rw [fN_H η h.hη.le]; exact mul_le_mul_of_nonneg_left (h.h1 e he) h.hη.le

theorem LocRep.H_diff (h : LocRep V η A a1 a2 InC) (z : PeriodicLatticeSite L) (d d' : Fin 3)
    (h0 : InC (z, d)) (h1 : InC (periodicLatticeShift z d', d)) :
    frobNorm (Hof η A (z, d) - Hof η A (periodicLatticeShift z d', d)) ≤ η ^ 2 * a2 := by
  unfold Hof
  rw [← smul_sub, fN_H η h.hη.le]
  have e : A (z, d) - A (periodicLatticeShift z d', d)
      = (-η : ℝ) • ((η⁻¹ : ℝ) • (A (periodicLatticeShift z d', d) - A (z, d))) := by
    rw [smul_smul, show (-η) * η⁻¹ = -1 by field_simp [h.hη.ne']]; simp
  rw [e, fN_rsmul, abs_neg, abs_of_pos h.hη]
  have := h.h2 z d d' h0 h1
  have hη := h.hη
  nlinarith

theorem LocRep.curl_le (h : LocRep V η A a1 a2 InC) (y : PeriodicLatticeSite L) (ν μ : Fin 3)
    (b1 : InC (y, ν)) (b2 : InC (periodicLatticeShift y ν, μ)) (b3 : InC (periodicLatticeShift y μ, ν))
    (b4 : InC (y, μ)) : frobNorm (curlA η A y ν μ) ≤ 2 * a2 := by
  unfold curlA
  have e : (η⁻¹ : ℝ) • (A (periodicLatticeShift y ν, μ) - A (y, μ) - A (periodicLatticeShift y μ, ν) + A (y, ν))
      = (η⁻¹ : ℝ) • (A (periodicLatticeShift y ν, μ) - A (y, μ))
        - (η⁻¹ : ℝ) • (A (periodicLatticeShift y μ, ν) - A (y, ν)) := by
    rw [← smul_sub]; congr 1; abel
  rw [e]
  refine (fN_sub _ _).trans ?_
  have := h.h2 y μ ν b4 b2
  have := h.h2 y ν μ b1 b3
  linarith

/-- **the expansion of `F_{νμ}(y)`** -/
theorem LocRep.F_expand (h : LocRep V η A a1 a2 InC) (ν μ : Fin 3) (hνμ : ν ≠ μ) (y : PeriodicLatticeSite L)
    (b1 : InC (y, ν)) (b2 : InC (periodicLatticeShift y ν, μ)) (b3 : InC (periodicLatticeShift y μ, ν))
    (b4 : InC (y, μ)) :
    ∃ R : Mt, FnuMu V ν μ y = (η ^ 2 : ℝ) • curlA η A y ν μ + Kpl (Hof η A) ν μ y + R
      ∧ frobNorm R ≤ 1024 * η ^ 3 * a1 ^ 3 := by
  have hη := h.hη
  have ha1 := h.a1_nonneg _ b1
  have hH : ∀ e, InC e → AHT (Hof η A e) := fun e he => HT_AHT η (A e) (h.ht e he)
  have hHle : ∀ e, InC e → frobNorm (Hof η A e) ≤ η * a1 := fun e he => h.H_le e he
  have hsig : ∀ (e1 e2 e3 e4 : Bond L), InC e1 → InC e2 → InC e3 → InC e4 →
      frobNorm (Hof η A e1) + frobNorm (Hof η A e2) + frobNorm (-Hof η A e3) + frobNorm (-Hof η A e4) ≤ 4 * (η * a1) := by
    intro e1 e2 e3 e4 h1 h2 h3 h4
    rw [fN_neg, fN_neg]
    linarith [hHle e1 h1, hHle e2 h2, hHle e3 h3, hHle e4 h4]
  have hcube : ∀ σ : ℝ, 0 ≤ σ → σ ≤ 4 * (η * a1) → 16 * σ ^ 3 ≤ 1024 * η ^ 3 * a1 ^ 3 := by
    intro σ h0 h1
    have := pow_le_pow_left₀ h0 h1 3
    nlinarith
  have hrep_inv : ∀ e, InC e → ((V e : SU2) : Mt)ᴴ = NormedSpace.exp (-Hof η A e) := by
    intro e he
    rw [h.rep e he]
    exact exp_conjT _ (hH e he)
  -- the main term identity
  have hmain : ∀ (X1 X2 X3 X4 : Mt), (1 / (2 * Complex.I) : ℂ) • ((2 : ℂ) • (((η : ℂ) * Complex.I) • X1
      + ((η : ℂ) * Complex.I) • X2 + -(((η : ℂ) * Complex.I) • X3) + -(((η : ℂ) * Complex.I) • X4)))
      = (η : ℂ) • (X1 + X2 - X3 - X4) := by
    intro X1 X2 X3 X4
    rw [smul_smul, smul_add, smul_add, smul_add, smul_neg, smul_neg, smul_smul, smul_smul, smul_smul, smul_smul]
    have hc : 1 / (2 * Complex.I) * 2 * ((η : ℂ) * Complex.I) = (η : ℂ) := by
      field_simp
    rw [hc]
    module
  have hcurl : ∀ (X : Mt), (η ^ 2 : ℝ) • ((η⁻¹ : ℝ) • X) = (η : ℂ) • X := by
    intro X
    rw [smul_smul, show η ^ 2 * η⁻¹ = η by field_simp]
    ext i j; simp
  rcases lt_or_gt_of_ne hνμ with hlt | hgt
  · -- ν < μ
    obtain ⟨Rp, hRp, hRb⟩ := plaq_expand (Hof η A (y, ν)) (Hof η A (periodicLatticeShift y ν, μ))
      (-Hof η A (periodicLatticeShift y μ, ν)) (-Hof η A (y, μ)) (hH _ b1) (hH _ b2) (hH _ b3).neg (hH _ b4).neg
      (by have := hsig _ _ _ _ b1 b2 b3 b4; linarith [h.small])
    refine ⟨Rp, ?_, ?_⟩
    · have hF : FnuMu V ν μ y = piProj (imHolonomy V (y, ⟨(ν, μ), hlt⟩)) := by
        unfold FnuMu; rw [dif_pos hlt]
      rw [hF, imHol_eq, hol_coe, h.rep _ b1, h.rep _ b2, hrep_inv _ b3, hrep_inv _ b4]
      change piProj (imP (NormedSpace.exp (Hof η A (y, ν)) * NormedSpace.exp (Hof η A (periodicLatticeShift y ν, μ))
        * NormedSpace.exp (-Hof η A (periodicLatticeShift y μ, ν)) * NormedSpace.exp (-Hof η A (y, μ)))) = _
      rw [hRp]
      unfold Kpl
      rw [if_pos hlt]
      congr 2
      unfold S4 Hof curlA
      rw [hmain, hcurl]
      congr 1; abel
    · refine (hRb).trans ?_
      have := hsig _ _ _ _ b1 b2 b3 b4
      exact hcube _ (add_nonneg (add_nonneg (add_nonneg (frobNorm_nonneg _) (frobNorm_nonneg _)) (frobNorm_nonneg _)) (frobNorm_nonneg _)) this
  · -- μ < ν
    obtain ⟨Rp, hRp, hRb⟩ := plaq_expand (Hof η A (y, μ)) (Hof η A (periodicLatticeShift y μ, ν))
      (-Hof η A (periodicLatticeShift y ν, μ)) (-Hof η A (y, ν)) (hH _ b4) (hH _ b3) (hH _ b2).neg (hH _ b1).neg
      (by have := hsig _ _ _ _ b4 b3 b2 b1; linarith [h.small])
    refine ⟨-Rp, ?_, ?_⟩
    · have hF : FnuMu V ν μ y = -piProj (imHolonomy V (y, ⟨(μ, ν), hgt⟩)) := by
        unfold FnuMu; rw [dif_neg (not_lt.mpr hgt.le), dif_pos hgt]
      rw [hF, imHol_eq, hol_coe, h.rep _ b4, h.rep _ b3, hrep_inv _ b2, hrep_inv _ b1]
      change -piProj (imP (NormedSpace.exp (Hof η A (y, μ)) * NormedSpace.exp (Hof η A (periodicLatticeShift y μ, ν))
        * NormedSpace.exp (-Hof η A (periodicLatticeShift y ν, μ)) * NormedSpace.exp (-Hof η A (y, ν)))) = _
      rw [hRp]
      unfold Kpl
      rw [if_neg (not_lt.mpr hgt.le)]
      unfold S4 Hof curlA
      rw [hmain, hcurl]
      have e : (η : ℂ) • (A (y, ν) + A (periodicLatticeShift y ν, μ) - A (periodicLatticeShift y μ, ν) - A (y, μ))
          = -((η : ℂ) • (A (y, μ) + A (periodicLatticeShift y μ, ν) - A (periodicLatticeShift y ν, μ) - A (y, ν))) := by
        rw [← smul_neg]; congr 1; abel
      have e2 : A (periodicLatticeShift y ν, μ) - A (y, μ) - A (periodicLatticeShift y μ, ν) + A (y, ν)
          = A (y, ν) + A (periodicLatticeShift y ν, μ) - A (periodicLatticeShift y μ, ν) - A (y, μ) := by abel
      rw [e2, e]
      abel
    · rw [fN_neg]
      refine (hRb).trans ?_
      have := hsig _ _ _ _ b4 b3 b2 b1
      exact hcube _ (add_nonneg (add_nonneg (add_nonneg (frobNorm_nonneg _) (frobNorm_nonneg _)) (frobNorm_nonneg _)) (frobNorm_nonneg _)) this

theorem LocRep.Kpl_le (h : LocRep V η A a1 a2 InC) (ν μ : Fin 3) (y : PeriodicLatticeSite L)
    (b1 : InC (y, ν)) (b2 : InC (periodicLatticeShift y ν, μ)) (b3 : InC (periodicLatticeShift y μ, ν))
    (b4 : InC (y, μ)) : frobNorm (Kpl (Hof η A) ν μ y) ≤ 6 * (η * a1) ^ 2 := by
  have hHle : ∀ e, InC e → frobNorm (Hof η A e) ≤ η * a1 := fun e he => h.H_le e he
  have hneg : ∀ e, InC e → frobNorm (-Hof η A e) ≤ η * a1 := fun e he => by rw [fN_neg]; exact hHle e he
  have hhalf : ‖(1 / (2 * Complex.I) : ℂ)‖ = 1 / 2 := by simp
  unfold Kpl
  split_ifs
  · rw [fN_csmul, hhalf]
    have := Kc_le _ _ _ _ (η * a1) (hHle _ b1) (hHle _ b2) (hneg _ b3) (hneg _ b4)
    linarith
  · rw [fN_neg, fN_csmul, hhalf]
    have := Kc_le _ _ _ _ (η * a1) (hHle _ b4) (hHle _ b3) (hneg _ b2) (hneg _ b1)
    linarith

end Local

#print axioms shift_comm
#print axioms imHol_eq
#print axioms hol_coe
#print axioms comm_diff
#print axioms Kc_le
#print axioms Kc_diff
#print axioms LocRep.H_diff
#print axioms LocRep.curl_le
#print axioms LocRep.F_expand
#print axioms LocRep.Kpl_le

end AdalyFormal.DLayer
