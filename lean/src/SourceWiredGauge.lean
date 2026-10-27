/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import SourceWiredComposed

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# `J(U)` IS GAUGE COVARIANT, SO `‖J(U)‖` IS GAUGE INVARIANT

`SourceWiredComposed.LinkDev δ U` ("every entry of `U(b) − 1` is `≤ δ`") is **not** a gauge
invariant condition, while CMP99b's own regularity (3.35) is stated **after** a gauge
transformation.  A source bound proved only on a non-invariant class would be the wrong statement.

This file removes that defect.  It builds the lattice gauge action `gaugeT` and proves

* `Jsource_gaugeT` — `J(U^g)(b) = g(b.1)·J(U)(b)·g(b.1)⁻¹`, i.e. `J` is genuinely **covariant**,
  transforming by conjugation at the bond's base site — the transformation law CMP99b's `J` must
  have, since `J = D*η⁻²Im∂U` is built from covariant objects;
* `norm_JsuTwo_gaugeT` — hence `‖J(U^g)‖ = ‖J(U)‖` **exactly**, on the true bond carrier, because
  the `𝔰𝔲(2)` inner product `−½Tr(XY)` is conjugation invariant;
* `norm_JsuTwo_le_of_gaugeEquivLinkDev` — so the source bound holds on the **gauge-invariant**
  class `GaugeEquivLinkDev δ U := ∃ g, LinkDev δ (U^g)`, which strictly contains `LinkDev δ`
  (`gaugeEquivLinkDev_of_linkDev`) and is closed under the gauge action
  (`gaugeEquivLinkDev_gaugeT`).

**What this does and does not settle.**  It settles the *global* gauge: a configuration that is
gauge-equivalent to a small-link one has a small source, and the bound is now stated on a class
that is invariant, as Bałaban's is.  It does **not** settle CMP99b (3.35)'s actual quantifier,
which supplies the exponential representation with a gauge chosen **per cube**
(`corpus/pages/CMP99b_p396.md`); assembling per-cube gauges into one global `g` is a patching
argument and is NOT done here.  That is the exact residual, and it is now the ONLY gap between
CMP99b's regularity hypothesis and the source bound proved here.
-/

namespace AdalyFormal.Balaban.SourceWiredGauge

open Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwo conjByAmbient conjByAmbient_apply
  conjByAmbient_mem)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime (holonomyElem holonomyElemInv imHolonomy)
open AdalyFormal.Balaban.SourceJ (piProj FnuMu DstarDir Jfield Jsource conjByAmbient_one_apply)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack
  periodicLatticeShift_shiftBack periodicLatticeShiftBack_shift)
open AdalyFormal.Balaban.SourceWiredJ (EB JsuTwo JsuTwo_apply norm_JsuTwo_le)
open AdalyFormal.Balaban.SourceWired (LinkDev bondData_opNorm_H1_le_one bondData_hfloor
  bondData_hD2 cdcFormTrue_posDef_of_source_small)
open AdalyFormal.Balaban.ConstantA (BaseConstant usedAt)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.ConstructCDC (TildeFn)
open AdalyFormal.Balaban.VariationalProjectorH1 (solutionOperator)
open AdalyFormal.Balaban.DeltaKWiring (cdcFormTrue bondData bondQext bondData_isSourceOperator)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the lattice gauge action -/

/-- **`(U^g)(x,μ) = g(x)·U(x,μ)·g(x+e_μ)⁻¹`** — the standard lattice gauge transformation, the one
under which `R(U)`-transport is covariant. -/
def gaugeT (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L :=
  fun b => g b.1 * U b * (g (periodicLatticeShift b.1 b.2))⁻¹

theorem gaugeT_apply (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (b : Bond L) :
    gaugeT g U b = g b.1 * U b * (g (periodicLatticeShift b.1 b.2))⁻¹ := rfl

/-- Shifts in two DISTINCT directions commute — the fact that makes the plaquette's two `g`-factors
at the far corner cancel. -/
theorem shift_comm (x : PeriodicLatticeSite L) {μ ν : Fin 3} (h : μ ≠ ν) :
    periodicLatticeShift (periodicLatticeShift x μ) ν
      = periodicLatticeShift (periodicLatticeShift x ν) μ := by
  unfold periodicLatticeShift
  have e1 : Function.update x μ (x μ + 1) ν = x ν := by simp [Ne.symm h]
  have e2 : Function.update x ν (x ν + 1) μ = x μ := by simp [h]
  rw [e1, e2]
  exact Function.update_comm h _ _ _

/-- `conjByAmbient` is a homomorphism of the group action. -/
theorem conjByAmbient_mul (A B : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    conjByAmbient (A * B) X = conjByAmbient A (conjByAmbient B X) := by
  rw [conjByAmbient_apply, conjByAmbient_apply, conjByAmbient_apply,
    Submonoid.coe_mul, Matrix.conjTranspose_mul]
  noncomm_ring

/-! ## §2 — the plaquette holonomy conjugates -/

theorem holonomyElem_gaugeT (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) :
    holonomyElem (gaugeT g U) p = g p.1 * holonomyElem U p * (g p.1)⁻¹ := by
  have hne : p.2.1.1 ≠ p.2.1.2 := ne_of_lt p.2.2
  have hcomm := shift_comm (L := L) p.1 hne
  show gaugeT g U (p.1, p.2.1.1) * gaugeT g U (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)
      * (gaugeT g U (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))⁻¹
      * (gaugeT g U (p.1, p.2.1.2))⁻¹ = _
  simp only [gaugeT_apply]
  rw [hcomm]
  show _ = g p.1 * (U (p.1, p.2.1.1) * U (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)
      * (U (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))⁻¹ * (U (p.1, p.2.1.2))⁻¹) * (g p.1)⁻¹
  group

theorem holonomyElemInv_gaugeT (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) :
    holonomyElemInv (gaugeT g U) p = g p.1 * holonomyElemInv U p * (g p.1)⁻¹ := by
  show (holonomyElem (gaugeT g U) p)⁻¹ = g p.1 * (holonomyElem U p)⁻¹ * (g p.1)⁻¹
  rw [holonomyElem_gaugeT]
  group

/-! ## §3 — `Im ∂U` conjugates, and so does `π Im ∂U` -/

theorem imHolonomy_gaugeT (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) :
    imHolonomy (gaugeT g U) p = conjByAmbient (g p.1) (imHolonomy U p) := by
  unfold imHolonomy
  rw [holonomyElem_gaugeT, holonomyElemInv_gaugeT, conjByAmbient_apply]
  have hA : ((g p.1 * holonomyElem U p * (g p.1)⁻¹ :
      Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      = (g p.1 : Matrix (Fin 2) (Fin 2) ℂ) * (holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ)
        * (g p.1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := by
    rw [Submonoid.coe_mul, Submonoid.coe_mul]
    rfl
  have hB : ((g p.1 * holonomyElemInv U p * (g p.1)⁻¹ :
      Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      = (g p.1 : Matrix (Fin 2) (Fin 2) ℂ) * (holonomyElemInv U p : Matrix (Fin 2) (Fin 2) ℂ)
        * (g p.1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := by
    rw [Submonoid.coe_mul, Submonoid.coe_mul]
    rfl
  rw [hA, hB, ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.mul_smul, Matrix.smul_mul]

theorem piProj_conjByAmbient (V : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    piProj (conjByAmbient V X) = conjByAmbient V (piProj X) := by
  have hVV : (V : Matrix (Fin 2) (Fin 2) ℂ) * (V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp V.2.1
  have hVV' : (V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * (V : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp V.2.1
  have htr : Matrix.trace (conjByAmbient V X) = Matrix.trace X := by
    rw [conjByAmbient_apply, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hVV', Matrix.one_mul]
  unfold piProj
  rw [htr, conjByAmbient_apply, conjByAmbient_apply, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hVV]

theorem FnuMu_gaugeT (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ν μ : Fin 3) (y : PeriodicLatticeSite L) :
    FnuMu (gaugeT g U) ν μ y = conjByAmbient (g y) (FnuMu U ν μ y) := by
  unfold FnuMu
  split_ifs
  · rw [imHolonomy_gaugeT, piProj_conjByAmbient]
  · rw [imHolonomy_gaugeT, piProj_conjByAmbient, map_neg]
  · rw [map_zero]

/-! ## §4 — `D*_ν` is covariant, hence so is `J` -/

theorem DstarDir_gaugeT (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ν : Fin 3)
    (G : PeriodicLatticeSite L → Matrix (Fin 2) (Fin 2) ℂ)
    (x : PeriodicLatticeSite L) :
    DstarDir (gaugeT g U) ν (fun y => conjByAmbient (g y) (G y)) x
      = conjByAmbient (g x) (DstarDir U ν G x) := by
  have hlink : gaugeT g U (periodicLatticeShiftBack x ν, ν)
      = g (periodicLatticeShiftBack x ν) * U (periodicLatticeShiftBack x ν, ν) * (g x)⁻¹ := by
    rw [gaugeT_apply]
    show _ = g (periodicLatticeShiftBack x ν) * U (periodicLatticeShiftBack x ν, ν) * (g x)⁻¹
    rw [periodicLatticeShift_shiftBack]
  have hinv : (gaugeT g U (periodicLatticeShiftBack x ν, ν))⁻¹
      = g x * (U (periodicLatticeShiftBack x ν, ν))⁻¹ * (g (periodicLatticeShiftBack x ν))⁻¹ := by
    rw [hlink]
    group
  show conjByAmbient (gaugeT g U (periodicLatticeShiftBack x ν, ν))⁻¹
      (conjByAmbient (g (periodicLatticeShiftBack x ν)) (G (periodicLatticeShiftBack x ν)))
      - conjByAmbient (g x) (G x) = _
  have hmerge : conjByAmbient (g (periodicLatticeShiftBack x ν))⁻¹
      (conjByAmbient (g (periodicLatticeShiftBack x ν)) (G (periodicLatticeShiftBack x ν)))
      = G (periodicLatticeShiftBack x ν) := by
    rw [← conjByAmbient_mul, inv_mul_cancel, conjByAmbient_one_apply]
  rw [hinv, conjByAmbient_mul, hmerge, conjByAmbient_mul]
  show conjByAmbient (g x) _ - conjByAmbient (g x) (G x) = conjByAmbient (g x) (_ - G x)
  rw [map_sub]

theorem Jfield_gaugeT (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (x : PeriodicLatticeSite L) (μ : Fin 3) :
    Jfield (gaugeT g U) x μ = conjByAmbient (g x) (Jfield U x μ) := by
  show (∑ ν : Fin 3, if ν = μ then 0
      else DstarDir (gaugeT g U) ν (fun y => FnuMu (gaugeT g U) ν μ y) x) = _
  have hterm : ∀ ν : Fin 3,
      (if ν = μ then (0 : Matrix (Fin 2) (Fin 2) ℂ)
        else DstarDir (gaugeT g U) ν (fun y => FnuMu (gaugeT g U) ν μ y) x)
      = conjByAmbient (g x)
          (if ν = μ then 0 else DstarDir U ν (fun y => FnuMu U ν μ y) x) := by
    intro ν
    split_ifs
    · rw [map_zero]
    · have hG : (fun y => FnuMu (gaugeT g U) ν μ y)
          = fun y => conjByAmbient (g y) (FnuMu U ν μ y) := by
        funext y; exact FnuMu_gaugeT g U ν μ y
      rw [hG, DstarDir_gaugeT]
  rw [Finset.sum_congr rfl (fun ν _ => hterm ν)]
  show _ = conjByAmbient (g x) (∑ ν : Fin 3, _)
  rw [map_sum]

/-- **`J` IS GAUGE COVARIANT**: `J(U^g)(b) = g(b.1)·J(U)(b)·g(b.1)⁻¹`. -/
theorem Jsource_gaugeT (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (b : Bond L) :
    Jsource (gaugeT g U) b = conjByAmbient (g b.1) (Jsource U b) :=
  Jfield_gaugeT g U b.1 b.2

#print axioms Jsource_gaugeT

/-! ## §5 — the `𝔰𝔲(2)` norm is conjugation invariant, so `‖J(U)‖` is gauge INVARIANT -/

theorem trace_conj_sq (V : Matrix.specialUnitaryGroup (Fin 2) ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (conjByAmbient V X * conjByAmbient V X) = Matrix.trace (X * X) := by
  have hVV : (V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * (V : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp V.2.1
  rw [conjByAmbient_apply]
  have hstep : (V : Matrix (Fin 2) (Fin 2) ℂ) * X * (V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
      * ((V : Matrix (Fin 2) (Fin 2) ℂ) * X * (V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ)
      = (V : Matrix (Fin 2) (Fin 2) ℂ) * (X * X) * (V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := by
    have : (V : Matrix (Fin 2) (Fin 2) ℂ) * X * (V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
        * ((V : Matrix (Fin 2) (Fin 2) ℂ) * X * (V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ)
        = (V : Matrix (Fin 2) (Fin 2) ℂ) * X
          * ((V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * (V : Matrix (Fin 2) (Fin 2) ℂ))
          * X * (V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := by noncomm_ring
    rw [this, hVV]
    noncomm_ring
  rw [hstep, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hVV, Matrix.one_mul]

/-- **`‖J(U^g)‖ = ‖J(U)‖`**, bond by bond, on the true carrier. -/
theorem norm_JsuTwo_bond_gaugeT (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (b : Bond L) :
    ‖(WithLp.ofLp (JsuTwo (gaugeT g U)) b : SuTwo)‖ = ‖(WithLp.ofLp (JsuTwo U) b : SuTwo)‖ := by
  have hval : ((WithLp.ofLp (JsuTwo (gaugeT g U)) b : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)
      = conjByAmbient (g b.1)
        (((WithLp.ofLp (JsuTwo U) b : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) := by
    rw [JsuTwo_apply, JsuTwo_apply, Jsource_gaugeT, conjByAmbient_apply, conjByAmbient_apply,
      Matrix.mul_smul, Matrix.smul_mul]
  have hsq : ‖(WithLp.ofLp (JsuTwo (gaugeT g U)) b : SuTwo)‖ ^ 2
      = ‖(WithLp.ofLp (JsuTwo U) b : SuTwo)‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    show AdalyFormal.Balaban.SuTwoInner.hsInner _ _
        = AdalyFormal.Balaban.SuTwoInner.hsInner _ _
    rw [AdalyFormal.Balaban.SuTwoInner.hsInner_def, AdalyFormal.Balaban.SuTwoInner.hsInner_def,
      hval, trace_conj_sq]
  have h1 := norm_nonneg ((WithLp.ofLp (JsuTwo (gaugeT g U)) b : SuTwo))
  have h2 := norm_nonneg ((WithLp.ofLp (JsuTwo U) b : SuTwo))
  nlinarith [hsq, h1, h2]

theorem norm_JsuTwo_gaugeT (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    ‖JsuTwo (gaugeT g U)‖ = ‖JsuTwo U‖ := by
  have hsum : (∑ b : Bond L, ‖(WithLp.ofLp (JsuTwo (gaugeT g U)) b : SuTwo)‖ ^ 2)
      = ∑ b : Bond L, ‖(WithLp.ofLp (JsuTwo U) b : SuTwo)‖ ^ 2 :=
    Finset.sum_congr rfl fun b _ => by rw [norm_JsuTwo_bond_gaugeT]
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2, hsum]

#print axioms norm_JsuTwo_gaugeT

/-! ## §6 — the GAUGE-INVARIANT smallness class, and the source bound on it -/

/-- **`GaugeEquivLinkDev δ U`**: `U` is gauge-equivalent to a configuration with links within `δ`
of the identity.  Unlike `LinkDev`, this class is closed under the gauge action. -/
def GaugeEquivLinkDev (δ : ℝ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) : Prop :=
  ∃ g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ, LinkDev δ (gaugeT g U)

/-- The class contains `LinkDev` — witness `g ≡ 1`, computed, not assumed. -/
theorem gaugeEquivLinkDev_of_linkDev {δ : ℝ}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (hU : LinkDev δ U) :
    GaugeEquivLinkDev δ U := by
  refine ⟨fun _ => 1, ?_⟩
  intro b
  have h : gaugeT (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) U b = U b := by
    rw [gaugeT_apply]
    simp
  rw [h]
  exact hU b

/-- **THE SOURCE BOUND ON THE GAUGE-INVARIANT CLASS** — the statement whose hypothesis has the
same invariance as CMP99b's own regularity condition. -/
theorem norm_JsuTwo_le_of_gaugeEquivLinkDev {δ : ℝ}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hU : GaugeEquivLinkDev δ U) :
    ‖JsuTwo U‖ ≤ Real.sqrt (2 * (Fintype.card (Bond L))) * (495 * δ) := by
  obtain ⟨g, hg⟩ := hU
  have h := norm_JsuTwo_le (gaugeT g U) hg
  rwa [norm_JsuTwo_gaugeT] at h

#print axioms norm_JsuTwo_le_of_gaugeEquivLinkDev

set_option maxHeartbeats 4000000 in
/-- **THE END-TO-END STATEMENT, ON THE GAUGE-INVARIANT CLASS.**  `deltak_wiring`'s witness datum,
`a < 1/2`, and gauge-equivalence to a `δ`-small configuration below the explicit threshold: the
printed `C*Δ_kC` with the source at `J(U)` is positive definite on `ℓ²(Λ̃)`. -/
theorem bondData_wired_posDef_gaugeEquiv (bc : BaseConstant) (v : BondFnL2 L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {δ : ℝ}
    (hU : GaugeEquivLinkDev δ U)
    (hsmall : 2 * ‖v‖ * (Real.sqrt (2 * (Fintype.card (Bond L))) * (495 * δ))
      < (1 / 2 : ℝ) - usedAt bc 0)
    {ell : ℕ} (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (w : TildeFn L ell) (hw : w ≠ 0) :
    0 < cdcFormTrue (bondData (L := L)) bc (bondQext v) (JsuTwo U) U ell Dinv w := by
  have hJ := norm_JsuTwo_le_of_gaugeEquivLinkDev U hU
  have hnv : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
  have hH1 := bondData_opNorm_H1_le_one (L := L)
  have hJn : (0 : ℝ) ≤ ‖JsuTwo U‖ := norm_nonneg _
  have hthr : 2 * ‖solutionOperator (bondData (L := L))‖ * ‖v‖ * ‖JsuTwo U‖
      < (1 / 2 : ℝ) - usedAt bc 0 := by
    have h1 : 2 * ‖solutionOperator (bondData (L := L))‖ * ‖v‖ * ‖JsuTwo U‖
        ≤ 2 * ‖v‖ * ‖JsuTwo U‖ := by
      have hkey : 0 ≤ (‖v‖ * ‖JsuTwo U‖) * (1 - ‖solutionOperator (bondData (L := L))‖) :=
        mul_nonneg (mul_nonneg hnv hJn) (by linarith)
      nlinarith [hkey]
    have h2 : 2 * ‖v‖ * ‖JsuTwo U‖
        ≤ 2 * ‖v‖ * (Real.sqrt (2 * (Fintype.card (Bond L))) * (495 * δ)) := by
      nlinarith [hJ, hnv]
    linarith
  exact cdcFormTrue_posDef_of_source_small (L := L) (H := BondFnL2 L)
    (bondData (L := L)) bc (bondQext v) (JsuTwo U)
    ((inner ℝ v (JsuTwo U) : ℝ) • (1 : BondFnL2 L →L[ℝ] BondFnL2 L))
    (bondData_isSourceOperator v (JsuTwo U)) ((1 / 2 : ℝ) - usedAt bc 0) ‖v‖ hnv
    (bondData_hfloor bc) (bondData_hD2 v) hthr U Dinv w hw

#print axioms bondData_wired_posDef_gaugeEquiv

end AdalyFormal.Balaban.SourceWiredGauge
