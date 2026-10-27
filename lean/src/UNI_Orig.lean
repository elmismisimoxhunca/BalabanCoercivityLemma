import UNI_Base

/-!
# UNI_Orig -- the ORIGINAL-bound family class (lane mixed_20261017, round 2)

`PerCubeRegularQ ell M Fm k S α η U` : every cube `(sites, j, f)` of the family that is a described class cube of factor `f` is regular with ITS OWN printed bound `f M α (ell^j η)^{-n}` (`RegBodyH` at `b = f`).
`ClassCoupledQ := CoversOmQ ∧ PerCubeRegularQ`.  `ClassCoupledQ.toHQ` : under the per-cube smallness `f M α ≤ 12 M α'` it is the hybrid class of bound factor 12 at `α'`.
`famC c` : the family of ALL triples of factor `c`; `classCoupledQ_famC` : `ClassCoupledQ (famC c)` is `ClassCoupled ell M c`.
-/
set_option autoImplicit false

namespace UNI.AllC

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2

def PerCubeRegularQ {L : PeriodicLatticeExtent} (ell M : ℕ) (Fm : CF) (k : ℕ) (S : Tower L) (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  ∀ (f : ℕ) (sites : Set (PeriodicLatticeSite L)) (j : ℕ), (sites, j, f) ∈ Fm L →
    IsClassUnion ell M k S sites j → RegBodyH ell M f sites j α₀ η U

def ClassCoupledQ {L : PeriodicLatticeExtent} (ell M : ℕ) (Fm : CF) (k : ℕ) (S : Tower L) (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  CoversOmQ ell M Fm k S ∧ PerCubeRegularQ ell M Fm k S α₀ η U

theorem ClassCoupledQ.toHQ {L : PeriodicLatticeExtent} {ell M k : ℕ} {Fm : CF} [CubeFamOK Fm] {S : Tower L} {α₀ α' η : ℝ} {U : LinkCfg L}
    (hM : 0 < M) (hη : 0 ≤ η)
    (hsm : ∀ (s : Set (PeriodicLatticeSite L)) (j f : ℕ), (s, j, f) ∈ Fm L → (f : ℝ) * M * α₀ ≤ ((12 : ℕ) : ℝ) * M * α')
    (h : ClassCoupledQ ell M Fm k S α₀ η U) : ClassCoupledHQ ell M Fm 12 k S α' η U := by
  refine ⟨h.1, fun f sites j hm hq => ?_⟩
  have h1 := RegBodyH.toFactor (f := 12) (by norm_num) (h.2 f sites j hm hq)
  refine RegBodyH.mono hη ?_ h1
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have := hsm sites j f hm
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < ((12 : ℕ) : ℝ))]
  have h2 : (f : ℝ) * α₀ * M ≤ α' * ((12 : ℕ) : ℝ) * M := by nlinarith
  exact le_of_mul_le_mul_right h2 hMr

/-- the family of ALL triples of factor `c`. -/
def famC (c : ℕ) : CF := fun _ => {t | t.2.2 = c}

theorem famC_ok' {c : ℕ} (h : 10 ≤ c) : CubeFamOK (famC c) := ⟨fun _ _ _ f hm => by
  have : f = c := hm
  subst this; exact h⟩

end UNI.AllC

#print axioms UNI.AllC.ClassCoupledQ.toHQ
