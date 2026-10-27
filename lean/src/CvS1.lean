import CvN7

/-!
# CvS1 -- the WD readings of the coverage-free headline (lane cover_strong_20261016)

Two readings of "the coverage-free claim, granting that the printed objects exist":

* `P428Target8NCWD`: ZT5A's WD variant (`CoercG8AtWD` / `P428Core8WD` / `P428Genuine8WD`, outer quantifiers of `P428Target8`)
  with ONE change, mirroring NC1: the class hypothesis `ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U` is replaced by
  `PerCubeRegular2 ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U` (coverage `CoversOm0p` dropped).  Here `WellDefG` is a CONCLUSION.
* `P428Target8NCWDH`: the same, with `WellDefG` moved from the conclusion to a HYPOTHESIS:
  `PerCubeRegular2 .. U → WellDefG (gparams ..) → InstIneq ..`.  This is the reading "at every in-class configuration where
  every printed object exists, the printed inequality holds".

Facts proved here:
* `P428Target8NCWD.toNC : P428Target8NCWD → P428Target8NC` and `toWDH_of_NC : P428Target8NC → P428Target8NCWDH`.
* `not_P428Target8NCWD` follows from `not_P428Target8NC` ALONE (via `toNC`).  So `¬ P428Target8NCWD` does NOT express
  "coverage is necessary even granting that the printed objects exist": it is refuted already at a point where they do not exist.
* `tip_not_WellDefG`: on the CvN6 tip instance there is an in-class configuration at which `WellDefG` FAILS.
* `P428Target8NCWDH` is NOT decided here (see the lane NOTES / REPORT for the analysis).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverStrong

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.NoCover
open AdalyFormal.GeneralClass
open AdalyFormal.CoverNec
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

/-! ## `P428Target8NCWD`: ZT5A's WD headline with `ClassCoupled → PerCubeRegular2` -/

/-- `CoercG8AtWD` (ZT5A) with `ClassCoupled` replaced by `PerCubeRegular2` (no coverage). -/
def CoercG8AtNCWD (ell M R k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent)
    (c : ℕ) (α₀ γ₀ : ℝ) : Prop :=
  TorusOK ell M Lu →
  ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S →
  ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
  ∀ (U : LinkCfg (scaleUp ell k Lu)),
    PerCubeRegular2 ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    InstAtWD ell k hell a Lu γ₀ S Lam U

/-- `P428Core8WD` (ZT5A) over `CoercG8AtNCWD`. -/
def P428Core8NCWD (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * M * α₀ ≤ a₀ →
      CoercG8AtNCWD ell M R k hell a Lu 12 α₀ γ₀

/-- `P428Genuine8WD` (ZT5A) over `P428Core8NCWD`. -/
def P428Genuine8NCWD (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  SidePow6 ell M a ∧ P428Core8NCWD ell M R hell a

/-- **`P428Target8NCWD`**: the outer quantifiers of `P428Target8` over `P428Genuine8NCWD`. -/
def P428Target8NCWD : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      P428Genuine8NCWD ell (ell ^ m) R (by omega) a

/-! ## `P428Target8NCWDH`: `WellDefG` as a HYPOTHESIS -/

/-- at one point: IF every printed object exists (`WellDefG`), THEN the printed inequality holds. -/
def InstIneqWDH (ell k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent) (γ₀ : ℝ)
    (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu)) : Prop :=
  GenP.WellDefG (gparams ell k Lu hell S U a Lam) → InstIneq ell k hell a Lu γ₀ S Lam U

def CoercG8AtNCWDH (ell M R k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent)
    (c : ℕ) (α₀ γ₀ : ℝ) : Prop :=
  TorusOK ell M Lu →
  ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S →
  ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
  ∀ (U : LinkCfg (scaleUp ell k Lu)),
    PerCubeRegular2 ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    InstIneqWDH ell k hell a Lu γ₀ S Lam U

def P428Core8NCWDH (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * M * α₀ ≤ a₀ →
      CoercG8AtNCWDH ell M R k hell a Lu 12 α₀ γ₀

def P428Genuine8NCWDH (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  SidePow6 ell M a ∧ P428Core8NCWDH ell M R hell a

/-- **`P428Target8NCWDH`**: the coverage-free headline at configurations where every printed object exists. -/
def P428Target8NCWDH : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      P428Genuine8NCWDH ell (ell ^ m) R (by omega) a

/-! ## pins (definitional unfoldings; a mutant of any definition breaks the corresponding `Iff.rfl`) -/

theorem coercNCWD_unfold (ell M R k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent) (c : ℕ) (α₀ γ₀ : ℝ) :
    CoercG8AtNCWD ell M R k hell a Lu c α₀ γ₀ ↔
      (TorusOK ell M Lu → ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S →
        ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
        ∀ (U : LinkCfg (scaleUp ell k Lu)), PerCubeRegular2 ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
          GenP.WellDefG (gparams ell k Lu hell S U a Lam) ∧ InstIneq ell k hell a Lu γ₀ S Lam U) := Iff.rfl

theorem coercNCWDH_unfold (ell M R k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent) (c : ℕ) (α₀ γ₀ : ℝ) :
    CoercG8AtNCWDH ell M R k hell a Lu c α₀ γ₀ ↔
      (TorusOK ell M Lu → ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S →
        ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
        ∀ (U : LinkCfg (scaleUp ell k Lu)), PerCubeRegular2 ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
          GenP.WellDefG (gparams ell k Lu hell S U a Lam) → InstIneq ell k hell a Lu γ₀ S Lam U) := Iff.rfl

/-- pin: NCWD's inner claim is ZT5A's `CoercG8AtWD` with the class slot `PerCubeRegular2` (a hypothesis of the r8 form implies
the NCWD form by weakening `ClassCoupled = CoversOm0p ∧ PerCubeRegular2` to its second conjunct). -/
theorem CoercG8AtNCWD.toR8 {ell M R k : ℕ} {hell : 0 < ell} {a : ℝ} {Lu : PeriodicLatticeExtent} {c : ℕ} {α₀ γ₀ : ℝ}
    (h : CoercG8AtNCWD ell M R k hell a Lu c α₀ γ₀) : CoercG8AtWD ell M R k hell a Lu c α₀ γ₀ :=
  fun hT S hS Lam hL U hU => h hT S hS Lam hL U hU.2

/-! ## implications -/

theorem P428Target8NCWD.toNC (h : P428Target8NCWD) : AdalyFormal.NoCover.P428Target8NC := by
  intro ell hell a ha
  obtain ⟨m₀, hm₀, hm⟩ := h ell hell a ha
  refine ⟨m₀, hm₀, fun m hm' => ?_⟩
  obtain ⟨R₀, hR⟩ := hm m hm'
  refine ⟨R₀, fun R hR' => ?_⟩
  obtain ⟨hs, a₀, ha₀, γ₀, hγ, hc⟩ := hR R hR'
  refine ⟨hs, a₀, ha₀, γ₀, hγ, fun k hk Lu α₀ h1 h2 => ?_⟩
  have h2' : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ := by simpa using h2
  exact fun hT S hS Lam hL U hU => (hc k hk Lu α₀ h1 h2' hT S hS Lam hL U hU).2

theorem toWDH_of_NC (h : AdalyFormal.NoCover.P428Target8NC) : P428Target8NCWDH := by
  intro ell hell a ha
  obtain ⟨m₀, hm₀, hm⟩ := h ell hell a ha
  refine ⟨m₀, hm₀, fun m hm' => ?_⟩
  obtain ⟨R₀, hR⟩ := hm m hm'
  refine ⟨R₀, fun R hR' => ?_⟩
  obtain ⟨hs, a₀, ha₀, γ₀, hγ, hc⟩ := hR R hR'
  refine ⟨hs, a₀, ha₀, γ₀, hγ, fun k hk Lu α₀ h1 h2 => ?_⟩
  have h2' : ((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ := by simpa using h2
  exact fun hT S hS Lam hL U hU _ => hc k hk Lu α₀ h1 h2' hT S hS Lam hL U hU

/-- **`¬ P428Target8NCWD`** -- obtained from `¬ P428Target8NC` alone (no point with all printed objects is used). -/
theorem not_P428Target8NCWD : ¬ P428Target8NCWD := fun h => not_P428Target8NC h.toNC

/-- the r8 headline (with coverage) holds and its WD reading without coverage is false. -/
theorem coverage_necessary_WD :
    AdalyFormal.StatementLaneG.P428Target8 ∧ ¬ P428Target8NCWD :=
  ⟨AdalyFormal.M2RightInv.p428Target8, not_P428Target8NCWD⟩

/-- refuting the WDH reading would refute both other coverage-free readings. -/
theorem not_NC_of_not_WDH (h : ¬ P428Target8NCWDH) :
    ¬ AdalyFormal.NoCover.P428Target8NC ∧ ¬ P428Target8NCWD :=
  ⟨fun h' => h (toWDH_of_NC h'), fun h' => h (toWDH_of_NC h'.toNC)⟩

/-! ## the instance: in class, and the printed objects do NOT exist -/

theorem not_WellDefG_of_not_unit (P : IngrBParams) (h : ¬ IsUnit P.data.Ginv) : ¬ GenP.WellDefG P :=
  fun hW => h hW.2.2.1

/-- **on the CvN6 tip instance there is an in-class configuration where `WellDefG` fails** (every hypothesis of the inner claim
holds, for the r8 factor-12 class and the general class at every `F`, every `α₀ > 0`). -/
theorem tip_not_WellDefG {m R : ℕ} (hm : 1 ≤ m) (hR : 28 ≤ R) {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∃ v : Matrix.specialUnitaryGroup (Fin 2) ℂ,
      TorusOK 3 (3 ^ m) (ncLu (3 ^ m) R) ∧ Admissible 3 (3 ^ m) R 1 (gcS 3 (3 ^ m) R) ∧
      LambdaOK2 3 (3 ^ m) R 1 (gcS 3 (3 ^ m) R) (ncLam (3 ^ m) R) ∧ (ncLam (3 ^ m) R).Nonempty ∧
      (∀ α₀ : ℝ, 0 < α₀ → PerCubeRegular2 3 (3 ^ m) 12 1 (gcS 3 (3 ^ m) R) α₀ ((3 : ℝ) ^ 1)⁻¹
        (Function.update (fun _ => 1) ((xtG 3 (3 ^ m) R (by norm_num) (by positivity), 1) : Bond _) v)) ∧
      (∀ (F : ℕ) (α₀ : ℝ), 0 < α₀ → PerCubeRegularG 3 (3 ^ m) F 1 (gcS 3 (3 ^ m) R) α₀ ((3 : ℝ) ^ 1)⁻¹
        (Function.update (fun _ => 1) ((xtG 3 (3 ^ m) R (by norm_num) (by positivity), 1) : Bond _) v)) ∧
      ¬ GenP.WellDefG (gparams 3 1 (ncLu (3 ^ m) R) (by norm_num) (gcS 3 (3 ^ m) R)
        (Function.update (fun _ => 1) ((xtG 3 (3 ^ m) R (by norm_num) (by positivity), 1) : Bond _) v) a
        (ncLam (3 ^ m) R)) := by
  have hM : 0 < 3 ^ m := by positivity
  have hM2 : 2 ≤ 3 ^ m := le_trans (by norm_num) (Nat.le_self_pow (by omega) 3)
  have hdvd : 3 ∣ 3 ^ m := dvd_pow_self 3 (by omega)
  obtain ⟨v, hv⟩ := exists_singular_tip (ell := 3) (M := 3 ^ m) (R := R) le_rfl (by norm_num) hM2 (by omega) ha ha1
    (ncLam (3 ^ m) R)
  have hunc := gc_tip_uncovered (ell := 3) (R := R) (by norm_num) (by norm_num) hM (by omega)
  have hη : (0 : ℝ) < ((3 : ℝ) ^ 1)⁻¹ := by norm_num
  refine ⟨v, torusOK_nc le_rfl hdvd hM, gc_admissible (by norm_num) hM, lambdaOK2_gc le_rfl hdvd hM (by omega),
    ncLam_nonempty hM, ?_, ?_, not_WellDefG_of_not_unit _ hv⟩
  · intro α₀ hα
    exact perCube_update (perCube_one (by norm_num) hM (by norm_num) hα hη) _
      (fun sites j hq => hunc 12 sites j (isClassCube_toG (gc_admissible (R := R) (by norm_num) hM).1 (by norm_num) hq)) v
  · intro F α₀ hα
    exact perCubeG_update (perCubeG_one (by norm_num) hM hα hη) _ (fun f sites j _ hq => hunc f sites j hq) v

#print axioms coercNCWD_unfold
#print axioms coercNCWDH_unfold
#print axioms CoercG8AtNCWD.toR8
#print axioms P428Target8NCWD.toNC
#print axioms toWDH_of_NC
#print axioms not_P428Target8NCWD
#print axioms coverage_necessary_WD
#print axioms not_NC_of_not_WDH
#print axioms not_WellDefG_of_not_unit
#print axioms tip_not_WellDefG

end AdalyFormal.CoverStrong
