/-
Owned file (compute/m1_si1_l18/l6/). Compiles the three sub-equalities named by
`expand/CHANNEL_EXPANSION.md` §7 lemma L6 ("Fitted sums / both means") and the dispatch's own
phrasing, all UNDER the geometric-fitting hypotheses `(fit)` of §6 (`m > 0`, `c₋ ∈ CoarseLattice L
m`, `m ∣ (L μ + 1)` for each μ) — the package L1–L5 explicitly declined to invoke:

1. `partner_bijOn_blockOf` — `OneStep124.partner c` maps `B_- = blockOf c.1.1 m` BIJECTIVELY onto
   `B_+ = blockOf (OneStep124.cPlus c) m`. Injectivity of `partner c` (an iterate of the already
   globally-injective `periodicLatticeShift`) is unconditional; landing exactly on `B_+` (not
   merely into it) is the genuinely fitted content, via the already-paid `shift_mul_blockOf`
   (`ThirdLevelArrows.lean`, base package) instantiated at unit-step count `i := 1`.
2. `logData_Z_eq_ubarBracket` — `OneStep124.LogData.Z (sourcePrincipalLogData 1 m V) c` (the `ν`
   = `|B_-|⁻¹`-weighted mean of §6) equals `ubarBracket V m (c.1.1, c.2)` (the noloop stage's
   already-paid FIXED `w = m⁻³`-weighted raw bracket, `compute/m1_si1_noloop/phi/
   RawUbarDerivNoLoop.lean`), packaged into `SuTwo` via `ubarBracket`'s own already-paid
   `ubarBracket_conjTranspose`/`ubarBracket_trace` skew/trace lemmas (not a fresh logarithm or a
   fresh skew/trace derivation). The two means agree termwise once `unitSitesOf_card_eq` (already
   paid in `T1MainSegment.lean`, itself needing exactly this stage's fitting hypotheses) replaces
   `|B_-|` by `m³`; the site-set identification uses the sibling L1 stage's already-paid
   `unitSitesOf_one_image_eq_blockOf` (unconditional) composed with the base package's own
   `stepBlockOf_one`, and the rational-vs-real scalar mismatch uses the noloop stage's own
   already-paid `qsmul_eq_rsmul`. None of these four imported facts is redone.
3. `e3_ofBackground_eq_w_mean` — the E3 inner mean substitution named by the dispatch
   ("E3 inner mean ν=w"): `Coeff124.ofBackground`'s own `E3` field, which sums
   `gInvOp (adOp (D.Zx c u.1))` with the `ν = |B_-|⁻¹` weight, equals the SAME sum reweighted by
   the fixed `w = m⁻³`, again via `unitSitesOf_card_eq`. General in the background data `D`, not
   restricted to the principal one.

The §6 residuals `R_partner`, `R_Z`, `R_E3weight` themselves — and the claim that they VANISH — are
NOT asserted here; only the three named cardinality/mean identifications the dispatch requests are
proved, exactly as `(fit)` licenses. No L7/L8 channel assembly, no boxed SI1 claim, no `HasDerivAt`
claim is made in this file.

DEPENDENCIES, all copied READ-ONLY into `l6/deps/` for `LEAN_PATH` visibility, each hash-verified
byte-identical against its own already-verified origin copy in a sibling L1/L2/noloop directory
(never re-derived, re-proved, or edited): `T1MainSegment.lean` (`LogData`, `Coeff124.ofBackground`,
`OneStep124.partner`/`cPlus`, `unitSitesOf_card_eq` — from `l2/deps`, itself hash-matching `l1/deps`
and `l5/deps`), `L1CPlusBridge.lean` + `L1ForwardCarrier.lean` (for `unitSitesOf_one_image_eq_
blockOf` — from `l2/deps`), `RawAverageDeriv.lean`/`ModifiedAverageDeriv.lean`/`IngredientDeriv.lean`
(transitive deps of the next file, from `l2/deps`), `NonzeroExpDeriv.lean` (from
`compute/m1_si1_noloop/phi/deps/`, hash-matching its origin `compute/m1_si1_phi2/exp/
NonzeroExpDeriv.lean`), and `RawUbarDerivNoLoop.lean` (source AND its own already-compiled,
sorry-free, standard-axiom `.olean` from `compute/m1_si1_noloop/phi/attempt4/`, source hash
independently re-verified against the live `compute/m1_si1_noloop/phi/RawUbarDerivNoLoop.lean`
before copying) — for `ubarBracket`/`ubarBracket_conjTranspose`/`ubarBracket_trace`/
`qsmul_eq_rsmul`.
-/
import AdalyFormal.Balaban.ThirdLevelArrows
import AdalyFormal.Balaban.AdmissibleSubspace
import AdalyFormal.Balaban.QjComposite
import AdalyFormal.Balaban.LatticeOperators
import AdalyFormal.Balaban.UbarTowerCovariance
import AdalyFormal.Balaban.SuTwoLogExpCore
import AdalyFormal.Balaban.CoarseCurl
import AdalyFormal.Balaban.QOne
import T1MainSegment
import L1ForwardCarrier
import RawUbarDerivNoLoop

set_option autoImplicit false

open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLatticeSite
  PeriodicLatticeEdge PeriodicLinkConfiguration)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Log)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice blockOf)
open AdalyFormal.Balaban.QjComposite (stepBlockOf stepBlockOf_one)
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf shift_mul_blockOf)
open AdalyFormal.Balaban.CoarseCurl (periodicLatticeShift_injective)
open AdalyFormal.Balaban.UbarTowerCov (loopVar)
open AdalyFormal.Balaban.QOne (pathSite)
open OneStep124 (partner cPlus LogData gOp gInvOp adOp expOp Coeff124 unitSitesOf_card_eq)
open AdalyFormal.DeltaKR66 (sourcePrincipalLogData)
open AdalySI1.RawUbarDerivNoLoop (ubarBracket ubarBracket_conjTranspose ubarBracket_trace
  qsmul_eq_rsmul)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — `partner` is a bijection of `B_-` onto `B_+`, under `(fit)` -/

/-- `partner`'s translation direction/distance is fixed across all base points, so it is an
iterate of the globally injective `periodicLatticeShift` — UNCONDITIONAL, no fitting hypothesis. -/
theorem partner_injective (m : ℕ) (c : CoarseBond L (1 * m)) :
    Function.Injective (partner c) :=
  Function.Injective.iterate (periodicLatticeShift_injective c.2) (m * 1)

/-- **L6, part 1.** Under `(fit)`, `partner c` maps `B_- = blockOf c.1.1 m` bijectively onto
`B_+ = blockOf (cPlus c) m` — the genuinely fitted content is landing EXACTLY on `B_+`, via
`shift_mul_blockOf` at unit-step count `1`; injectivity needs no fitting hypothesis. -/
theorem partner_bijOn_blockOf {m : ℕ} (hm : 0 < m) (hdvd : ∀ μ : Fin 3, m ∣ (L μ + 1))
    (c : CoarseBond L (1 * m)) :
    Set.BijOn (partner c) (↑(blockOf c.1.1 m)) (↑(blockOf (cPlus c) m)) := by
  have hu : c.1.1 ∈ CoarseLattice L m := by simpa using c.1.2
  have hshift := shift_mul_blockOf hm hdvd hu c.2 1
  have hnat : m * 1 = 1 * m := mul_comm m 1
  have hcp : cPlus c = pathSite c.1.1 c.2 (1 * m) := congrArg (pathSite c.1.1 c.2) hnat
  have hpart : (fun x : PeriodicLatticeSite L => pathSite x c.2 (1 * m)) = partner c := by
    funext x
    exact (congrArg (pathSite x c.2) hnat).symm
  have himg : (blockOf c.1.1 m).image (partner c) = blockOf (cPlus c) m := by
    rw [← hpart, ← hshift, hcp]
  have himgSet : (partner c) '' (↑(blockOf c.1.1 m) : Set (PeriodicLatticeSite L))
      = ↑(blockOf (cPlus c) m) := by
    rw [← Finset.coe_image, himg]
  have hbij := ((partner_injective m c).injOn
    (s := (↑(blockOf c.1.1 m) : Set (PeriodicLatticeSite L)))).bijOn_image
  rwa [himgSet] at hbij

/-! ## §2 — `LogData.Z` equals `ubarBracket`, packaged into `SuTwo` -/

/-- **L6, part 2.** Under `(fit)`, the source `ν`-weighted mean `LogData.Z (sourcePrincipalLogData
1 m V) c` equals the noloop stage's already-paid FIXED `w`-weighted `ubarBracket`, packaged into
`SuTwo` via `ubarBracket`'s own already-paid skewness/trace lemmas — not an additional logarithm,
not a fresh skew/trace computation. -/
theorem logData_Z_eq_ubarBracket {m : ℕ} (hdvd : ∀ μ : Fin 3, m ∣ (L μ + 1))
    (V : PeriodicLinkConfiguration SU2 L) (c : CoarseBond L (1 * m)) :
    LogData.Z (sourcePrincipalLogData 1 m V) c
      = (⟨ubarBracket V m (c.1.1, c.2), ubarBracket_conjTranspose V m (c.1.1, c.2),
          ubarBracket_trace V m (c.1.1, c.2)⟩ : SuTwo) := by
  apply Subtype.ext
  have hcard : (unitSitesOf 1 (1 * m) c.1.1).card = m ^ 3 :=
    unitSitesOf_card_eq (ell := 1) (m := m) Nat.one_pos c.1.2 (fun μ => by simpa using hdvd μ)
  have hcardR : ((unitSitesOf 1 (1 * m) c.1.1).card : ℝ) = (m : ℝ) ^ 3 := by exact_mod_cast hcard
  have hLHS : (LogData.Z (sourcePrincipalLogData 1 m V) c : M2)
      = ∑ u ∈ unitSitesOf 1 (1 * m) c.1.1,
          (1 / (m : ℝ) ^ 3) • su2Log (loopVar 1 m V (c.1.1, c.2) u.1) := by
    unfold LogData.Z
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    rw [hcardR]
    exact Finset.sum_congr rfl (fun x _ => rfl)
  have hRHS : ubarBracket V m (c.1.1, c.2)
      = ∑ x ∈ blockOf c.1.1 m, (1 / (m : ℝ) ^ 3) • su2Log (loopVar 1 m V (c.1.1, c.2) x) := by
    show ∑ x ∈ stepBlockOf (c.1.1, c.2).1 1 m,
        ((m : ℚ) ^ 3)⁻¹ • su2Log (loopVar 1 m V (c.1.1, c.2) x) = _
    rw [show (c.1.1, c.2).1 = c.1.1 from rfl, stepBlockOf_one]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [qsmul_eq_rsmul m, one_div]
  show (LogData.Z (sourcePrincipalLogData 1 m V) c : M2) = ubarBracket V m (c.1.1, c.2)
  rw [hLHS, hRHS, ← unitSitesOf_one_image_eq_blockOf c.1.1 m,
    Finset.sum_image (fun a _ b _ h => Subtype.ext h)]

/-! ## §3 — the `E3` inner mean, `ν = w`, general in the background data `D` -/

/-- **L6, part 3.** Under `(fit)`, `Coeff124.ofBackground`'s own `E3` field — which sums
`gInvOp (adOp (D.Zx c u.1))` with the source's `ν = |B_-|⁻¹` weight — equals the SAME sum
reweighted by the fixed `w = m⁻³`, via `unitSitesOf_card_eq`. General in `D`, not restricted to
the principal background. -/
theorem e3_ofBackground_eq_w_mean {m : ℕ} (hdvd : ∀ μ : Fin 3, m ∣ (L μ + 1))
    (V : PeriodicLinkConfiguration SU2 L) (D : LogData L 1 m) (c : CoarseBond L (1 * m)) :
    (Coeff124.ofBackground 1 m V D).E3 c
      = expOp (adOp (D.Z c)) - gOp (-(adOp (D.Z c))) *
          (∑ u ∈ unitSitesOf 1 (1 * m) c.1.1, (1 / (m : ℝ) ^ 3) • gInvOp (adOp (D.Zx c u.1))) := by
  have hcard : (unitSitesOf 1 (1 * m) c.1.1).card = m ^ 3 :=
    unitSitesOf_card_eq (ell := 1) (m := m) Nat.one_pos c.1.2 (fun μ => by simpa using hdvd μ)
  have hcardR : ((unitSitesOf 1 (1 * m) c.1.1).card : ℝ) = (m : ℝ) ^ 3 := by exact_mod_cast hcard
  show expOp (adOp (D.Z c)) - gOp (-(adOp (D.Z c))) *
      (∑ u ∈ unitSitesOf 1 (1 * m) c.1.1,
        (1 / ((unitSitesOf 1 (1 * m) c.1.1).card : ℝ)) • gInvOp (adOp (D.Zx c u.1)))
    = _
  rw [hcardR]

#print axioms partner_injective
#print axioms partner_bijOn_blockOf
#print axioms logData_Z_eq_ubarBracket
#print axioms e3_ofBackground_eq_w_mean
