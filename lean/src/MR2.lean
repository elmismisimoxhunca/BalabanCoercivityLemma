import MR1
import NP12

/-!
# MR2 -- `PatchCoercive` from PER-PATCH LOCAL CHARTS (m2_route, 2026-10-14)

NP12 `patchCoercive_inst` asks, per G3 patch `(j, w)`, for an instance `hinst` at one level `i`:
`i = j` when `Ball w ((c+1)G_j)` meets `Ω_{j+1}` (up case), `i = j - 1` when `j ≥ 1` and it does not (down case);
case A (`j = 0`, no `Ω_1` point) uses no instance.  NP12 produces `hinst` from lane B's GLOBAL `M1Regular U`.

* `ChartOn ell U η a' i w r` : one gauge `g` and a field `A` (Hermitian traceless everywhere) with `U^g = exp(iηA)` on
  bonds based in `Ball w r`, clause 1 (`|A| < a'(ell^i η)⁻¹`) on bonds based in `Ball w r` and clause 2
  (`|η⁻¹∇_μ A| < a'(ell^i η)⁻²`) for `x, x+μ ∈ Ball w r`.  No clause 3.
* `PatchCharts` : `ChartOn` at the level and radius `c G_j + d ell^i + 64 ell^{i+2}` NP12 uses, for every patch, only in
  the case that patch uses (up: `i = j`; down: `i = j-1`).
* `patchCoercive_charts` : NP12 `patchCoercive_inst` with `hinst` supplied by MR1 `inst_chart` from `PatchCharts`.
* **`patchCoercive_charts_exists`** : NP12 `patchCoercive_nonflat` with `M1Regular U` (and `α₀`) replaced by
  `PatchCharts … η a'`, `0 < a' ≤ a₀`, any `η > 0`.  Same constants `cW`, `a₀`, `D` (depending on `ell`, `a` only), same
  conclusion.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.M2Route

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.SuTwoLogExp (M2)
open AdalyFormal.StatementLane (Tower BlockClosed Admissible bigSide pdist scaleUp)
open AdalyFormal.StatementLaneR8 (Ball pdist_comm pdist_triangle)
open AdalyFormal.M1Patch (patchTower LemIFlat Kflat)
open AdalyFormal.RegBgKU (KUSmall kapHat)
open AdalyFormal.W3NF (lamC ThetaP KG0 KG0_pos rhoM1)
open AdalyFormal.M1IMS (G0form Fform HatPack HolRegime etaC nuC sandwich N_le_wnorm PatchCoercive ginvForm wN ginv_form)
open AdalyFormal.M1 (IsPatch gsp patch gsp_pos wnormSq)
open AdalyFormal.M1W2 (locG0 caseB_up caseB_down g0_caseA)
open AdalyFormal.M1NonFlat (SU2 epsNF PkA thetaN thetaN_nonneg g0_caseB_nf smallA epsNF_small PkA_ge_one)

variable {L : PeriodicLatticeExtent}

/-- a local chart of `U` on `Ball w r` at the level-`i` scale (clauses 1-2 of lane B's `M1Bounds`, no clause 3). -/
def ChartOn (ell : ℕ) (U : Cfg L) (η a' : ℝ) (i : ℕ) (w : PeriodicLatticeSite L) (r : ℕ) : Prop :=
  ∃ (g : PeriodicLatticeSite L → SU2) (A : Bond L → M2),
    (∀ e, AdalyFormal.StatementLane.HT (A e)) ∧
    (∀ e : Bond L, pdist w e.1 ≤ r →
      ((periodicGaugeTransform g U e : SU2) : M2) = NormedSpace.exp (((η : ℂ) * Complex.I) • A e)) ∧
    (∀ e : Bond L, pdist w e.1 ≤ r → frobNorm (A e) < a' * (((ell : ℝ) ^ i * η)⁻¹ ^ 1)) ∧
    (∀ (μ ν : Fin 3) (x : PeriodicLatticeSite L), pdist w x ≤ r → pdist w (periodicLatticeShift x μ) ≤ r →
      frobNorm ((η⁻¹ : ℝ) • (A (periodicLatticeShift x μ, ν) - A (x, ν))) < a' * (((ell : ℝ) ^ i * η)⁻¹ ^ 2))

/-- the chart radius NP12 needs at a patch `(j, w)` and level `i`. -/
def chartRad (ell M κ c d j i : ℕ) : ℕ := c * gsp ell M κ j + d * ell ^ i + 64 * ell ^ (i + 2)

/-- **the per-patch input of `PatchCoercive`**, exactly in the cases NP12 uses it. -/
def PatchCharts (ell M k κ c d : ℕ) (S : Tower L) (U : Cfg L) (η a' : ℝ) : Prop :=
  ∀ (j : ℕ) (w : PeriodicLatticeSite L), IsPatch ell M k κ S j w →
    ((∃ y ∈ Ball w ((c + 1) * gsp ell M κ j), y ∈ S.Om (j + 1)) →
        ChartOn ell U η a' j w (chartRad ell M κ c d j j)) ∧
    (1 ≤ j → (¬ ∃ y ∈ Ball w ((c + 1) * gsp ell M κ j), y ∈ S.Om (j + 1)) →
        ChartOn ell U η a' (j - 1) w (chartRad ell M κ c d j (j - 1)))

/-- a chart at level `i` is a chart at every level `i' ≤ i` (weaker bounds), on any smaller ball. -/
theorem ChartOn.mono {ell : ℕ} (hell : 1 ≤ ell) {U : Cfg L} {η a' : ℝ} (hη : 0 < η) (ha' : 0 ≤ a')
    {i i' : ℕ} (hii : i' ≤ i) {w : PeriodicLatticeSite L} {r r' : ℕ} (hrr : r' ≤ r)
    (h : ChartOn ell U η a' i w r) : ChartOn ell U η a' i' w r' := by
  obtain ⟨g, A, hHT, hUA, h1, h2⟩ := h
  have hl : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hp : (ell : ℝ) ^ i' ≤ (ell : ℝ) ^ i := pow_le_pow_right₀ hl hii
  have hp0 : 0 < (ell : ℝ) ^ i' := by positivity
  have hinv : ((ell : ℝ) ^ i * η)⁻¹ ≤ ((ell : ℝ) ^ i' * η)⁻¹ :=
    inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_right hp hη.le)
  have hinv0 : 0 ≤ ((ell : ℝ) ^ i * η)⁻¹ := by positivity
  refine ⟨g, A, hHT, fun e he => hUA e (he.trans hrr), fun e he => ?_, fun μ ν x hx hx' => ?_⟩
  · refine (h1 e (he.trans hrr)).trans_le ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hinv0 hinv 1) ha'
  · refine (h2 μ ν x (hx.trans hrr) (hx'.trans hrr)).trans_le ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hinv0 hinv 2) ha'

section main
variable {ell M R k κ c : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) {S : Tower (scaleUp ell k Lu)}
  (hS : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M) (hell : 2 ≤ ell) (hR1 : 1 ≤ R)
  (hR4 : (c + 4) * κ * ell ≤ R) (hroom : 17 * ell ≤ R * M) {d : ℕ} (hdM : d + 64 * ell ^ 2 ≤ κ * M)
  {W : ℕ} (hW : 1 ≤ W) (hWR : W ≤ R * M * ell)
include hell0 hS hκ hM hell hR1 hR4 hroom hdM hW hWR

/-- **`PatchCoercive` from per-patch local charts** (NP12 `patchCoercive_inst` with `hinst` from MR1 `inst_chart`). -/
theorem patchCoercive_charts {a Ci : ℝ} (ha : 0 < a) (hCi : 0 ≤ Ci) (hI : LemIFlat ell a Ci)
    (a₀ : ℝ) (ha₀1 : a₀ ≤ 1 / 2)
    (hsmall : ∀ a' : ℝ, 0 ≤ a' → a' ≤ a₀ →
      KUSmall ell (rhoM1 ell (2 * a')) ∧
      432 * kapHat ell (rhoM1 ell (2 * a')) ^ 2 ≤ 1 ∧
      kapHat ell (rhoM1 ell (2 * a')) ≤ 1 / (1000 * (ell : ℝ) ^ 3) ∧
      kapHat ell (rhoM1 ell (2 * a')) ≤ 1 ∧
      324 * lamC ell * kapHat ell (rhoM1 ell (2 * a')) ≤ 1 ∧
      2 * ThetaP ell a (kapHat ell (rhoM1 ell (2 * a'))) ≤ 1 / Kflat a Ci ∧
      8 * (272 * (kapHat ell (rhoM1 ell (2 * a')) / (3 * Real.pi)) / (4 * Real.sqrt 2)) ≤ 1 / Kflat a Ci)
    (hd : 12 * ell + 10 ≤ d)
    (U : LinkCfg (scaleUp ell k Lu)) (cs : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hreg : HolRegime S ell k U ρ) (ε1 : ℝ) (hε1 : 0 < ε1) (hη : etaC ell W cs ρ ε1 < 1)
    (η : ℝ) (hη0 : 0 < η) (a' : ℝ) (ha'0 : 0 < a') (ha'a : a' ≤ a₀)
    (hch : PatchCharts ell M k κ c d S U η a') :
    PatchCoercive ell M k κ c Lu hell0 S U a Lam
      ((1 - etaC ell W cs ρ ε1) * min a (1 / ((ell : ℝ) ^ 2 * KG0 a Ci) - epsNF ell (PkA a) (thetaN ell) d)
        - 2 * nuC ell ρ) := by
  set cW : ℝ := 1 / ((ell : ℝ) ^ 2 * KG0 a Ci) - epsNF ell (PkA a) (thetaN ell) d with hcW
  intro j w hpj A hA
  have ha0 : 0 ≤ a := ha.le
  set B : BondFnL2 (scaleUp ell k Lu) := (A : BondFnL2 (scaleUp ell k Lu)) with hBdef
  have hFA : ginvForm ell k Lu hell0 S U a Lam A = Fform S ell k U a B := by
    unfold ginvForm
    rw [ginv_form hell0 S U a Lam ha0 hp.hu]
    rfl
  have hsand := (sandwich hS hell hR1 (by omega) hW hWR U a cs hp ρ hρ hreg ε1 hε1 B).1
  have hN := N_le_wnorm hS hell0 B
  have hBsupp : ∀ b : Bond (scaleUp ell k Lu), (WithLp.ofLp B) b ≠ 0 →
      b.1 ∈ Ball w (c * gsp ell M κ j) ∨ periodicLatticeShift b.1 b.2 ∈ Ball w (c * gsp ell M κ j) := hA
  have hOm0 : ∀ b : Bond (scaleUp ell k Lu), (WithLp.ofLp B) b ≠ 0 →
      b.1 ∈ S.Om 0 ∨ periodicLatticeShift b.1 b.2 ∈ S.Om 0 := by
    intro b hb
    by_contra hn
    exact hb (A.2 b hn)
  have hw0 : 0 ≤ wnormSq S ell k B := by unfold wnormSq; exact Finset.sum_nonneg (fun b _ => by positivity)
  have hG0 : min a cW * wnormSq S ell k B ≤ G0form S ell k U a B := by
    by_cases hB : ∃ y ∈ Ball w ((c + 1) * gsp ell M κ j), y ∈ S.Om (j + 1)
    · obtain ⟨hjk, hZi, hZ2⟩ := caseB_up hS hell hκ hM hR4 hpj hB
      obtain ⟨g, Af, hHT, hUA, h1, h2⟩ := (hch j w hpj).1 hB
      obtain ⟨Up, hUp, hW3⟩ := inst_chart hell ha hCi hI a₀ ha₀1 hsmall hS j hjk w (gsp ell M κ j) d hd η hη0 a' ha'0
        ha'a U g Af hHT hUA h1 h2
      have h := g0_caseB_nf hS hell hroom hdM (le_refl j) hjk hZi hZ2 U Up hUp a cW ha0 hW3 B hBsupp
      have hm := min_le_right a cW
      nlinarith
    · by_cases hj : 1 ≤ j
      · have hZi := caseB_down hS hell hκ hM hR4 hpj hj
        have hZ2 : ∀ z ∈ Ball w ((c + 1) * gsp ell M κ j), z ∉ S.Om (j - 1 + 2) := by
          rw [show j - 1 + 2 = j + 1 by omega]
          intro z hz hz1
          exact hB ⟨z, hz, hz1⟩
        have hik : j - 1 + 1 ≤ k := by have := hpj.1; omega
        obtain ⟨g, Af, hHT, hUA, h1, h2⟩ := (hch j w hpj).2 hj hB
        obtain ⟨Up, hUp, hW3⟩ := inst_chart hell ha hCi hI a₀ ha₀1 hsmall hS (j - 1) hik w (gsp ell M κ j) d hd η hη0
          a' ha'0 ha'a U g Af hHT hUA h1 h2
        have h := g0_caseB_nf hS hell hroom hdM (i := j - 1) (by omega) hik hZi hZ2 U Up
          hUp a cW ha0 hW3 B hBsupp
        have hm := min_le_right a cW
        nlinarith
      · have hj0 : j = 0 := by omega
        have hg := gsp_pos hκ hM hell0 (ell := ell) j
        have hZ1 : ∀ z ∈ Ball w (c * gsp ell M κ j + 1), z ∉ S.Om 1 := by
          intro z hz hz1
          refine hB ⟨z, ?_, by rw [hj0]; exact hz1⟩
          have hz' : pdist w z ≤ c * gsp ell M κ j + 1 := hz
          show pdist w z ≤ (c + 1) * gsp ell M κ j
          nlinarith
        have h := g0_caseA hS hell hκ hM hZ1 U a ha0 B hOm0 hBsupp
        have hm := min_le_left a cW
        nlinarith
  rw [hFA]
  show ((1 - etaC ell W cs ρ ε1) * min a cW - 2 * nuC ell ρ) * wnormSq S ell k B ≤ Fform S ell k U a B
  have hη1 : 0 ≤ 1 - etaC ell W cs ρ ε1 := by linarith
  have hν : 0 ≤ nuC ell ρ := by
    unfold nuC; have : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num); positivity
  have hs' : (1 - etaC ell W cs ρ ε1) * G0form S ell k U a B
      - 2 * nuC ell ρ * ‖AdalyFormal.DLayer.bondWt (-AdalyFormal.M1IMS.sigG (geomOf ell k S)) B‖ ^ 2
      ≤ Fform S ell k U a B := hsand
  have h1 := mul_le_mul_of_nonneg_left hG0 hη1
  have h2 := mul_le_mul_of_nonneg_left hN (by linarith : (0 : ℝ) ≤ 2 * nuC ell ρ)
  nlinarith

end main

/-- **`PatchCoercive` from per-patch local charts, constants packaged as in NP12 `patchCoercive_nonflat`.**
Same `cW`, `a₀`, `D` (depending on `ell`, `a` only); `M1Regular U` and `α₀` are replaced by `PatchCharts … η a'`
with `0 < a' ≤ a₀`, `0 < η`. -/
theorem patchCoercive_charts_exists {ell : ℕ} (hell : 2 ≤ ell) {a : ℝ} (ha : 0 < a) :
    ∃ cW : ℝ, 0 < cW ∧ ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ D : ℕ, 12 * ell + 10 ≤ D ∧
    (∀ d, D ≤ d → epsNF ell (PkA a) (thetaN ell) d ≤ cW / 2) ∧
    ∀ {M R k κ c : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell)
      {S : Tower (scaleUp ell k Lu)} (_hS : Admissible ell M R k S) (_hκ : 0 < κ) (_hM : 0 < M) (_hR1 : 1 ≤ R)
      (_hR4 : (c + 4) * κ * ell ≤ R) (_hroom : 17 * ell ≤ R * M) {d : ℕ} (_hdD : D ≤ d)
      (_hdM : d + 64 * ell ^ 2 ≤ κ * M)
      {W : ℕ} (_hW : 1 ≤ W) (_hWR : W ≤ R * M * ell)
      (U : LinkCfg (scaleUp ell k Lu)) (cs : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
      (_hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs)
      (ρ : ℝ) (_hρ : 0 ≤ ρ) (_hreg : HolRegime S ell k U ρ) (ε1 : ℝ) (_hε1 : 0 < ε1) (_hη : etaC ell W cs ρ ε1 < 1)
      (η : ℝ) (_hη0 : 0 < η) (a' : ℝ) (_ha'0 : 0 < a') (_ha'a : a' ≤ a₀)
      (_hch : PatchCharts ell M k κ c d S U η a'),
      PatchCoercive ell M k κ c Lu hell0 S U a Lam
        ((1 - etaC ell W cs ρ ε1) * min a (cW - epsNF ell (PkA a) (thetaN ell) d) - 2 * nuC ell ρ) := by
  set Ci := AdalyFormal.LemIFlat.CS ell a * AdalyFormal.LemIFlat.KV ell a with hCi
  have hCi0 : 0 ≤ Ci := AdalyFormal.W3NF.CSKV_nonneg ell ha
  have hI : LemIFlat ell a Ci := AdalyFormal.LemIFlat.lemIFlat ell (by omega) a ha
  have hKG := KG0_pos ha hCi0
  set cW : ℝ := 1 / ((ell : ℝ) ^ 2 * KG0 a Ci) with hcW
  have hcW0 : 0 < cW := by
    have : (0 : ℝ) < ell := by exact_mod_cast (by omega : 0 < ell)
    positivity
  obtain ⟨a₀, ha₀, ha₀1, hsmall⟩ := smallA ell hell a Ci ha hCi0
  obtain ⟨D, hD, hDle⟩ := epsNF_small ell (by omega) (PkA_ge_one a) (thetaN_nonneg ell) (cW / 2) (by linarith)
  refine ⟨cW, hcW0, a₀, ha₀, D, hD, hDle, ?_⟩
  intro M R k κ c Lu hell0 S hS hκ hM hR1 hR4 hroom d hdD hdM W hW hWR U cs Lam hp ρ hρ hreg ε1 hε1 hη η hη0 a' ha'0
    ha'a hch
  have hd : 12 * ell + 10 ≤ d := le_trans hD hdD
  exact patchCoercive_charts hell0 hS hκ hM hell hR1 hR4 hroom hdM hW hWR ha hCi0 hI a₀ ha₀1 hsmall hd U cs Lam hp ρ hρ
    hreg ε1 hε1 hη η hη0 a' ha'0 ha'a hch

end AdalyFormal.M2Route

#print axioms AdalyFormal.M2Route.ChartOn.mono
#print axioms AdalyFormal.M2Route.patchCoercive_charts
#print axioms AdalyFormal.M2Route.patchCoercive_charts_exists
