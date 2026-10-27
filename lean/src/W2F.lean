import W2E
import PW8

/-!
# W2F -- lane D's flat W3 IS the flat case of `W3G0At` (M1 lane W2, 2026-10-13)

* `ginv_eq_G0_flat` : at the flat configuration the genuine r8 `Ginv` form EQUALS the decoupled form `G0`
  (`Δ_π` reduces to the masked curl because `curl ∘ D = 0` and `Δ' = 0` at `U = 1`; no invertibility hypothesis);
* **`w3G0_of_flat`** : lane D's `W3FlatStmt ell hell a` gives `∃ c > 0, ∀ L, W3G0At ell L 1 a c` (same `c`; the torus of
  `W3FlatStmt` is `scaleUp ell (i+1) Lu'`, and every torus whose sides are multiples of `ell^{i+1}` is of that form);
* **`patchCoercive_W2_flatW3`** : `patchCoercive_W2` with the W3 input supplied by `W3FlatStmt ell hell a`, for a real
  configuration `U` equal to `1` on the bonds based within `(c+1) G_j` of every patch centre (comparison configuration `1` at
  every patch): `∃ cW > 0` (the `c` of `W3FlatStmt`) with `PatchCoercive … ((1 − etaC) · min(a, cW − δ) − 2 nuC)`, given
  `OptDecayAt … 1 δ d`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.M1W2

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower BlockClosed Admissible bigSide pdist scaleUp)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.M1Patch (patchTower W3FlatStmt GP om0_univ)
open AdalyFormal.M1IMS (G0form Ymass inner_MassFull_eq HatPack HolRegime etaC nuC PatchCoercive)
open AdalyFormal.M1 (IsPatch gsp wnormSq)
open AdalyFormal.StatementLane (pdist)

/-- **at `U = 1` the genuine `Ginv` form is the decoupled form** (any tower, any `Λ`). -/
theorem ginv_eq_G0_flat (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell0 : 0 < ell) (S : Tower (scaleUp ell k Lu))
    (a : ℝ) (ha : 0 ≤ a) (Lam : Set (PeriodicLatticeSite Lu))
    (A : ↥(bondSupp (gparams ell k Lu hell0 S (flatCfg : Cfg (scaleUp ell k Lu)) a Lam).G)) :
    ⟪A, (gparams ell k Lu hell0 S (flatCfg : Cfg (scaleUp ell k Lu)) a Lam).data.Ginv A⟫
      = G0form S ell k (flatCfg : Cfg (scaleUp ell k Lu)) a (A : BondFnL2 (scaleUp ell k Lu)) := by
  rw [(gparams ell k Lu hell0 S (flatCfg : Cfg (scaleUp ell k Lu)) a Lam).data.inner_Ginv A]
  have h1 : ⟪A, (gparams ell k Lu hell0 S (flatCfg : Cfg (scaleUp ell k Lu)) a Lam).data.Dpi A⟫
      = ⟪(A : BondFnL2 _), DpiFull (geomOf ell k S) (flatCfg : Cfg (scaleUp ell k Lu)) a A⟫ := by
    show ⟪A, pE _ (DpiFull (geomOf ell k S) (flatCfg : Cfg (scaleUp ell k Lu)) a (iE _ A))⟫ = _
    rw [pE_inner_right]; rfl
  have h3 : ⟪A, (gparams ell k Lu hell0 S (flatCfg : Cfg (scaleUp ell k Lu)) a Lam).data.Mass A⟫
      = ⟪(A : BondFnL2 _), MassFull (geomOf ell k S) a (bondSectorOf (geomOf ell k S) (flatCfg : Cfg (scaleUp ell k Lu))) A⟫ := by
    show ⟪A, pE _ (MassFull (geomOf ell k S) a (bondSectorOf (geomOf ell k S) (flatCfg : Cfg (scaleUp ell k Lu))) (iE _ A))⟫ = _
    rw [pE_inner_right]; rfl
  have h2 : (gparams ell k Lu hell0 S (flatCfg : Cfg (scaleUp ell k Lu)) a Lam).data.T A
      = Tfull (geomOf ell k S) (flatCfg : Cfg (scaleUp ell k Lu)) A := rfl
  rw [h1, h2, h3, inner_MassFull_eq _ _ a ha, AdalyFormal.StatementLaneG.inner_DpiFull_flat]
  rfl

/-- every torus whose sides are multiples of `ell^n` is `scaleUp ell n` of a unit torus. -/
theorem exists_scaleUp (ell n : ℕ) (hell0 : 0 < ell) (L : PeriodicLatticeExtent) (hdiv : ∀ μ : Fin 3, ell ^ n ∣ L μ + 1) :
    ∃ Lu : PeriodicLatticeExtent, scaleUp ell n Lu = L := by
  refine ⟨fun μ => (L μ + 1) / ell ^ n - 1, funext (fun μ => ?_)⟩
  show ((L μ + 1) / ell ^ n - 1 + 1) * ell ^ n - 1 = L μ
  have hp : 0 < ell ^ n := pow_pos hell0 n
  have h1 : (L μ + 1) / ell ^ n * ell ^ n = L μ + 1 := Nat.div_mul_cancel (hdiv μ)
  have h2 : 1 ≤ (L μ + 1) / ell ^ n := by
    rcases Nat.eq_zero_or_pos ((L μ + 1) / ell ^ n) with h | h
    · rw [h, zero_mul] at h1; omega
    · exact h
  rw [Nat.sub_add_cancel h2, h1]
  omega

/-- **lane D's flat W3 is the flat case of the decoupled-form input.** -/
theorem w3G0_of_flat (ell : ℕ) (hell0 : 0 < ell) (a : ℝ) (ha : 0 ≤ a) (h : W3FlatStmt ell hell0 a) :
    ∃ c : ℝ, 0 < c ∧ ∀ L : PeriodicLatticeExtent, W3G0At ell L (flatCfg : Cfg L) a c := by
  obtain ⟨c, hc, hall⟩ := h
  refine ⟨c, hc, fun L i Rg hRg hdiv A => ?_⟩
  obtain ⟨Lu', hL⟩ := exists_scaleUp ell (i + 1) hell0 L hdiv
  subst hL
  have hx : (A : BondFnL2 _) ∈ bondSupp (GP ell i Lu' Rg) := by
    intro b hb
    exfalso
    apply hb
    left
    rw [om0_univ]
    trivial
  have h1 := hall i Lu' Rg hRg ∅ ⟨A, hx⟩
  rw [ginv_eq_G0_flat ell (i + 1) Lu' hell0 (patchTower i Rg) a ha ∅ ⟨A, hx⟩] at h1
  exact h1

/-- **the flat corollary**: lane D's flat W3 + the flat decay input give lane E's `PatchCoercive` at every real `U` that is flat
near every patch. -/
theorem patchCoercive_W2_flatW3 {ell M R k κ c : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell)
    {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M) (hell : 2 ≤ ell) (hR1 : 1 ≤ R)
    (hR4 : (c + 4) * κ * ell ≤ R) (hroom : 17 * ell ≤ R * M) {d : ℕ} (hdM : d + 32 * ell ^ 2 ≤ κ * M)
    {W : ℕ} (hW : 1 ≤ W) (hWR : W ≤ R * M * ell)
    (U : LinkCfg (scaleUp ell k Lu)) (a cs : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hreg : HolRegime S ell k U ρ) (ε1 : ℝ) (hε1 : 0 < ε1) (hη : etaC ell W cs ρ ε1 < 1)
    (hflat : ∀ j w, IsPatch ell M k κ S j w → ∀ e : Bond (scaleUp ell k Lu),
      pdist w e.1 ≤ (c + 1) * gsp ell M κ j → U e = (flatCfg : Cfg (scaleUp ell k Lu)) e)
    (hF : W3FlatStmt ell hell0 a) (δ : ℝ)
    (hDec : OptDecayAt ell (scaleUp ell k Lu) (flatCfg : Cfg (scaleUp ell k Lu)) δ d) :
    ∃ cW : ℝ, 0 < cW ∧
      PatchCoercive ell M k κ c Lu hell0 S U a Lam ((1 - etaC ell W cs ρ ε1) * min a (cW - δ) - 2 * nuC ell ρ) := by
  obtain ⟨cW, hcW, hall⟩ := w3G0_of_flat ell hell0 a hp.ha.le hF
  exact ⟨cW, hcW, patchCoercive_W2 hell0 hS hκ hM hell hR1 hR4 hroom hdM hW hWR U a cs Lam hp ρ hρ hreg ε1 hε1 hη
    (fun _ _ => (flatCfg : Cfg (scaleUp ell k Lu))) hflat cW δ (fun _ _ _ => hall _) (fun _ _ _ => hDec)⟩

end AdalyFormal.M1W2

#print axioms AdalyFormal.M1W2.ginv_eq_G0_flat
#print axioms AdalyFormal.M1W2.exists_scaleUp
#print axioms AdalyFormal.M1W2.w3G0_of_flat
#print axioms AdalyFormal.M1W2.patchCoercive_W2_flatW3
