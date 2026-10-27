import R7Fork.ZXG3J2

/-!
# G3K -- transport between the unit torus `Lu` and the fine torus `scaleUp ell 0 Lu` at `k = 0`
(they are the same lattice; `embY` is the identity on coordinates): fields, shifts, plaquettes, curl energy.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

namespace AdalyFormal.StatementLaneG

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 curlValueCovariant RMap_one)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)

section
variable (ell : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)

/-- the unit site below a fine site at `k = 0` -/
def invSite (z' : PeriodicLatticeSite (scaleUp ell 0 Lu)) : PeriodicLatticeSite Lu :=
  fun μ => ⟨(z' μ).val, by
    have h := (z' μ).isLt
    have h2 : scaleUp ell 0 Lu μ + 1 = Lu μ + 1 := by
      have := scaleUp_succ ell 0 Lu hell μ
      simpa using this
    omega⟩

theorem embY_invSite (z' : PeriodicLatticeSite (scaleUp ell 0 Lu)) :
    embY ell 0 Lu hell (invSite ell Lu hell z') = z' := by
  funext μ; apply Fin.ext; simp [embY, invSite]

theorem invSite_embY (z : PeriodicLatticeSite Lu) : invSite ell Lu hell (embY ell 0 Lu hell z) = z := by
  funext μ; apply Fin.ext; simp [embY, invSite]

theorem shift_embY0 (z : PeriodicLatticeSite Lu) (hN : ∀ μ, 1 ≤ Lu μ) (a : Fin 3) :
    periodicLatticeShift (embY ell 0 Lu hell z) a = embY ell 0 Lu hell (periodicLatticeShift z a) := by
  have h := coarseShift_embY ell 0 Lu hell hN z a
  simpa [AdalyFormal.Balaban.CoarseCurl.coarseShift] using h

/-- the fine field carried by a unit field -/
def fineOf (B : Bond Lu → SuTwo) : BondFnL2 (scaleUp ell 0 Lu) :=
  WithLp.toLp 2 (fun b' => B (invSite ell Lu hell b'.1, b'.2))

theorem fineOf_emb (B : Bond Lu → SuTwo) (e : Bond Lu) :
    (WithLp.ofLp (fineOf ell Lu hell B)) (unitBondEmb ell 0 Lu hell e) = B e := by
  show B (invSite ell Lu hell (embY ell 0 Lu hell e.1), e.2) = B e
  rw [invSite_embY]

end

#print axioms embY_invSite
#print axioms shift_embY0
#print axioms fineOf_emb


section curl
variable (ell : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)

theorem curl_fineOf_emb (hN : ∀ μ, 1 ≤ Lu μ) (B : Bond Lu → SuTwo) (p : PeriodicLatticePlaquette Lu) :
    curlValueCovariant (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell 0 Lu))
      (WithLp.ofLp (fineOf ell Lu hell B)) (embY ell 0 Lu hell p.1, p.2) =
    curlValueCovariant (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Lu) B p := by
  unfold curlValueCovariant
  simp only [flatCfg, RMap_one]
  rw [shift_embY0 ell Lu hell p.1 hN, shift_embY0 ell Lu hell p.1 hN]
  have h1 : ∀ (w : PeriodicLatticeSite Lu) (d : Fin 3),
      (WithLp.ofLp (fineOf ell Lu hell B)) (embY ell 0 Lu hell w, d) = B (w, d) := fun w d =>
    fineOf_emb ell Lu hell B (w, d)
  rw [h1, h1, h1, h1]

theorem plaq_emb_bijective : Function.Bijective
    (fun p : PeriodicLatticePlaquette Lu => ((embY ell 0 Lu hell p.1, p.2) : PeriodicLatticePlaquette (scaleUp ell 0 Lu))) := by
  constructor
  · intro p q h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    exact Prod.ext (embY_injective ell 0 Lu hell h1) h2
  · intro p'
    exact ⟨(invSite ell Lu hell p'.1, p'.2), by simp [embY_invSite]⟩

/-- the curl energy of the carried field equals that of the unit field -/
theorem curl_energy_fineOf (hN : ∀ μ, 1 ≤ Lu μ) (B : Bond Lu → SuTwo) :
    ∑ p' : PeriodicLatticePlaquette (scaleUp ell 0 Lu),
      ‖curlValueCovariant (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell 0 Lu))
        (WithLp.ofLp (fineOf ell Lu hell B)) p'‖ ^ 2 =
    ∑ p : PeriodicLatticePlaquette Lu,
      ‖curlValueCovariant (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Lu) B p‖ ^ 2 := by
  rw [← Function.Bijective.sum_comp (plaq_emb_bijective ell Lu hell)
    (fun p' => ‖curlValueCovariant (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell 0 Lu))
        (WithLp.ofLp (fineOf ell Lu hell B)) p'‖ ^ 2)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [curl_fineOf_emb ell Lu hell hN B p]

end curl

#print axioms curl_fineOf_emb
#print axioms plaq_emb_bijective
#print axioms curl_energy_fineOf

end AdalyFormal.StatementLaneG
