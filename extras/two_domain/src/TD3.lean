import TD2

/-!
# TD3 -- the other classes in two-domain form (lane two_domain_20261019)

* `famTwoDom_cap`    : the p.408 cap class (`ClassCoupledCap`, level-0 boxes may leave `Omega_0`, regularity on `cube ∩ Omega_0`) read from `Sc`.  `DescribedAtAlt` does not see `Om 0`, and the regularity
                       clause is monotone in `Om 0`, so `ClassCoupledCap .. Sc` implies `ClassCoupledCap .. S`.
* `famTwoDom_box`    : the box class (`boxClass`, cubes `z + f M ell^j`), from the cap form (a level-0 box of `Sc` is a `DescribedAt0` box of `S`).
* `mixedTwoDom`, `totalTwoDom`, `target8TwoDom` : the mixed / fixed-factor / frozen forms, from the box family.
-/
set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 8000

namespace AdalyFormal.TwoDom

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open UNI.AllC UNI.Total
open AdalyFormal.ThinLayer (AdmSplitNB)
open AdalyFormal.L0C
open AdalyFormal.P409L (DescribedAt0)

variable {L : PeriodicLatticeExtent}

/-- a level-`0` described cube of `Sc` is a `DescribedAt0` box of `S` -/
theorem descAt0_of_described {ell M f k : ℕ} {S Sc : Tower L} (hag : ∀ j : ℕ, 1 ≤ j → Sc.Om j = S.Om j)
    {C : Set (PeriodicLatticeSite L)} (hd : DescribedAt ell M f k Sc C 0) : DescribedAt0 ell M f S C := by
  obtain ⟨-, hbox, hsub, w, hwC, hw0⟩ := hd
  have h1 : Sc.Om 1 = S.Om 1 := hag 1 le_rfl
  have h2 : Sc.Om 2 = S.Om 2 := hag 2 (by omega)
  refine ⟨hbox, ?_, w, hwC, ?_⟩
  · intro y hy
    rcases hsub hy with h | h
    · left; intro h'; exact h.2 (by rw [h1]; exact h')
    · right; unfold towerBj at h ⊢; rw [h1, h2] at h; exact h
  · intro h'; exact hw0.2 (by rw [h1]; exact h')

/-- the descriptor of the altered class does not distinguish `S` from `Sc` -/
theorem descAlt_congr {ell M f k : ℕ} {S Sc : Tower L} (hag : ∀ j : ℕ, 1 ≤ j → Sc.Om j = S.Om j)
    {C : Set (PeriodicLatticeSite L)} {j : ℕ} :
    DescribedAtAlt ell M f k Sc C j ↔ DescribedAtAlt ell M f k S C j := by
  have h1 : Sc.Om 1 = S.Om 1 := hag 1 le_rfl
  have h2 : Sc.Om 2 = S.Om 2 := hag 2 (by omega)
  have e0 : DescribedAt0 ell M f Sc C ↔ DescribedAt0 ell M f S C := by
    unfold DescribedAt0 towerBj
    rw [h1, h2]
  have ej : 1 ≤ j → (DescribedAt ell M f k Sc C j ↔ DescribedAt ell M f k S C j) := by
    intro hj
    unfold DescribedAt towerBj
    rw [hag j hj, hag (j + 1) (by omega), hag (j + 1 + 1) (by omega)]
  unfold DescribedAtAlt
  constructor
  · rintro (⟨h0, h⟩ | ⟨hj, h⟩)
    · exact Or.inl ⟨h0, e0.1 h⟩
    · exact Or.inr ⟨hj, (ej hj).1 h⟩
  · rintro (⟨h0, h⟩ | ⟨hj, h⟩)
    · exact Or.inl ⟨h0, e0.2 h⟩
    · exact Or.inr ⟨hj, (ej hj).2 h⟩

/-- the cap headline, two-domain form -/
def TwoDomCapP : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ m : ℕ, m₁ ≤ m → ∀ R0 : ℕ, R₁ ≤ R0 → ∀ Rs : ℕ → ℕ, (∀ j, 1 ≤ j → R0 ≤ Rs j) → ∀ RL : ℕ, R0 ≤ RL →
        ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        ∀ F : CubeFam (scaleUp ell k Lu),
          (∀ (s : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j f : ℕ), (s, j, f) ∈ F →
            10 ≤ f ∧ (f : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀) →
          TorusOK ell (ell ^ m) Lu →
          ∀ (S : Tower (scaleUp ell k Lu)), AdmSplitNB ell (ell ^ m) R0 Rs k S →
          ∀ (Sc : Tower (scaleUp ell k Lu)), (∀ j : ℕ, 1 ≤ j → Sc.Om j = S.Om j) → S.Om 0 ⊆ Sc.Om 0 →
          ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) RL k S Lam →
          ∀ (U : LinkCfg (scaleUp ell k Lu)),
            ClassCoupledCap ell (ell ^ m) F k Sc α₀ ((ell : ℝ) ^ k)⁻¹ U →
            InstAtWD ell k (by omega) a Lu γ₀ S Lam U

theorem classCoupledCap_of_two {ell M k : ℕ} {F : CubeFam L} {S Sc : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (hag : ∀ j : ℕ, 1 ≤ j → Sc.Om j = S.Om j) (hsub : S.Om 0 ⊆ Sc.Om 0)
    (h : ClassCoupledCap ell M F k Sc α₀ η U) : ClassCoupledCap ell M F k S α₀ η U := by
  obtain ⟨c1, c2, c3⟩ := h
  refine ⟨fun x hx => ?_, fun p hp => ?_, fun f sites j hmem hd => ?_⟩
  · obtain ⟨sites, j, ⟨f, hf, hq⟩, hxs⟩ := c1 x (hsub hx)
    exact ⟨sites, j, ⟨f, hf, descAlt_congr hag |>.1 hq⟩, hxs⟩
  · obtain ⟨sites, j, ⟨f, hf, hq⟩, hcb⟩ := c2 p (fun e he => ⟨hsub (hp e he).1, hsub (hp e he).2⟩)
    exact ⟨sites, j, ⟨f, hf, descAlt_congr hag |>.1 hq⟩, hcb⟩
  · exact UNI.Joint.regBody_mono_sites (Set.inter_subset_inter_right _ hsub) (c3 f sites j hmem (descAlt_congr hag |>.2 hd))

theorem famTwoDom_cap : TwoDomCapP := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hF⟩ := AdalyFormal.ThinLayer.famTorusLayerCap ell hell a ha
  refine ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, ?_⟩
  intro m hm R0 hR0 Rs hR RL hRL k hk Lu α₀ hα F hFs hT S hS Sc hag hsub Lam hL U hU
  exact hF m hm R0 hR0 Rs hR RL hRL k hk Lu α₀ hα F hFs hT S hS Lam hL U (classCoupledCap_of_two hag hsub hU)

/-- the box headline, two-domain form (the class of cubes `z + f M ell^j` read from `Sc`) -/
theorem famTwoDom_box : TwoDomFamP boxClass := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hF⟩ := AdalyFormal.ThinLayer.famTorusLayerCap ell hell a ha
  refine ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, ?_⟩
  intro m hm R0 hR0 Rs hR RL hRL k hk Lu α₀ hα F hFs hT S hS Sc hag hsub Lam hL U hU
  obtain ⟨c1, c2, c3⟩ := hU
  let F3 : CubeFam (scaleUp ell k Lu) := {t | t ∈ F ∧ IsClassCube ell (ell ^ m) t.2.2 k Sc t.1 t.2.1}
  have hdesc : ∀ (f : ℕ) (C : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ),
      DescribedAt ell (ell ^ m) f k Sc C j → DescribedAtAlt ell (ell ^ m) f k S C j := by
    intro f C j hd
    by_cases hj : j = 0
    · subst hj; exact Or.inl ⟨rfl, descAt0_of_described hag hd⟩
    · exact (descAlt_congr hag).1 (Or.inr ⟨by omega, hd⟩)
  have hcap : ClassCoupledCap ell (ell ^ m) F3 k S α₀ ((ell : ℝ) ^ k)⁻¹ U := by
    refine ⟨fun x hx => ?_, fun p hp => ?_, fun f sites j hmem _ => ?_⟩
    · obtain ⟨sites, j, ⟨f, hf, hq⟩, hxs⟩ := c1 x (hsub hx)
      exact ⟨sites, j, ⟨f, ⟨hf, hq⟩, hdesc f sites j hq.1⟩, hxs⟩
    · obtain ⟨sites, j, ⟨f, hf, hq⟩, hcb⟩ := c2 p (fun e he => ⟨hsub (hp e he).1, hsub (hp e he).2⟩)
      exact ⟨sites, j, ⟨f, ⟨hf, hq⟩, hdesc f sites j hq.1⟩, hcb⟩
    · exact UNI.Joint.regBody_mono_sites Set.inter_subset_left (c3 f sites j hmem.1 hmem.2)
  exact hF m hm R0 hR0 Rs hR RL hRL k hk Lu α₀ hα F3 (fun s j f hmem => hFs s j f hmem.1) hT S hS Lam hL U hcap

/-- consistency: taking `Sc := S` the two-domain headline contains the one-domain headline of lane thin_layer (same constants) -/
theorem oneDom_of_twoDom {Cl : ClassPred} (h : TwoDomFamP Cl) : AdalyFormal.ThinLayer.FamTorusLayerP Cl := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hF⟩ := h ell hell a ha
  exact ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, fun m hm R0 hR0 Rs hR RL hRL k hk Lu α₀ hα F hFs hT S hS Lam hL U hU =>
    hF m hm R0 hR0 Rs hR RL hRL k hk Lu α₀ hα F hFs hT S hS S (fun _ _ => rfl) subset_rfl Lam hL U hU⟩

theorem oneDomCap_of_twoDom (h : TwoDomCapP) : AdalyFormal.ThinLayer.FamTorusCapLayer := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hF⟩ := h ell hell a ha
  exact ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, fun m hm R0 hR0 Rs hR RL hRL k hk Lu α₀ hα F hFs hT S hS Lam hL U hU =>
    hF m hm R0 hR0 Rs hR RL hRL k hk Lu α₀ hα F hFs hT S hS S (fun _ _ => rfl) subset_rfl Lam hL U hU⟩

end AdalyFormal.TwoDom

#print axioms AdalyFormal.TwoDom.famTwoDom_cap
#print axioms AdalyFormal.TwoDom.famTwoDom_box
#print axioms AdalyFormal.TwoDom.oneDom_of_twoDom
#print axioms AdalyFormal.TwoDom.oneDomCap_of_twoDom
