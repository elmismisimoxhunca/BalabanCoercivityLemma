import TD3

/-!
# TD4 -- mixed, fixed-factor and frozen forms in two-domain form (lane two_domain_20261019)
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

/-- the mixed per-cube-factor headline, two-domain form -/
def MixedTwoDom : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ Φ : Set ℕ, (∀ f ∈ Φ, 10 ≤ f) → ∀ m : ℕ, m₁ ≤ m → ∀ R0 : ℕ, R₁ ≤ R0 →
        ∀ Rs : ℕ → ℕ, (∀ j, 1 ≤ j → R0 ≤ Rs j) → ∀ RL : ℕ, R0 ≤ RL →
        ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        (∀ f ∈ Φ, (f : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀) →
          TorusOK ell (ell ^ m) Lu →
          ∀ (S : Tower (scaleUp ell k Lu)), AdmSplitNB ell (ell ^ m) R0 Rs k S →
          ∀ (Sc : Tower (scaleUp ell k Lu)), (∀ j : ℕ, 1 ≤ j → Sc.Om j = S.Om j) → S.Om 0 ⊆ Sc.Om 0 →
          ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) RL k S Lam →
          ∀ (U : LinkCfg (scaleUp ell k Lu)),
            MXP.AllC.ClassCoupledΦ ell (ell ^ m) Φ k Sc α₀ ((ell : ℝ) ^ k)⁻¹ U →
            InstAtWD ell k (by omega) a Lu γ₀ S Lam U

theorem mixedTwoDom : MixedTwoDom := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hF⟩ := famTwoDom_box ell hell a ha
  refine ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, ?_⟩
  intro Φ hΦ m hm R0 hR0 Rs hR RL hRL k hk Lu α₀ hα hsm hT S hS Sc hag hsub Lam hL U hU
  obtain ⟨⟨c1, c2⟩, c3⟩ := hU
  let FΦ : CubeFam (scaleUp ell k Lu) := {t | t.2.2 ∈ Φ ∧ IsClassCube ell (ell ^ m) t.2.2 k Sc t.1 t.2.1}
  refine hF m hm R0 hR0 Rs hR RL hRL k hk Lu α₀ hα FΦ (fun s j f hmem => ⟨hΦ f hmem.1, hsm f hmem.1⟩) hT S hS Sc hag hsub Lam hL U ?_
  refine ⟨fun x hx => ?_, fun p hp => ?_, fun f sites j hmem hq => ?_⟩
  · obtain ⟨sites, j, ⟨f, hfΦ, hq⟩, hxs⟩ := c1 x hx
    exact ⟨sites, j, ⟨f, ⟨hfΦ, hq⟩, hq⟩, hxs⟩
  · obtain ⟨sites, j, ⟨f, hfΦ, hq⟩, hcb⟩ := c2 p hp
    exact ⟨sites, j, ⟨f, ⟨hfΦ, hq⟩, hq⟩, hcb⟩
  · exact (perCubeRegular2_iff.1 (c3 f hmem.1)) sites j hq

/-- the fixed-factor headline, two-domain form -/
def TotalTwoDom : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ c : ℕ, 10 ≤ c → ∀ m : ℕ, m₁ ≤ m → ∀ R0 : ℕ, R₁ ≤ R0 → ∀ Rs : ℕ → ℕ, (∀ j, 1 ≤ j → R0 ≤ Rs j) → ∀ RL : ℕ, R0 ≤ RL →
        ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        (c : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
          TorusOK ell (ell ^ m) Lu →
          ∀ (S : Tower (scaleUp ell k Lu)), AdmSplitNB ell (ell ^ m) R0 Rs k S →
          ∀ (Sc : Tower (scaleUp ell k Lu)), (∀ j : ℕ, 1 ≤ j → Sc.Om j = S.Om j) → S.Om 0 ⊆ Sc.Om 0 →
          ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) RL k S Lam →
          ∀ (U : LinkCfg (scaleUp ell k Lu)),
            ClassCoupled ell (ell ^ m) c k Sc α₀ ((ell : ℝ) ^ k)⁻¹ U →
            InstAtWD ell k (by omega) a Lu γ₀ S Lam U

theorem totalTwoDom : TotalTwoDom := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hT⟩ := mixedTwoDom ell hell a ha
  refine ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, ?_⟩
  intro c hc m hm R0 hR0 Rs hR RL hRL k hk Lu α₀ hα h2 hTor S hS Sc hag hsub Lam hL U hU
  exact hT {c} (fun f hf => by rw [Set.mem_singleton_iff] at hf; omega) m hm R0 hR0 Rs hR RL hRL k hk Lu α₀ hα
    (fun f hf => by rw [Set.mem_singleton_iff] at hf; subst hf; exact h2) hTor S hS Sc hag hsub Lam hL U
    (MXP.AllC.classCoupledΦ_single.2 hU)

/-- the frozen `P428Target8` (cube factor `12`, `InstIneq` conclusion), two-domain form: operators on `S` (`AdmNoBase`, one radius), class read from `Sc`. -/
def Target8TwoDom : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      SidePow6 ell (ell ^ m) a ∧ ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
        ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
          TorusOK ell (ell ^ m) Lu → ∀ (S : Tower (scaleUp ell k Lu)), AdalyFormal.ThinLayer.AdmNoBase ell (ell ^ m) R k S →
          ∀ (Sc : Tower (scaleUp ell k Lu)), (∀ j : ℕ, 1 ≤ j → Sc.Om j = S.Om j) → S.Om 0 ⊆ Sc.Om 0 →
          ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam →
          ∀ (U : LinkCfg (scaleUp ell k Lu)), ClassCoupled ell (ell ^ m) 12 k Sc α₀ ((ell : ℝ) ^ k)⁻¹ U →
            InstIneq ell k (by omega) a Lu γ₀ S Lam U

theorem target8TwoDom : Target8TwoDom := by
  intro ell hell a ha
  obtain ⟨m₀', hm₀', h⟩ := AdalyFormal.ThinLayer.target8Layer ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hT⟩ := totalTwoDom ell hell a ha
  refine ⟨max m₀' m₁, le_trans hm₀' (le_max_left _ _), fun m hm => ?_⟩
  obtain ⟨R₀', hR₀'⟩ := h m (le_trans (le_max_left _ _) hm)
  refine ⟨max R₀' R₁, fun R hR => ?_⟩
  obtain ⟨hp, -⟩ := hR₀' R (le_trans (le_max_left _ _) hR)
  refine ⟨hp, a₀, ha₀, γ₀, hγ, fun k hk Lu α₀ hα h12 hTor S hS Sc hag hsub Lam hL U hU => ?_⟩
  have hS' : AdmSplitNB ell (ell ^ m) R (fun _ => R) k S := by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hS
    exact ⟨h1, h2, h3, h4, h5 0 (Nat.zero_le _), fun j _ hj => h5 j hj⟩
  exact (hT 12 (by norm_num) m (le_trans (le_max_right _ _) hm) R (le_trans (le_max_right _ _) hR) (fun _ => R) (fun _ _ => le_rfl) R le_rfl
    k hk Lu α₀ hα h12 hTor S hS' Sc hag hsub Lam hL U hU).2

theorem totalLayer_of_twoDom (h : TotalTwoDom) : AdalyFormal.ThinLayer.TotalLayer := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hF⟩ := h ell hell a ha
  exact ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, fun c hc m hm R0 hR0 Rs hR RL hRL k hk Lu α₀ hα h2 hT S hS Lam hL U hU =>
    hF c hc m hm R0 hR0 Rs hR RL hRL k hk Lu α₀ hα h2 hT S hS S (fun _ _ => rfl) subset_rfl Lam hL U hU⟩

end AdalyFormal.TwoDom

#print axioms AdalyFormal.TwoDom.mixedTwoDom
#print axioms AdalyFormal.TwoDom.totalTwoDom
#print axioms AdalyFormal.TwoDom.target8TwoDom
#print axioms AdalyFormal.TwoDom.totalLayer_of_twoDom
