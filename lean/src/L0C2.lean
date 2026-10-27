import L0C1
import UNI_Red

/-!
# L0C2 -- the headline for the class with p.408 level-0 cubes (lane level0_class_20261019)

Class `level0ClassW`: a level-0 cube is `DescribedAt0` (grid box of side `f M`, `sites ⊆ (Omega_1)^c ∪ B^1`, meets `(Omega_1)^c`; may leave `Omega_0`);
a cube of index `i ≥ 1` is the original `DescribedAt`.  No index-uniqueness clause (`level0Class` adds it; the two coincide on admissible towers).
`FamTorusP level0ClassW` follows from the union headline by intersecting each level-0 cube with the global `Omega_0`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.L0C

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.P409L (DescribedAt0)
open UNI.AllC UNI.Total

variable {L : PeriodicLatticeExtent}

/-- descriptor of the altered class at index `i`: `i = 0` p.408 reading `B^0 := T_1 \ Omega_1`; `i ≥ 1` the original `DescribedAt`. -/
def DescribedAtAlt (ell M f k : ℕ) (S : Tower L) (sites : Set (PeriodicLatticeSite L)) (i : ℕ) : Prop :=
  (i = 0 ∧ DescribedAt0 ell M f S sites) ∨ (1 ≤ i ∧ DescribedAt ell M f k S sites i)

/-- the altered class with the unique-index clause of p.396. -/
def IsClassCubeAlt (ell M f k : ℕ) (S : Tower L) (sites : Set (PeriodicLatticeSite L)) (j : ℕ) : Prop :=
  DescribedAtAlt ell M f k S sites j ∧ ∀ i : ℕ, DescribedAtAlt ell M f k S sites i → i = j

/-- wide altered class (descriptor only). -/
def level0ClassW : ClassPred := fun L ell M k S f sites j => DescribedAtAlt ell M f k S sites j

/-- altered class with unique index. -/
def level0Class : ClassPred := fun L ell M k S f sites j => IsClassCubeAlt ell M f k S sites j

/-- the altered headline hypotheses for the wide class: the headline `FamTorusP level0ClassW`. -/
def Level0HeadlineW : Prop := FamTorusP level0ClassW

def Level0Headline : Prop := FamTorusP level0Class

/-- index uniqueness of the altered class is automatic on a monotone tower. -/
theorem alt_unique {ell M f k : ℕ} {S : Tower L} (hmono : ∀ j, S.Om (j + 1) ⊆ S.Om j)
    {sites : Set (PeriodicLatticeSite L)} {i j : ℕ}
    (hi : DescribedAtAlt ell M f k S sites i) (hj : DescribedAtAlt ell M f k S sites j) : i = j := by
  have hanti : Antitone S.Om := antitone_nat_of_succ_le hmono
  have key : ∀ {n : ℕ}, 1 ≤ n → DescribedAt0 ell M f S sites → DescribedAt ell M f k S sites n → False := by
    intro n hn h0 hd
    obtain ⟨-, -, hsub, -⟩ := hd
    obtain ⟨-, -, y, hy, hy1⟩ := h0
    rcases hsub hy with h | h
    · exact hy1 (hanti hn h.1)
    · exact hy1 (hanti (by omega : 1 ≤ n + 1) h.1)
  rcases hi with ⟨hi0, hi⟩ | ⟨hi1, hi⟩ <;> rcases hj with ⟨hj0, hj⟩ | ⟨hj1, hj⟩
  · omega
  · exact (key hj1 hi hj).elim
  · exact (key hi1 hj hi).elim
  · exact (AdalyFormal.Thin.isClassCube_of_described hmono hi).2 j hj |>.symm

theorem level0Class_iff {ell M R k f : ℕ} {S : Tower L} (hS : Admissible ell M R k S)
    (sites : Set (PeriodicLatticeSite L)) (j : ℕ) :
    IsClassCubeAlt ell M f k S sites j ↔ DescribedAtAlt ell M f k S sites j :=
  ⟨fun h => h.1, fun h => ⟨h, fun i hi => alt_unique hS.1 hi h⟩⟩

/-- a smaller class gives a weaker headline: the larger class headline implies the smaller. -/
theorem famTorusP_sub {Cl1 Cl2 : ClassPred}
    (hsub : ∀ (ell m R k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu)),
      Admissible ell (ell ^ m) R k S → ∀ (f : ℕ) (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ),
        Cl2 (scaleUp ell k Lu) ell (ell ^ m) k S f sites j → Cl1 (scaleUp ell k Lu) ell (ell ^ m) k S f sites j)
    (h : FamTorusP Cl1) : FamTorusP Cl2 := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hF⟩ := h ell hell a ha
  refine ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, fun m hm R hR k hk Lu α₀ hα F hFs hT S hS Lam hL U hU => ?_⟩
  let F' : CubeFam (scaleUp ell k Lu) := {t | t ∈ F ∧ Cl2 (scaleUp ell k Lu) ell (ell ^ m) k S t.2.2 t.1 t.2.1}
  refine hF m hm R hR k hk Lu α₀ hα F' (fun s j f hmem => hFs s j f hmem.1) hT S hS Lam hL U ?_
  obtain ⟨c1, c2, c3⟩ := hU
  refine ⟨fun x hx => ?_, fun p hp => ?_, fun f sites j hmem _ => c3 f sites j hmem.1 hmem.2⟩
  · obtain ⟨sites, j, ⟨f, hf, hq⟩, hx'⟩ := c1 x hx
    exact ⟨sites, j, ⟨f, ⟨hf, hq⟩, hsub ell m R k Lu S hS f sites j hq⟩, hx'⟩
  · obtain ⟨sites, j, ⟨f, hf, hq⟩, hx'⟩ := c2 p hp
    exact ⟨sites, j, ⟨f, ⟨hf, hq⟩, hsub ell m R k Lu S hS f sites j hq⟩, hx'⟩

/-- the intersection of a `DescribedAt0` cube with `Omega_0` is a class union of index `0` (when it is nonempty). -/
theorem unionAt_cap {ell M R k f : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hM : 0 < M) (hMR : 1 ≤ R * M)
    {C : Set (PeriodicLatticeSite L)} (hC : DescribedAt0 ell M f S C) {x : PeriodicLatticeSite L}
    (hxC : x ∈ C) (hx0 : x ∈ S.Om 0) :
    UnionAt ell M k S (C ∩ S.Om 0) 0 := by
  obtain ⟨⟨z, hz, hCz⟩, hsub, w, hwC, hw1⟩ := hC
  have hb0 : bigSide M ell 0 = M := by simp [bigSide]
  refine ⟨Nat.zero_le _, ?_, ?_, ?_⟩
  · -- block closed
    have hbox : BlockClosed M C := by
      rw [hCz]
      apply box_blockClosed hM (fun μ => by simpa [hb0] using hS.2.2.1 0 (Nat.zero_le _) μ)
      · simpa [hb0] using hz
      · rw [hb0]; exact Dvd.intro_left _ rfl
    have hom : BlockClosed M (S.Om 0) := by simpa [hb0] using hS.2.2.2.1 0 (Nat.zero_le _)
    rw [hb0]
    intro u hu v huv
    exact ⟨hbox u hu.1 v huv, hom u hu.2 v huv⟩
  · intro y hy
    rcases hsub hy.1 with h | h
    · exact Or.inl ⟨hy.2, h⟩
    · exact Or.inr h
  · by_cases hx1 : x ∈ S.Om 1
    · -- walk from x to w inside the box
      rw [hCz] at hxC hwC
      obtain ⟨u, hu, hu0, hu1⟩ := path_exists hS hMR hxC hx1 _ w hwC rfl hw1
      exact ⟨u, ⟨by rw [hCz]; exact hu, hu0⟩, hu0, hu1⟩
    · exact ⟨x, ⟨hxC, hx0⟩, hx0, hx1⟩

/-- original descriptor => altered descriptor. -/
theorem descAlt_of_desc {ell M f k : ℕ} {S : Tower L} {sites : Set (PeriodicLatticeSite L)} {j : ℕ}
    (hd : DescribedAt ell M f k S sites j) : DescribedAtAlt ell M f k S sites j := by
  by_cases hj : j = 0
  · subst hj
    obtain ⟨-, hbox, hsub, y, hy, hyb⟩ := hd
    refine Or.inl ⟨rfl, hbox, ?_, y, hy, hyb.2⟩
    intro x hx
    rcases hsub hx with h | h
    · exact Or.inl h.2
    · exact Or.inr h
  · exact Or.inr ⟨by omega, hd⟩

/-- a cube of index `j ≥ 1` lies in `Omega_0`. -/
theorem alt_pos_sub {ell M R f k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) {sites : Set (PeriodicLatticeSite L)} {j : ℕ}
    (hj : 1 ≤ j) (hd : DescribedAt ell M f k S sites j) : sites ⊆ S.Om 0 := by
  have hanti : Antitone S.Om := antitone_nat_of_succ_le hS.1
  intro x hx
  rcases hd.2.2.1 hx with h | h
  · exact hanti (Nat.zero_le j) h.1
  · exact hanti (Nat.zero_le (j + 1)) h.1

/-- **the class hypothesis with regularity only on the part of the cube inside `Omega_0`** (p.396: "these regularity conditions do not impose any constraints on U outside the domain Omega_0"). -/
def ClassCoupledCap {L : PeriodicLatticeExtent} (ell M : ℕ) (F : CubeFam L) (k : ℕ) (S : Tower L) (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  (∀ x ∈ S.Om 0, ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ),
    (∃ f, (sites, j, f) ∈ F ∧ DescribedAtAlt ell M f k S sites j) ∧ x ∈ sites) ∧
  (∀ p : PeriodicLatticePlaquette L, (∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond (S.Om 0) e) →
    ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), (∃ f, (sites, j, f) ∈ F ∧ DescribedAtAlt ell M f k S sites j) ∧
      ∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond sites e) ∧
  (∀ (f : ℕ) (sites : Set (PeriodicLatticeSite L)) (j : ℕ), (sites, j, f) ∈ F →
    DescribedAtAlt ell M f k S sites j → RegBodyH ell M f (sites ∩ S.Om 0) j α₀ η U)

/-- the headline with the cap hypothesis. -/
def FamTorusCap : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, R₁ ≤ R → ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        ∀ F : CubeFam (scaleUp ell k Lu),
          (∀ (s : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j f : ℕ), (s, j, f) ∈ F →
            10 ≤ f ∧ (f : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀) →
          TorusOK ell (ell ^ m) Lu →
          ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
          ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam →
          ∀ (U : LinkCfg (scaleUp ell k Lu)),
            ClassCoupledCap ell (ell ^ m) F k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
            InstAtWD ell k (by omega) a Lu γ₀ S Lam U

theorem headline_cap (h : P428Target8FamilyTorusU) : FamTorusCap := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hF⟩ := h ell hell a ha
  refine ⟨m₁, hm₁, max R₁ 1, a₀, ha₀, γ₀, hγ, fun m hm R hR k hk Lu α₀ hα F hFs hT S hS Lam hL U hU => ?_⟩
  have hR1 : 1 ≤ R := le_trans (le_max_right _ _) hR
  have hM : 0 < ell ^ m := pow_pos (by omega) m
  have hMR : 1 ≤ R * ell ^ m := Nat.mul_pos (by omega) hM
  let F' : CubeFam (scaleUp ell k Lu) :=
    {t | (∃ C : Set (PeriodicLatticeSite (scaleUp ell k Lu)), (C, 0, t.2.2) ∈ F ∧ DescribedAt0 ell (ell ^ m) t.2.2 S C ∧
            t.2.1 = 0 ∧ t.1 = C ∩ S.Om 0) ∨
         (t ∈ F ∧ 1 ≤ t.2.1 ∧ DescribedAt ell (ell ^ m) t.2.2 k S t.1 t.2.1)}
  have hFs' : ∀ (s : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j f : ℕ), (s, j, f) ∈ F' →
      10 ≤ f ∧ (f : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ := by
    intro s j f hmem
    rcases hmem with ⟨C, hCF, -, -, -⟩ | ⟨hmF, -, -⟩
    · exact hFs C 0 f hCF
    · exact hFs s j f hmF
  have hU' : ClassCoupledU ell (ell ^ m) F' k S α₀ ((ell : ℝ) ^ k)⁻¹ U := by
    obtain ⟨c1, c2, c3⟩ := hU
    refine ⟨fun x hx => ?_, fun p hp => ?_, fun f sites' j hmem hCl => ?_⟩
    · obtain ⟨sites, j, ⟨f, hf, hq⟩, hx'⟩ := c1 x hx
      rcases hq with ⟨hj0, hd0⟩ | ⟨hj1, hd⟩
      · subst hj0
        have hu := unionAt_cap hS hM hMR hd0 hx' hx
        exact ⟨sites ∩ S.Om 0, 0, ⟨f, Or.inl ⟨sites, hf, hd0, rfl, rfl⟩, isClassUnion_of_unionAt hS.1 hu⟩, ⟨hx', hx⟩⟩
      · exact ⟨sites, j, ⟨f, Or.inr ⟨hf, hj1, hd⟩, isClassUnion_of_unionAt hS.1 (unionAt_of_described hS hd)⟩, hx'⟩
    · obtain ⟨sites, j, ⟨f, hf, hq⟩, hcb⟩ := c2 p hp
      rcases hq with ⟨hj0, hd0⟩ | ⟨hj1, hd⟩
      · subst hj0
        have he0 : ((p.1, p.2.1.1) : PeriodicLatticeEdge (scaleUp ell k Lu)) ∈ periodicPlaquetteBoundaryEdges p := by
          simp [periodicPlaquetteBoundaryEdges]
        have hx0 := (hp _ he0).1
        have hxs := (hcb _ he0).1
        have hu := unionAt_cap hS hM hMR hd0 hxs hx0
        refine ⟨sites ∩ S.Om 0, 0, ⟨f, Or.inl ⟨sites, hf, hd0, rfl, rfl⟩, isClassUnion_of_unionAt hS.1 hu⟩, ?_⟩
        intro e he
        exact ⟨⟨(hcb e he).1, (hp e he).1⟩, ⟨(hcb e he).2, (hp e he).2⟩⟩
      · exact ⟨sites, j, ⟨f, Or.inr ⟨hf, hj1, hd⟩, isClassUnion_of_unionAt hS.1 (unionAt_of_described hS hd)⟩, hcb⟩
    · rcases hmem with ⟨C, hCF, hd0, hj0, hs'⟩ | ⟨hmF, hj1, hd⟩
      · have hreg := c3 f C 0 hCF (show DescribedAtAlt ell (ell ^ m) f k S C 0 from Or.inl ⟨rfl, hd0⟩)
        subst hj0; subst hs'
        exact hreg
      · have hreg := c3 f sites' j hmF (show DescribedAtAlt ell (ell ^ m) f k S sites' j from Or.inr ⟨hj1, hd⟩)
        have hsub : sites' ⊆ S.Om 0 := alt_pos_sub hS hj1 hd
        rw [Set.inter_eq_left.2 hsub] at hreg
        exact hreg
  exact hF m hm R (le_trans (le_max_left _ _) hR) k hk Lu α₀ hα F' hFs' hT S hS Lam hL U hU'

/-- the cap headline implies the wide-class headline (regularity on the whole cube is more than regularity on its part in `Omega_0`). -/
theorem capHeadline_imp_W (h : FamTorusCap) : Level0HeadlineW := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hF⟩ := h ell hell a ha
  refine ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, fun m hm R hR k hk Lu α₀ hα F hFs hT S hS Lam hL U hU => ?_⟩
  obtain ⟨c1, c2, c3⟩ := hU
  exact hF m hm R hR k hk Lu α₀ hα F hFs hT S hS Lam hL U ⟨c1, c2, fun f sites j hmem hd =>
    UNI.Joint.regBody_mono_sites Set.inter_subset_left (c3 f sites j hmem hd)⟩

/-- the cap headline implies the original box headline (`MXQ.Total.P428Target8FamilyTorus = FamTorusP boxClass`). -/
theorem capHeadline_imp_box (h : FamTorusCap) : FamTorusP boxClass := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hF⟩ := h ell hell a ha
  refine ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, fun m hm R hR k hk Lu α₀ hα F hFs hT S hS Lam hL U hU => ?_⟩
  let F' : CubeFam (scaleUp ell k Lu) := {t | t ∈ F ∧ boxClass (scaleUp ell k Lu) ell (ell ^ m) k S t.2.2 t.1 t.2.1}
  refine hF m hm R hR k hk Lu α₀ hα F' (fun s j f hmem => hFs s j f hmem.1) hT S hS Lam hL U ?_
  obtain ⟨c1, c2, c3⟩ := hU
  refine ⟨fun x hx => ?_, fun p hp => ?_, fun f sites j hmem hAlt => ?_⟩
  · obtain ⟨sites, j, ⟨f, hf, hq⟩, hx'⟩ := c1 x hx
    exact ⟨sites, j, ⟨f, ⟨hf, hq⟩, descAlt_of_desc hq.1⟩, hx'⟩
  · obtain ⟨sites, j, ⟨f, hf, hq⟩, hx'⟩ := c2 p hp
    exact ⟨sites, j, ⟨f, ⟨hf, hq⟩, descAlt_of_desc hq.1⟩, hx'⟩
  · exact UNI.Joint.regBody_mono_sites Set.inter_subset_left (c3 f sites j hmem.1 hmem.2)

theorem headline_level0W (h : P428Target8FamilyTorusU) : Level0HeadlineW :=
  capHeadline_imp_W (headline_cap h)

theorem headline_level0 (h : P428Target8FamilyTorusU) : Level0Headline :=
  famTorusP_sub (fun ell m R k Lu S hS f sites j hc => ((level0Class_iff hS sites j).1 hc)) (headline_level0W h)

/-- **unconditional**: the cap headline (and hence the wide and unique-index headlines and the original box headline). -/
theorem cap_unconditional : FamTorusCap := headline_cap UNI.Total.p428Target8FamilyTorusU
theorem level0W_unconditional : Level0HeadlineW := capHeadline_imp_W cap_unconditional
theorem level0_unconditional : Level0Headline := headline_level0 UNI.Total.p428Target8FamilyTorusU

end AdalyFormal.L0C

#print axioms AdalyFormal.L0C.headline_cap
#print axioms AdalyFormal.L0C.capHeadline_imp_W
#print axioms AdalyFormal.L0C.capHeadline_imp_box
#print axioms AdalyFormal.L0C.cap_unconditional
#print axioms AdalyFormal.L0C.level0W_unconditional
#print axioms AdalyFormal.L0C.level0_unconditional
#print axioms AdalyFormal.L0C.alt_unique
#print axioms AdalyFormal.L0C.unionAt_cap
