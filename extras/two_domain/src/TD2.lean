import TD1

/-!
# TD2 -- the TWO-DOMAIN transfer for the printed (union) class (lane two_domain_20261019)

Two level-0 domains: the operators (`gparams`, `plaqIn (S.Om 0)`, `siteMask`) are read from the tower `S` (`Omega_0^op = S.Om 0`, an `AdmSplitNB` tower, i.e. any union of `M`-blocks
with the strict level-0 collar), the class `ClassCoupledP Cl` (cubes, coverage of sites and plaquettes, regularity) is read from a SECOND tower `Sc` (`Omega_0^cl = Sc.Om 0`) that agrees with `S`
at the levels `>= 1` and has `S.Om 0 ⊆ Sc.Om 0`.  `Sc` is not assumed admissible, block-closed or radial.

`famTwoDom_union` : the union-class family headline in this two-domain form, with the threshold `max R_1 4`.

Method: `F'` := all `S`-class unions that are regular (with a factor occurring in `F`).  A cube `C` of `Sc` at level `j >= 1` is an `S`-class union as it stands; a cube at level `0`
is cut to `C ∩ S.Om 0`; if the cut misses `B^0(S)` (a DISCONNECTED union whose part in `S.Om 1` is separated from its part in `Sc.Om 0 \ S.Om 0`) a far block `E ⊆ B^0(S)`
(`pdist >= 4` from `S.Om 1`, `far_block_exists`) is glued on (`regBody_glue`); `E` is regular because the coverage hypothesis of `Sc` covers its sites.
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

/-- **the two-domain family headline** for the class predicate `Cl`: the operators are those of the tower `S` (`AdmSplitNB`), the class hypothesis is read from `Sc`
(`Sc.Om j = S.Om j` for `j >= 1`, `S.Om 0 ⊆ Sc.Om 0`). -/
def TwoDomFamP (Cl : ClassPred) : Prop :=
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
            ClassCoupledP Cl ell (ell ^ m) F k Sc α₀ ((ell : ℝ) ^ k)⁻¹ U →
            InstAtWD ell k (by omega) a Lu γ₀ S Lam U

section union

variable {L : PeriodicLatticeExtent}

theorem bigSide_zero (M ell : ℕ) : bigSide M ell 0 = M := by simp [bigSide]

/-- the key covering lemma: a regular `Sc`-class union of level `j` whose cut to `S.Om 0` is nonempty is contained in a regular `S`-class union of the family `F'`. -/
theorem cover_cut {ell M k R0 : ℕ} {Rs : ℕ → ℕ} {S Sc : Tower L} (hM : 0 < M) (hR0 : 4 ≤ R0)
    (hS : AdmSplitNB ell M R0 Rs k S) (hag : ∀ j : ℕ, 1 ≤ j → Sc.Om j = S.Om j) (hsub : S.Om 0 ⊆ Sc.Om 0)
    {α₀ η : ℝ} (hα : 0 ≤ α₀) (hη : 0 ≤ η) {U : LinkCfg L} {F : CubeFam L}
    (hc1 : ∀ x ∈ Sc.Om 0, ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCubeP unionClass ell M F k Sc sites j ∧ x ∈ sites)
    (hc3 : ∀ (f : ℕ) (sites : Set (PeriodicLatticeSite L)) (j : ℕ), (sites, j, f) ∈ F →
      unionClass L ell M k Sc f sites j → RegBodyH ell M f sites j α₀ η U)
    {C : Set (PeriodicLatticeSite L)} {j f : ℕ} (hCF : (C, j, f) ∈ F) (hCl : IsClassUnion ell M k Sc C j)
    (hne : (C ∩ S.Om 0).Nonempty) :
    ∃ (Q : Set (PeriodicLatticeSite L)) (j' f' : ℕ), IsClassUnion ell M k S Q j' ∧ RegBodyH ell M f' Q j' α₀ η U ∧
      (∃ C' j0, (C', j0, f') ∈ F) ∧ C ∩ S.Om 0 ⊆ Q := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS
  have hanti : Antitone S.Om := antitone_nat_of_succ_le h1
  have hreg : RegBodyH ell M f C j α₀ η U := hc3 f C j hCF hCl
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · -- level 0: cut
    obtain ⟨⟨-, hbc, hsubC, w, hwC, hw0⟩, -⟩ := hCl
    obtain ⟨x, hxC, hx0⟩ := hne
    have hSc1 : Sc.Om 1 = S.Om 1 := hag 1 le_rfl
    have hSc2 : Sc.Om 2 = S.Om 2 := hag 2 (by omega)
    have hregD : RegBodyH ell M f (C ∩ S.Om 0) 0 α₀ η U := UNI.Joint.regBody_mono_sites Set.inter_subset_left hreg
    have hbcD : BlockClosed (bigSide M ell 0) (C ∩ S.Om 0) := by
      intro u hu v huv
      exact ⟨hbc u hu.1 v huv, h4 0 (Nat.zero_le _) u hu.2 v huv⟩
    have hsubD : C ∩ S.Om 0 ⊆ towerBj S 0 ∪ towerBj S 1 := by
      intro y hy
      rcases hsubC hy.1 with h | h
      · left
        refine ⟨hy.2, ?_⟩
        rw [← hSc1]; exact h.2
      · right
        unfold towerBj at h ⊢
        rw [hSc1, hSc2] at h
        exact h
    by_cases hmeet : ((C ∩ S.Om 0) ∩ towerBj S 0).Nonempty
    · have hu : UnionAt ell M k S (C ∩ S.Om 0) 0 := ⟨Nat.zero_le _, hbcD, hsubD, hmeet⟩
      exact ⟨C ∩ S.Om 0, 0, f, isClassUnion_of_unionAt h1 hu, hregD, ⟨C, 0, hCF⟩, subset_rfl⟩
    · -- the cut misses B^0: it lies in B^1 ⊆ Om 1
      have hD1 : ∀ y ∈ C ∩ S.Om 0, y ∈ S.Om 1 := by
        intro y hy
        rcases hsubD hy with h | h
        · exact absurd ⟨y, hy, h⟩ hmeet
        · exact h.1
      have hwS : w ∉ S.Om 0 := by
        intro hw
        apply hmeet
        refine ⟨w, ⟨hwC, hw⟩, hw, ?_⟩
        rw [← hSc1]; exact hw0.2 ∘ id
      have hx1 : x ∈ S.Om 1 := hD1 x ⟨hxC, hx0⟩
      have h5' : ∀ z : PeriodicLatticeSite L, z ∉ S.Om 0 → ∀ y ∈ S.Om 1, R0 * M < pdist z y := by
        intro z hz y hy
        have := h5 z hz y hy
        rwa [bigSide_zero] at this
      obtain ⟨v, hv0, hvfar⟩ := far_block_exists hM hR0 h5' hx1 hwS
      have hv1 : v ∉ S.Om 1 := fun h => by
        have := hvfar v h
        rw [pd_self] at this
        omega
      have h40 := h4 0 (Nat.zero_le _)
      rw [bigSide_zero] at h40
      have hbcD' := hbcD
      rw [bigSide_zero] at hbcD'
      have hEsub0 : ∀ u ∈ blockOf M v, u ∈ S.Om 0 := fun u hu => h40 v hv0 u (fun μ => hu μ)
      have hEsep : ∀ u ∈ blockOf M v, ∀ y ∈ S.Om 1, 4 ≤ pdist u y := by
        intro u hu y hy
        have b1 := pdist_block_le hM hu
        have t1 := pd_tri v u y
        have c1 := pd_comm v u
        have f1 := hvfar y hy
        omega
      have hu1 : ∀ u ∈ blockOf M v, u ∉ S.Om 1 := fun u hu h => by
        have := hEsep u hu u h
        rw [pd_self] at this
        omega
      have hsep : ∀ s ∈ C ∩ S.Om 0, ∀ t ∈ blockOf M v, 4 ≤ pdist s t := by
        intro s hs t ht
        rw [pd_comm]
        exact hEsep t ht s (hD1 s hs)
      -- the coverage hypothesis of `Sc` covers `v`
      obtain ⟨Cu, ju, ⟨fu, hfu, hqu⟩, hvCu⟩ := hc1 v (hsub hv0)
      have hqu' : IsClassUnion ell M k Sc Cu ju := hqu
      obtain rfl : ju = 0 := by
        by_contra hju
        have hj1 : 1 ≤ ju := Nat.one_le_iff_ne_zero.2 hju
        rcases hqu'.1.2.2.1 hvCu with h | h
        · apply hv1
          have : v ∈ S.Om ju := by rw [← hag ju hj1]; exact h.1
          exact hanti hj1 this
        · apply hv1
          have : v ∈ S.Om (ju + 1) := by rw [← hag (ju + 1) (by omega)]; exact h.1
          exact hanti (by omega) this
      have hregCu : RegBodyH ell M fu Cu 0 α₀ η U := hc3 fu Cu 0 hfu hqu
      have hbcCu : BlockClosed M Cu := by
        have := hqu'.1.2.1
        rwa [bigSide_zero] at this
      have hECu : blockOf M v ⊆ Cu := fun u hu => hbcCu v hvCu u (fun μ => hu μ)
      have hregE : RegBodyH ell M fu (blockOf M v) 0 α₀ η U := UNI.Joint.regBody_mono_sites hECu hregCu
      have hregDb := regBody_mono_b (le_max_left f fu) hα hη hregD
      have hregEb := regBody_mono_b (le_max_right f fu) hα hη hregE
      have hglue := regBody_glue hsep hregDb hregEb
      have hU0 : UnionAt ell M k S ((C ∩ S.Om 0) ∪ blockOf M v) 0 := by
        refine ⟨Nat.zero_le _, ?_, ?_, ⟨v, Or.inr (mem_blockOf_self M v), hv0, hv1⟩⟩
        · rw [bigSide_zero]
          intro u hu w huv
          rcases hu with hu | hu
          · exact Or.inl (hbcD' u hu w huv)
          · exact Or.inr (blockOf_blockClosed v u hu w huv)
        · intro y hy
          rcases hy with hy | hy
          · exact hsubD hy
          · exact Or.inl ⟨hEsub0 y hy, hu1 y hy⟩
      have hbF : ∃ C' j0, (C', j0, max f fu) ∈ F := by
        rcases max_choice f fu with h | h
        · rw [h]; exact ⟨C, 0, hCF⟩
        · rw [h]; exact ⟨Cu, 0, hfu⟩
      exact ⟨(C ∩ S.Om 0) ∪ blockOf M v, 0, max f fu, isClassUnion_of_unionAt h1 hU0, hglue, hbF, Set.subset_union_left⟩
  · -- level >= 1: the cube is an S-class union as it stands
    obtain ⟨hU0, -⟩ := hCl
    have e1 : towerBj Sc j = towerBj S j := by
      unfold towerBj; rw [hag j hj, hag (j + 1) (by omega)]
    have e2 : towerBj Sc (j + 1) = towerBj S (j + 1) := by
      unfold towerBj; rw [hag (j + 1) (by omega), hag (j + 1 + 1) (by omega)]
    obtain ⟨hjk, hbc, hsubC, hnn⟩ := hU0
    rw [e1, e2] at hsubC
    rw [e1] at hnn
    have hu : UnionAt ell M k S C j := ⟨hjk, hbc, hsubC, hnn⟩
    exact ⟨C, j, f, isClassUnion_of_unionAt h1 hu, hreg, ⟨C, j, hCF⟩, Set.inter_subset_left⟩

/-- **`famTwoDom_union`**: the union-class family headline with the operators on `S` (`Omega_0^op`) and the class read from `Sc` (`Omega_0^cl ⊇ Omega_0^op`).  The threshold is `max R_1 4`. -/
theorem famTwoDom_union : TwoDomFamP unionClass := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hF⟩ := AdalyFormal.ThinLayer.famTorusLayer_union ell hell a ha
  refine ⟨m₁, hm₁, max R₁ 4, a₀, ha₀, γ₀, hγ, ?_⟩
  intro m hm R0 hR0 Rs hR RL hRL k hk Lu α₀ hα F hFs hT S hS Sc hag hsub Lam hL U hU
  have hM : 0 < ell ^ m := pow_pos (by omega) m
  have hR4 : 4 ≤ R0 := le_trans (le_max_right _ _) hR0
  have hη : (0 : ℝ) ≤ ((ell : ℝ) ^ k)⁻¹ := by positivity
  obtain ⟨hc1, hc2, hc3⟩ := hU
  let F' : CubeFam (scaleUp ell k Lu) :=
    {t | IsClassUnion ell (ell ^ m) k S t.1 t.2.1 ∧ RegBodyH ell (ell ^ m) t.2.2 t.1 t.2.1 α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
      ∃ (C : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j0 : ℕ), (C, j0, t.2.2) ∈ F}
  have hFs' : ∀ (s : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j f : ℕ), (s, j, f) ∈ F' →
      10 ≤ f ∧ (f : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ := by
    intro s j f hmem
    obtain ⟨-, -, C, j0, hCF⟩ := hmem
    exact hFs C j0 f hCF
  have hU' : ClassCoupledP unionClass ell (ell ^ m) F' k S α₀ ((ell : ℝ) ^ k)⁻¹ U := by
    refine ⟨fun x hx => ?_, fun p hp => ?_, fun f sites j hmem _ => hmem.2.1⟩
    · obtain ⟨C, j, ⟨f, hf, hq⟩, hxC⟩ := hc1 x (hsub hx)
      obtain ⟨Q, j', f', hQ, hreg, hF'm, hCQ⟩ := cover_cut hM hR4 hS hag hsub hα.le hη hc1 hc3 hf hq ⟨x, hxC, hx⟩
      exact ⟨Q, j', ⟨f', ⟨hQ, hreg, hF'm⟩, hQ⟩, hCQ ⟨hxC, hx⟩⟩
    · have hp' : ∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond (Sc.Om 0) e :=
        fun e he => ⟨hsub (hp e he).1, hsub (hp e he).2⟩
      obtain ⟨C, j, ⟨f, hf, hq⟩, hcb⟩ := hc2 p hp'
      have he0 : ((p.1, p.2.1.1) : PeriodicLatticeEdge (scaleUp ell k Lu)) ∈ periodicPlaquetteBoundaryEdges p := by
        simp [periodicPlaquetteBoundaryEdges]
      obtain ⟨Q, j', f', hQ, hreg, hF'm, hCQ⟩ :=
        cover_cut hM hR4 hS hag hsub hα.le hη hc1 hc3 hf hq ⟨_, (hcb _ he0).1, (hp _ he0).1⟩
      exact ⟨Q, j', ⟨f', ⟨hQ, hreg, hF'm⟩, hQ⟩, fun e he =>
        ⟨hCQ ⟨(hcb e he).1, (hp e he).1⟩, hCQ ⟨(hcb e he).2, (hp e he).2⟩⟩⟩
  exact hF m hm R0 (le_trans (le_max_left _ _) hR0) Rs hR RL hRL k hk Lu α₀ hα F' hFs' hT S hS Lam hL U hU'

end union

end AdalyFormal.TwoDom

#print axioms AdalyFormal.TwoDom.cover_cut
#print axioms AdalyFormal.TwoDom.famTwoDom_union
