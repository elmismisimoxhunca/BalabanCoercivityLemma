import THL3
import TD4

/-!
# TD6 -- the plain cut can miss `B^0` (lane two_domain_20261019)

In the slab witness geometry of TD5 (`S` = level-0 radius `R`, `Sc` = level-0 radius `Rb > R`), the union of two `M`-slabs
`C = {x | x_0 / M = ell^2 T  or  x_0 / M = ell^2 T - Rb}` is an `IsClassUnion` of index `0` for `Sc` (one slab inside `B^1`, one inside `B^0(Sc) \ Om0(S)`), its cut `C ∩ S.Om 0`
is the first slab (nonempty, inside `S.Om 1`) and is NOT a `UnionAt` of index `0` for `S` (it does not meet `B^0(S)`).  So the naive reduction `C ↦ C ∩ S.Om 0` does not map the class of `Sc`
into the class of `S` for disconnected unions: `cover_cut` (TD2) needs the glued far block.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 64000000

namespace AdalyFormal.TwoDom

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.ThinLayer (AdmSplitNB)
open AdalyFormal.NonVacC
open UNI.AllC
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

variable {L : PeriodicLatticeExtent}

/-- the slab tower of lane nonvac_c at level-0 radius `R`, layout scale `T` -/
def slabT (ell M R T : ℕ) : Tower (scaleUp ell 2 (nvcLu M T)) :=
  slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M R T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T)

theorem slabT_two {ell M R Rb T : ℕ} (hell : 2 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hRb : R < Rb) (hRbT : Rb ≤ T) (hRT : R ≤ T) (hT : 1 ≤ T) :
    AdmSplitNB ell M R (fun _ => Rb) 2 (slabT ell M R T) ∧ Admissible ell M Rb 2 (slabT ell M Rb T) ∧
    (∀ j : ℕ, 1 ≤ j → (slabT ell M Rb T).Om j = (slabT ell M R T).Om j) ∧
    (∀ x, x ∈ (slabT ell M R T).Om 0 → x ∈ (slabT ell M Rb T).Om 0) := by
  have hell0 : 0 < ell := by omega
  have G := slabGeo_inst hell hM hdvd hRT hT
  have hN : ∀ μ, scaleUp ell 2 (nvcLu M T) μ + 1 = nvcN ell M T := fun μ => scaleUp_nvc hell0 hM μ
  have hAdm := slab3_admissible G hN
  have Gb := slabGeo_inst (R := Rb) hell hM hdvd hRbT hT
  have hAdmB := slab3_admissible Gb hN
  refine ⟨?_, hAdmB, ?_, ?_⟩
  · obtain ⟨a1, a2, a3, a4, a5, -⟩ := hAdm
    obtain ⟨-, -, -, -, b5, -⟩ := hAdmB
    refine ⟨a1, a2, a3, a4, a5 0 (Nat.zero_le _), fun j hj1 hj2 x hx y hy => ?_⟩
    refine b5 j hj2 x ?_ y ?_
    · have h0 : j ≠ 0 := by omega
      simpa [slabT, slab3, h0] using hx
    · have h0 : j + 1 ≠ 0 := by omega
      simpa [slabT, slab3, h0] using hy
  · intro j hj
    have h0 : j ≠ 0 := by omega
    simp [slabT, slab3, h0]
  · intro x hx
    simp only [slabT, om0_mem] at hx ⊢
    have h1 : nvcP0 ell M Rb T ≤ nvcP0 ell M R T := by
      simp only [nvcP0]; exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_left hRb.le _)
    have h2 : nvcQ0 ell M R T ≤ nvcQ0 ell M Rb T := by
      simp only [nvcQ0]; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hRb.le) _
    omega

theorem div_eq_iff_range {M x a : ℕ} (hM : 0 < M) : x / M = a ↔ M * a ≤ x ∧ x < M * a + M := by
  constructor
  · intro h
    subst h
    have h1 := Nat.div_add_mod x M
    have h2 := Nat.mod_lt x hM
    generalize M * (x / M) = X at h1 ⊢
    omega
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · apply Nat.le_of_lt_succ
      rw [Nat.div_lt_iff_lt_mul hM]
      nlinarith
    · rw [Nat.le_div_iff_mul_le hM]
      nlinarith

theorem plain_cut_fails {ell M R Rb T : ℕ} (hell : 2 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (hRb : R < Rb) (hRbT : Rb ≤ T) (hRT : R ≤ T) (hT : 1 ≤ T) :
    ∃ C : Set (PeriodicLatticeSite (scaleUp ell 2 (nvcLu M T))),
      IsClassUnion ell M 2 (slabT ell M Rb T) C 0 ∧ (C ∩ (slabT ell M R T).Om 0).Nonempty ∧
      C ∩ (slabT ell M R T).Om 0 ⊆ (slabT ell M R T).Om 1 ∧
      ¬ UnionAt ell M 2 (slabT ell M R T) (C ∩ (slabT ell M R T).Om 0) 0 := by
  have hell0 : 0 < ell := by omega
  obtain ⟨-, hAdmB, -, -⟩ := slabT_two hell hdvd hM hRb hRbT hRT hT
  have Gb := slabGeo_inst (R := Rb) hell hM hdvd hRbT hT
  have G := slabGeo_inst hell hM hdvd hRT hT
  obtain ⟨e, he⟩ : ∃ e, e = ell ^ 2 := ⟨_, rfl⟩
  have he4 : 4 ≤ e := by rw [he]; nlinarith
  have hTe : 4 * T ≤ e * T := Nat.mul_le_mul_right T he4
  have hP0R : nvcP0 ell M R T = M * (e * T - R) := by simp only [nvcP0, he]
  have hP0b : nvcP0 ell M Rb T = M * (e * T - Rb) := by simp only [nvcP0, he]
  have hP1 : nvcP1 ell M T = M * (e * T) := by simp only [nvcP1, he]; ring
  have hP2 : nvcP2 ell M T = M * (2 * (e * T)) := by simp only [nvcP2, he]; ring
  have hQ1 : nvcQ1 ell M T = M * (5 * (e * T) + e) := by simp only [nvcQ1, he]; ring
  have hQ0R : nvcQ0 ell M R T = M * (5 * (e * T) + e + R) := by simp only [nvcQ0, he]; ring
  -- the two slabs
  let C : Set (PeriodicLatticeSite (scaleUp ell 2 (nvcLu M T))) :=
    {x | (x 0).val / M = e * T ∨ (x 0).val / M = e * T - Rb}
  have hCbc : BlockClosed M C := by
    intro x hx y hxy
    have := hxy 0
    rcases hx with hx | hx
    · left; rw [this]; exact hx
    · right; rw [this]; exact hx
  have hNN : nvcN ell M T = M * (e * (6 * T + 2)) := by simp only [nvcN, he]; ring
  -- coordinates
  have hxv : ∀ x : PeriodicLatticeSite (scaleUp ell 2 (nvcLu M T)), (x 0).val < nvcN ell M T := by
    intro x
    have h1 := (x 0).isLt
    have h2 := scaleUp_nvc (ell := ell) (T := T) hell0 hM 0
    omega
  have key1 : ∀ x : PeriodicLatticeSite (scaleUp ell 2 (nvcLu M T)), (x 0).val / M = e * T →
      nvcP1 ell M T ≤ (x 0).val ∧ (x 0).val < nvcP1 ell M T + M := by
    intro x hx
    rw [div_eq_iff_range hM] at hx
    rw [hP1]; constructor <;> nlinarith [hx.1, hx.2]
  have key2 : ∀ x : PeriodicLatticeSite (scaleUp ell 2 (nvcLu M T)), (x 0).val / M = e * T - Rb →
      nvcP0 ell M Rb T ≤ (x 0).val ∧ (x 0).val < nvcP0 ell M Rb T + M := by
    intro x hx
    rw [div_eq_iff_range hM] at hx
    rw [hP0b]; constructor <;> nlinarith [hx.1, hx.2]
  -- numeric facts
  have hP0bR : nvcP0 ell M Rb T + M ≤ nvcP0 ell M R T := by
    rw [hP0b, hP0R]
    have : e * T - Rb + 1 ≤ e * T - R := by omega
    calc M * (e * T - Rb) + M = M * (e * T - Rb + 1) := by ring
      _ ≤ M * (e * T - R) := Nat.mul_le_mul_left _ this
  have hP0R1 : nvcP0 ell M R T < nvcP1 ell M T := by
    rw [hP0R, hP1]; exact Nat.mul_lt_mul_of_pos_left (by omega) hM
  have hP1P2 : nvcP1 ell M T + M ≤ nvcP2 ell M T := by
    rw [hP1, hP2]
    calc M * (e * T) + M ≤ M * (e * T) + M * (e * T) := by
          have : M ≤ M * (e * T) := Nat.le_mul_of_pos_right M (by omega)
          omega
      _ = M * (2 * (e * T)) := by ring
  have hP1Q0 : nvcP1 ell M T + M ≤ nvcQ0 ell M R T := by
    rw [hP1, hQ0R]
    calc M * (e * T) + M = M * (e * T + 1) := by ring
      _ ≤ M * (5 * (e * T) + e + R) := Nat.mul_le_mul_left _ (by omega)
  have hP1Q1 : nvcP1 ell M T + M ≤ nvcQ1 ell M T := by
    rw [hP1, hQ1]
    calc M * (e * T) + M = M * (e * T + 1) := by ring
      _ ≤ M * (5 * (e * T) + e) := Nat.mul_le_mul_left _ (by omega)
  -- the site on the first slab
  have hv1 : nvcP1 ell M T < nvcN ell M T := by
    have := Gb.nest01; have := Gb.nest12; have := Gb.nestw; have := Gb.nest21; have := Gb.nest10; have := Gb.QN; omega
  have hv0 : nvcP0 ell M Rb T < nvcN ell M T := by
    have := Gb.nest01; have := Gb.nest12; have := Gb.nestw; have := Gb.nest21; have := Gb.nest10; have := Gb.QN; omega
  let s1 := siteAt0 (T := T) hell0 hM (nvcP1 ell M T) hv1
  let s0 := siteAt0 (T := T) hell0 hM (nvcP0 ell M Rb T) hv0
  have hs1 : (s1 0).val = nvcP1 ell M T := siteAt0_val hell0 hM _ hv1
  have hs0 : (s0 0).val = nvcP0 ell M Rb T := siteAt0_val hell0 hM _ hv0
  have hs1C : s1 ∈ C := by
    left; rw [hs1, hP1, Nat.mul_div_cancel_left _ hM]
  have hs0C : s0 ∈ C := by
    right; rw [hs0, hP0b, Nat.mul_div_cancel_left _ hM]
  -- membership in the towers
  have hGb := Gb
  have hunion : UnionAt ell M 2 (slabT ell M Rb T) C 0 := by
    refine ⟨Nat.zero_le _, ?_, ?_, ⟨s0, hs0C, ?_⟩⟩
    · simpa [bigSide] using hCbc
    · intro x hx
      have hx' : x ∈ C := hx
      rcases hx' with hx' | hx'
      · right
        have := key1 x hx'
        show x ∈ towerBj (slab3 _ _ _ _ _ _ _) 1
        rw [bj1]
        have := Gb.nest12; have := Gb.nest01; have := Gb.nest21; have := Gb.nest10
        constructor <;> omega
      · left
        have := key2 x hx'
        show x ∈ towerBj (slab3 _ _ _ _ _ _ _) 0
        rw [bj0]
        have := Gb.nest01; have := Gb.nest12; have := Gb.nestw; have := Gb.nest21; have := Gb.nest10
        constructor <;> omega
    · show s0 ∈ towerBj (slab3 _ _ _ _ _ _ _) 0
      rw [bj0, hs0]
      have := Gb.nest01; have := Gb.nest12; have := Gb.nestw; have := Gb.nest21; have := Gb.nest10
      have := Gb.QN
      constructor
      · constructor <;> omega
      · omega
  have hnestB := hAdmB.1
  have hcut : ∀ x, x ∈ C → x ∈ (slabT ell M R T).Om 0 → x ∈ (slabT ell M R T).Om 1 := by
    intro x hxC hx0
    simp only [slabT, om0_mem, om1_mem] at hx0 ⊢
    rcases hxC with h | h
    · have := key1 x h
      have := G.nest01; have := G.nest12; have := G.nestw; have := G.nest21; have := G.nest10
      constructor <;> omega
    · have := key2 x h
      omega
  refine ⟨C, isClassUnion_of_unionAt hnestB hunion, ⟨s1, hs1C, ?_⟩, fun x hx => hcut x hx.1 hx.2, ?_⟩
  · simp only [slabT, om0_mem]
    rw [hs1]
    have := G.nest01; have := G.nest12; have := G.nestw; have := G.nest21; have := G.nest10; have := G.QN
    constructor <;> omega
  · rintro ⟨-, -, -, ⟨y, hy, hy0⟩⟩
    exact hy0.2 (hcut y hy.1 hy.2)


/-- the M1 regime (one global gauge and field, stratum-scaled bounds) gives regularity of every `UnionAt` set of index `j` on an admissible tower -/
theorem regBody_of_M1_union {ell M R f k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L} (hA : Admissible ell M R k S)
    (h : AdalyFormal.M1.M1Regular ell M f k S α₀ η U) {sites : Set (PeriodicLatticeSite L)} {j : ℕ}
    (hu : UnionAt ell M k S sites j) : RegBodyH ell M f sites j α₀ η U := by
  obtain ⟨g, A, hU, hHT, h1, h2, h3⟩ := h
  have hsubj : sites ⊆ S.Om j := by
    intro x hx
    rcases hu.2.2.1 hx with h | h
    · exact h.1
    · exact (antitone_nat_of_succ_le hA.1) (Nat.le_succ j) h.1
  have hb : ∀ e : AdalyFormal.Balaban.AdmissibleSubspace.Bond L, CubeBond sites e → j ≤ AdalyFormal.M1.bstrat S k e :=
    fun e he => AdalyFormal.M1.le_bstrat_of_mem hu.1 e (hsubj he.1) (hsubj he.2)
  refine ⟨g, A, fun e he => ⟨hHT e, hU e, h1 e j (hb e he)⟩, fun μ ν x hx hy => h2 μ ν x j (hb _ hx) (hb _ hy), ?_⟩
  intro μ x hr
  refine h3 μ x j (fun ν hν => ?_)
  obtain ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩⟩ := hr ν hν
  exact ⟨⟨hb _ a1, hb _ a2, hb _ a3, hb _ a4⟩, ⟨hb _ b1, hb _ b2, hb _ b3, hb _ b4⟩⟩

/-- the family of ALL triples of factor `f` (used only for the joint instance) -/
def famF (f : ℕ) (L : PeriodicLatticeExtent) : CubeFam L := {t | t.2.2 = f}

/-- on an admissible tower, the box coverage at factor `f` plus the M1 regime give the UNION-class family hypothesis for the family of ALL triples of factor `f` -/
theorem classCoupledU_of_M1 {ell M R f k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L} (hA : Admissible ell M R k S)
    (hcov : CoversOm0p ell M f k S) (hreg : AdalyFormal.M1.M1Regular ell M f k S α₀ η U) :
    UNI.Total.ClassCoupledP UNI.Total.unionClass ell M (famF f L) k S α₀ η U := by
  obtain ⟨hs, hp⟩ := hcov
  refine ⟨fun x hx => ?_, fun p hp' => ?_, fun f' sites j hmem hq => ?_⟩
  · obtain ⟨sites, j, hq, hxs⟩ := hs x hx
    exact ⟨sites, j, ⟨f, rfl, isClassUnion_of_unionAt hA.1 (UNI.Total.unionAt_of_described hA hq.1)⟩, hxs⟩
  · obtain ⟨sites, j, hq, hb⟩ := hp p hp'
    exact ⟨sites, j, ⟨f, rfl, isClassUnion_of_unionAt hA.1 (UNI.Total.unionAt_of_described hA hq.1)⟩, hb⟩
  · have hf' : f' = f := hmem
    subst hf'
    exact regBody_of_M1_union hA hreg hq.1

end AdalyFormal.TwoDom

#print axioms AdalyFormal.TwoDom.slabT_two
#print axioms AdalyFormal.TwoDom.plain_cut_fails
#print axioms AdalyFormal.TwoDom.regBody_of_M1_union
#print axioms AdalyFormal.TwoDom.classCoupledU_of_M1
