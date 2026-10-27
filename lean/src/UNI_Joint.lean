import UNI_NV

/-!
# UNI_Joint -- JOINT non-vacuity of all hypotheses of `P428Target8FamilyTorusU` WITH a union-only member (lane union_cubes_20261018)

The first part (`regBody_mono_sites`, `sitesU`, ...) is new.  `joint_union_only` is the prosecutor's `PRO.joint_nonvacuous`
(compute/union_cubes_prosecution_20261018/PRO_Joint.lean; proof body copied and extended) with the family enlarged by ONE extra member `(sitesU, k, 10)`:
`sitesU` = the union of the two diagonal level-`k` blocks `{x | all x_μ/b = 0} ∪ {x | all x_μ/b = 1}`, `b = M ℓ^k`, on the full tower (`Ω_j = univ`, `j ≤ k`, so `B^k = univ`).
The conclusion adds: that member is an `IsClassUnion` of the tower and is NOT an `IsClassCube` for any factor.  It is not needed for coverage (the box members already cover); it carries the (3.35)/(3.36) regularity of `U` as a union.
-/
set_option autoImplicit false

namespace UNI.Joint

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.IngredientFamilyR2 (fullTower)
open UNI.AllC UNI.Total

theorem cubeBond_mono {L : PeriodicLatticeExtent} {A B : Set (PeriodicLatticeSite L)} (h : A ⊆ B) {e : Bond L}
    (he : CubeBond A e) : CubeBond B e := ⟨h he.1, h he.2⟩

theorem curlReads_mono {L : PeriodicLatticeExtent} {A B : Set (PeriodicLatticeSite L)} (h : A ⊆ B)
    {x : PeriodicLatticeSite L} {a b : Fin 3} (hr : CurlReads A x a b) : CurlReads B x a b := by
  obtain ⟨h1, h2, h3, h4⟩ := hr
  exact ⟨cubeBond_mono h h1, cubeBond_mono h h2, cubeBond_mono h h3, cubeBond_mono h h4⟩

/-- regularity on a set gives regularity on every subset (same index, same factor). -/
theorem regBody_mono_sites {L : PeriodicLatticeExtent} {ell M b : ℕ} {A B : Set (PeriodicLatticeSite L)} (h : A ⊆ B) {j : ℕ}
    {α₀ η : ℝ} {U : LinkCfg L} (hr : RegBodyH ell M b B j α₀ η U) : RegBodyH ell M b A j α₀ η U := by
  obtain ⟨g, A', h1, h2, h3⟩ := hr
  exact ⟨g, A', fun e he => h1 e (cubeBond_mono h he),
    fun μ ν x a c => h2 μ ν x (cubeBond_mono h a) (cubeBond_mono h c),
    fun μ x hx => h3 μ x (fun ν hν => ⟨curlReads_mono h (hx ν hν).1, curlReads_mono h (hx ν hν).2⟩)⟩

/-- two diagonal level-`b` blocks. -/
def sitesU (L : PeriodicLatticeExtent) (b : ℕ) : Set (PeriodicLatticeSite L) :=
  {x | (∀ μ, (x μ).val / b = 0) ∨ (∀ μ, (x μ).val / b = 1)}

theorem blockClosed_sitesU {L : PeriodicLatticeExtent} (b : ℕ) : BlockClosed b (sitesU L b) := by
  intro x hx y hxy
  rcases hx with hx | hx
  · left; intro μ; rw [hxy μ]; exact hx μ
  · right; intro μ; rw [hxy μ]; exact hx μ

theorem not_box_sitesU {L : PeriodicLatticeExtent} {b : ℕ} (hb0 : 0 < b) (hb : b < L 0 + 1) (hb1 : b < L 1 + 1) (hb2 : b < L 2 + 1)
    {s : ℕ} {z : PeriodicLatticeSite L} : sitesU L b ≠ siteBox z s := by
  intro hz
  let a : PeriodicLatticeSite L := fun _ => ⟨0, by omega⟩
  let bb : PeriodicLatticeSite L := fun μ => ⟨b, by fin_cases μ <;> assumption⟩
  let c : PeriodicLatticeSite L := fun μ => if h : μ = 2 then ⟨b, by subst h; exact hb2⟩ else ⟨0, by omega⟩
  have ha : a ∈ sitesU L b := Or.inl (fun μ => by simp [a])
  have hbb : bb ∈ sitesU L b := Or.inr (fun μ => by simp [bb, Nat.div_self hb0])
  rw [hz] at ha hbb
  have hc : c ∈ siteBox z s := by
    intro μ
    by_cases h : μ = 2
    · have := hbb μ; simpa [c, h, bb] using this
    · have := ha μ; simpa [c, h, a] using this
  rw [← hz] at hc
  rcases hc with hc | hc
  · have := hc 2; simp [c, Nat.div_self hb0] at this
  · have := hc 0; simp [c] at this

theorem joint_union_only (ell m R k : ℕ) (a₀ : ℝ) (hell : 2 ≤ ell) (hm : 1 ≤ m) (hk : 1 ≤ k) (ha₀ : 0 < a₀) :
    ∃ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ ∧
      ∃ F : CubeFam (scaleUp ell k Lu),
        (∀ (s : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j f : ℕ), (s, j, f) ∈ F →
            10 ≤ f ∧ (f : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀) ∧
        TorusOK ell (ell ^ m) Lu ∧
        ∃ S : Tower (scaleUp ell k Lu), Admissible ell (ell ^ m) R k S ∧
        ∃ Lam : Set (PeriodicLatticeSite Lu), AdalyFormal.StatementLaneG.LambdaOK2 (Lu := Lu) (Lf := scaleUp ell k Lu) ell (ell ^ m) R k S Lam ∧
        ∃ U : LinkCfg (scaleUp ell k Lu),
          ClassCoupledU ell (ell ^ m) F k S α₀ (((ell : ℝ) ^ k)⁻¹) U ∧
          ∃ (s : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j f : ℕ), (s, j, f) ∈ F ∧
            IsClassUnion ell (ell ^ m) k S s j ∧ ∀ f' : ℕ, ¬ IsClassCube ell (ell ^ m) f' k S s j := by
  have hell0 : 0 < ell := by omega
  have hM : 0 < ell ^ m := pow_pos hell0 _
  let Lu : PeriodicLatticeExtent := fun _ => ell ^ (m + 1) - 1
  have hLu : ∀ μ : Fin 3, Lu μ + 1 = ell ^ (m + 1) := by
    intro μ; have : 0 < ell ^ (m + 1) := pow_pos hell0 _
    show ell ^ (m + 1) - 1 + 1 = _; omega
  have hT1 : ∀ μ : Fin 3, ell ^ m ∣ Lu μ + 1 := fun μ => by rw [hLu μ]; exact pow_dvd_pow ell (by omega)
  have hT2 : ∀ μ : Fin 3, ell ∣ Lu μ + 1 := fun μ => by rw [hLu μ]; exact dvd_pow_self ell (by omega)
  have hT3 : ∀ μ : Fin 3, ell < Lu μ + 1 := fun μ => by
    rw [hLu μ]
    calc ell = ell ^ 1 := (pow_one ell).symm
      _ < ell ^ (m + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
  have hMr : (0:ℝ) < ((ell ^ m : ℕ) : ℝ) := by exact_mod_cast hM
  let α₀ : ℝ := a₀ / (10 * ((ell ^ m : ℕ) : ℝ))
  have hα : 0 < α₀ := by positivity
  have hχ : ∀ e : AdalyFormal.Balaban.AdmissibleSubspace.Bond (scaleUp ell k Lu), |(fun _ => (0:ℝ)) e| ≤ α₀ * (((ell : ℝ) ^ k)⁻¹) ^ 2 / 10 := fun e => by
    simp only [abs_zero]; positivity
  obtain ⟨hadm, hlam, ⟨⟨hs, hp⟩, hreg⟩⟩ := AdalyFormal.AllC.classHyps_nonvacuous ell (ell ^ m) R k 10 hell0 hM le_rfl Lu hT1 hα hk
    (fun _ => 0) hχ
  -- geometry of the torus
  have hN : ∀ μ : Fin 3, scaleUp ell k Lu μ + 1 = (Lu μ + 1) * ell ^ k := by
    intro μ; unfold scaleUp
    have : 1 ≤ (Lu μ + 1) * ell ^ k := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  set b : ℕ := bigSide (ell ^ m) ell k with hbdef
  have hb0 : 0 < b := Nat.mul_pos hM (pow_pos hell0 k)
  have hNb : ∀ μ : Fin 3, scaleUp ell k Lu μ + 1 = ell * b := by
    intro μ; rw [hN μ, hLu μ, hbdef]; unfold bigSide; ring
  have hbN : ∀ μ : Fin 3, 2 * b ≤ scaleUp ell k Lu μ + 1 := fun μ => by
    rw [hNb μ]; exact Nat.mul_le_mul_right b hell
  -- the full tower: B^k = univ
  have hBk : ∀ x : PeriodicLatticeSite (scaleUp ell k Lu), x ∈ towerBj (fullTower ell k Lu) k := by
    intro x
    show x ∈ (fullTower ell k Lu).Om k ∧ x ∉ (fullTower ell k Lu).Om (k + 1)
    simp [fullTower]
  let F0 : CubeFam (scaleUp ell k Lu) := {t | t.2.2 = 10 ∧ boxShape (scaleUp ell k Lu) ell (ell ^ m) 10 t.1 t.2.1}
  have hmem : ∀ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ),
      IsClassCube ell (ell ^ m) 10 k (fullTower ell k Lu) sites j → (sites, j, 10) ∈ F0 := fun sites j hq =>
    ⟨rfl, hq.1.2.1⟩
  let F : CubeFam (scaleUp ell k Lu) := {t | t ∈ F0 ∨ t = (sitesU (scaleUp ell k Lu) b, k, 10)}
  have hnew : (sitesU (scaleUp ell k Lu) b, k, 10) ∈ F := Or.inr rfl
  -- the union is a class union of index k
  have hz0 : ∀ μ, (0 : ℕ) < scaleUp ell k Lu μ + 1 := fun μ => by omega
  let z0 : PeriodicLatticeSite (scaleUp ell k Lu) := fun μ => ⟨0, hz0 μ⟩
  have hunion : UnionAt ell (ell ^ m) k (fullTower ell k Lu) (sitesU (scaleUp ell k Lu) b) k := by
    refine ⟨le_rfl, blockClosed_sitesU b, fun x _ => Or.inl (hBk x), ⟨z0, Or.inl (fun μ => by simp [z0]), hBk z0⟩⟩
  have hcu : IsClassUnion ell (ell ^ m) k (fullTower ell k Lu) (sitesU (scaleUp ell k Lu) b) k :=
    isClassUnion_of_unionAt hadm.1 hunion
  have hnb : ∀ f' : ℕ, ¬ IsClassCube ell (ell ^ m) f' k (fullTower ell k Lu) (sitesU (scaleUp ell k Lu) b) k := by
    intro f' hc
    obtain ⟨⟨-, ⟨z, -, hz⟩, -, -⟩, -⟩ := hc
    exact not_box_sitesU hb0 (by have := hNb 0; have := hbN 0; omega) (by have := hNb 1; have := hbN 1; omega)
      (by have := hNb 2; have := hbN 2; omega) hz
  -- regularity of the union: it lies in a class box of factor 10 and index k
  have hbox : IsClassCube ell (ell ^ m) 10 k (fullTower ell k Lu) (siteBox z0 (10 * bigSide (ell ^ m) ell k)) k := by
    refine AdalyFormal.Thin.isClassCube_of_described hadm.1 ⟨le_rfl, ⟨z0, fun μ => by simp [z0], rfl⟩, fun x _ => Or.inl (hBk x), ⟨z0, ?_, hBk z0⟩⟩
    intro μ
    have h1 : (0 + (scaleUp ell k Lu μ + 1) - (z0 μ).val) % (scaleUp ell k Lu μ + 1) = 0 := by simp [z0]
    show ((z0 μ).val + (scaleUp ell k Lu μ + 1) - (z0 μ).val) % (scaleUp ell k Lu μ + 1) < 10 * bigSide (ell ^ m) ell k
    have : ((z0 μ).val + (scaleUp ell k Lu μ + 1) - (z0 μ).val) % (scaleUp ell k Lu μ + 1) = 0 := by simp [z0]
    rw [this]; omega
  have hsub : sitesU (scaleUp ell k Lu) b ⊆ siteBox z0 (10 * bigSide (ell ^ m) ell k) := by
    intro x hx μ
    have hxlt : (x μ).val < 2 * b := by
      rcases hx with hx | hx
      · have := hx μ; have h2 : (x μ).val / b < 2 := by omega
        exact (Nat.div_lt_iff_lt_mul hb0).1 h2 |>.trans_le (by omega)
      · have := hx μ; have h2 : (x μ).val / b < 2 := by omega
        exact (Nat.div_lt_iff_lt_mul hb0).1 h2 |>.trans_le (by omega)
    have hxN : (x μ).val < scaleUp ell k Lu μ + 1 := (x μ).isLt
    show ((x μ).val + (scaleUp ell k Lu μ + 1) - (z0 μ).val) % (scaleUp ell k Lu μ + 1) < 10 * bigSide (ell ^ m) ell k
    have : ((x μ).val + (scaleUp ell k Lu μ + 1) - (z0 μ).val) % (scaleUp ell k Lu μ + 1) = (x μ).val := by
      have e : (x μ).val + (scaleUp ell k Lu μ + 1) - (z0 μ).val = (x μ).val + (scaleUp ell k Lu μ + 1) := by simp [z0]
      rw [e, Nat.add_mod_right]; exact Nat.mod_eq_of_lt hxN
    rw [this]
    have : 10 * bigSide (ell ^ m) ell k = 10 * b := rfl
    omega
  have hregU : RegBodyH ell (ell ^ m) 10 (sitesU (scaleUp ell k Lu) b) k α₀ (((ell : ℝ) ^ k)⁻¹) (Ufield (((ell : ℝ) ^ k)⁻¹) (fun _ => 0)) :=
    regBody_mono_sites hsub (hreg _ k hbox)
  refine ⟨Lu, α₀, hα, F, ?_, ⟨hT2, hT3, hT1⟩, fullTower ell k Lu, hadm, Set.univ, hlam, Ufield (((ell : ℝ) ^ k)⁻¹) (fun _ => 0), ?_, ?_⟩
  · have hsm : ((10:ℕ):ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ = a₀ := by
      simp only [α₀]; push_cast; field_simp
    intro s j f hmF
    rcases hmF with hmF | hmF
    · have h1 : f = 10 := hmF.1
      subst h1
      exact ⟨le_rfl, le_of_eq hsm⟩
    · have h1 : f = 10 := (Prod.mk.inj (Prod.mk.inj hmF).2).2
      subst h1
      exact ⟨le_rfl, le_of_eq hsm⟩
  · refine ⟨fun x hx => ?_, fun p hp' => ?_, fun f sites j hm hu => ?_⟩
    · obtain ⟨sites, j, hq, hx'⟩ := hs x hx
      exact ⟨sites, j, ⟨10, Or.inl (hmem sites j hq), ((boxClass_iff hadm 10 sites j).1 hq).1⟩, hx'⟩
    · obtain ⟨sites, j, hq, hb⟩ := hp p hp'
      exact ⟨sites, j, ⟨10, Or.inl (hmem sites j hq), ((boxClass_iff hadm 10 sites j).1 hq).1⟩, hb⟩
    · rcases hm with hm | hm
      · obtain ⟨hfc, hbox'⟩ := hm
        have hf : f = 10 := hfc
        subst hf
        exact hreg sites j ((boxClass_iff hadm 10 sites j).2 ⟨hu, hbox'⟩)
      · have e1 : sites = sitesU (scaleUp ell k Lu) b := (Prod.mk.inj hm).1
        have e2 : j = k := (Prod.mk.inj (Prod.mk.inj hm).2).1
        have e3 : f = 10 := (Prod.mk.inj (Prod.mk.inj hm).2).2
        subst e1 e2 e3
        exact hregU
  · exact ⟨sitesU (scaleUp ell k Lu) b, k, 10, hnew, hcu, hnb⟩

end UNI.Joint

#print axioms UNI.Joint.joint_union_only
#print axioms UNI.Joint.regBody_mono_sites
