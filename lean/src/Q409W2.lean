import Q409W1

/-!
# Q409W2 -- p.409 containment for the union-of-blocks reading `IsClassSetW`, all admissible towers.

`setw_contains`: for every tower `S` over a torus `L`, `Admissible ell M R k S`, `(c+3)*ell <= R`, `5 <= c`,
`ell >= 2`, `M > 0`, side condition `bigSide M ell k < L mu + 1`, and every patch `IsPatch ell M k 1 S j w`:
there are a set `sites` and an index `i` with `IsClassSetW ell M (2*c*ell+1) k S sites i` and
`{y | y in patch ell M 1 c j w /\ y in S.Om 0} subset sites`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.P409W

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneR8 (pdist_comm pdist_triangle)
open AdalyFormal.GeneralClass (IsClassSetW)
open AdalyFormal.M1 (strat IsPatch patch gsp)

variable {L : PeriodicLatticeExtent}

theorem bigSide_zero (M ell : ℕ) : bigSide M ell 0 = M := by simp [bigSide]

theorem bigSide_pos' {M ell : ℕ} (hM : 0 < M) (hell : 0 < ell) (i : ℕ) : 0 < bigSide M ell i :=
  Nat.mul_pos hM (pow_pos hell i)

theorem bigSide_mono' {M ell : ℕ} (hell : 0 < ell) {i j : ℕ} (h : i ≤ j) : bigSide M ell i ≤ bigSide M ell j :=
  Nat.mul_le_mul_left M (Nat.pow_le_pow_right hell h)

theorem toward_site (M R : ℕ) (z y : PeriodicLatticeSite L) (hM : 0 < M) (hR : 4 ≤ R)
    (hN : ∀ μ, 2 * M ≤ L μ + 1) (hd : pdist z y ≤ R * M) :
    ∃ (μ : Fin 3) (s : ℕ), (s = M ∨ s + M = L μ + 1) ∧ pdist (sh z μ s) y ≤ R * M := by
  have hRM : 4 * M ≤ R * M := Nat.mul_le_mul_right M hR
  by_cases hA : ∃ μ : Fin 3, M ≤ pcd (L μ + 1) (z μ).val (y μ).val
  · obtain ⟨μ, hμ⟩ := hA
    obtain ⟨s, hs, h1, -⟩ := pcd_toward (L μ + 1) M (z μ).val (y μ).val hM (hN μ) (z μ).isLt (y μ).isLt
    have sw := pdist_swap z (sh z μ s) y μ (fun ν hν => sh_ne z μ ν s hν)
    rw [sh_self] at sw
    have := h1 hμ
    exact ⟨μ, s, hs, by omega⟩
  · push Not at hA
    obtain ⟨s, hs, -, h2⟩ := pcd_toward (L 0 + 1) M (z 0).val (y 0).val hM (hN 0) (z 0).isLt (y 0).isLt
    have sw := pdist_swap z (sh z 0 s) y 0 (fun ν hν => sh_ne z 0 ν s hν)
    rw [sh_self] at sw
    have h3 := h2 (hA 0)
    have hlt : pdist z y < 3 * M := by
      unfold pdist
      rw [Fin.sum_univ_three]
      have := hA 0; have := hA 1; have := hA 2
      omega
    exact ⟨0, s, hs, by omega⟩

theorem setw_core {ell M R k c j : ℕ} {S : Tower L} {w : PeriodicLatticeSite L}
    (hell : 2 ≤ ell) (hM : 0 < M) (hc : 4 ≤ c) (hR : (c + 3) * ell ≤ R)
    (hA : Admissible ell M R k S) (hgt : ∀ μ : Fin 3, bigSide M ell k < L μ + 1)
    (hp : IsPatch ell M k 1 S j w) :
    ∃ i : ℕ, i ≤ j ∧ bigSide M ell i ∣ bigSide M ell j ∧ bigSide M ell j ≤ ell * bigSide M ell i ∧
      (∀ y, y ∈ patch ell M 1 c j w → y ∈ S.Om 0 → y ∈ towerBj S i ∪ towerBj S (i + 1)) ∧
      (∃ y, y ∈ patch ell M 1 c j w ∧ y ∈ S.Om 0 ∧ y ∈ towerBj S i) ∧
      (∃ a b : PeriodicLatticeSite L, (a ∈ patch ell M 1 c j w ∧ a ∈ S.Om 0) ∧ (b ∈ patch ell M 1 c j w ∧ b ∈ S.Om 0) ∧
        ∃ μ : Fin 3, (a μ).val / bigSide M ell i ≠ (b μ).val / bigSide M ell i) := by
  have hjk : j ≤ k := hp.1
  have hell0 : 0 < ell := by omega
  obtain ⟨x₀, hx0j, hs0, hd0⟩ := hp.anchor (by norm_num) hM hell0
  have hG : gsp ell M 1 j = bigSide M ell j := by simp [gsp]
  rw [hG] at hd0
  set G := bigSide M ell j with hGdef
  have hGpos : 0 < G := bigSide_pos' hM hell0 j
  have hx00 : x₀ ∈ S.Om 0 := AdalyFormal.M1.om_anti hA (Nat.zero_le j) hx0j
  have hx0n : x₀ ∉ S.Om (j + 1) := by
    have := AdalyFormal.M1.not_mem_strat_succ hA x₀
    rwa [hs0] at this
  have hRc : (c + 3) * ell ≤ R := hR
  have hRell : 2 * (c + 3) ≤ R := by nlinarith
  -- patch membership
  have hmem : ∀ y, y ∈ patch ell M 1 c j w ↔ pdist w y ≤ c * G := by
    intro y; show pdist w y ≤ c * gsp ell M 1 j ↔ _; rw [hG]
  have hw0 : pdist w x₀ ≤ 3 * G := by rw [pdist_comm]; exact hd0
  have hK1 : ∀ y, pdist w y ≤ c * G → pdist x₀ y ≤ (c + 3) * G := by
    intro y hy
    have := pdist_triangle x₀ w y
    rw [pdist_comm x₀ w] at this
    nlinarith
  have hK1' : ∀ y, pdist w y ≤ c * G → pdist y x₀ ≤ (c + 3) * G := by
    intro y hy; rw [pdist_comm]; exact hK1 y hy
  have hx0P : pdist w x₀ ≤ c * G := by nlinarith
  -- lower stratum
  have hK2 : ∀ j', j = j' + 1 → ∀ y, pdist w y ≤ c * G → y ∈ S.Om j' := by
    intro j' hj' y hy
    by_contra hn
    have hx1 : x₀ ∈ S.Om (j' + 1) := hj' ▸ hx0j
    have hcol := AdalyFormal.M1.collar hA (j := j') (by omega) hn hx1
    have hb : G = bigSide M ell j' * ell := by rw [hGdef, hj']; exact AdalyFormal.M1.bigSide_succ M ell j'
    have h1 := hK1' y hy
    have h2 : (c + 3) * G ≤ R * bigSide M ell j' := by
      rw [hb]
      calc (c + 3) * (bigSide M ell j' * ell) = ((c + 3) * ell) * bigSide M ell j' := by ring
        _ ≤ R * bigSide M ell j' := Nat.mul_le_mul_right _ hRc
    omega
  -- the final assembly
  have finish : ∀ i : ℕ, i ≤ j → bigSide M ell i ∣ G → G ≤ ell * bigSide M ell i →
      (∀ y, pdist w y ≤ c * G → y ∈ S.Om 0 → y ∈ towerBj S i ∪ towerBj S (i + 1)) →
      (∃ y, pdist w y ≤ c * G ∧ y ∈ S.Om 0 ∧ y ∈ towerBj S i) →
      (∃ a b : PeriodicLatticeSite L, (pdist w a ≤ c * G ∧ a ∈ S.Om 0) ∧ (pdist w b ≤ c * G ∧ b ∈ S.Om 0) ∧
        ∃ μ : Fin 3, (a μ).val / bigSide M ell i ≠ (b μ).val / bigSide M ell i) →
      ∃ i : ℕ, i ≤ j ∧ bigSide M ell i ∣ bigSide M ell j ∧ bigSide M ell j ≤ ell * bigSide M ell i ∧
      (∀ y, y ∈ patch ell M 1 c j w → y ∈ S.Om 0 → y ∈ towerBj S i ∪ towerBj S (i + 1)) ∧
      (∃ y, y ∈ patch ell M 1 c j w ∧ y ∈ S.Om 0 ∧ y ∈ towerBj S i) ∧
      (∃ a b : PeriodicLatticeSite L, (a ∈ patch ell M 1 c j w ∧ a ∈ S.Om 0) ∧ (b ∈ patch ell M 1 c j w ∧ b ∈ S.Om 0) ∧
        ∃ μ : Fin 3, (a μ).val / bigSide M ell i ≠ (b μ).val / bigSide M ell i) := by
    intro i hij hdvd hle hsub hmeet htwo
    refine ⟨i, hij, hdvd, hle, ?_, ?_, ?_⟩
    · intro y hy hy0; exact hsub y ((hmem y).1 hy) hy0
    · obtain ⟨y, h1, h2, h3⟩ := hmeet
      exact ⟨y, (hmem y).2 h1, h2, h3⟩
    · obtain ⟨a, b, ha, hb, μ, hμ⟩ := htwo
      exact ⟨a, b, ⟨(hmem a).2 ha.1, ha.2⟩, ⟨(hmem b).2 hb.1, hb.2⟩, μ, hμ⟩
  -- the shifted point (levels j >= 1)
  have hshift : 1 ≤ j → ∀ i : ℕ, i ≤ j → bigSide M ell i ∣ G →
      (∃ a b : PeriodicLatticeSite L, (pdist w a ≤ c * G ∧ a ∈ S.Om 0) ∧ (pdist w b ≤ c * G ∧ b ∈ S.Om 0) ∧
        ∃ μ : Fin 3, (a μ).val / bigSide M ell i ≠ (b μ).val / bigSide M ell i) := by
    intro hj1 i hij hdvd
    obtain ⟨j', hj'⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hNd : bigSide M ell i ∣ L 0 + 1 := hA.2.2.1 i (by omega) 0
    have hGk : G ≤ bigSide M ell k := bigSide_mono' hell0 hjk
    have hGN : G < L 0 + 1 := lt_of_le_of_lt hGk (hgt 0)
    have hdG := pdist_sh_le x₀ 0 G hGN.le
    have hy : pdist w (sh x₀ 0 G) ≤ c * G := by
      have := pdist_triangle w x₀ (sh x₀ 0 G)
      nlinarith [hdG.1]
    have hy0 : sh x₀ 0 G ∈ S.Om 0 :=
      AdalyFormal.M1.om_anti hA (Nat.zero_le j') (hK2 j' hj' _ hy)
    refine ⟨x₀, sh x₀ 0 G, ⟨hx0P, hx00⟩, ⟨hy, hy0⟩, 0, ?_⟩
    have hgpos : 0 < bigSide M ell i := bigSide_pos' hM hell0 i
    have := blocks_ne (bigSide M ell i) (L 0 + 1) (x₀ 0).val G hgpos hNd hdvd hGpos hGN (x₀ 0).isLt
    rw [sh_self]
    exact fun h => this h.symm
  by_cases hQ : ∃ y, pdist w y ≤ c * G ∧ y ∈ S.Om 0 ∧ y ∉ S.Om j
  · -- two strata j-1, j
    obtain ⟨xq, hxq, hxq0, hxqn⟩ := hQ
    obtain ⟨i, hi⟩ : ∃ i, j = i + 1 := by
      refine ⟨j - 1, ?_⟩
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h; exact absurd hxq0 hxqn
      · omega
    have hGi : G = bigSide M ell i * ell := by rw [hGdef, hi]; exact AdalyFormal.M1.bigSide_succ M ell i
    have hgi : 0 < bigSide M ell i := bigSide_pos' hM hell0 i
    have hxqi : xq ∈ S.Om i := hK2 i hi xq hxq
    have hxqn' : xq ∉ S.Om (i + 1) := hi ▸ hxqn
    refine finish i (by omega) ?_ ?_ ?_ ?_ ?_
    · rw [hGi]; exact Dvd.intro _ rfl
    · rw [hGi]; nlinarith
    · intro y hy hy0
      have hyi : y ∈ S.Om i := hK2 i hi y hy
      have hyn : y ∉ S.Om (i + 2) := by
        intro hy2
        have hcol := AdalyFormal.M1.collar hA (j := i + 1) (by omega) hxqn' (show y ∈ S.Om (i + 1 + 1) from hy2)
        have h1 := pdist_triangle xq w y
        rw [pdist_comm xq w] at h1
        have h2 : pdist w xq ≤ c * G := hxq
        have h3 : 2 * c * G ≤ R * G := by
          have : 2 * c ≤ R := by omega
          exact Nat.mul_le_mul_right _ this
        have h4 : bigSide M ell (i + 1) = G := by rw [hGdef, hi]
        rw [h4] at hcol
        nlinarith
      by_cases hy1 : y ∈ S.Om (i + 1)
      · exact Or.inr ⟨hy1, hyn⟩
      · exact Or.inl ⟨hyi, hy1⟩
    · exact ⟨xq, hxq, hxq0, hxqi, hxqn'⟩
    · exact hshift (by omega) i (by omega) (by rw [hGi]; exact Dvd.intro _ rfl)
  · push Not at hQ
    have hsub : ∀ y, pdist w y ≤ c * G → y ∈ S.Om 0 → y ∈ towerBj S j ∪ towerBj S (j + 1) := by
      intro y hy hy0
      have hyj : y ∈ S.Om j := hQ y hy hy0
      have hyn : y ∉ S.Om (j + 2) := by
        intro hy2
        by_cases hjk1 : j + 1 ≤ k
        · have hcol := AdalyFormal.M1.collar hA (j := j + 1) hjk1 hx0n (show y ∈ S.Om (j + 1 + 1) from hy2)
          have h1 := hK1 y hy
          have h4 : bigSide M ell (j + 1) = G * ell := AdalyFormal.M1.bigSide_succ M ell j
          rw [h4] at hcol
          have h5 : (c + 3) * G ≤ R * (G * ell) := by
            calc (c + 3) * G ≤ ((c + 3) * ell) * G := by nlinarith
              _ ≤ R * G := Nat.mul_le_mul_right _ hRc
              _ ≤ R * (G * ell) := Nat.mul_le_mul_left _ (by nlinarith)
          omega
        · rw [hA.2.1 (j + 2) (by omega)] at hy2; exact hy2
      by_cases hy1 : y ∈ S.Om (j + 1)
      · exact Or.inr ⟨hy1, hyn⟩
      · exact Or.inl ⟨hyj, hy1⟩
    by_cases hj0 : j = 0
    · -- j = 0 : a second M-block through the collar clause of Omega_0
      subst hj0
      have hG0 : G = M := bigSide_zero M ell
      have hMk : M ≤ bigSide M ell k := by
        have := bigSide_mono' (M := M) hell0 (Nat.zero_le k)
        rwa [bigSide_zero] at this
      have hNd : ∀ μ : Fin 3, M ∣ L μ + 1 := fun μ => by
        have := hA.2.2.1 0 (Nat.zero_le k) μ; rwa [bigSide_zero] at this
      have hN2 : ∀ μ : Fin 3, 2 * M ≤ L μ + 1 := fun μ => by
        obtain ⟨t, ht⟩ := hNd μ
        have h1 := hgt μ
        have h2 : M < M * t := by omega
        have h3 : 2 ≤ t := by
          by_contra hh; push Not at hh
          interval_cases t <;> omega
        have := Nat.mul_le_mul_left M h3
        omega
      have h6 := (hA.2.2.2.2.2 x₀).1 hx00
      obtain ⟨y₁, hy₁, z, hz, hzd⟩ := h6
      have hRM : 4 ≤ R := by nlinarith
      obtain ⟨μ, s, hs, hzs⟩ := toward_site M R z y₁ hM hRM hN2 hzd
      have hN2μ := hN2 μ
      have hsN : s ≤ L μ + 1 := by omega
      have hMs : M ∣ s := by
        rcases hs with rfl | h
        · exact dvd_rfl
        · have h7 := hNd μ
          have : s = (L μ + 1) - M := by omega
          rw [this]; exact Nat.dvd_sub h7 dvd_rfl
      have hx'0 : sh x₀ μ s ∈ S.Om 0 := by
        refine (hA.2.2.2.2.2 _).2 ⟨y₁, hy₁, sh z μ s, ?_, hzs⟩
        intro ν
        by_cases hν : ν = μ
        · subst hν
          rw [sh_self, sh_self]
          exact div_shift M (L ν + 1) (z ν).val (x₀ ν).val s hM (hNd ν) hMs (hz ν)
        · rw [sh_ne z μ ν s hν, sh_ne x₀ μ ν s hν]; exact hz ν
      have hdx := pdist_sh_le x₀ μ s hsN
      have hdM : pdist x₀ (sh x₀ μ s) ≤ M := by
        rcases hs with rfl | h
        · exact hdx.1
        · have := hdx.2; omega
      have hx'P : pdist w (sh x₀ μ s) ≤ c * G := by
        have := pdist_triangle w x₀ (sh x₀ μ s)
        rw [hG0] at hw0 ⊢
        nlinarith
      refine finish 0 (le_refl _) dvd_rfl (by nlinarith) ?_ ?_ ?_
      · exact hsub
      · exact ⟨x₀, hx0P, hx00, hx0j, hx0n⟩
      · refine ⟨x₀, sh x₀ μ s, ⟨hx0P, hx00⟩, ⟨hx'P, hx'0⟩, μ, ?_⟩
        have hs0' : 0 < s := by rcases hs with rfl | h <;> omega
        have hsN' : s < L μ + 1 := by
          rcases hs with rfl | h
          · have := hN2 μ; omega
          · omega
        have := blocks_ne (bigSide M ell 0) (L μ + 1) (x₀ μ).val s (bigSide_pos' hM hell0 0)
          (by rw [bigSide_zero]; exact hNd μ) (by rw [bigSide_zero]; exact hMs) hs0' hsN' (x₀ μ).isLt
        rw [sh_self]
        exact fun h => this h.symm
    · exact finish j le_rfl dvd_rfl (by nlinarith) hsub ⟨x₀, hx0P, hx00, hx0j, hx0n⟩
        (hshift (by omega) j le_rfl dvd_rfl)

end AdalyFormal.P409W
