/-
══════════════════════════════════════════════════════════════════════════════
  SolvabilityBelow60.lean
══════════════════════════════════════════════════════════════════════════════

  File     : SolvabilityBelow60.lean
  Author   : (Masaru Numagaki)
  Date     : February 2026

  STATUS:  sorry = 0 | axiom = 0

══════════════════════════════════════════════════════════════════════════════
-/

import A5_SM_Pathway.Auxiliary

set_option maxRecDepth 4000

namespace CosmicNecessity

open Classical

private theorem card_mul_index_fintype {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) : Fintype.card H * H.index = Fintype.card G := by
  have := Subgroup.card_mul_index H
  rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at this

private theorem index_eq_fintype_card {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) : H.index = Fintype.card (G ⧸ H) := by
  show Nat.card (G ⧸ H) = Fintype.card (G ⧸ H)
  exact Nat.card_eq_fintype_card

private theorem isSolvable_of_isPGroup' {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact (Nat.Prime p)] (h : IsPGroup p G) : IsSolvable G := by
  haveI := h.isNilpotent; infer_instance

private theorem isSolvable_of_solvable_extension {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] [IsSolvable N] [IsSolvable (G ⧸ N)] : IsSolvable G :=
  solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

private theorem orderOf_dvd_fintype_card {G : Type*} [Group G] [Fintype G] (g : G) :
    orderOf g ∣ Fintype.card G := orderOf_dvd_card (x := g)

/-!
══════════════════════════════════════════════════════════════════════════════
  §S1.
══════════════════════════════════════════════════════════════════════════════
-/

section OrderCases

private theorem fact6_val3 : (6 : ℕ).factorization 3 = 1 := by native_decide
private theorem fact10_val5 : (10 : ℕ).factorization 5 = 1 := by native_decide
private theorem fact15_val5 : (15 : ℕ).factorization 5 = 1 := by native_decide
private theorem fact30_val5 : (30 : ℕ).factorization 5 = 1 := by native_decide
private theorem fact30_val3 : (30 : ℕ).factorization 3 = 1 := by native_decide
private theorem fact42_val7 : (42 : ℕ).factorization 7 = 1 := by native_decide

theorem isSolvable_of_card_4 {G : Type*} [Group G] [Fintype G]
    (h : Fintype.card G = 4) : IsSolvable G :=
  isSolvable_of_prime_power (by norm_num : Nat.Prime 2) (show Fintype.card G = 2^2 by omega)

theorem isSolvable_of_card_8 {G : Type*} [Group G] [Fintype G]
    (h : Fintype.card G = 8) : IsSolvable G :=
  isSolvable_of_prime_power (by norm_num : Nat.Prime 2) (show Fintype.card G = 2^3 by omega)

theorem isSolvable_of_card_9 {G : Type*} [Group G] [Fintype G]
    (h : Fintype.card G = 9) : IsSolvable G :=
  isSolvable_of_prime_power (by norm_num : Nat.Prime 3) (show Fintype.card G = 3^2 by omega)

theorem isSolvable_of_card_16 {G : Type*} [Group G] [Fintype G]
    (h : Fintype.card G = 16) : IsSolvable G :=
  isSolvable_of_prime_power (by norm_num : Nat.Prime 2) (show Fintype.card G = 2^4 by omega)

theorem isSolvable_of_card_25 {G : Type*} [Group G] [Fintype G]
    (h : Fintype.card G = 25) : IsSolvable G :=
  isSolvable_of_prime_power (by norm_num : Nat.Prime 5) (show Fintype.card G = 5^2 by omega)

theorem isSolvable_of_card_27 {G : Type*} [Group G] [Fintype G]
    (h : Fintype.card G = 27) : IsSolvable G :=
  isSolvable_of_prime_power (by norm_num : Nat.Prime 3) (show Fintype.card G = 3^3 by omega)

theorem isSolvable_of_card_32 {G : Type*} [Group G] [Fintype G]
    (h : Fintype.card G = 32) : IsSolvable G :=
  isSolvable_of_prime_power (by norm_num : Nat.Prime 2) (show Fintype.card G = 2^5 by omega)

theorem isSolvable_of_card_49 {G : Type*} [Group G] [Fintype G]
    (h : Fintype.card G = 49) : IsSolvable G :=
  isSolvable_of_prime_power (by norm_num : Nat.Prime 7) (show Fintype.card G = 7^2 by omega)


/-!
══════════════════════════════════════════════════════════════════════════════
  §S2.
══════════════════════════════════════════════════════════════════════════════
-/

theorem isSolvable_of_card_6
    {G : Type*} [Group G] [Fintype G]
    (hcard : Fintype.card G = 6) : IsSolvable G := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have h_mod := card_sylow_modEq_one 3 G
  rw [Nat.card_eq_fintype_card] at h_mod
  have h_mod' : Fintype.card (Sylow 3 G) % 3 = 1 := by
    rwa [Nat.ModEq, Nat.one_mod] at h_mod
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 G))
  have h_dvd := P.card_dvd_index
  rw [Nat.card_eq_fintype_card] at h_dvd
  have h_card_P : Fintype.card P = 3 := by
    have h := P.card_eq_multiplicity
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hcard, fact6_val3] at h
    simpa using h
  have h_index : (P : Subgroup G).index = 2 := by
    have h_mul := card_mul_index_fintype (P : Subgroup G)
    rw [h_card_P, hcard] at h_mul; omega
  rw [h_index] at h_dvd
  have h_unique : Fintype.card (Sylow 3 G) = 1 := by
    have : ∀ n : ℕ, n ∣ 2 → n % 3 = 1 → n = 1 := by
      intro n hd hm; have := Nat.le_of_dvd (by omega) hd; interval_cases n <;> omega
    exact this _ h_dvd h_mod'
  have h_normal := sylow_normal_of_unique G 3 h_unique P
  haveI := h_normal
  haveI : IsSolvable (P : Subgroup G) :=
    isSolvable_of_isPGroup' P.isPGroup'
  haveI : IsSolvable (G ⧸ (P : Subgroup G)) := by
    have h_card_Q : Fintype.card (G ⧸ (P : Subgroup G)) = 2 := by
      rw [← index_eq_fintype_card]
      have h_mul := card_mul_index_fintype (P : Subgroup G)
      rw [h_card_P, hcard] at h_mul; omega
    have h_pg : IsPGroup 2 (G ⧸ (P : Subgroup G)) := by
      intro g
      have h_ord := orderOf_dvd_fintype_card g
      rw [h_card_Q] at h_ord
      rcases (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) _ h_ord) with h | h
      · exact ⟨0, by rw [pow_zero]; exact h ▸ pow_orderOf_eq_one g⟩
      · exact ⟨1, by rw [pow_one]; exact h ▸ pow_orderOf_eq_one g⟩
    exact isSolvable_of_isPGroup' h_pg
  exact isSolvable_of_solvable_extension (P : Subgroup G)

theorem isSolvable_of_card_10
    {G : Type*} [Group G] [Fintype G]
    (hcard : Fintype.card G = 10) : IsSolvable G := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have h_mod := card_sylow_modEq_one 5 G
  rw [Nat.card_eq_fintype_card] at h_mod
  have h_mod' : Fintype.card (Sylow 5 G) % 5 = 1 := by
    rwa [Nat.ModEq, Nat.one_mod] at h_mod
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 5 G))
  have h_dvd := P.card_dvd_index
  rw [Nat.card_eq_fintype_card] at h_dvd
  have h_card_P : Fintype.card P = 5 := by
    have h := sylow_card_of_factorization 5 P hcard fact10_val5; simpa using h
  have h_index : (P : Subgroup G).index = 2 := by
    have h_mul := card_mul_index_fintype (P : Subgroup G)
    rw [h_card_P, hcard] at h_mul; omega
  rw [h_index] at h_dvd
  have h_unique : Fintype.card (Sylow 5 G) = 1 := by
    have : ∀ n : ℕ, n ∣ 2 → n % 5 = 1 → n = 1 := by
      intro n hd hm; have := Nat.le_of_dvd (by omega) hd; interval_cases n <;> omega
    exact this _ h_dvd h_mod'
  have h_normal := sylow_normal_of_unique G 5 h_unique P
  haveI := h_normal
  haveI : IsSolvable (P : Subgroup G) := isSolvable_of_isPGroup' P.isPGroup'
  haveI : IsSolvable (G ⧸ (P : Subgroup G)) := by
    have h_card_Q : Fintype.card (G ⧸ (P : Subgroup G)) = 2 := by
      rw [← index_eq_fintype_card]
      have h_mul := card_mul_index_fintype (P : Subgroup G)
      rw [h_card_P, hcard] at h_mul; omega
    have h_pg : IsPGroup 2 (G ⧸ (P : Subgroup G)) := by
      intro g; have h_ord := orderOf_dvd_fintype_card g
      rw [h_card_Q] at h_ord
      rcases (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) _ h_ord) with h | h
      · exact ⟨0, by rw [pow_zero]; exact h ▸ pow_orderOf_eq_one g⟩
      · exact ⟨1, by rw [pow_one]; exact h ▸ pow_orderOf_eq_one g⟩
    exact isSolvable_of_isPGroup' h_pg
  exact isSolvable_of_solvable_extension (P : Subgroup G)

theorem isSolvable_of_card_15
    {G : Type*} [Group G] [Fintype G]
    (hcard : Fintype.card G = 15) : IsSolvable G := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h_mod := card_sylow_modEq_one 5 G
  rw [Nat.card_eq_fintype_card] at h_mod
  have h_mod' : Fintype.card (Sylow 5 G) % 5 = 1 := by
    rwa [Nat.ModEq, Nat.one_mod] at h_mod
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 5 G))
  have h_dvd := P.card_dvd_index
  rw [Nat.card_eq_fintype_card] at h_dvd
  have h_card_P : Fintype.card P = 5 := by
    have h := sylow_card_of_factorization 5 P hcard fact15_val5; simpa using h
  have h_index : (P : Subgroup G).index = 3 := by
    have h_mul := card_mul_index_fintype (P : Subgroup G)
    rw [h_card_P, hcard] at h_mul; omega
  rw [h_index] at h_dvd
  have h_unique : Fintype.card (Sylow 5 G) = 1 := by
    have : ∀ n : ℕ, n ∣ 3 → n % 5 = 1 → n = 1 := by
      intro n hd hm; have := Nat.le_of_dvd (by omega) hd; interval_cases n <;> omega
    exact this _ h_dvd h_mod'
  have h_normal := sylow_normal_of_unique G 5 h_unique P
  haveI := h_normal
  haveI : IsSolvable (P : Subgroup G) := isSolvable_of_isPGroup' P.isPGroup'
  haveI : IsSolvable (G ⧸ (P : Subgroup G)) := by
    have h_card_Q : Fintype.card (G ⧸ (P : Subgroup G)) = 3 := by
      rw [← index_eq_fintype_card]
      have h_mul := card_mul_index_fintype (P : Subgroup G)
      rw [h_card_P, hcard] at h_mul; omega
    have h_pg : IsPGroup 3 (G ⧸ (P : Subgroup G)) := by
      intro g; have h_ord := orderOf_dvd_fintype_card g
      rw [h_card_Q] at h_ord
      rcases (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) _ h_ord) with h | h
      · exact ⟨0, by rw [pow_zero]; exact h ▸ pow_orderOf_eq_one g⟩
      · exact ⟨1, by rw [pow_one]; exact h ▸ pow_orderOf_eq_one g⟩
    exact isSolvable_of_isPGroup' h_pg
  exact isSolvable_of_solvable_extension (P : Subgroup G)


/-!
══════════════════════════════════════════════════════════════════════════════
  §S3.
══════════════════════════════════════════════════════════════════════════════
-/

theorem isSolvable_of_card_30
    {G : Type*} [Group G] [Fintype G]
    (hcard : Fintype.card G = 30) : IsSolvable G := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI := Classical.decEq G
  have h5_mod := card_sylow_modEq_one 5 G
  rw [Nat.card_eq_fintype_card] at h5_mod
  have h5_mod' : Fintype.card (Sylow 5 G) % 5 = 1 := by
    rwa [Nat.ModEq, Nat.one_mod] at h5_mod
  obtain ⟨P5⟩ := (inferInstance : Nonempty (Sylow 5 G))
  have h5_dvd := P5.card_dvd_index
  rw [Nat.card_eq_fintype_card] at h5_dvd
  have h5_card' : Fintype.card P5 = 5 := by
    have h := sylow_card_of_factorization 5 P5 hcard fact30_val5; simpa using h
  have h5_index : (P5 : Subgroup G).index = 6 := by
    have h_mul := card_mul_index_fintype (P5 : Subgroup G)
    rw [h5_card', hcard] at h_mul; omega
  rw [h5_index] at h5_dvd
  have h5_cands : Fintype.card (Sylow 5 G) = 1 ∨ Fintype.card (Sylow 5 G) = 6 := by
    have : ∀ n : ℕ, n ∣ 6 → n % 5 = 1 → n = 1 ∨ n = 6 := by
      intro n hd hm; have := Nat.le_of_dvd (by omega) hd; interval_cases n <;> omega
    exact this _ h5_dvd h5_mod'
  rcases h5_cands with h5_eq | h5_eq
  · have h_normal := sylow_normal_of_unique G 5 h5_eq P5
    haveI := h_normal
    haveI : IsSolvable (P5 : Subgroup G) := isSolvable_of_isPGroup' P5.isPGroup'
    haveI : IsSolvable (G ⧸ (P5 : Subgroup G)) := by
      have h_card_Q : Fintype.card (G ⧸ (P5 : Subgroup G)) = 6 := by
        rw [← index_eq_fintype_card]; have h_mul := card_mul_index_fintype (P5 : Subgroup G)
        rw [h5_card', hcard] at h_mul; omega
      exact isSolvable_of_card_6 h_card_Q
    exact isSolvable_of_solvable_extension (P5 : Subgroup G)
  ·
    have h3_mod := card_sylow_modEq_one 3 G
    rw [Nat.card_eq_fintype_card] at h3_mod
    have h3_mod' : Fintype.card (Sylow 3 G) % 3 = 1 := by
      rwa [Nat.ModEq, Nat.one_mod] at h3_mod
    obtain ⟨P3⟩ := (inferInstance : Nonempty (Sylow 3 G))
    have h3_dvd := P3.card_dvd_index
    rw [Nat.card_eq_fintype_card] at h3_dvd
    have h3_card' : Fintype.card P3 = 3 := by
      have h := sylow_card_of_factorization 3 P3 hcard fact30_val3; simpa using h
    have h3_index : (P3 : Subgroup G).index = 10 := by
      have h_mul := card_mul_index_fintype (P3 : Subgroup G)
      rw [h3_card', hcard] at h_mul; omega
    rw [h3_index] at h3_dvd
    have h3_cands : Fintype.card (Sylow 3 G) = 1 ∨ Fintype.card (Sylow 3 G) = 10 := by
      have : ∀ n : ℕ, n ∣ 10 → n % 3 = 1 → n = 1 ∨ n = 10 := by
        intro n hd hm; have := Nat.le_of_dvd (by omega) hd; interval_cases n <;> omega
      exact this _ h3_dvd h3_mod'
    rcases h3_cands with h3_eq | h3_eq
    · have h_normal := sylow_normal_of_unique G 3 h3_eq P3
      haveI := h_normal
      haveI : IsSolvable (P3 : Subgroup G) := isSolvable_of_isPGroup' P3.isPGroup'
      haveI : IsSolvable (G ⧸ (P3 : Subgroup G)) := by
        have h_card_Q : Fintype.card (G ⧸ (P3 : Subgroup G)) = 10 := by
          rw [← index_eq_fintype_card]; have h_mul := card_mul_index_fintype (P3 : Subgroup G)
          rw [h3_card', hcard] at h_mul; omega
        exact isSolvable_of_card_10 h_card_Q
      exact isSolvable_of_solvable_extension (P3 : Subgroup G)
    · exact absurd (not_both_sylow_max hcard h5_eq h3_eq) (by trivial)


theorem isSolvable_of_card_42
    {G : Type*} [Group G] [Fintype G]
    (hcard : Fintype.card G = 42) : IsSolvable G := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h_mod := card_sylow_modEq_one 7 G
  rw [Nat.card_eq_fintype_card] at h_mod
  have h_mod' : Fintype.card (Sylow 7 G) % 7 = 1 := by
    rwa [Nat.ModEq, Nat.one_mod] at h_mod
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 7 G))
  have h_dvd := P.card_dvd_index
  rw [Nat.card_eq_fintype_card] at h_dvd
  have h_card_P : Fintype.card P = 7 := by
    have h := sylow_card_of_factorization 7 P hcard fact42_val7; simpa using h
  have h_index : (P : Subgroup G).index = 6 := by
    have h_mul := card_mul_index_fintype (P : Subgroup G)
    rw [h_card_P, hcard] at h_mul; omega
  rw [h_index] at h_dvd
  have h_unique : Fintype.card (Sylow 7 G) = 1 := by
    have : ∀ n : ℕ, n ∣ 6 → n % 7 = 1 → n = 1 := by
      intro n hd hm; have := Nat.le_of_dvd (by omega) hd; interval_cases n <;> omega
    exact this _ h_dvd h_mod'
  have h_normal := sylow_normal_of_unique G 7 h_unique P
  haveI := h_normal
  haveI : IsSolvable (P : Subgroup G) := isSolvable_of_isPGroup' P.isPGroup'
  haveI : IsSolvable (G ⧸ (P : Subgroup G)) := by
    have h_card_Q : Fintype.card (G ⧸ (P : Subgroup G)) = 6 := by
      rw [← index_eq_fintype_card]; have h_mul := card_mul_index_fintype (P : Subgroup G)
      rw [h_card_P, hcard] at h_mul; omega
    exact isSolvable_of_card_6 h_card_Q
  exact isSolvable_of_solvable_extension (P : Subgroup G)


/-!
══════════════════════════════════════════════════════════════════════════════
  §S4.
══════════════════════════════════════════════════════════════════════════════
-/

private theorem isSolvable_of_card_pq
    {G : Type*} [Group G] [Fintype G]
    (p q : ℕ) [hp : Fact (Nat.Prime p)] [hq : Fact (Nat.Prime q)]
    (hpq : p < q)
    (hcard : Fintype.card G = p * q)
    (hval : (p * q).factorization q = 1) : IsSolvable G := by
  have h_mod := card_sylow_modEq_one q G
  rw [Nat.card_eq_fintype_card] at h_mod
  have h_mod' : Fintype.card (Sylow q G) % q = 1 := by
    rwa [Nat.ModEq, Nat.mod_eq_of_lt (Nat.Prime.one_lt hq.out)] at h_mod
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow q G))
  have h_dvd := P.card_dvd_index
  rw [Nat.card_eq_fintype_card] at h_dvd
  have h_card_P : Fintype.card P = q := by
    have h := sylow_card_of_factorization q P hcard hval; simpa using h
  have h_index : (P : Subgroup G).index = p := by
    have h_mul := card_mul_index_fintype (P : Subgroup G)
    rw [h_card_P, hcard, mul_comm p q] at h_mul
    exact mul_left_cancel₀ (Nat.Prime.pos hq.out).ne' h_mul
  rw [h_index] at h_dvd
  have h_lt : Fintype.card (Sylow q G) < q :=
    lt_of_le_of_lt (Nat.le_of_dvd (Nat.Prime.pos hp.out) h_dvd) hpq
  have h_unique : Fintype.card (Sylow q G) = 1 := by
    rw [Nat.mod_eq_of_lt h_lt] at h_mod'; exact h_mod'
  have h_normal := sylow_normal_of_unique G q h_unique P
  haveI := h_normal
  haveI : IsSolvable (P : Subgroup G) := isSolvable_of_isPGroup' P.isPGroup'
  haveI : IsSolvable (G ⧸ (P : Subgroup G)) := by
    have h_card_Q : Fintype.card (G ⧸ (P : Subgroup G)) = p := by
      rw [← index_eq_fintype_card]; exact h_index
    exact isSolvable_of_prime_card p h_card_Q
  exact isSolvable_of_solvable_extension (P : Subgroup G)

theorem isSolvable_of_card_14 {G : Type*} [Group G] [Fintype G]
    (h : Fintype.card G = 14) : IsSolvable G :=
  @isSolvable_of_card_pq G _ _ 2 7 ⟨by norm_num⟩ ⟨by norm_num⟩ (by omega)
    (show Fintype.card G = 2 * 7 by omega) (by native_decide)

theorem isSolvable_of_card_21 {G : Type*} [Group G] [Fintype G]
    (h : Fintype.card G = 21) : IsSolvable G :=
  @isSolvable_of_card_pq G _ _ 3 7 ⟨by norm_num⟩ ⟨by norm_num⟩ (by omega)
    (show Fintype.card G = 3 * 7 by omega) (by native_decide)

theorem isSolvable_of_card_22 {G : Type*} [Group G] [Fintype G]
    (h : Fintype.card G = 22) : IsSolvable G :=
  @isSolvable_of_card_pq G _ _ 2 11 ⟨by norm_num⟩ ⟨by norm_num⟩ (by omega)
    (show Fintype.card G = 2 * 11 by omega) (by native_decide)

theorem isSolvable_of_card_26 {G : Type*} [Group G] [Fintype G]
    (h : Fintype.card G = 26) : IsSolvable G :=
  @isSolvable_of_card_pq G _ _ 2 13 ⟨by norm_num⟩ ⟨by norm_num⟩ (by omega)
    (show Fintype.card G = 2 * 13 by omega) (by native_decide)

theorem isSolvable_of_card_33 {G : Type*} [Group G] [Fintype G]
    (h : Fintype.card G = 33) : IsSolvable G :=
  @isSolvable_of_card_pq G _ _ 3 11 ⟨by norm_num⟩ ⟨by norm_num⟩ (by omega)
    (show Fintype.card G = 3 * 11 by omega) (by native_decide)

theorem isSolvable_of_card_34 {G : Type*} [Group G] [Fintype G]
    (h : Fintype.card G = 34) : IsSolvable G :=
  @isSolvable_of_card_pq G _ _ 2 17 ⟨by norm_num⟩ ⟨by norm_num⟩ (by omega)
    (show Fintype.card G = 2 * 17 by omega) (by native_decide)

theorem isSolvable_of_card_35 {G : Type*} [Group G] [Fintype G]
    (h : Fintype.card G = 35) : IsSolvable G :=
  @isSolvable_of_card_pq G _ _ 5 7 ⟨by norm_num⟩ ⟨by norm_num⟩ (by omega)
    (show Fintype.card G = 5 * 7 by omega) (by native_decide)

theorem isSolvable_of_card_38 {G : Type*} [Group G] [Fintype G]
    (h : Fintype.card G = 38) : IsSolvable G :=
  @isSolvable_of_card_pq G _ _ 2 19 ⟨by norm_num⟩ ⟨by norm_num⟩ (by omega)
    (show Fintype.card G = 2 * 19 by omega) (by native_decide)

theorem isSolvable_of_card_39 {G : Type*} [Group G] [Fintype G]
    (h : Fintype.card G = 39) : IsSolvable G :=
  @isSolvable_of_card_pq G _ _ 3 13 ⟨by norm_num⟩ ⟨by norm_num⟩ (by omega)
    (show Fintype.card G = 3 * 13 by omega) (by native_decide)

theorem isSolvable_of_card_46 {G : Type*} [Group G] [Fintype G]
    (h : Fintype.card G = 46) : IsSolvable G :=
  @isSolvable_of_card_pq G _ _ 2 23 ⟨by norm_num⟩ ⟨by norm_num⟩ (by omega)
    (show Fintype.card G = 2 * 23 by omega) (by native_decide)

theorem isSolvable_of_card_51 {G : Type*} [Group G] [Fintype G]
    (h : Fintype.card G = 51) : IsSolvable G :=
  @isSolvable_of_card_pq G _ _ 3 17 ⟨by norm_num⟩ ⟨by norm_num⟩ (by omega)
    (show Fintype.card G = 3 * 17 by omega) (by native_decide)

theorem isSolvable_of_card_55 {G : Type*} [Group G] [Fintype G]
    (h : Fintype.card G = 55) : IsSolvable G :=
  @isSolvable_of_card_pq G _ _ 5 11 ⟨by norm_num⟩ ⟨by norm_num⟩ (by omega)
    (show Fintype.card G = 5 * 11 by omega) (by native_decide)

theorem isSolvable_of_card_57 {G : Type*} [Group G] [Fintype G]
    (h : Fintype.card G = 57) : IsSolvable G :=
  @isSolvable_of_card_pq G _ _ 3 19 ⟨by norm_num⟩ ⟨by norm_num⟩ (by omega)
    (show Fintype.card G = 3 * 19 by omega) (by native_decide)

theorem isSolvable_of_card_58 {G : Type*} [Group G] [Fintype G]
    (h : Fintype.card G = 58) : IsSolvable G :=
  @isSolvable_of_card_pq G _ _ 2 29 ⟨by norm_num⟩ ⟨by norm_num⟩ (by omega)
    (show Fintype.card G = 2 * 29 by omega) (by native_decide)


/-!
══════════════════════════════════════════════════════════════════════════════
  §S5.
══════════════════════════════════════════════════════════════════════════════
-/

theorem isSolvable_of_card_18 {G : Type*} [Group G] [Fintype G]
    (hcard : Fintype.card G = 18) : IsSolvable G := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hval : (18 : ℕ).factorization 3 = 2 := by native_decide
  have h_mod := card_sylow_modEq_one 3 G
  rw [Nat.card_eq_fintype_card] at h_mod
  have h_mod' : Fintype.card (Sylow 3 G) % 3 = 1 := by rwa [Nat.ModEq, Nat.one_mod] at h_mod
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 G))
  have h_dvd := P.card_dvd_index; rw [Nat.card_eq_fintype_card] at h_dvd
  have h_card_P : Fintype.card P = 9 := by
    have h := sylow_card_of_factorization 3 P hcard hval; norm_num at h; exact h
  have h_index : (P : Subgroup G).index = 2 := by
    have h_mul := card_mul_index_fintype (P : Subgroup G); rw [h_card_P, hcard] at h_mul; omega
  rw [h_index] at h_dvd
  have h_unique : Fintype.card (Sylow 3 G) = 1 := by
    have : ∀ n : ℕ, n ∣ 2 → n % 3 = 1 → n = 1 := by intro n hd hm; have := Nat.le_of_dvd (by omega) hd; interval_cases n <;> omega
    exact this _ h_dvd h_mod'
  have h_normal := sylow_normal_of_unique G 3 h_unique P; haveI := h_normal
  haveI : IsSolvable (P : Subgroup G) := isSolvable_of_isPGroup' P.isPGroup'
  haveI : IsSolvable (G ⧸ (P : Subgroup G)) := by
    have h_card_Q : Fintype.card (G ⧸ (P : Subgroup G)) = 2 := by
      rw [← index_eq_fintype_card]; have h_mul := card_mul_index_fintype (P : Subgroup G)
      rw [h_card_P, hcard] at h_mul; omega
    exact isSolvable_of_prime_card 2 h_card_Q
  exact isSolvable_of_solvable_extension (P : Subgroup G)

theorem isSolvable_of_card_20 {G : Type*} [Group G] [Fintype G]
    (hcard : Fintype.card G = 20) : IsSolvable G := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hval : (20 : ℕ).factorization 5 = 1 := by native_decide
  have h_mod := card_sylow_modEq_one 5 G; rw [Nat.card_eq_fintype_card] at h_mod
  have h_mod' : Fintype.card (Sylow 5 G) % 5 = 1 := by rwa [Nat.ModEq, Nat.one_mod] at h_mod
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 5 G))
  have h_dvd := P.card_dvd_index; rw [Nat.card_eq_fintype_card] at h_dvd
  have h_card_P : Fintype.card P = 5 := by
    have h := sylow_card_of_factorization 5 P hcard hval; simpa using h
  have h_index : (P : Subgroup G).index = 4 := by
    have h_mul := card_mul_index_fintype (P : Subgroup G); rw [h_card_P, hcard] at h_mul; omega
  rw [h_index] at h_dvd
  have h_unique : Fintype.card (Sylow 5 G) = 1 := by
    have : ∀ n : ℕ, n ∣ 4 → n % 5 = 1 → n = 1 := by intro n hd hm; have := Nat.le_of_dvd (by omega) hd; interval_cases n <;> omega
    exact this _ h_dvd h_mod'
  have h_normal := sylow_normal_of_unique G 5 h_unique P; haveI := h_normal
  haveI : IsSolvable (P : Subgroup G) := isSolvable_of_isPGroup' P.isPGroup'
  haveI : IsSolvable (G ⧸ (P : Subgroup G)) := by
    have : Fintype.card (G ⧸ (P : Subgroup G)) = 4 := by
      rw [← index_eq_fintype_card]; have := card_mul_index_fintype (P : Subgroup G)
      rw [h_card_P, hcard] at this; omega
    exact isSolvable_of_card_4 this
  exact isSolvable_of_solvable_extension (P : Subgroup G)

theorem isSolvable_of_card_28 {G : Type*} [Group G] [Fintype G]
    (hcard : Fintype.card G = 28) : IsSolvable G := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hval : (28 : ℕ).factorization 7 = 1 := by native_decide
  have h_mod := card_sylow_modEq_one 7 G; rw [Nat.card_eq_fintype_card] at h_mod
  have h_mod' : Fintype.card (Sylow 7 G) % 7 = 1 := by rwa [Nat.ModEq, Nat.one_mod] at h_mod
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 7 G))
  have h_dvd := P.card_dvd_index; rw [Nat.card_eq_fintype_card] at h_dvd
  have h_card_P : Fintype.card P = 7 := by
    have h := sylow_card_of_factorization 7 P hcard hval; simpa using h
  have h_index : (P : Subgroup G).index = 4 := by
    have := card_mul_index_fintype (P : Subgroup G); rw [h_card_P, hcard] at this; omega
  rw [h_index] at h_dvd
  have h_unique : Fintype.card (Sylow 7 G) = 1 := by
    have : ∀ n : ℕ, n ∣ 4 → n % 7 = 1 → n = 1 := by intro n hd hm; have := Nat.le_of_dvd (by omega) hd; interval_cases n <;> omega
    exact this _ h_dvd h_mod'
  have h_normal := sylow_normal_of_unique G 7 h_unique P; haveI := h_normal
  haveI : IsSolvable (P : Subgroup G) := isSolvable_of_isPGroup' P.isPGroup'
  haveI : IsSolvable (G ⧸ (P : Subgroup G)) := by
    have : Fintype.card (G ⧸ (P : Subgroup G)) = 4 := by
      rw [← index_eq_fintype_card]; have := card_mul_index_fintype (P : Subgroup G)
      rw [h_card_P, hcard] at this; omega
    exact isSolvable_of_card_4 this
  exact isSolvable_of_solvable_extension (P : Subgroup G)

theorem isSolvable_of_card_40 {G : Type*} [Group G] [Fintype G]
    (hcard : Fintype.card G = 40) : IsSolvable G := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hval : (40 : ℕ).factorization 5 = 1 := by native_decide
  have h_mod := card_sylow_modEq_one 5 G; rw [Nat.card_eq_fintype_card] at h_mod
  have h_mod' : Fintype.card (Sylow 5 G) % 5 = 1 := by rwa [Nat.ModEq, Nat.one_mod] at h_mod
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 5 G))
  have h_dvd := P.card_dvd_index; rw [Nat.card_eq_fintype_card] at h_dvd
  have h_card_P : Fintype.card P = 5 := by
    have h := sylow_card_of_factorization 5 P hcard hval; simpa using h
  have h_index : (P : Subgroup G).index = 8 := by
    have := card_mul_index_fintype (P : Subgroup G); rw [h_card_P, hcard] at this; omega
  rw [h_index] at h_dvd
  have h_unique : Fintype.card (Sylow 5 G) = 1 := by
    have : ∀ n : ℕ, n ∣ 8 → n % 5 = 1 → n = 1 := by intro n hd hm; have := Nat.le_of_dvd (by omega) hd; interval_cases n <;> omega
    exact this _ h_dvd h_mod'
  have h_normal := sylow_normal_of_unique G 5 h_unique P; haveI := h_normal
  haveI : IsSolvable (P : Subgroup G) := isSolvable_of_isPGroup' P.isPGroup'
  haveI : IsSolvable (G ⧸ (P : Subgroup G)) := by
    have : Fintype.card (G ⧸ (P : Subgroup G)) = 8 := by
      rw [← index_eq_fintype_card]; have := card_mul_index_fintype (P : Subgroup G)
      rw [h_card_P, hcard] at this; omega
    exact isSolvable_of_card_8 this
  exact isSolvable_of_solvable_extension (P : Subgroup G)

theorem isSolvable_of_card_44 {G : Type*} [Group G] [Fintype G]
    (hcard : Fintype.card G = 44) : IsSolvable G := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hval : (44 : ℕ).factorization 11 = 1 := by native_decide
  have h_mod := card_sylow_modEq_one 11 G; rw [Nat.card_eq_fintype_card] at h_mod
  have h_mod' : Fintype.card (Sylow 11 G) % 11 = 1 := by rwa [Nat.ModEq, Nat.one_mod] at h_mod
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 11 G))
  have h_dvd := P.card_dvd_index; rw [Nat.card_eq_fintype_card] at h_dvd
  have h_card_P : Fintype.card P = 11 := by
    have h := sylow_card_of_factorization 11 P hcard hval; simpa using h
  have h_index : (P : Subgroup G).index = 4 := by
    have := card_mul_index_fintype (P : Subgroup G); rw [h_card_P, hcard] at this; omega
  rw [h_index] at h_dvd
  have h_unique : Fintype.card (Sylow 11 G) = 1 := by
    have : ∀ n : ℕ, n ∣ 4 → n % 11 = 1 → n = 1 := by intro n hd hm; have := Nat.le_of_dvd (by omega) hd; interval_cases n <;> omega
    exact this _ h_dvd h_mod'
  have h_normal := sylow_normal_of_unique G 11 h_unique P; haveI := h_normal
  haveI : IsSolvable (P : Subgroup G) := isSolvable_of_isPGroup' P.isPGroup'
  haveI : IsSolvable (G ⧸ (P : Subgroup G)) := by
    have : Fintype.card (G ⧸ (P : Subgroup G)) = 4 := by
      rw [← index_eq_fintype_card]; have := card_mul_index_fintype (P : Subgroup G)
      rw [h_card_P, hcard] at this; omega
    exact isSolvable_of_card_4 this
  exact isSolvable_of_solvable_extension (P : Subgroup G)

theorem isSolvable_of_card_45 {G : Type*} [Group G] [Fintype G]
    (hcard : Fintype.card G = 45) : IsSolvable G := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hval : (45 : ℕ).factorization 5 = 1 := by native_decide
  have h_mod := card_sylow_modEq_one 5 G; rw [Nat.card_eq_fintype_card] at h_mod
  have h_mod' : Fintype.card (Sylow 5 G) % 5 = 1 := by rwa [Nat.ModEq, Nat.one_mod] at h_mod
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 5 G))
  have h_dvd := P.card_dvd_index; rw [Nat.card_eq_fintype_card] at h_dvd
  have h_card_P : Fintype.card P = 5 := by
    have h := sylow_card_of_factorization 5 P hcard hval; simpa using h
  have h_index : (P : Subgroup G).index = 9 := by
    have := card_mul_index_fintype (P : Subgroup G); rw [h_card_P, hcard] at this; omega
  rw [h_index] at h_dvd
  have h_unique : Fintype.card (Sylow 5 G) = 1 := by
    have : ∀ n : ℕ, n ∣ 9 → n % 5 = 1 → n = 1 := by intro n hd hm; have := Nat.le_of_dvd (by omega) hd; interval_cases n <;> omega
    exact this _ h_dvd h_mod'
  have h_normal := sylow_normal_of_unique G 5 h_unique P; haveI := h_normal
  haveI : IsSolvable (P : Subgroup G) := isSolvable_of_isPGroup' P.isPGroup'
  haveI : IsSolvable (G ⧸ (P : Subgroup G)) := by
    have : Fintype.card (G ⧸ (P : Subgroup G)) = 9 := by
      rw [← index_eq_fintype_card]; have := card_mul_index_fintype (P : Subgroup G)
      rw [h_card_P, hcard] at this; omega
    exact isSolvable_of_card_9 this
  exact isSolvable_of_solvable_extension (P : Subgroup G)

theorem isSolvable_of_card_50 {G : Type*} [Group G] [Fintype G]
    (hcard : Fintype.card G = 50) : IsSolvable G := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hval : (50 : ℕ).factorization 5 = 2 := by native_decide
  have h_mod := card_sylow_modEq_one 5 G; rw [Nat.card_eq_fintype_card] at h_mod
  have h_mod' : Fintype.card (Sylow 5 G) % 5 = 1 := by rwa [Nat.ModEq, Nat.one_mod] at h_mod
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 5 G))
  have h_dvd := P.card_dvd_index; rw [Nat.card_eq_fintype_card] at h_dvd
  have h_card_P : Fintype.card P = 25 := by
    have h := sylow_card_of_factorization 5 P hcard hval; norm_num at h; exact h
  have h_index : (P : Subgroup G).index = 2 := by
    have := card_mul_index_fintype (P : Subgroup G); rw [h_card_P, hcard] at this; omega
  rw [h_index] at h_dvd
  have h_unique : Fintype.card (Sylow 5 G) = 1 := by
    have : ∀ n : ℕ, n ∣ 2 → n % 5 = 1 → n = 1 := by intro n hd hm; have := Nat.le_of_dvd (by omega) hd; interval_cases n <;> omega
    exact this _ h_dvd h_mod'
  have h_normal := sylow_normal_of_unique G 5 h_unique P; haveI := h_normal
  haveI : IsSolvable (P : Subgroup G) := isSolvable_of_isPGroup' P.isPGroup'
  haveI : IsSolvable (G ⧸ (P : Subgroup G)) := by
    have : Fintype.card (G ⧸ (P : Subgroup G)) = 2 := by
      rw [← index_eq_fintype_card]; have := card_mul_index_fintype (P : Subgroup G)
      rw [h_card_P, hcard] at this; omega
    exact isSolvable_of_prime_card 2 this
  exact isSolvable_of_solvable_extension (P : Subgroup G)

theorem isSolvable_of_card_52 {G : Type*} [Group G] [Fintype G]
    (hcard : Fintype.card G = 52) : IsSolvable G := by
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hval : (52 : ℕ).factorization 13 = 1 := by native_decide
  have h_mod := card_sylow_modEq_one 13 G; rw [Nat.card_eq_fintype_card] at h_mod
  have h_mod' : Fintype.card (Sylow 13 G) % 13 = 1 := by rwa [Nat.ModEq, Nat.one_mod] at h_mod
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 13 G))
  have h_dvd := P.card_dvd_index; rw [Nat.card_eq_fintype_card] at h_dvd
  have h_card_P : Fintype.card P = 13 := by
    have h := sylow_card_of_factorization 13 P hcard hval; simpa using h
  have h_index : (P : Subgroup G).index = 4 := by
    have := card_mul_index_fintype (P : Subgroup G); rw [h_card_P, hcard] at this; omega
  rw [h_index] at h_dvd
  have h_unique : Fintype.card (Sylow 13 G) = 1 := by
    have : ∀ n : ℕ, n ∣ 4 → n % 13 = 1 → n = 1 := by intro n hd hm; have := Nat.le_of_dvd (by omega) hd; interval_cases n <;> omega
    exact this _ h_dvd h_mod'
  have h_normal := sylow_normal_of_unique G 13 h_unique P; haveI := h_normal
  haveI : IsSolvable (P : Subgroup G) := isSolvable_of_isPGroup' P.isPGroup'
  haveI : IsSolvable (G ⧸ (P : Subgroup G)) := by
    have : Fintype.card (G ⧸ (P : Subgroup G)) = 4 := by
      rw [← index_eq_fintype_card]; have := card_mul_index_fintype (P : Subgroup G)
      rw [h_card_P, hcard] at this; omega
    exact isSolvable_of_card_4 this
  exact isSolvable_of_solvable_extension (P : Subgroup G)

theorem isSolvable_of_card_54 {G : Type*} [Group G] [Fintype G]
    (hcard : Fintype.card G = 54) : IsSolvable G := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hval : (54 : ℕ).factorization 3 = 3 := by native_decide
  have h_mod := card_sylow_modEq_one 3 G; rw [Nat.card_eq_fintype_card] at h_mod
  have h_mod' : Fintype.card (Sylow 3 G) % 3 = 1 := by rwa [Nat.ModEq, Nat.one_mod] at h_mod
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 G))
  have h_dvd := P.card_dvd_index; rw [Nat.card_eq_fintype_card] at h_dvd
  have h_card_P : Fintype.card P = 27 := by
    have h := sylow_card_of_factorization 3 P hcard hval; norm_num at h; exact h
  have h_index : (P : Subgroup G).index = 2 := by
    have := card_mul_index_fintype (P : Subgroup G); rw [h_card_P, hcard] at this; omega
  rw [h_index] at h_dvd
  have h_unique : Fintype.card (Sylow 3 G) = 1 := by
    have : ∀ n : ℕ, n ∣ 2 → n % 3 = 1 → n = 1 := by intro n hd hm; have := Nat.le_of_dvd (by omega) hd; interval_cases n <;> omega
    exact this _ h_dvd h_mod'
  have h_normal := sylow_normal_of_unique G 3 h_unique P; haveI := h_normal
  haveI : IsSolvable (P : Subgroup G) := isSolvable_of_isPGroup' P.isPGroup'
  haveI : IsSolvable (G ⧸ (P : Subgroup G)) := by
    have : Fintype.card (G ⧸ (P : Subgroup G)) = 2 := by
      rw [← index_eq_fintype_card]; have := card_mul_index_fintype (P : Subgroup G)
      rw [h_card_P, hcard] at this; omega
    exact isSolvable_of_prime_card 2 this
  exact isSolvable_of_solvable_extension (P : Subgroup G)

end OrderCases


/-!
══════════════════════════════════════════════════════════════════════════════
  §S6.
══════════════════════════════════════════════════════════════════════════════
-/

section NotSimple

private theorem not_simple_of_card_12
    {G : Type*} [Group G] [Fintype G]
    (hcard : Fintype.card G = 12) : ¬ IsSimpleGroup G := by
  intro h_simple
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have h_mod := card_sylow_modEq_one 2 G; rw [Nat.card_eq_fintype_card] at h_mod
  have h_mod' : Fintype.card (Sylow 2 G) % 2 = 1 := by rwa [Nat.ModEq, Nat.one_mod] at h_mod
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 G))
  have h_dvd := P.card_dvd_index; rw [Nat.card_eq_fintype_card] at h_dvd
  have hval : (12 : ℕ).factorization 2 = 2 := by native_decide
  have h_card_P : Fintype.card P = 4 := by
    have h := sylow_card_of_factorization 2 P hcard hval; norm_num at h; exact h
  have h_index : (P : Subgroup G).index = 3 := by
    have := card_mul_index_fintype (P : Subgroup G); rw [h_card_P, hcard] at this; omega
  rw [h_index] at h_dvd
  have h_cands : Fintype.card (Sylow 2 G) = 1 ∨ Fintype.card (Sylow 2 G) = 3 := by
    have : ∀ n : ℕ, n ∣ 3 → n % 2 = 1 → n = 1 ∨ n = 3 := by
      intro n hd hm; have := Nat.le_of_dvd (by omega) hd; interval_cases n <;> omega
    exact this _ h_dvd h_mod'
  rcases h_cands with h_eq | h_eq
  · exact simple_no_proper_normal_sylow 2 h_simple P
      (sylow_normal_of_unique G 2 h_eq P) (by omega) (by omega)
  · have h_le := simple_card_le_sylow_factorial 2 h_simple (by rw [h_eq]; omega)
    rw [h_eq, hcard] at h_le; norm_num at h_le

private theorem not_simple_of_card_24
    {G : Type*} [Group G] [Fintype G]
    (hcard : Fintype.card G = 24) : ¬ IsSimpleGroup G := by
  intro h_simple
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have h_mod := card_sylow_modEq_one 2 G; rw [Nat.card_eq_fintype_card] at h_mod
  have h_mod' : Fintype.card (Sylow 2 G) % 2 = 1 := by rwa [Nat.ModEq, Nat.one_mod] at h_mod
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 G))
  have h_dvd := P.card_dvd_index; rw [Nat.card_eq_fintype_card] at h_dvd
  have hval : (24 : ℕ).factorization 2 = 3 := by native_decide
  have h_card_P : Fintype.card P = 8 := by
    have h := sylow_card_of_factorization 2 P hcard hval; norm_num at h; exact h
  have h_index : (P : Subgroup G).index = 3 := by
    have := card_mul_index_fintype (P : Subgroup G); rw [h_card_P, hcard] at this; omega
  rw [h_index] at h_dvd
  have h_cands : Fintype.card (Sylow 2 G) = 1 ∨ Fintype.card (Sylow 2 G) = 3 := by
    have : ∀ n : ℕ, n ∣ 3 → n % 2 = 1 → n = 1 ∨ n = 3 := by
      intro n hd hm; have := Nat.le_of_dvd (by omega) hd; interval_cases n <;> omega
    exact this _ h_dvd h_mod'
  rcases h_cands with h_eq | h_eq
  · exact simple_no_proper_normal_sylow 2 h_simple P
      (sylow_normal_of_unique G 2 h_eq P) (by omega) (by omega)
  · have h_le := simple_card_le_sylow_factorial 2 h_simple (by rw [h_eq]; omega)
    rw [h_eq, hcard] at h_le; norm_num at h_le

private theorem not_simple_of_card_36
    {G : Type*} [Group G] [Fintype G]
    (hcard : Fintype.card G = 36) : ¬ IsSimpleGroup G := by
  intro h_simple
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h_mod := card_sylow_modEq_one 3 G; rw [Nat.card_eq_fintype_card] at h_mod
  have h_mod' : Fintype.card (Sylow 3 G) % 3 = 1 := by rwa [Nat.ModEq, Nat.one_mod] at h_mod
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 G))
  have h_dvd := P.card_dvd_index; rw [Nat.card_eq_fintype_card] at h_dvd
  have hval : (36 : ℕ).factorization 3 = 2 := by native_decide
  have h_card_P : Fintype.card P = 9 := by
    have h := sylow_card_of_factorization 3 P hcard hval; norm_num at h; exact h
  have h_index : (P : Subgroup G).index = 4 := by
    have := card_mul_index_fintype (P : Subgroup G); rw [h_card_P, hcard] at this; omega
  rw [h_index] at h_dvd
  have h_cands : Fintype.card (Sylow 3 G) = 1 ∨ Fintype.card (Sylow 3 G) = 4 := by
    have : ∀ n : ℕ, n ∣ 4 → n % 3 = 1 → n = 1 ∨ n = 4 := by
      intro n hd hm; have := Nat.le_of_dvd (by omega) hd; interval_cases n <;> omega
    exact this _ h_dvd h_mod'
  rcases h_cands with h_eq | h_eq
  · exact simple_no_proper_normal_sylow 3 h_simple P
      (sylow_normal_of_unique G 3 h_eq P) (by omega) (by omega)
  · have h_le := simple_card_le_sylow_factorial 3 h_simple (by rw [h_eq]; omega)
    rw [h_eq, hcard] at h_le; norm_num at h_le

private theorem not_simple_of_card_48
    {G : Type*} [Group G] [Fintype G]
    (hcard : Fintype.card G = 48) : ¬ IsSimpleGroup G := by
  intro h_simple
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have h_mod := card_sylow_modEq_one 2 G; rw [Nat.card_eq_fintype_card] at h_mod
  have h_mod' : Fintype.card (Sylow 2 G) % 2 = 1 := by rwa [Nat.ModEq, Nat.one_mod] at h_mod
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 G))
  have h_dvd := P.card_dvd_index; rw [Nat.card_eq_fintype_card] at h_dvd
  have hval : (48 : ℕ).factorization 2 = 4 := by native_decide
  have h_card_P : Fintype.card P = 16 := by
    have h := sylow_card_of_factorization 2 P hcard hval; norm_num at h; exact h
  have h_index : (P : Subgroup G).index = 3 := by
    have := card_mul_index_fintype (P : Subgroup G); rw [h_card_P, hcard] at this; omega
  rw [h_index] at h_dvd
  have h_cands : Fintype.card (Sylow 2 G) = 1 ∨ Fintype.card (Sylow 2 G) = 3 := by
    have : ∀ n : ℕ, n ∣ 3 → n % 2 = 1 → n = 1 ∨ n = 3 := by
      intro n hd hm; have := Nat.le_of_dvd (by omega) hd; interval_cases n <;> omega
    exact this _ h_dvd h_mod'
  rcases h_cands with h_eq | h_eq
  · exact simple_no_proper_normal_sylow 2 h_simple P
      (sylow_normal_of_unique G 2 h_eq P) (by omega) (by omega)
  · have h_le := simple_card_le_sylow_factorial 2 h_simple (by rw [h_eq]; omega)
    rw [h_eq, hcard] at h_le; norm_num at h_le

end NotSimple


/-!
══════════════════════════════════════════════════════════════════════════════
  §S7.
══════════════════════════════════════════════════════════════════════════════
-/

section Order56

theorem isSolvable_of_card_56
    {G : Type*} [Group G] [Fintype G]
    (hcard : Fintype.card G = 56) : IsSolvable G := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hval7 : (56 : ℕ).factorization 7 = 1 := by native_decide
  have hval2 : (56 : ℕ).factorization 2 = 3 := by native_decide
  have h7_mod := card_sylow_modEq_one 7 G; rw [Nat.card_eq_fintype_card] at h7_mod
  have h7_mod' : Fintype.card (Sylow 7 G) % 7 = 1 := by rwa [Nat.ModEq, Nat.one_mod] at h7_mod
  obtain ⟨P7⟩ := (inferInstance : Nonempty (Sylow 7 G))
  have h7_dvd := P7.card_dvd_index; rw [Nat.card_eq_fintype_card] at h7_dvd
  have h7_card : Fintype.card P7 = 7 := by
    have h := sylow_card_of_factorization 7 P7 hcard hval7; simpa using h
  have h7_index : (P7 : Subgroup G).index = 8 := by
    have := card_mul_index_fintype (P7 : Subgroup G); rw [h7_card, hcard] at this; omega
  rw [h7_index] at h7_dvd
  have h7_cands : Fintype.card (Sylow 7 G) = 1 ∨ Fintype.card (Sylow 7 G) = 8 := by
    have : ∀ n : ℕ, n ∣ 8 → n % 7 = 1 → n = 1 ∨ n = 8 := by
      intro n hd hm; have := Nat.le_of_dvd (by omega) hd; interval_cases n <;> omega
    exact this _ h7_dvd h7_mod'
  rcases h7_cands with h7_eq | h7_eq
  ·
    have h_normal := sylow_normal_of_unique G 7 h7_eq P7; haveI := h_normal
    haveI : IsSolvable (P7 : Subgroup G) := isSolvable_of_isPGroup' P7.isPGroup'
    haveI : IsSolvable (G ⧸ (P7 : Subgroup G)) := by
      have : Fintype.card (G ⧸ (P7 : Subgroup G)) = 8 := by
        rw [← index_eq_fintype_card]; have := card_mul_index_fintype (P7 : Subgroup G)
        rw [h7_card, hcard] at this; omega
      exact isSolvable_of_card_8 this
    exact isSolvable_of_solvable_extension (P7 : Subgroup G)
  ·
    have h2_mod := card_sylow_modEq_one 2 G; rw [Nat.card_eq_fintype_card] at h2_mod
    have h2_mod' : Fintype.card (Sylow 2 G) % 2 = 1 := by rwa [Nat.ModEq, Nat.one_mod] at h2_mod
    obtain ⟨P2⟩ := (inferInstance : Nonempty (Sylow 2 G))
    have h2_dvd := P2.card_dvd_index; rw [Nat.card_eq_fintype_card] at h2_dvd
    have h2_card : Fintype.card P2 = 8 := by
      have h := sylow_card_of_factorization 2 P2 hcard hval2; simpa using h
    have h2_index : (P2 : Subgroup G).index = 7 := by
      have := card_mul_index_fintype (P2 : Subgroup G); rw [h2_card, hcard] at this; omega
    rw [h2_index] at h2_dvd
    have h2_cands : Fintype.card (Sylow 2 G) = 1 ∨ Fintype.card (Sylow 2 G) = 7 := by
      have : ∀ n : ℕ, n ∣ 7 → n % 2 = 1 → n = 1 ∨ n = 7 := by
        intro n hd hm; have := Nat.le_of_dvd (by omega) hd; interval_cases n <;> omega
      exact this _ h2_dvd h2_mod'
    rcases h2_cands with h2_eq | h2_eq
    ·
      have h_normal := sylow_normal_of_unique G 2 h2_eq P2; haveI := h_normal
      haveI : IsSolvable (P2 : Subgroup G) := isSolvable_of_isPGroup' P2.isPGroup'
      haveI : IsSolvable (G ⧸ (P2 : Subgroup G)) := by
        have : Fintype.card (G ⧸ (P2 : Subgroup G)) = 7 := by
          rw [← index_eq_fintype_card]; have := card_mul_index_fintype (P2 : Subgroup G)
          rw [h2_card, hcard] at this; omega
        exact isSolvable_of_prime_card 7 this
      exact isSolvable_of_solvable_extension (P2 : Subgroup G)
    ·
      exfalso
      haveI := Classical.decEq G
      have hval7' : (Fintype.card G).factorization 7 = 1 := by rw [hcard]; native_decide
      have hc7 : Fintype.card (NISigma 7 G) = 48 := by
        simp [niSigma_card 7 hval7', h7_eq]
      have h_inj7 := niEmbed_injective 7 hval7'
      let S := Finset.univ.image (niEmbed 7 (G := G))
      have hS_card : S.card = 48 := by
        rw [Finset.card_image_of_injective _ h_inj7, Finset.card_univ, hc7]
      have hSc_card : (Finset.univ \ S).card = 8 := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hcard, hS_card]
      have h_ord_disj : ∀ (Q : Sylow 2 G) (g : G),
          g ∈ (Q : Subgroup G) → g ∉ S := by
        intro Q g hgQ hgS
        rw [Finset.mem_image] at hgS
        obtain ⟨⟨P', x, hx_ne⟩, _, rfl⟩ := hgS
        simp only [niEmbed] at hgQ
        obtain ⟨a, ha⟩ := P'.isPGroup' x
        obtain ⟨b, hb⟩ := Q.isPGroup' ⟨(x : G), hgQ⟩
        have ha' : (x : G) ^ 7 ^ a = 1 := by
          have := congr_arg Subtype.val ha; simpa using this
        have hb' : (x : G) ^ 2 ^ b = 1 := by
          have := congr_arg Subtype.val hb; simpa using this
        have h_dvd7 : orderOf (x : G) ∣ 7 ^ a := orderOf_dvd_of_pow_eq_one ha'
        have h_dvd2 : orderOf (x : G) ∣ 2 ^ b := orderOf_dvd_of_pow_eq_one hb'
        have h_cop : Nat.Coprime (7 ^ a) (2 ^ b) :=
          (by norm_num : Nat.Coprime 7 2).pow a b
        have h_ord1 : orderOf (x : G) = 1 := by
          have h1 := Nat.dvd_gcd h_dvd7 h_dvd2; rw [h_cop] at h1
          exact Nat.dvd_one.mp h1
        exact hx_ne (Subtype.ext (orderOf_eq_one_iff.mp h_ord1))
      have h_Sc_sub_P2 : ∀ g : G, g ∈ Finset.univ \ S → g ∈ (P2 : Subgroup G) := by
        let T := Finset.univ.image (Subtype.val : ↥(P2 : Subgroup G) → G)
        have hT_card : T.card = 8 := by
          rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ, h2_card]
        have hT_sub : T ⊆ Finset.univ \ S := by
          intro x hx; rw [Finset.mem_image] at hx
          obtain ⟨⟨y, hy⟩, _, rfl⟩ := hx
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h_ord_disj P2 y hy⟩
        have hSc_sub_T : Finset.univ \ S ⊆ T := by
          by_contra h_not
          rw [Finset.not_subset] at h_not
          obtain ⟨g, hg_Sc, hg_not_T⟩ := h_not
          have : (insert g T).card ≤ (Finset.univ \ S).card :=
            Finset.card_le_card (Finset.insert_subset hg_Sc hT_sub)
          rw [Finset.card_insert_of_notMem hg_not_T, hT_card, hSc_card] at this; omega
        intro g hg
        have hg_T := hSc_sub_T hg; rw [Finset.mem_image] at hg_T
        obtain ⟨⟨_, hy⟩, _, heq⟩ := hg_T; rwa [← heq]
      have h_all_le : ∀ Q : Sylow 2 G, (Q : Subgroup G) ≤ (P2 : Subgroup G) := by
        intro Q g hgQ
        exact h_Sc_sub_P2 g (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h_ord_disj Q g hgQ⟩)
      have h_all_eq : ∀ Q : Sylow 2 G, Q = P2 := by
        intro Q; apply Sylow.ext
        exact subgroup_eq_of_le_of_card_eq _ _ (h_all_le Q) (by
          have : Fintype.card (Q : Subgroup G) = 8 := by
            have h := sylow_card_of_factorization 2 Q hcard hval2; simpa using h
          rw [this, h2_card])
      have h_one : Fintype.card (Sylow 2 G) = 1 :=
        Fintype.card_eq_one_iff.mpr ⟨P2, fun Q => h_all_eq Q⟩
      linarith [h2_eq]

end Order56


/-!
══════════════════════════════════════════════════════════════════════════════
  §S8.
══════════════════════════════════════════════════════════════════════════════
-/

section StrongInduction

private theorem solvable_of_card_lt_sixty :
    ∀ (n : ℕ), n < 60 →
      ∀ (G : Type*) [Group G] [Fintype G],
        Fintype.card G = n → IsSolvable G := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro h_lt G _grp _fin h_card
    by_contra h_ns
    by_cases h_simple : IsSimpleGroup G
    · have h_nt : Nontrivial G := by
        by_contra h_triv; rw [not_nontrivial_iff_subsingleton] at h_triv
        haveI := h_triv; exact h_ns inferInstance
      have h_card_ge : Fintype.card G ≥ 2 := by
        haveI := h_nt; exact Fintype.one_lt_card
      exfalso; apply h_ns
      haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
      haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
      haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
      haveI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
      haveI : Fact (Nat.Prime 19) := ⟨by norm_num⟩
      haveI : Fact (Nat.Prime 23) := ⟨by norm_num⟩
      haveI : Fact (Nat.Prime 29) := ⟨by norm_num⟩
      haveI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
      haveI : Fact (Nat.Prime 37) := ⟨by norm_num⟩
      haveI : Fact (Nat.Prime 41) := ⟨by norm_num⟩
      haveI : Fact (Nat.Prime 43) := ⟨by norm_num⟩
      haveI : Fact (Nat.Prime 47) := ⟨by norm_num⟩
      haveI : Fact (Nat.Prime 53) := ⟨by norm_num⟩
      haveI : Fact (Nat.Prime 59) := ⟨by norm_num⟩
      interval_cases n
      all_goals (first
        | (exfalso; omega)
        | exact isSolvable_of_prime_card 2 h_card
        | exact isSolvable_of_prime_card 3 h_card
        | exact isSolvable_of_prime_card 5 h_card
        | exact isSolvable_of_prime_card 7 h_card
        | exact isSolvable_of_prime_card 11 h_card
        | exact isSolvable_of_prime_card 13 h_card
        | exact isSolvable_of_prime_card 17 h_card
        | exact isSolvable_of_prime_card 19 h_card
        | exact isSolvable_of_prime_card 23 h_card
        | exact isSolvable_of_prime_card 29 h_card
        | exact isSolvable_of_prime_card 31 h_card
        | exact isSolvable_of_prime_card 37 h_card
        | exact isSolvable_of_prime_card 41 h_card
        | exact isSolvable_of_prime_card 43 h_card
        | exact isSolvable_of_prime_card 47 h_card
        | exact isSolvable_of_prime_card 53 h_card
        | exact isSolvable_of_prime_card 59 h_card
        | exact isSolvable_of_card_4 h_card
        | exact isSolvable_of_card_8 h_card
        | exact isSolvable_of_card_9 h_card
        | exact isSolvable_of_card_16 h_card
        | exact isSolvable_of_card_25 h_card
        | exact isSolvable_of_card_27 h_card
        | exact isSolvable_of_card_32 h_card
        | exact isSolvable_of_card_49 h_card
        | exact isSolvable_of_card_6 h_card
        | exact isSolvable_of_card_10 h_card
        | exact isSolvable_of_card_15 h_card
        | exact isSolvable_of_card_30 h_card
        | exact isSolvable_of_card_42 h_card
        | exact isSolvable_of_card_56 h_card
        | exact isSolvable_of_card_14 h_card
        | exact isSolvable_of_card_21 h_card
        | exact isSolvable_of_card_22 h_card
        | exact isSolvable_of_card_26 h_card
        | exact isSolvable_of_card_33 h_card
        | exact isSolvable_of_card_34 h_card
        | exact isSolvable_of_card_35 h_card
        | exact isSolvable_of_card_38 h_card
        | exact isSolvable_of_card_39 h_card
        | exact isSolvable_of_card_46 h_card
        | exact isSolvable_of_card_51 h_card
        | exact isSolvable_of_card_55 h_card
        | exact isSolvable_of_card_57 h_card
        | exact isSolvable_of_card_58 h_card
        | exact isSolvable_of_card_18 h_card
        | exact isSolvable_of_card_20 h_card
        | exact isSolvable_of_card_28 h_card
        | exact isSolvable_of_card_40 h_card
        | exact isSolvable_of_card_44 h_card
        | exact isSolvable_of_card_45 h_card
        | exact isSolvable_of_card_50 h_card
        | exact isSolvable_of_card_52 h_card
        | exact isSolvable_of_card_54 h_card
        | (exfalso; exact absurd h_simple (not_simple_of_card_12 h_card))
        | (exfalso; exact absurd h_simple (not_simple_of_card_24 h_card))
        | (exfalso; exact absurd h_simple (not_simple_of_card_36 h_card))
        | (exfalso; exact absurd h_simple (not_simple_of_card_48 h_card)))
    ·
      have h_nt : Nontrivial G := by
        by_contra h_triv; rw [not_nontrivial_iff_subsingleton] at h_triv
        haveI := h_triv; exact h_ns inferInstance
      obtain ⟨N, hN_normal, hN_bot, hN_top⟩ :=
        exists_proper_normal_of_not_simple h_nt h_simple
      haveI := hN_normal
      rcases nonsolvable_factor_or_quotient N h_ns with h_fac | h_fac
      · have h_N_lt : Fintype.card N < n := h_card ▸ card_lt_of_ne_top N hN_top
        exact h_fac (ih (Fintype.card N) h_N_lt (by omega) N rfl)
      · have h_Q_lt : Fintype.card (G ⧸ N) < n :=
          h_card ▸ card_quotient_lt_of_ne_bot N hN_bot
        exact h_fac (ih (Fintype.card (G ⧸ N)) h_Q_lt (by omega) (G ⧸ N) rfl)

theorem nonsolvable_order_ge_60 {G : Type*} [Group G] [Fintype G]
    (h_ns : ¬ IsSolvable G) : Fintype.card G ≥ 60 := by
  by_contra h_lt; push_neg at h_lt
  exact h_ns (solvable_of_card_lt_sixty _ h_lt G rfl)

end StrongInduction



theorem groups_below_60_solvable {G : Type*} [Group G] [Fintype G]
    (h : Fintype.card G < 60) : IsSolvable G := by
  by_contra h_ns; exact absurd h (not_lt.mpr (nonsolvable_order_ge_60 h_ns))


theorem A4_solvable : IsSolvable (alternatingGroup (Fin 4)) := by
  apply groups_below_60_solvable
  have : Fintype.card (alternatingGroup (Fin 4)) = 12 := by native_decide
  omega

theorem S4_solvable : IsSolvable (Equiv.Perm (Fin 4)) := by
  apply groups_below_60_solvable
  have : Fintype.card (Equiv.Perm (Fin 4)) = 24 := by native_decide
  omega

theorem S4_not_perfect :
    ⁅(⊤ : Subgroup (Equiv.Perm (Fin 4))),
      (⊤ : Subgroup (Equiv.Perm (Fin 4)))⁆ ≠ ⊤ := by
  apply not_perfect_of_solvable_nontrivial S4_solvable
  have : Fintype.card (Equiv.Perm (Fin 4)) = 24 := by native_decide
  omega

theorem A4_not_perfect :
    ⁅(⊤ : Subgroup (alternatingGroup (Fin 4))),
      (⊤ : Subgroup (alternatingGroup (Fin 4)))⁆ ≠ ⊤ := by
  apply not_perfect_of_solvable_nontrivial A4_solvable
  have : Fintype.card (alternatingGroup (Fin 4)) = 12 := by native_decide
  omega

theorem H3_perfectness_classification :
    (⁅(⊤ : Subgroup (alternatingGroup (Fin 5))), (⊤ : Subgroup (alternatingGroup (Fin 5)))⁆ = ⊤) ∧
    (⁅(⊤ : Subgroup (Equiv.Perm (Fin 4))), (⊤ : Subgroup (Equiv.Perm (Fin 4)))⁆ ≠ ⊤) ∧
    (⁅(⊤ : Subgroup (alternatingGroup (Fin 4))), (⊤ : Subgroup (alternatingGroup (Fin 4)))⁆ ≠ ⊤) :=
  ⟨A5_perfect, S4_not_perfect, A4_not_perfect⟩

end CosmicNecessity
