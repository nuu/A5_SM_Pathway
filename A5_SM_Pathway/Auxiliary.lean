/-
══════════════════════════════════════════════════════════════════════════════
  Auxiliary.lean — （Sylow ）
  Auxiliary lemmas: number theory, combinatorics, Sylow toolkit
══════════════════════════════════════════════════════════════════════════════

  File     : WallOf60/Auxiliary.lean
  Paper    : §3.1 — Auxiliary module (~276 lines)
  Author   : (Masaru Numagaki)
  Date     : February 2026

  STATUS:  sorry = 0 | axiom = 0

  :
    - 
    - Sylow （）
    - （NISigma, niEmbed）
    - /
══════════════════════════════════════════════════════════════════════════════
-/

import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

set_option maxRecDepth 4000

namespace CosmicNecessity

open Classical

/-!
══════════════════════════════════════════════════════════════════════════════
  §A1. 
══════════════════════════════════════════════════════════════════════════════
-/

/-- A nonsolvable group must have a nonsolvable normal subgroup or quotient. -/
theorem nonsolvable_factor_or_quotient
    {G : Type*} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal] (h_ns : ¬ IsSolvable G) :
    ¬ IsSolvable N ∨ ¬ IsSolvable (G ⧸ N) := by
  by_contra h; push_neg at h
  obtain ⟨hN, hQ⟩ := h
  exact h_ns (by
    haveI := hN; haveI := hQ
    exact solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype]))

/-- A non-simple nontrivial group has a proper nontrivial normal subgroup. -/
theorem exists_proper_normal_of_not_simple
    {G : Type*} [Group G] [Fintype G]
    (h_nt : Nontrivial G) (h_ns : ¬ IsSimpleGroup G) :
    ∃ (N : Subgroup G), N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
  by_contra h; push_neg at h
  haveI := h_nt
  exact h_ns ⟨fun N hN => by
    by_cases hbot : N = ⊥
    · exact Or.inl hbot
    · exact Or.inr (h N hN hbot)⟩

/-- A proper subgroup has strictly smaller cardinality. -/
theorem card_lt_of_ne_top {G : Type*} [Group G] [Fintype G]
    (N : Subgroup G) (h : N ≠ ⊤) :
    Fintype.card N < Fintype.card G := by
  have h_mul := Subgroup.card_mul_index N
  simp only [Nat.card_eq_fintype_card] at h_mul
  have h_idx_ne : N.index ≠ 1 := fun h1 => h (Subgroup.index_eq_one.mp h1)
  have h_idx_pos : 0 < N.index := by
    rcases Nat.eq_zero_or_pos N.index with h0 | h0
    · rw [h0, mul_zero] at h_mul; linarith [Fintype.card_pos (α := G)]
    · exact h0
  have h_idx_ge : 2 ≤ N.index := by omega
  have h_N_pos : 0 < Fintype.card N := Fintype.card_pos
  nlinarith

/-- A quotient by a nontrivial normal subgroup has strictly smaller cardinality. -/
theorem card_quotient_lt_of_ne_bot {G : Type*} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal] (h : N ≠ ⊥) :
    Fintype.card (G ⧸ N) < Fintype.card G := by
  have h_mul := Subgroup.card_mul_index N
  simp only [Nat.card_eq_fintype_card] at h_mul
  have h_idx_eq : N.index = Fintype.card (G ⧸ N) := by
    rw [Subgroup.index, Nat.card_eq_fintype_card]
  rw [h_idx_eq] at h_mul
  have h_N_ge : 2 ≤ Fintype.card N := by
    by_contra h_lt; push_neg at h_lt
    apply h
    haveI : Subsingleton N := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    exact Subgroup.eq_bot_of_subsingleton N
  have h_Q_pos : 0 < Fintype.card (G ⧸ N) := Fintype.card_pos
  nlinarith

/--  2  -/
theorem card_ge_two_of_ne_bot {G : Type*} [Group G] [Fintype G]
    (N : Subgroup G) (h : N ≠ ⊥) : 2 ≤ Fintype.card N := by
  by_contra h_lt; push_neg at h_lt
  exact h (by
    haveI : Subsingleton N := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    exact Subgroup.eq_bot_of_subsingleton N)

/--  2  -/
theorem card_quotient_ge_two_of_ne_top {G : Type*} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal] (h : N ≠ ⊤) : 2 ≤ Fintype.card (G ⧸ N) := by
  by_contra h_lt; push_neg at h_lt
  apply h
  rw [Subgroup.eq_top_iff']
  intro g
  have h_Q_le := show Fintype.card (G ⧸ N) ≤ 1 by omega
  have h_Q_ss := Fintype.card_le_one_iff_subsingleton.mp h_Q_le
  have : (QuotientGroup.mk g : G ⧸ N) = (QuotientGroup.mk 1 : G ⧸ N) :=
    h_Q_ss.elim _ _
  have h_mem := QuotientGroup.eq.mp this
  simp only [mul_one] at h_mem
  exact N.inv_mem_iff.mp h_mem


/-!
══════════════════════════════════════════════════════════════════════════════
  §A2. Sylow 
══════════════════════════════════════════════════════════════════════════════
-/

section SylowToolkit

/-- Sylow  -/
theorem sylow_normal_of_unique (G : Type*) [Group G] [Fintype G]
    (p : ℕ) [Fact (Nat.Prime p)]
    (h_one : Fintype.card (Sylow p G) = 1)
    (P : Sylow p G) : (P : Subgroup G).Normal := by
  haveI : Subsingleton (Sylow p G) :=
    Fintype.card_le_one_iff_subsingleton.mp (le_of_eq h_one)
  exact P.normal_of_subsingleton

/-- Sylow  factorization  -/
theorem sylow_card_of_factorization
    {G : Type*} [Group G] [Fintype G]
    (p : ℕ) [Fact (Nat.Prime p)]
    (P : Sylow p G)
    {n : ℕ} (hcard : Fintype.card G = n)
    {k : ℕ} (hval : n.factorization p = k) :
    Fintype.card P = p ^ k := by
  have h := P.card_eq_multiplicity
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
  rw [hcard, hval] at h; exact h

/-- A group of prime order is solvable. -/
theorem isSolvable_of_prime_card
    {G : Type*} [Group G] [Fintype G]
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    (hcard : Fintype.card G = p) : IsSolvable G := by
  have h_pg : IsPGroup p G := by
    intro g
    have h_ord : orderOf g ∣ Fintype.card G := orderOf_dvd_card
    rw [hcard] at h_ord
    rcases hp.out.eq_one_or_self_of_dvd _ h_ord with h | h
    · exact ⟨0, by rw [pow_zero, pow_one]; exact orderOf_eq_one_iff.mp h⟩
    · exact ⟨1, by rw [pow_one, ← h]; exact pow_orderOf_eq_one g⟩
  haveI := h_pg.isNilpotent; infer_instance

/-- |G| = p^k (p )  p- -/
private theorem isPGroup_of_card_prime_pow {G : Type*} [Group G] [Fintype G]
    {p : ℕ} (hp : Nat.Prime p) {k : ℕ} (hcard : Fintype.card G = p ^ k) :
    IsPGroup p G := by
  intro g
  have h_dvd : orderOf g ∣ p ^ k := by
    have := @orderOf_dvd_card G _ _ g; rwa [hcard] at this
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow hp).mp h_dvd
  exact ⟨j, by rw [← hj]; exact pow_orderOf_eq_one g⟩

/-- A group of prime power order is solvable. -/
theorem isSolvable_of_prime_power {G : Type*} [Group G] [Fintype G]
    {p : ℕ} (hp : Nat.Prime p) {k : ℕ} (hcard : Fintype.card G = p ^ k) :
    IsSolvable G := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI := (isPGroup_of_card_prime_pow hp hcard).isNilpotent; infer_instance

/-- Sylow p  p  →  -/
theorem simple_no_proper_normal_sylow
    (p : ℕ) [Fact (Nat.Prime p)]
    {G : Type*} [Group G] [Fintype G]
    (h_simple : IsSimpleGroup G)
    (P : Sylow p G)
    (h_normal : (P : Subgroup G).Normal)
    (h_ne_bot : Fintype.card (P : Subgroup G) ≠ 1)
    (h_ne_top : Fintype.card (P : Subgroup G) ≠ Fintype.card G) :
    False := by
  rcases h_simple.2 (P : Subgroup G) h_normal with h | h
  · apply h_ne_bot
    have : Nat.card (P : Subgroup G) = 1 := by rw [h, Subgroup.card_bot]
    rwa [← Nat.card_eq_fintype_card]
  · apply h_ne_top
    have : Nat.card (P : Subgroup G) = Nat.card G := by rw [h, Subgroup.card_top]
    rwa [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card (α := G)]

/--  Sylow p  > 1  |G| ≤ n! -/
theorem simple_card_le_sylow_factorial
    (p : ℕ) [Fact (Nat.Prime p)]
    {G : Type*} [Group G] [Fintype G]
    (h_simple : IsSimpleGroup G)
    (h_gt : Fintype.card (Sylow p G) > 1) :
    Fintype.card G ≤ Nat.factorial (Fintype.card (Sylow p G)) := by
  -- Sylow  φ : G →* Perm(Sylow p G) 
  set φ := MulAction.toPermHom G (Sylow p G)
  --  → ker = ⊥ → φ 
  have h_ker : φ.ker = ⊥ := by
    rcases h_simple.2 φ.ker (inferInstance : φ.ker.Normal) with h | h
    · exact h
    · -- ker = ⊤ →  Sylow  → Sylow  1 
      exfalso
      have h_fix : ∀ (g : G) (P : Sylow p G), g • P = P := by
        intro g P
        have hg : g ∈ φ.ker := h ▸ Subgroup.mem_top g
        have h_one : φ g = 1 := MonoidHom.mem_ker.mp hg
        have := Equiv.Perm.ext_iff.mp h_one P
        simpa [φ] using this
      --  Sylow  → card = 1 → 
      have : Subsingleton (Sylow p G) := by
        constructor; intro P Q
        obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
        rwa [h_fix g P] at hg
      exact Nat.lt_irrefl 1 (lt_of_lt_of_le h_gt
        (Fintype.card_le_one_iff_subsingleton.mpr this))
  have h_inj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp h_ker
  calc Fintype.card G
      ≤ Fintype.card (Equiv.Perm (Sylow p G)) :=
        Fintype.card_le_of_injective _ h_inj
    _ = Nat.factorial (Fintype.card (Sylow p G)) := Fintype.card_perm

end SylowToolkit


/-!
══════════════════════════════════════════════════════════════════════════════
  §A3. 
══════════════════════════════════════════════════════════════════════════════
-/

section IntersectionLemma

theorem card_le_of_subgroup_le {G : Type*} [Group G] [Fintype G]
    (H K : Subgroup G) (h_le : H ≤ K) :
    Fintype.card H ≤ Fintype.card K := by
  apply Fintype.card_le_of_injective (fun ⟨g, hg⟩ => ⟨g, h_le hg⟩)
  intro ⟨a, _⟩ ⟨b, _⟩ h
  simp [Subtype.ext_iff] at h ⊢; exact h

theorem subgroup_eq_of_le_of_card_eq {G : Type*} [Group G] [Fintype G]
    (H K : Subgroup G) (h_le : H ≤ K) (h_card : Fintype.card H = Fintype.card K) :
    H = K := by
  have h_bij : Function.Bijective (Subgroup.inclusion h_le) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨Subgroup.inclusion_injective h_le, h_card⟩
  ext g; constructor
  · exact fun hg => h_le hg
  · intro hg
    obtain ⟨⟨x, hx⟩, hx_eq⟩ := h_bij.2 ⟨g, hg⟩
    simp [Subgroup.inclusion, Subtype.ext_iff] at hx_eq
    rw [← hx_eq]; exact hx

/--  Sylow （factorization = 1） -/
theorem sylow_inf_eq_bot_of_ne
    {G : Type*} [Group G] [Fintype G]
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    (P Q : Sylow p G)
    (h_val : (Fintype.card G).factorization p = 1)
    (hne : P ≠ Q) :
    (P : Subgroup G) ⊓ (Q : Subgroup G) = ⊥ := by
  set I : Subgroup G := (P : Subgroup G) ⊓ (Q : Subgroup G) with I_def
  have hP_card : Fintype.card (P : Subgroup G) = p := by
    have h := P.card_eq_multiplicity
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, h_val] at h
    simpa using h
  have hQ_card : Fintype.card (Q : Subgroup G) = p := by
    have h := Q.card_eq_multiplicity
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, h_val] at h
    simpa using h
  have h_le_P : I ≤ (P : Subgroup G) := inf_le_left
  have h_card_le : Fintype.card I ≤ p := by
    calc Fintype.card I
        ≤ Fintype.card (P : Subgroup G) := card_le_of_subgroup_le _ _ h_le_P
      _ = p := hP_card
  have h_pg_PQ : IsPGroup p I := by
    intro ⟨g, hg⟩
    have hg_in_P : g ∈ (P : Subgroup G) := h_le_P hg
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨g, hg_in_P⟩
    exact ⟨k, Subtype.ext (by
      have := Subtype.ext_iff.mp hk
      simpa using this)⟩
  obtain ⟨k, hk⟩ := h_pg_PQ.exists_card_eq
  rw [Nat.card_eq_fintype_card] at hk
  have hk_le : k ≤ 1 := by
    by_contra h_gt; push_neg at h_gt
    have : p ^ k ≥ p ^ 2 := Nat.pow_le_pow_right (Nat.Prime.pos hp.out) h_gt
    have : p ^ 2 > p := by have := hp.out.one_lt; nlinarith
    linarith [hk ▸ h_card_le]
  interval_cases k
  · rw [pow_zero] at hk
    haveI : Subsingleton I := Fintype.card_le_one_iff_subsingleton.mp (le_of_eq hk)
    exact Subgroup.eq_bot_of_subsingleton I
  · exfalso; rw [pow_one] at hk
    have h_eq_P := subgroup_eq_of_le_of_card_eq _ _ h_le_P (by rw [hk, hP_card])
    have h_PQ : (P : Subgroup G) ≤ (Q : Subgroup G) := by
      rw [← h_eq_P]; exact inf_le_right
    have h_eq := subgroup_eq_of_le_of_card_eq _ _ h_PQ (by rw [hP_card, hQ_card])
    exact hne (Sylow.ext h_eq)

end IntersectionLemma


/-!
══════════════════════════════════════════════════════════════════════════════
  §A4. （NISigma, niEmbed）
══════════════════════════════════════════════════════════════════════════════

  Sylow 
  
══════════════════════════════════════════════════════════════════════════════
-/

section ElementCounting

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

theorem card_ne_one {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    Fintype.card { x : α // x ≠ a } = Fintype.card α - 1 := by
  rw [show Fintype.card { x : α // x ≠ a } =
      Fintype.card { x : α // ¬(x = a) } from rfl]
  rw [Fintype.card_subtype_compl]
  have h_eq_card : Fintype.card { x : α // x = a } = 1 := by
    convert Fintype.card_unique
    exact { default := ⟨a, rfl⟩, uniq := fun ⟨x, hx⟩ => Subtype.ext hx }
  omega

/-- Σ: Sylow p  -/
abbrev NISigma (p : ℕ) [Fact (Nat.Prime p)] (G : Type*) [Group G] [Fintype G] :=
  Σ (P : Sylow p G), { g : (P : Subgroup G) // g ≠ 1 }

/-- NISigma  G  -/
def niEmbed (p : ℕ) [Fact (Nat.Prime p)] {G : Type*} [Group G] [Fintype G] :
    NISigma p G → G :=
  fun ⟨_, g, _⟩ => (g : G)

/-- factorization = 1  niEmbed  -/
theorem niEmbed_injective
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (h_val : (Fintype.card G).factorization p = 1) :
    Function.Injective (niEmbed p (G := G)) := by
  intro ⟨P₁, g₁, hg₁⟩ ⟨P₂, g₂, hg₂⟩ h_eq
  simp only [niEmbed] at h_eq
  have hP_eq : P₁ = P₂ := by
    by_contra hne
    have h_bot := sylow_inf_eq_bot_of_ne p P₁ P₂ h_val hne
    have hg_inf : (g₁ : G) ∈ (P₁ : Subgroup G) ⊓ (P₂ : Subgroup G) :=
      Subgroup.mem_inf.mpr ⟨g₁.property, h_eq ▸ g₂.property⟩
    rw [h_bot] at hg_inf
    exact hg₁ (Subtype.ext (Subgroup.mem_bot.mp hg_inf))
  subst hP_eq
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext (Subtype.ext h_eq)))

/-- NISigma  = (Sylow ) × (p - 1) -/
theorem niSigma_card
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (h_val : (Fintype.card G).factorization p = 1) :
    Fintype.card (NISigma p G) = Fintype.card (Sylow p G) * (p - 1) := by
  rw [Fintype.card_sigma]
  have h_fiber : ∀ P : Sylow p G,
      Fintype.card { g : (P : Subgroup G) // g ≠ 1 } = p - 1 := by
    intro P
    have h_card_P : Fintype.card (P : Subgroup G) = p := by
      have h := P.card_eq_multiplicity
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, h_val] at h
      simpa using h
    rw [card_ne_one, h_card_P]
  simp_rw [h_fiber, Finset.sum_const, Finset.card_univ]
  ring

/--  p ≠ q  Sylow  G  -/
theorem niEmbed_images_disjoint_general
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {p q : ℕ} [hp : Fact (Nat.Prime p)] [hq : Fact (Nat.Prime q)]
    (hpq : p ≠ q) :
    ∀ x : NISigma p G, ∀ y : NISigma q G,
      niEmbed p x ≠ niEmbed q y := by
  intro ⟨P, gP, hgP⟩ ⟨Q, gQ, hgQ⟩ h_eq
  simp only [niEmbed] at h_eq
  -- gP ∈ Sylow p → orderOf (↑gP : G) divides p^a
  obtain ⟨a, ha⟩ := P.isPGroup' gP
  have h_dvd_p : orderOf (gP : G) ∣ p ^ a := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_dvd_of_pow_eq_one ha
  -- gQ ∈ Sylow q → orderOf (↑gQ : G) divides q^b
  obtain ⟨b, hb⟩ := Q.isPGroup' gQ
  have h_dvd_q : orderOf (gQ : G) ∣ q ^ b := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_dvd_of_pow_eq_one hb
  -- h_eq : (↑gP : G) = (↑gQ : G) → same orderOf
  rw [h_eq] at h_dvd_p
  -- orderOf (↑gQ) divides coprime p^a and q^b → orderOf = 1
  have h_coprime : Nat.Coprime (p ^ a) (q ^ b) :=
    Nat.coprime_pow_primes a b hp.out hq.out hpq
  have h_one : orderOf (gQ : G) = 1 :=
    Nat.eq_one_of_dvd_coprimes h_coprime h_dvd_p h_dvd_q
  exact hgQ (Subtype.ext (orderOf_eq_one_iff.mp h_one))

/-- 5  3  Sylow （ 30 ） -/
theorem niEmbed_images_disjoint_5_3
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    [Fact (Nat.Prime 5)] [Fact (Nat.Prime 3)] :
    ∀ x : NISigma 5 G, ∀ y : NISigma 3 G,
      niEmbed 5 x ≠ niEmbed 3 y :=
  niEmbed_images_disjoint_general (by omega : (5:ℕ) ≠ 3)

/-- n₅=6 ∧ n₃=10 → |G|=30 （） -/
theorem not_both_sylow_max
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (hcard : Fintype.card G = 30)
    (hn5 : Fintype.card (Sylow 5 G) = 6)
    (hn3 : Fintype.card (Sylow 3 G) = 10) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hval5 : (Fintype.card G).factorization 5 = 1 := by rw [hcard]; native_decide
  have hval3 : (Fintype.card G).factorization 3 = 1 := by rw [hcard]; native_decide
  have hc5 : Fintype.card (NISigma 5 G) = 24 := by
    rw [niSigma_card 5 hval5, hn5]
  have hc3 : Fintype.card (NISigma 3 G) = 20 := by
    rw [niSigma_card 3 hval3, hn3]
  have h_inj5 := niEmbed_injective 5 hval5
  have h_inj3 := niEmbed_injective 3 hval3
  have h_disj := @niEmbed_images_disjoint_5_3 G _ _ _ ⟨by norm_num⟩ ⟨by norm_num⟩
  let f : NISigma 5 G ⊕ NISigma 3 G → G :=
    fun x => match x with
    | Sum.inl a => niEmbed 5 a
    | Sum.inr b => niEmbed 3 b
  have hf_inj : Function.Injective f := by
    intro a b hab
    match a, b with
    | Sum.inl a', Sum.inl b' => exact congrArg _ (h_inj5 hab)
    | Sum.inr a', Sum.inr b' => exact congrArg _ (h_inj3 hab)
    | Sum.inl a', Sum.inr b' => exact absurd hab (h_disj a' b')
    | Sum.inr a', Sum.inl b' => exact absurd hab.symm (h_disj b' a')
  have h_le := Fintype.card_le_of_injective f hf_inj
  rw [Fintype.card_sum, hc5, hc3, hcard] at h_le
  omega

end ElementCounting


/-!
══════════════════════════════════════════════════════════════════════════════
  §A5.  (Solvable + Nontrivial → Not Perfect)
══════════════════════════════════════════════════════════════════════════════
-/

section Perfectness

/-- **** -/
theorem not_perfect_of_solvable_nontrivial
    {G : Type*} [Group G] [Fintype G]
    (h_solv : IsSolvable G) (h_card : 1 < Fintype.card G) :
    ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≠ (⊤ : Subgroup G) := by
  intro h_perf
  have h_all_top : ∀ n, derivedSeries G n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      show ⁅derivedSeries G n, derivedSeries G n⁆ = ⊤
      rw [ih]; exact h_perf
  obtain ⟨n, hn⟩ := h_solv.solvable
  rw [h_all_top n] at hn
  have h_triv : ∀ g : G, g = 1 := by
    intro g
    have hg : g ∈ (⊤ : Subgroup G) := Subgroup.mem_top g
    rw [hn] at hg
    exact Subgroup.mem_bot.mp hg
  have : Fintype.card G ≤ 1 := by
    rw [Fintype.card_le_one_iff]
    intro a b; rw [h_triv a, h_triv b]
  omega

end Perfectness


/-!
══════════════════════════════════════════════════════════════════════════════
  §A6. 
══════════════════════════════════════════════════════════════════════════════
-/

section SolvabilityTransfer

/-- **** -/
theorem solvable_of_injective_to_solvable
    {G Q : Type*} [Group G] [Group Q] [Fintype Q] [IsSolvable Q]
    (f : G →* Q) (hf : Function.Injective f) : IsSolvable G :=
  solvable_of_solvable_injective hf

end SolvabilityTransfer


/-!
══════════════════════════════════════════════════════════════════════════════
  §A6.  — Shared Primitive Definitions
══════════════════════════════════════════════════════════════════════════════
-/

--  (icosahedron) 
def Ico_F : ℕ := 20   -- 
def Ico_E : ℕ := 30   -- 
def Ico_V : ℕ := 12   -- 
def Ico_n : ℕ := 3    --  ()
def Ico_chi : ℕ := 2  -- Euler 
def Ico_ord : ℕ := 60 -- |A₅|

-- 
def Stab_face : ℕ := 3  --  (Z₃)
def Stab_edge : ℕ := 2  --  (Z₂)
def Stab_vert : ℕ := 5  --  (Z₅)

-- 
def Tet_F : ℕ := 4
def Tet_E : ℕ := 6
def Tet_V : ℕ := 4

-- 
def Oct_F : ℕ := 8
def Oct_E : ℕ := 12
def Oct_V : ℕ := 6

-- KleinType: Klein  5  (Klein 1884)
inductive KleinType where
  | cyclic     : ℕ → KleinType      -- C_n ( n)
  | dihedral   : ℕ → KleinType      -- D_n ( 2n)
  | tetrahedral : KleinType          -- A₄ ≅ T ( 12)
  | octahedral  : KleinType          -- S₄ ≅ O ( 24)
  | icosahedral : KleinType          -- A₅ ≅ I ( 60)
  deriving DecidableEq, Repr

def KleinType.order : KleinType → ℕ
  | .cyclic n    => n
  | .dihedral n  => 2 * n
  | .tetrahedral => 12
  | .octahedral  => 24
  | .icosahedral => 60

def KleinType.isPolyhedral : KleinType → Bool
  | .cyclic _    => false
  | .dihedral _  => false
  | .tetrahedral => true
  | .octahedral  => true
  | .icosahedral => true

def kleintypePassesH2 : KleinType → Bool
  | KleinType.cyclic _    => false
  | KleinType.dihedral _  => false
  | KleinType.tetrahedral => true
  | KleinType.octahedral  => true
  | KleinType.icosahedral => true

def kleintypePassesH3 : KleinType → Bool
  | KleinType.cyclic n    => n ≤ 1
  | KleinType.dihedral _  => false
  | KleinType.tetrahedral => false
  | KleinType.octahedral  => false
  | KleinType.icosahedral => true

--  A₅/A₄/S₄ 
theorem A5_card : Fintype.card (alternatingGroup (Fin 5)) = 60 := by native_decide
theorem A4_card : Fintype.card (alternatingGroup (Fin 4)) = 12 := by native_decide
theorem S4_card : Fintype.card (Equiv.Perm (Fin 4)) = 24 := by native_decide
theorem A5_is_simple : IsSimpleGroup (alternatingGroup (Fin 5)) :=
  alternatingGroup.isSimpleGroup_five
theorem A5_not_commutative :
    ¬ ∀ (a b : alternatingGroup (Fin 5)), a * b = b * a := by
  push_neg
  let σ : alternatingGroup (Fin 5) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 2 3,
     Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩
  let τ : alternatingGroup (Fin 5) :=
    ⟨Equiv.swap 1 2 * Equiv.swap 3 4,
     Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩
  exact ⟨σ, τ, by rw [Ne, Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_mul]; decide⟩
theorem A5_not_solvable : ¬ IsSolvable (alternatingGroup (Fin 5)) := by
  rw [← IsSimpleGroup.comm_iff_isSolvable]
  intro h_comm
  let σ : alternatingGroup (Fin 5) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 2 3,
     Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩
  let τ : alternatingGroup (Fin 5) :=
    ⟨Equiv.swap 1 2 * Equiv.swap 3 4,
     Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩
  exact (show σ * τ ≠ τ * σ by
    rw [Ne, Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_mul]; decide) (h_comm σ τ)
theorem S5_not_solvable : ¬ IsSolvable (Equiv.Perm (Fin 5)) :=
  Equiv.Perm.fin_5_not_solvable

/-- **A₅ ** (perfect): [A₅, A₅] = A₅ -/
theorem A5_perfect :
    ⁅(⊤ : Subgroup (alternatingGroup (Fin 5))),
      (⊤ : Subgroup (alternatingGroup (Fin 5)))⁆ = ⊤ := by
  let G := alternatingGroup (Fin 5)
  haveI hsimple : IsSimpleGroup G := alternatingGroup.isSimpleGroup_five
  have h_ne_bot : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≠ ⊥ := by
    intro hbot
    have hcomm : ∀ a b : G, a * b = b * a := by
      have hcenter : Subgroup.center G = ⊤ :=
        (commutator_eq_bot_iff_center_eq_top (G := G)).mp hbot
      intro a b
      have ha : a ∈ Subgroup.center G := by simp [hcenter]
      exact ((Subgroup.mem_center_iff.mp ha) b).symm
    exact A5_not_solvable ((IsSimpleGroup.comm_iff_isSolvable).mp hcomm)
  have h_bot_or_top : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊥ ∨ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤ :=
    Subgroup.Normal.eq_bot_or_eq_top
      (H := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆)
      (Subgroup.commutator_normal ⊤ ⊤)
  exact h_bot_or_top.resolve_left h_ne_bot

end CosmicNecessity
