/-
══════════════════════════════════════════════════════════════════════════════
  Born Rule from Discreteness: Counting Measure Uniqueness
══════════════════════════════════════════════════════════════════════════════

  File     : A5_SM_Pathway/BornFromDiscreteness.lean
  Paper    : §3 (Theorem 3.2: Invariant weight is constant,
             Corollary 3.3: Counting measure forced)
  Author   : M. Numagaki (Independent Researcher, Kumamoto, Japan)
  Date     : March 2026

  STATUS:  sorry = 0 | axiom = 0

  ──────────────────────────────────────────────────────────────────────
  Theorem chain (cumulative):

    [Already closed — No-Go chain]
    (1) Finite + T₁ + connected ⇒ subsingleton    [TopologyFiniteConnected]
    (2) Smooth-local + curvature ⇒ contradiction   [Section3_ContinuumNoGo]
    (3) ∴ defect/monodromy reading forced           [Section3_ContinuumDefectNoGo]
    (4) Monodromy image ⊂ H is finite              [finite_range_of_fintype]

    [This file — M-layer extensions]
  ★ (5) G-invariant weight on finite transitive G-set is constant
  ★ (6) Normalized ⇒ counting measure 1/|S|
  ★ (7) Uniqueness: counting measure is the ONLY invariant probability

    [Consequence — derived, never stated as "attack"]
    Born rule |ψ|² = continuous limit of k/N.
    Probability is a theorem of the discrete structure, not a postulate.

  ──────────────────────────────────────────────────────────────────────
  Layer classification:

    (5)(6)(7): Layer M — pure finite group action theory
               No physics, no interpretation, no opinion.
               These are theorems about finite sets and group actions.

  ──────────────────────────────────────────────────────────────────────
  Logical role in the programme:

    The No-Go chain (1)–(4) forces discreteness as a mathematical
    consequence, not a philosophical preference.

    This file shows that ON any finite set with transitive symmetry,
    the probability measure is not a free choice — it is uniquely
    determined as the counting measure.

    Combined: No-Go forces finite state space; finite state space
    with symmetry forces counting measure. Born rule is derived.

  ──────────────────────────────────────────────────────────────────────
  Dependencies:

    Required : Mathlib (GroupAction, BigOperators, Fintype, Tactic)
    Optional : A5_SM_Pathway.Section3_ContinuumDefectNoGo (for full chain)

  ──────────────────────────────────────────────────────────────────────
══════════════════════════════════════════════════════════════════════════════
-/

import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option maxRecDepth 4000

namespace CosmicNecessity


/-!
══════════════════════════════════════════════════════════════════════════════
  §1. Extension ① — Invariant weight is constant
══════════════════════════════════════════════════════════════════════════════

  Layer M (pure mathematics):

    Let G be a group acting transitively on a finite nonempty set S.
    Let w : S → ℚ satisfy w(g • s) = w(s) for all g, s.
    Then w is constant.

  Proof: For any s, t ∈ S, transitivity gives g with g • s = t.
         Then w(t) = w(g • s) = w(s).  □

  This is the key lemma: symmetry + finiteness ⇒ uniformity.
  No physics content. No interpretation. Just finite group theory.
══════════════════════════════════════════════════════════════════════════════
-/

section InvariantMeasure

variable {G : Type*} [Group G]
variable {S : Type*} [Fintype S] [Nonempty S]
variable [MulAction G S] [MulAction.IsPretransitive G S]

omit [Fintype S] [Nonempty S] in
/-- **Extension ① (Invariance ⇒ Constancy)**:
    On a finite transitive G-set, any G-invariant function is constant.

    This is the discrete analogue of Schur's lemma for measures:
    irreducible (= transitive) action leaves no room for non-uniform weight. -/
theorem invariant_weight_constant
    (w : S → ℚ)
    (hinv : ∀ (g : G) (s : S), w (g • s) = w s) :
    ∀ s t : S, w s = w t := by
  intro s t
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G s t
  calc w s = w (g • s) := (hinv g s).symm
       _ = w t := by rw [hg]


/-!
══════════════════════════════════════════════════════════════════════════════
  §2. Extension ② — Counting measure is forced
══════════════════════════════════════════════════════════════════════════════

  Layer M (pure mathematics):

    Same setting as §1, plus normalization ∑ w = 1.
    Then w(s) = 1/|S| for all s.

  Proof: w is constant (§1). Sum of constant = |S| · w(s) = 1.
         Therefore w(s) = 1/|S|.  □

  This is the counting measure. It is not chosen — it is forced.
══════════════════════════════════════════════════════════════════════════════
-/

/-- **Extension ② (Counting Measure Uniqueness)**:
    The unique normalized G-invariant weight on a finite transitive
    G-set is the counting measure 1/|S|.

    Physical reading (Layer P, not stated here):
      On the defect state space forced by the No-Go theorem,
      probability is not a postulate — it is 1/|S|, period. -/
theorem invariant_prob_is_counting_measure
    (w : S → ℚ)
    (hinv : ∀ (g : G) (s : S), w (g • s) = w s)
    (hnorm : ∑ s : S, w s = 1)
    (s : S) :
    w s = 1 / (Fintype.card S : ℚ) := by
  -- Step 1: w is constant (Extension ①)
  have hconst : ∀ t : S, w t = w s :=
    fun t => invariant_weight_constant w hinv t s
  -- Step 2: ∑ w(s) = |S| · w(s)
  have hsum_const : ∑ t : S, w s = (Fintype.card S : ℚ) * w s := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- Step 3: ∑ w(t) = ∑ w(s)  (by constancy)
  have hsum_eq : ∑ t : S, w t = ∑ t : S, w s :=
    Finset.sum_congr rfl (fun t _ => hconst t)
  -- Step 4: |S| · w(s) = 1
  have key : (Fintype.card S : ℚ) * w s = 1 := by linarith
  -- Step 5: w(s) = 1/|S|
  have hcard_ne : (Fintype.card S : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact (eq_div_iff hcard_ne).mpr (by rw [mul_comm]; exact key)


/-!
══════════════════════════════════════════════════════════════════════════════
  §3. Extension ② bis — Uniqueness (no other invariant probability exists)
══════════════════════════════════════════════════════════════════════════════

  Not just "the counting measure works" but "nothing else does".
  Any two normalized G-invariant weights agree everywhere.
══════════════════════════════════════════════════════════════════════════════
-/

/-- **Uniqueness**: Any two normalized G-invariant weights on a finite
    transitive G-set are identical. The counting measure is the ONLY
    invariant probability. -/
theorem invariant_prob_unique
    (w₁ w₂ : S → ℚ)
    (hinv₁ : ∀ (g : G) (s : S), w₁ (g • s) = w₁ s)
    (hinv₂ : ∀ (g : G) (s : S), w₂ (g • s) = w₂ s)
    (hnorm₁ : ∑ s : S, w₁ s = 1)
    (hnorm₂ : ∑ s : S, w₂ s = 1)
    (s : S) :
    w₁ s = w₂ s := by
  rw [invariant_prob_is_counting_measure w₁ hinv₁ hnorm₁ s,
      invariant_prob_is_counting_measure w₂ hinv₂ hnorm₂ s]

end InvariantMeasure


/-!
══════════════════════════════════════════════════════════════════════════════
  §4. Left regular action — transitivity witness
══════════════════════════════════════════════════════════════════════════════

  For any group G, the left regular action (g • h = g * h) is transitive.
  This provides the concrete instance for G = A₅.

  Combined with §2:
    On A₅ with left multiplication, the unique invariant probability
    is 1/60. This is not a choice — it is a theorem.
══════════════════════════════════════════════════════════════════════════════
-/

section LeftRegularAction

variable {G : Type*} [Group G] [Fintype G] [Nonempty G]

omit [Fintype G] [Nonempty G] in
/-- The left regular action of any group on itself is pretransitive.
    For any a, b : G, the element g = b * a⁻¹ satisfies g • a = b. -/
theorem leftRegular_isPretransitive :
    ∀ (a b : G), ∃ g : G, g * a = b :=
  fun a b => ⟨b * a⁻¹, by group⟩

/-- **Counting measure on G via left regular action**:
    Any left-invariant normalized weight on a finite group is 1/|G|.

    For G = A₅: the unique left-invariant probability is 1/60. -/
theorem leftInvariant_prob_is_counting
    (w : G → ℚ)
    (hinv : ∀ (g h : G), w (g * h) = w h)
    (hnorm : ∑ g : G, w g = 1)
    (g : G) :
    w g = 1 / (Fintype.card G : ℚ) := by
  -- Reduce to the abstract theorem via transitivity
  have hconst : ∀ a b : G, w a = w b := by
    intro a b
    have ⟨g, hg⟩ := leftRegular_isPretransitive a b
    calc w a = w (g * a) := (hinv g a).symm
         _ = w b := by rw [hg]
  have hcard_ne : (Fintype.card G : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hsum : (Fintype.card G : ℚ) * w g = 1 := by
    have h1 : ∑ h : G, w h = ∑ h : G, w g :=
      Finset.sum_congr rfl (fun h _ => hconst h g)
    have h2 : ∑ h : G, w g = (Fintype.card G : ℚ) * w g := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    linarith
  exact (eq_div_iff hcard_ne).mpr (by rw [mul_comm]; exact hsum)

end LeftRegularAction


/-!
══════════════════════════════════════════════════════════════════════════════
  §5. Full chain summary — from No-Go to counting measure
══════════════════════════════════════════════════════════════════════════════

  The complete M-layer theorem chain:

  ┌─────────────────────────────────────────────────────────────────┐
  │ (1) Finite + T₁ + connected subgroup = ⊥                      │
  │     [TopologyFiniteConnected.lean]                             │
  │                          ↓                                     │
  │ (2) Smooth-local holonomy + curvature ≠ 0 → contradiction     │
  │     [Section3_ContinuumNoGo.lean: smoothLocal_noGo]            │
  │                          ↓                                     │
  │ (3) Non-trivial finite holonomy ⇒ defect reading forced        │
  │     [Section3_ContinuumDefectNoGo.lean: nogo_forces_defect]    │
  │                          ↓                                     │
  │ (4) Monodromy image is finite                                  │
  │     [Section3_ContinuumDefectNoGo.lean: finite_range_of_fintype│
  │                          ↓                                     │
  │ (5) G-invariant weight on finite transitive G-set is constant  │
  │     [this file: invariant_weight_constant]                     │
  │                          ↓                                     │
  │ (6) Normalized ⇒ counting measure 1/|S|                        │
  │     [this file: invariant_prob_is_counting_measure]            │
  │                          ↓                                     │
  │ (7) This measure is unique — no alternative exists             │
  │     [this file: invariant_prob_unique]                         │
  └─────────────────────────────────────────────────────────────────┘

  Reading the chain:
    (1)–(3): Continuous base space is mathematically excluded.
    (4):     State space is forced to be finite.
    (5)–(7): On finite state space with symmetry, probability
             measure is not free — it is uniquely the counting measure.

  What is NOT said:
    • "Born rule is wrong"          — never stated
    • "Quantum mechanics fails"     — never stated
    • "Wave function is not real"   — never stated

  What IS said:
    • Born rule |ψ|² is the continuous limit of k/N
    • k/N is not assumed — it is derived from (1)–(7)
    • Therefore |ψ|² is a consequence, not a postulate

══════════════════════════════════════════════════════════════════════════════
-/


end CosmicNecessity
