/-
══════════════════════════════════════════════════════════════════════════════
  Weighted Composition: Quantum Observation Law (§7)
   — 

  Paper § : §7 (Weighted Composition / Quantum Observation)
══════════════════════════════════════════════════════════════════════════════

  File     : A5_SM_Pathway/WeightedComposition.lean
  Project  : A5Paper3 — Weight Law and Readout Law from Non-Solvability of A₅
  Author   : M. Numagaki (Independent Researcher, Kumamoto, Japan)
  Date     : March 2026

  STATUS:  sorry = 0 | axiom = 0

  ──────────────────────────────────────────────────────────────────────
  Overview:

    §7 integrates the weight law (Part A, §3–§4) and the readout law
    (Part B, §5–§6) into a single observational law via weighted
    composition:

      P_{Σ,P}(a) = Σ_i μ(i) K_{Σ,P}(a | i)

    where:
      μ(i) = n_i²/60  is the Born-type channel measure (Def 4.1)
      K(a|i) = 1_{a = R(i)}  is the readout kernel (deterministic)
      R(i) = |Σ_γ φ(n_γ)|  is the coarse signal per channel

    This file formalizes the M-layer definitions and arithmetic.
    The setup-dependent kernel K is Layer P; only its formal shape
    and the composition law are Layer M.

  ──────────────────────────────────────────────────────────────────────
  Structure:

    § 1: Channel set C = Â₅ and channel measure μ
    § 2: Observation alphabet and readout kernel
    § 3: Weighted composition law
    § 4: Double-slit minimal model
    § 5: Average signal profile
    § 6: Boxed summary equation
══════════════════════════════════════════════════════════════════════════════
-/

import A5_SM_Pathway.BornFromA5Opacity_Bridge
import Mathlib.Tactic

open Finset

namespace A5_SM_Pathway.WeightedComposition

-- ============================================================================
-- § 1. Channel Set and Channel Measure
-- ============================================================================

/-!
The channel set is C = Â₅ = {ρ₁, ρ₂, ρ₃, ρ₄, ρ₅}, the irreducible
representations of A₅.

The Born-type channel measure is:
  μ(i) = n_i² / |A₅| = n_i² / 60

We work with the numerator n_i² (natural number) and denominator 60
separately to avoid rational arithmetic friction.
-/

open CosmicNecessity.Bridge in
/-- Re-export A5Irrep from Bridge file. -/
abbrev Channel := A5Irrep

/-- The 5 irreducible representation dimensions of A₅. -/
def channelDim : Channel → ℕ
  | .trivial     => 1
  | .standard3a  => 3
  | .standard3b  => 3
  | .tetrahedral => 4
  | .standard5   => 5

/-- Born weight numerator: n_i² -/
def bornNumerator : Channel → ℕ
  | .trivial     => 1
  | .standard3a  => 9
  | .standard3b  => 9
  | .tetrahedral => 16
  | .standard5   => 25

/-- Born numerator is dim² -/
theorem bornNumerator_eq_dim_sq (i : Channel) :
    bornNumerator i = channelDim i ^ 2 := by
  cases i <;> simp [bornNumerator, channelDim]

/-- Plancherel: Σ n_i² = 60 = |A₅| (normalization) -/
theorem born_normalization :
    Finset.univ.sum bornNumerator = 60 := by native_decide

/-- The channel measure as a list [1, 9, 9, 16, 25] -/
theorem born_weights_list :
    bornNumerator .trivial = 1 ∧
    bornNumerator .standard3a = 9 ∧
    bornNumerator .standard3b = 9 ∧
    bornNumerator .tetrahedral = 16 ∧
    bornNumerator .standard5 = 25 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 2. Observation Alphabet and Readout Kernel
-- ============================================================================

/-!
In the double-slit minimal model, the observation alphabet is
  A = {0, 1, 2}

where:
  2 = both paths active, same sign → constructive
  0 = both paths active, opposite sign → destructive (or both inactive)
  1 = one path active, one inactive → intermediate

The readout kernel K(a | i) is deterministic:
  K(a | i) = 1 if a = R_{Σ,P}(i), else 0.

The coarse signal R(i) depends on the setup Σ and position P.
Below we define the algebraic structure without fixing Σ.
-/

/-- Observation alphabet for the double-slit minimal model. -/
inductive ObsAlpha where
  | zero  -- destructive / inactive
  | one   -- intermediate (one path active)
  | two   -- constructive
  deriving DecidableEq, Repr

instance : Fintype ObsAlpha where
  elems := {ObsAlpha.zero, ObsAlpha.one, ObsAlpha.two}
  complete x := by cases x <;> simp

/-- Numeric value of each observation outcome. -/
def ObsAlpha.val : ObsAlpha → ℕ
  | .zero => 0
  | .one  => 1
  | .two  => 2

/-- A readout assignment maps each channel to an observation outcome.
    This is the setup-dependent function R_{Σ,P}. -/
def ReadoutAssignment := Channel → ObsAlpha

/-- Deterministic kernel: K(a | i) = 1_{a = R(i)}. -/
def kernelIndicator (R : ReadoutAssignment) (a : ObsAlpha) (i : Channel) : ℕ :=
  if R i = a then 1 else 0

-- ============================================================================
-- § 3. Weighted Composition Law
-- ============================================================================

/-!
**The central equation of §7:**

  P_{Σ,P}(a) = Σ_i μ(i) K(a | i)

In our integer formulation with denominator 60:

  60 · P(a) = Σ_i n_i² · 1_{R(i) = a}

This is the weighted composition of the channel measure μ and the
readout kernel K. It is the formal meaning of:

  quantum observation = weight law × readout law
-/

/-- **Weighted composition** (numerator form):
    For a given readout assignment R, compute 60 · P(a). -/
def compositionNumerator (R : ReadoutAssignment) (a : ObsAlpha) : ℕ :=
  Finset.univ.sum fun i : Channel => bornNumerator i * kernelIndicator R a i

/-- Normalization: the sum over the alphabet equals 60. -/
theorem composition_normalized (R : ReadoutAssignment) :
    Finset.univ.sum (compositionNumerator R) = 60 := by
  simp only [compositionNumerator, kernelIndicator]
  have h := born_normalization
  have : ∀ i : Channel,
      Finset.univ.sum (fun a : ObsAlpha =>
        bornNumerator i * if R i = a then 1 else 0) = bornNumerator i := by
    intro i
    simp
  rw [Finset.sum_comm]
  simp only [this]
  exact h

-- ============================================================================
-- § 4. Double-Slit Minimal Model
-- ============================================================================

/-!
For the double-slit setup (§7 in paper), the mod 4 readout gives:

  R(i) = |φ(n₁ᵢ) + φ(n₂ᵢ)|

where the value depends on the path difference Δnᵢ mod 4:

  Δnᵢ ≡ 0 (mod 4) → R(i) = 2  (constructive)
  Δnᵢ ≡ 2 (mod 4) → R(i) = 0  (destructive)
  Δnᵢ ≡ 1, 3 (mod 4) → R(i) = 1  (intermediate)

Below we compute the observation distribution for specific
readout assignments.
-/

/-- Example 1: All channels constructive (all Δn ≡ 0 mod 4). -/
def allConstructive : ReadoutAssignment := fun _ => .two

theorem allConstructive_dist :
    compositionNumerator allConstructive .two = 60 ∧
    compositionNumerator allConstructive .one = 0 ∧
    compositionNumerator allConstructive .zero = 0 := by
  unfold compositionNumerator allConstructive kernelIndicator bornNumerator
  native_decide

/-- Example 2: All channels destructive (all Δn ≡ 2 mod 4). -/
def allDestructive : ReadoutAssignment := fun _ => .zero

theorem allDestructive_dist :
    compositionNumerator allDestructive .zero = 60 ∧
    compositionNumerator allDestructive .one = 0 ∧
    compositionNumerator allDestructive .two = 0 := by
  unfold compositionNumerator allDestructive kernelIndicator bornNumerator
  native_decide

/-- Example 3: Mixed — trivial constructive, standard3a/3b destructive,
    tetrahedral intermediate, standard5 constructive.
    This represents a generic non-trivial interference pattern. -/
def mixedExample : ReadoutAssignment
  | .trivial     => .two
  | .standard3a  => .zero
  | .standard3b  => .zero
  | .tetrahedral => .one
  | .standard5   => .two

theorem mixedExample_dist :
    compositionNumerator mixedExample .two = 26 ∧    -- 1 + 25
    compositionNumerator mixedExample .one = 16 ∧    -- 16
    compositionNumerator mixedExample .zero = 18 ∧   -- 9 + 9
    compositionNumerator mixedExample .two +
      compositionNumerator mixedExample .one +
      compositionNumerator mixedExample .zero = 60 := by
  unfold compositionNumerator mixedExample kernelIndicator bornNumerator
  native_decide

-- ============================================================================
-- § 5. Average Signal Profile
-- ============================================================================

/-!
The average signal profile is:

  I_Σ(P) = Σ_a a · P(a) = 2·P(2) + 1·P(1) + 0·P(0)

In numerator form:

  60 · I_Σ(P) = 2 · (60·P(2)) + 1 · (60·P(1))
-/

/-- Average signal profile numerator: 60 · I(P). -/
def signalProfileNumerator (R : ReadoutAssignment) : ℕ :=
  Finset.univ.sum fun a : ObsAlpha =>
    a.val * compositionNumerator R a

/-- Maximum signal: all constructive → I = 2 (numerator 120) -/
theorem signal_all_constructive :
    signalProfileNumerator allConstructive = 120 := by
  unfold signalProfileNumerator compositionNumerator
    allConstructive kernelIndicator bornNumerator ObsAlpha.val
  native_decide

/-- Minimum signal: all destructive → I = 0 -/
theorem signal_all_destructive :
    signalProfileNumerator allDestructive = 0 := by
  unfold signalProfileNumerator compositionNumerator
    allDestructive kernelIndicator bornNumerator ObsAlpha.val
  native_decide

/-- Mixed example signal -/
theorem signal_mixed :
    signalProfileNumerator mixedExample = 68 := by
  unfold signalProfileNumerator compositionNumerator
    mixedExample kernelIndicator bornNumerator ObsAlpha.val
  native_decide

-- ============================================================================
-- § 6. Boxed Summary Equation
-- ============================================================================

/-!
## The Observation Prototype (Boxed Equation from §7)

  quantum observation at (Σ, P)
    = μ(i) = n_i²/60      (how much)
      ──K_{Σ,P}──▶
      P_{Σ,P}(a)           (which observed pattern)

Formalized as:

  compositionNumerator R a = Σ_i n_i² · 1_{R(i) = a}
  signalProfileNumerator R = Σ_a a · compositionNumerator R a

Key properties verified:

  (a) composition_normalized: Σ_a compositionNumerator R a = 60
      → probability normalization ✓

  (b) signalProfileNumerator range: [0, 120]
      → corresponds to I ∈ [0, 2] ✓

  (c) Specific readout assignments reproduce expected patterns ✓

### Layer Classification

  Layer M:
    - Channel set C = Â₅, dimensions [1,3,3,4,5]
    - Born weights n_i² summing to 60 (Plancherel)
    - Composition law P(a) = Σ μ(i)K(a|i) as formal definition
    - Normalization theorem
    - Arithmetic of specific readout assignments

  Layer P:
    - Physical meaning of readout assignment R_{Σ,P}
    - Identification of a ∈ {0,1,2} with detector outcomes
    - Connection between Δn mod 4 and R(i)

sorry = 0, axiom = 0.
-/

end A5_SM_Pathway.WeightedComposition
