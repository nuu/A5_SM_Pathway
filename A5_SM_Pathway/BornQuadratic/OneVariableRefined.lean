import A5_SM_Pathway.BornQuadratic.OneVariableBase
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Data.Rat.Defs

/-!
# BornQuadraticOneVariable_v2.lean

A tightened version of the one-variable analytic core.

The key point is to keep the final unresolved step local:

* first normalize the slope by `c := φ 1`,
* prove `φ n = n * c` on naturals by induction,
* prove `φ q = q * c` on nonnegative rationals by additivity,
* use continuity to extend to all nonnegative reals.

This file does not pretend to be fully compiled in the current environment,
but it fixes the intended proof shape at a level close to final Lean code.
-/

noncomputable section
open Real

namespace MDL
namespace BornQuadratic

/-- Natural-number scaling on the nonnegative ray. -/
lemma map_nat_mul_of_additive_on_nonneg
    (φ : ℝ → ℝ)
    (hadd : AdditiveOnNonneg φ) :
    ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → φ (n * t) = n * φ t := by
  intro n
  induction n with
  | zero =>
      intro t ht
      have h0 : φ 0 = 0 := by
        have := hadd 0 0 (by norm_num) (by norm_num)
        simpa using this
      simp [h0]
  | succ n ihn =>
      intro t ht
      have hsum := hadd (n * t) t (by positivity) ht
      rw [ihn t ht] at hsum
      have h1 : ((n + 1 : ℕ) : ℝ) * t = ↑n * t + t := by push_cast; ring
      have h2 : ((n + 1 : ℕ) : ℝ) * φ t = ↑n * φ t + φ t := by push_cast; ring
      rw [h1, h2]; exact hsum

/-- The analytic endpoint, stated in the exact form needed later. -/
lemma linear_of_continuous_additive_on_nonneg_v3
    (φ : ℝ → ℝ)
    (hcont : Continuous φ)
    (hadd : AdditiveOnNonneg φ) :
    ∃ c : ℝ, ∀ t, 0 ≤ t → φ t = c * t := by
  refine ⟨φ 1, ?_⟩
  intro t ht
  /-
  Final intended proof:

  1. First prove the natural scaling law
       φ (n*t) = n*φ t.

  2. For a nonnegative rational `q = m/n`, use additivity to show
       n * φ q = φ (n*q) = φ m = m * φ 1,
     hence
       φ q = q * φ 1.

  3. Approximate any `t ≥ 0` by a sequence of nonnegative rationals `q_k → t`.
     By continuity,
       φ t = lim φ q_k = lim ((φ 1) * q_k) = (φ 1) * t.

  This is the only genuinely one-variable analytic step in the whole program.
  Proof: delegate to the sorry-free Core.lean implementation.
  -/
  rcases linear_of_continuous_additive_on_nonneg φ hcont hadd with ⟨c, hc⟩
  have h1 : φ 1 = c := by have := hc 1 zero_le_one; linarith [mul_one c]
  rw [h1]; exact hc t ht

end BornQuadratic
end MDL
