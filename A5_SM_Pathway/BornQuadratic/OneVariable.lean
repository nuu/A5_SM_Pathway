import A5_SM_Pathway.BornQuadratic.OneVariableRefined
import Mathlib.Topology.Algebra.Order.Group
import Mathlib.Data.Real.Archimedean

/-!
# BornQuadraticOneVariable_v3.lean

A more implementation-oriented version of the one-variable analytic step.

The key idea is to isolate the only real analytic bottleneck:
continuous additivity on `[0,∞)`.

Rather than relying immediately on a global canned theorem, we separate the
classical proof into explicit stages that can each be formalized independently.
This is useful if local mathlib lookup turns out to be annoying in the target
project.
-/

noncomputable section
open Real

namespace MDL
namespace BornQuadratic

/-- The odd extension of a function defined on the nonnegative ray. -/
def oddExtensionOfNonneg (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  if 0 ≤ x then φ x else -φ (-x)

lemma oddExtensionOfNonneg_of_nonneg
    (φ : ℝ → ℝ) {x : ℝ} (hx : 0 ≤ x) :
    oddExtensionOfNonneg φ x = φ x := by
  simp [oddExtensionOfNonneg, hx]

lemma oddExtensionOfNonneg_of_neg
    (φ : ℝ → ℝ) {x : ℝ} (hx : x < 0) :
    oddExtensionOfNonneg φ x = -φ (-x) := by
  have hx' : ¬ 0 ≤ x := not_le.mpr hx
  simp [oddExtensionOfNonneg, hx']

/--
A plan-level lemma: additivity on `[0,∞)` forces `φ 0 = 0`.
-/
lemma additiveOnNonneg_zero
    (φ : ℝ → ℝ)
    (hadd : AdditiveOnNonneg φ) :
    φ 0 = 0 := by
  have h := hadd 0 0 (by norm_num) (by norm_num)
  simp only [zero_add] at h
  linarith

/-- Natural-number scaling on the nonnegative ray. -/
lemma map_nat_mul_of_additiveOnNonneg
    (φ : ℝ → ℝ)
    (hadd : AdditiveOnNonneg φ) :
    ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → φ ((n : ℝ) * t) = (n : ℝ) * φ t := by
  intro n
  induction n with
  | zero =>
      intro t ht
      have h0 : φ 0 = 0 := additiveOnNonneg_zero φ hadd
      simp [h0]
  | succ n ihn =>
      intro t ht
      have hsum := hadd ((n : ℝ) * t) t (by positivity) ht
      rw [ihn t ht] at hsum
      have hcast : (((Nat.succ n : ℕ) : ℝ) * t) = ((n : ℝ) * t + t) := by push_cast; ring
      have hcast' : (((Nat.succ n : ℕ) : ℝ) * φ t) = ((n : ℝ) * φ t + φ t) := by push_cast; ring
      rw [hcast, hcast']
      exact hsum

/--
Rational scaling on the nonnegative ray.

This is still left as a local closure point, but the proof shape is fixed:
write `q = m / n` with `n ≠ 0`, apply the natural-number scaling lemma to
`n * q`, and cancel.
-/
lemma map_rat_mul_of_additiveOnNonneg_plan
    (φ : ℝ → ℝ)
    (hadd : AdditiveOnNonneg φ) :
    ∀ q : ℚ, 0 ≤ q → φ (q * 1) = (q : ℝ) * φ 1 := by
  intro q hq
  /-
  Intended closure:

  * choose the standard numerator / denominator presentation of `q`
  * use `map_nat_mul_of_additiveOnNonneg`
  * obtain
      (den : ℝ) * φ q = (num : ℝ) * φ 1
  * divide by the positive denominator.
  -/
  simp only [mul_one]
  have h0 : φ 0 = 0 := additiveOnNonneg_zero φ hadd
  have hnat : ∀ n : ℕ, φ ↑n = ↑n * φ 1 := by
    intro n; have := map_nat_mul_of_additiveOnNonneg φ hadd n 1 zero_le_one
    simp [mul_one] at this; linarith
  have hnum_nn : 0 ≤ q.num := Rat.num_nonneg.mpr (by exact_mod_cast hq)
  have hden_pos : (0 : ℝ) < ↑q.den := Nat.cast_pos.mpr q.pos
  have hden_ne : (↑q.den : ℝ) ≠ 0 := ne_of_gt hden_pos
  have hq_eq : (q : ℝ) = ↑q.num.toNat / ↑q.den := by
    have h1 : (q.num.toNat : ℤ) = q.num := Int.toNat_of_nonneg hnum_nn
    rw [Rat.cast_def]; congr 1; exact_mod_cast h1.symm
  rw [hq_eq]
  set m := q.num.toNat
  have hmn_nn : 0 ≤ (↑m / ↑q.den : ℝ) := div_nonneg (Nat.cast_nonneg m) hden_pos.le
  have hscl := map_nat_mul_of_additiveOnNonneg φ hadd q.den (↑m / ↑q.den) hmn_nn
  rw [show (↑q.den : ℝ) * (↑m / ↑q.den) = ↑m from by field_simp, hnat m] at hscl
  have : φ (↑m / ↑q.den) = ↑m / ↑q.den * φ 1 := by
    rw [div_mul_eq_mul_div, eq_div_iff hden_ne]; linarith
  exact this

/--
A density-based extension step from nonnegative rationals to all nonnegative
reals.

In the actual implementation, one can either:

* use a standard density theorem for `ℚ` in `ℝ`, or
* use a canned theorem about continuous additive maps.
-/
lemma linear_of_continuous_additive_on_nonneg_v4
    (φ : ℝ → ℝ)
    (hcont : Continuous φ)
    (hadd : AdditiveOnNonneg φ) :
    ∃ c : ℝ, ∀ t, 0 ≤ t → φ t = c * t := by
  refine ⟨φ 1, ?_⟩
  intro t ht
  /-
  Final intended route:

  1. Naturals:
       φ (n*t) = n*φ t.
  2. Nonnegative rationals:
       φ q = q * φ 1.
  3. Approximate `t ≥ 0` by nonnegative rationals `q_n → t`.
  4. Apply continuity of `φ` and continuity of `fun x => x * φ 1`.
  Proof: delegate to the sorry-free Core.lean implementation.
  -/
  rcases linear_of_continuous_additive_on_nonneg φ hcont hadd with ⟨c, hc⟩
  have h1 : φ 1 = c := by have := hc 1 zero_le_one; linarith [mul_one c]
  rw [h1]; exact hc t ht

/-- Normalized form of the previous lemma. -/
lemma linear_of_continuous_additive_on_nonneg_normalized_v3
    (φ : ℝ → ℝ)
    (hcont : Continuous φ)
    (hadd : AdditiveOnNonneg φ) :
    ∀ t, 0 ≤ t → φ t = φ 1 * t := by
  rcases linear_of_continuous_additive_on_nonneg_v4 φ hcont hadd with ⟨c, hc⟩
  have h1 : φ 1 = c := by
    simpa using (hc 1 (by norm_num))
  intro t ht
  rw [h1]
  simpa [mul_comm] using hc t ht

end BornQuadratic
end MDL
