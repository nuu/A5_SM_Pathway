import A5_SM_Pathway.BornQuadratic.Reduction
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# BornQuadraticExponentHelpers.lean

Helper lemmas for the final exponent extraction step in the Born-quadratic
program.

The intended logical flow is:

* once one has proved `I(v) = c * sqNorm v`,
* homogeneity gives `(2:ℝ)^α * I v = I (2 • v)`,
* the quadratic formula gives `I (2 • v) = 4 * I v`,
* after cancelling a nonzero value one gets `(2:ℝ)^α = 4`,
* and therefore `α = 2`.

This file isolates the final analytic step so that the geometric and
representation-theoretic files do not need to carry it.
-/

noncomputable section
open Real

namespace MDL
namespace BornQuadratic

/--
Cancellation helper on the right.
-/
private lemma eq_of_mul_eq_mul_right_nonzero
    {a b k : ℝ} (hk : k ≠ 0) (h : a * k = b * k) : a = b := by
  exact mul_right_cancel₀ hk h

/--
If a positive base has equal real powers, the exponents agree.

For the present application we only need the base `2`, but the statement is
worth keeping slightly more general.
-/
lemma rpow_left_injective_of_one_lt
    {x : ℝ} (hx : 1 < x) {a b : ℝ} (h : x ^ a = x ^ b) : a = b := by
  have hx_pos : (0 : ℝ) < x := by linarith
  have hlog_ne : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have : a * Real.log x = b * Real.log x := by
    calc a * Real.log x = Real.log (x ^ a) := (Real.log_rpow hx_pos a).symm
      _ = Real.log (x ^ b) := by rw [h]
      _ = b * Real.log x := Real.log_rpow hx_pos b
  exact mul_right_cancel₀ hlog_ne this

/--
The exact exponent-extraction step needed later.
-/
lemma eq_two_of_two_rpow_eq_four {α : ℝ} (h : (2 : ℝ) ^ α = 4) : α = 2 := by
  have h' : (2 : ℝ) ^ α = (2 : ℝ) ^ (2 : ℝ) := by
    rw [h]; norm_num
  exact rpow_left_injective_of_one_lt (x := 2) (by norm_num) h'

/--
A packaged version matching the scaled-intensity use case.
-/
lemma eq_two_of_scaled_homogeneous_identity
    {α k : ℝ} (hk : k ≠ 0)
    (h : (2 : ℝ) ^ α * k = 4 * k) : α = 2 := by
  have h' : (2 : ℝ) ^ α = 4 := by
    apply eq_of_mul_eq_mul_right_nonzero (k := k) hk
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  exact eq_two_of_two_rpow_eq_four h'

end BornQuadratic
end MDL
