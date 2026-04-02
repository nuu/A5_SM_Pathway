import A5_SM_Pathway.BornQuadratic.Core

/-!
# BornQuadraticAnalyticHelpers.lean

Analytic helper lemmas for the Born-quadratic program.

This file isolates the two non-geometric inputs:

1. continuity of the one-variable profile
   `φ(t) = I (sqrt t • e₀)`,
2. injectivity of the real-power map at base `2`, used to extract `α = 2`
   from `(2 : ℝ)^α = 4`.

Both are kept separate so that the geometric core can be developed
independently of the exact analysis API details in mathlib.
-/

noncomputable section
open Real

namespace MDL
namespace BornQuadratic

variable {V : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace OrthonormalPair

variable (hp : OrthonormalPair (V := V))

/--
Continuity of the profile `φ(t) = I (sqrt t • e₀)`.

The intended proof is the composition:

* `t ↦ Real.sqrt t` is continuous,
* `x ↦ x • e₀` is continuous,
* `I` is continuous.

Keeping this lemma isolated makes the main quadratic theorem independent of
which exact `Continuous` lemmas for `Real.sqrt` / scalar multiplication are
most convenient in the final implementation.
-/
lemma continuous_phi_of_continuous
    (I : V → ℝ)
    (hcont : Continuous I) :
    Continuous (hp.phi I) := by
  show Continuous (fun t => I ((Real.sqrt t) • hp.e₀))
  exact hcont.comp (Real.continuous_sqrt.smul continuous_const)

end OrthonormalPair

/--
A tiny algebraic helper: if `a*b = c*b` and `b ≠ 0`, then `a = c`.

This is intentionally recorded explicitly because the exponent argument ends by
cancelling the nonzero factor `c * sqNorm v` from both sides.
-/
lemma eq_of_mul_eq_mul_right_nonzero
    {a b c : ℝ} (hb : b ≠ 0) (h : a * b = c * b) : a = c := by
  exact mul_right_cancel₀ hb h

/--
The only genuinely transcendental step in the exponent extraction:
from `(2 : ℝ)^α = 4` infer `α = 2`.

The intended proof uses injectivity / strict monotonicity of `x ↦ (2:ℝ)^x`
on `ℝ`, valid because `2 > 1`.
-/
lemma eq_two_of_two_rpow_eq_four {α : ℝ} (h : (2 : ℝ)^α = 4) : α = 2 := by
  have h_pos : (0 : ℝ) < 2 := by norm_num
  have h_log_ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num : (1:ℝ) < 2))
  have hlog_eq : Real.log ((2 : ℝ) ^ α) = Real.log 4 := by rw [h]
  rw [Real.log_rpow h_pos] at hlog_eq
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.log_pow]; ring
  rw [hlog4] at hlog_eq
  exact mul_right_cancel₀ h_log_ne hlog_eq

/--
A packaged version of the cancellation step appearing in the exponent proof.

If `k ≠ 0` and `4*k = (2^α)*k`, then `2^α = 4`.
-/
lemma two_rpow_eq_four_of_scaled_eq
    {α k : ℝ} (hk : k ≠ 0) (h : 4 * k = (2 : ℝ)^α * k) : (2 : ℝ)^α = 4 := by
  exact (mul_right_cancel₀ hk h).symm

end BornQuadratic
end MDL
