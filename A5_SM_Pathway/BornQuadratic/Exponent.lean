import A5_SM_Pathway.BornQuadratic.ExponentHelpers
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# BornQuadraticExponent_v2.lean

A closer-to-final exponent extraction file.
-/

noncomputable section
open Real

namespace MDL
namespace BornQuadratic

lemma rpow_left_injective_of_one_lt_v2
    {x : ℝ} (hx : 1 < x) {a b : ℝ}
    (h : x ^ a = x ^ b) : a = b := by
  have hx0 : 0 < x := lt_trans (by norm_num) hx
  have hlog : Real.log (x ^ a) = Real.log (x ^ b) := by simp [h]
  have hloga : Real.log (x ^ a) = a * Real.log x := by
    rw [Real.log_rpow hx0]
  have hlogb : Real.log (x ^ b) = b * Real.log x := by
    rw [Real.log_rpow hx0]
  rw [hloga, hlogb] at hlog
  have hne : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  exact mul_right_cancel₀ hne hlog

lemma eq_two_of_two_rpow_eq_four_v2 {α : ℝ} (h : (2 : ℝ) ^ α = 4) : α = 2 := by
  have h' : (2 : ℝ) ^ α = (2 : ℝ) ^ (2 : ℝ) := by rw [h]; norm_num
  exact rpow_left_injective_of_one_lt_v2 (x := 2) (by norm_num) h'

end BornQuadratic
end MDL
