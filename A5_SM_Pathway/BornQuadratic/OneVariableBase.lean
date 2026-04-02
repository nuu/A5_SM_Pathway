import A5_SM_Pathway.BornQuadratic.Core

/-!
# BornQuadraticOneVariable.lean

One-variable analytic reduction for the Born-quadratic program.

The intended workflow is:

* geometric lemmas produce additivity of `φ` on `ℝ≥0`,
* continuity of `φ` upgrades additivity to linearity,
* linearity of `φ` upgrades radiality to global quadraticity.

This file keeps the one-variable part explicit and separate from the geometry.
-/

noncomputable section
open Real

namespace MDL
namespace BornQuadratic

/-- Additivity on the nonnegative reals. -/
def AdditiveOnNonneg (φ : ℝ → ℝ) : Prop :=
  ∀ s t, 0 ≤ s → 0 ≤ t → φ (s + t) = φ s + φ t

/--
Continuous additivity on `ℝ≥0` implies linearity there.

This is the exact analytic placeholder needed by the quadratic core.
A future proof can proceed either by restricting to `ℝ≥0` as an additive
submonoid and using a general theorem, or by the classical route:

* first prove `φ (n*t) = n*φ t` for natural `n`,
* then for nonnegative rationals,
* then extend to all nonnegative reals by continuity.
-/
lemma linear_of_continuous_additive_on_nonneg_v2
    (φ : ℝ → ℝ)
    (hcont : Continuous φ)
    (hadd : AdditiveOnNonneg φ) :
    ∃ c : ℝ, ∀ t, 0 ≤ t → φ t = c * t := by
  exact linear_of_continuous_additive_on_nonneg φ hcont hadd

/--
Convenient normalization: the slope can be taken to be `φ 1`.
-/
lemma linear_of_continuous_additive_on_nonneg_normalized
    (φ : ℝ → ℝ)
    (hcont : Continuous φ)
    (hadd : AdditiveOnNonneg φ) :
    ∀ t, 0 ≤ t → φ t = φ 1 * t := by
  rcases linear_of_continuous_additive_on_nonneg_v2 φ hcont hadd with ⟨c, hc⟩
  have h1 : φ 1 = c := by
    simpa using (hc 1 (by norm_num))
  intro t ht
  rw [h1]
  simpa [mul_comm] using hc t ht

end BornQuadratic
end MDL
