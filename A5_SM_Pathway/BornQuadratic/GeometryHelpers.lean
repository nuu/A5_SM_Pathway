import A5_SM_Pathway.BornQuadratic.PairCore

open scoped InnerProductSpace

/-!
# BornQuadraticGeometryHelpers.lean

Helper lemmas for the `phi_add` step in the Born-quadratic route.

This file does not claim finished formal proofs. Its purpose is to isolate the
small geometric facts that should be proved first in Lean, before attacking the
main theorem.

The guiding idea is:

* define `sqNorm v = ‖v‖^2`,
* work with an explicit orthonormal pair `(e₀,e₁)`,
* prove the Pythagorean identity for `u = √s • e₀`, `v = √t • e₁`,
* feed that into radiality and orthogonal additivity.

Compared with the earlier files, this one makes the geometry substantially more
modular.
-/

noncomputable section
open scoped BigOperators
open Real

namespace MDL
namespace BornQuadratic

variable {V : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Real scaling by a nonnegative scalar on a unit vector. -/
lemma sqNorm_smul_of_unit
    {e : V} (he : ‖e‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) :
    sqNorm ((Real.sqrt t) • e) = t := by
  unfold sqNorm
  rw [norm_smul, he, mul_one, Real.norm_of_nonneg (Real.sqrt_nonneg t)]
  exact mul_self_sqrt ht

/-- The two scaled unit vectors have the expected squared norms. -/
lemma sqNorm_pair_left
    (hp : OrthonormalPair (V := V))
    {s : ℝ} (hs : 0 ≤ s) :
    sqNorm ((Real.sqrt s) • hp.e₀) = s := by
  simpa using sqNorm_smul_of_unit hp.norm_e₀ hs

lemma sqNorm_pair_right
    (hp : OrthonormalPair (V := V))
    {t : ℝ} (ht : 0 ≤ t) :
    sqNorm ((Real.sqrt t) • hp.e₁) = t := by
  simpa using sqNorm_smul_of_unit hp.norm_e₁ ht

/-- Orthogonality is preserved by real scalar multiplication. -/
lemma pair_scaled_orth
    (hp : OrthonormalPair (V := V))
    (s t : ℝ) :
    ⟪(Real.sqrt s) • hp.e₀, (Real.sqrt t) • hp.e₁⟫_ℝ = 0 := by
  rw [inner_smul_left, inner_smul_right]
  simp [hp.orth]

/-- Pythagoras for the scaled orthonormal pair. -/
lemma sqNorm_pair_sum
    (hp : OrthonormalPair (V := V))
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    sqNorm ((Real.sqrt s) • hp.e₀ + (Real.sqrt t) • hp.e₁) = s + t := by
  set u := (Real.sqrt s) • hp.e₀
  set v := (Real.sqrt t) • hp.e₁
  have huv : ⟪u, v⟫_ℝ = 0 := pair_scaled_orth hp s t
  have hpyth : ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
    have := @norm_add_sq_real V _ _ u v; rw [huv, mul_zero, add_zero] at this; exact this
  unfold sqNorm
  have hsq : ‖u + v‖ * ‖u + v‖ = ‖u‖ * ‖u‖ + ‖v‖ * ‖v‖ := by nlinarith [hpyth]
  rw [hsq]
  have h_u : ‖u‖ * ‖u‖ = s := sqNorm_smul_of_unit hp.norm_e₀ hs
  have h_v : ‖v‖ * ‖v‖ = t := sqNorm_smul_of_unit hp.norm_e₁ ht
  linarith

namespace OrthonormalPair

variable (hp : OrthonormalPair (V := V))

/-- The radial comparison needed in the `phi_add` argument. -/
lemma sqNorm_sum_eq_sqNorm_axis
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    sqNorm ((Real.sqrt s) • hp.e₀ + (Real.sqrt t) • hp.e₁)
      = sqNorm ((Real.sqrt (s + t)) • hp.e₀) := by
  rw [sqNorm_pair_sum hp hs ht, sqNorm_pair_left hp (add_nonneg hs ht)]

/-- The right vector can be re-read through the left axis using radiality. -/
lemma radial_rewrite_right
    (I : V → ℝ)
    (hrad : Radial I)
    {t : ℝ} (ht : 0 ≤ t) :
    I ((Real.sqrt t) • hp.e₁) = I ((Real.sqrt t) • hp.e₀) := by
  apply hrad
  rw [sqNorm_pair_right hp ht, sqNorm_pair_left hp ht]

/-- A version of `phi_add` factored through the helper lemmas. -/
lemma phi_add_of_radial_orthAdd'
    (I : V → ℝ)
    (hrad : Radial I)
    (horth : OrthAdd I)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    hp.phi I (s + t) = hp.phi I s + hp.phi I t := by
  let u : V := (Real.sqrt s) • hp.e₀
  let v : V := (Real.sqrt t) • hp.e₁
  have huv : ⟪u, v⟫_ℝ = 0 := by
    simpa [u, v] using pair_scaled_orth hp s t
  have hsum : I (u + v) = I u + I v := horth u v huv
  have hrad_sum : I (u + v) = I ((Real.sqrt (s + t)) • hp.e₀) := by
    apply hrad
    simpa [u, v] using hp.sqNorm_sum_eq_sqNorm_axis hs ht
  have hright : I v = I ((Real.sqrt t) • hp.e₀) := by
    simpa [v] using hp.radial_rewrite_right I hrad ht
  calc
    hp.phi I (s + t)
        = I ((Real.sqrt (s + t)) • hp.e₀) := rfl
    _ = I (u + v) := by simpa using hrad_sum.symm
    _ = I u + I v := hsum
    _ = hp.phi I s + hp.phi I t := by
          simp [OrthonormalPair.phi, u, v, hright]

end OrthonormalPair

/--
A very small standalone target: from radiality and orthogonal additivity, the
profile extracted from an orthonormal pair is additive on `[0,∞)`.

This theorem is the main payoff of the helper file.
-/
theorem phi_add_nonneg_of_pair
    (hp : OrthonormalPair (V := V))
    (I : V → ℝ)
    (hrad : Radial I)
    (horth : OrthAdd I)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    hp.phi I (s + t) = hp.phi I s + hp.phi I t := by
  simpa using hp.phi_add_of_radial_orthAdd' I hrad horth hs ht

end BornQuadratic
end MDL
