import A5_SM_Pathway.BornQuadratic.Core

open scoped InnerProductSpace

/-!
# BornQuadraticPythagorasHelpers.lean

This file isolates the geometric heart of the Born-quadratic program:

* orthogonality kills the cross term,
* therefore the squared norm of an orthogonal sum is additive,
* therefore the profile `φ(t) = I (sqrt t • e₀)` is additive on `t ≥ 0`.

The point is not to settle exact mathlib lemma names here, but to expose a
compile-oriented decomposition so that the eventual implementation can fill the
small geometric gaps one by one.
-/

noncomputable section
open Real

namespace MDL
namespace BornQuadratic

variable {V : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/--
Real-inner-product expansion for the squared norm of a sum.

This is the intended doorway to the orthogonal case.  In a final implementation
this can often be obtained from an existing mathlib identity, but keeping it as
an explicit target lemma makes the later proof structure much cleaner.
-/
lemma sqNorm_add_expand (u v : V) :
    sqNorm (u + v) = sqNorm u + 2 * (⟪u, v⟫_ℝ) + sqNorm v := by
  unfold sqNorm
  have hsq : ∀ w : V, ‖w‖ * ‖w‖ = ⟪w, w⟫_ℝ := fun w =>
    real_inner_self_eq_norm_mul_norm.symm
  rw [hsq, hsq, hsq, inner_add_left, inner_add_right, inner_add_right]
  rw [real_inner_comm v u]
  ring

/--
Pythagoras for `sqNorm`.
-/
lemma sqNorm_add_of_orth (u v : V) (huv : ⟪u, v⟫_ℝ = 0) :
    sqNorm (u + v) = sqNorm u + sqNorm v := by
  have hexpand := sqNorm_add_expand (u := u) (v := v)
  calc
    sqNorm (u + v)
        = sqNorm u + 2 * (⟪u, v⟫_ℝ) + sqNorm v := hexpand
    _ = sqNorm u + sqNorm v := by simp [huv]

namespace OrthonormalPair

variable (hp : OrthonormalPair (V := V))

/--
A short wrapper around Pythagoras specialized to the scaled orthonormal pair.
-/
lemma sqNorm_sum_scaled_via_pythagoras {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    sqNorm ((Real.sqrt s) • hp.e₀ + (Real.sqrt t) • hp.e₁) = s + t := by
  let u : V := (Real.sqrt s) • hp.e₀
  let v : V := (Real.sqrt t) • hp.e₁
  have huv : ⟪u, v⟫_ℝ = 0 := by
    simpa [u, v] using hp.orth_scaled s t
  have hpyth : sqNorm (u + v) = sqNorm u + sqNorm v :=
    sqNorm_add_of_orth (u := u) (v := v) huv
  calc
    sqNorm ((Real.sqrt s) • hp.e₀ + (Real.sqrt t) • hp.e₁)
        = sqNorm u + sqNorm v := by simpa [u, v] using hpyth
    _ = s + t := by rw [hp.sqNorm_smul_e₀ hs, hp.sqNorm_smul_e₁ ht]

/--
Replacement version of `sqNorm_sum_scaled` that factors through the explicit
Pythagoras lemma above.
-/
lemma sqNorm_sum_scaled_refactored {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    sqNorm ((Real.sqrt s) • hp.e₀ + (Real.sqrt t) • hp.e₁) = s + t := by
  simpa using hp.sqNorm_sum_scaled_via_pythagoras hs ht

/--
A refactored version of `phi_add_of_radial_orthAdd` in which the geometry is
channeled only through `sqNorm_add_of_orth`.
-/
lemma phi_add_of_radial_orthAdd_refactored
    (I : V → ℝ)
    (hrad : Radial I)
    (horth : OrthAdd I)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    hp.phi I (s + t) = hp.phi I s + hp.phi I t := by
  let u : V := (Real.sqrt s) • hp.e₀
  let v : V := (Real.sqrt t) • hp.e₁
  have huv : ⟪u, v⟫_ℝ = 0 := by
    simpa [u, v] using hp.orth_scaled s t
  have hpyth : sqNorm (u + v) = s + t := by
    calc
      sqNorm (u + v) = sqNorm u + sqNorm v := sqNorm_add_of_orth (u := u) (v := v) huv
      _ = s + t := by rw [hp.sqNorm_smul_e₀ hs, hp.sqNorm_smul_e₁ ht]
  have hrad_sum : I ((Real.sqrt (s + t)) • hp.e₀) = I (u + v) := by
    apply hrad
    calc
      sqNorm ((Real.sqrt (s + t)) • hp.e₀) = s + t := hp.sqNorm_smul_e₀ (add_nonneg hs ht)
      _ = sqNorm (u + v) := hpyth.symm
  have hsum : I (u + v) = I u + I v := horth u v huv
  have hrad_right : I v = I ((Real.sqrt t) • hp.e₀) := by
    simpa [v] using hp.radial_rewrite_e₁ I hrad ht
  calc
    hp.phi I (s + t)
        = I ((Real.sqrt (s + t)) • hp.e₀) := rfl
    _ = I (u + v) := hrad_sum
    _ = I u + I v := hsum
    _ = hp.phi I s + hp.phi I t := by
          simp [OrthonormalPair.phi, u, v, hrad_right]

end OrthonormalPair

end BornQuadratic
end MDL
