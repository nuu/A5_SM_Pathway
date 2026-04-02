import A5_SM_Pathway.BornQuadratic.Core

open scoped InnerProductSpace

/-!
# BornQuadraticInnerBridge.lean

Bridge lemmas between the custom `sqNorm` wrapper and the ambient real inner
product structure.

This file is meant to make `sqNorm_add_expand` and the orthogonal Pythagoras
step feel almost mechanical once the exact mathlib rewrite lemmas are chosen.

The key idea is simple:

* first express `sqNorm v` through `⟪v,v⟫`,
* then expand `⟪u+v,u+v⟫`,
* then specialize to the orthogonal case.

The current file keeps the intended statements explicit, even when the final
implementation may decide to replace them by existing mathlib identities.
-/

noncomputable section
open Real

namespace MDL
namespace BornQuadratic

variable {V : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/--
`sqNorm` as the self-inner-product in the real case.
-/
lemma sqNorm_eq_inner_self (v : V) :
    sqNorm v = ⟪v, v⟫_ℝ := by
  unfold sqNorm
  exact real_inner_self_eq_norm_mul_norm.symm

/--
Inner-product expansion of the squared norm of a sum.
-/
lemma sqNorm_add_expand_v2 (u v : V) :
    sqNorm (u + v) = sqNorm u + 2 * (⟪u, v⟫_ℝ) + sqNorm v := by
  rw [sqNorm_eq_inner_self, sqNorm_eq_inner_self, sqNorm_eq_inner_self,
      inner_add_left, inner_add_right, inner_add_right, real_inner_comm v u]
  ring

/--
Pythagoras in `sqNorm` form.
-/
lemma sqNorm_add_of_orth_v2 (u v : V) (huv : ⟪u, v⟫_ℝ = 0) :
    sqNorm (u + v) = sqNorm u + sqNorm v := by
  have h := sqNorm_add_expand_v2 (u := u) (v := v)
  calc
    sqNorm (u + v)
        = sqNorm u + 2 * (⟪u, v⟫_ℝ) + sqNorm v := h
    _ = sqNorm u + sqNorm v := by simp [huv]

/--
A specialization exactly matching the scaled orthonormal-pair geometry used by
`phi_add`.
-/
namespace OrthonormalPair

variable (hp : OrthonormalPair (V := V))

lemma sqNorm_sum_scaled_from_inner {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    sqNorm ((Real.sqrt s) • hp.e₀ + (Real.sqrt t) • hp.e₁) = s + t := by
  let u : V := (Real.sqrt s) • hp.e₀
  let v : V := (Real.sqrt t) • hp.e₁
  have huv : ⟪u, v⟫_ℝ = 0 := by
    simpa [u, v] using hp.orth_scaled s t
  calc
    sqNorm ((Real.sqrt s) • hp.e₀ + (Real.sqrt t) • hp.e₁)
        = sqNorm u + sqNorm v := by
            simpa [u, v] using sqNorm_add_of_orth_v2 (u := u) (v := v) huv
    _ = s + t := by rw [hp.sqNorm_smul_e₀ hs, hp.sqNorm_smul_e₁ ht]

end OrthonormalPair

end BornQuadratic
end MDL
