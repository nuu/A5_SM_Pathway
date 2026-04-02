import A5_SM_Pathway.BornQuadratic.Core
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# BornQuadraticPairCore.lean

A cleaner core statement for the `α = 2` route.

Main correction relative to earlier drafts:
`G`-invariance or Schur uniqueness alone does **not** force radiality.
So the geometric core should be stated with three explicit hypotheses:

1. radiality with respect to the squared norm,
2. orthogonal additivity,
3. continuity.

Once these are available on a real inner-product space containing an explicit
orthonormal pair, the intended theorem is

`I v = c * ‖v‖^2`,

and only **after that** should one add a homogeneity law in order to deduce
`α = 2` as a corollary.

This file re-exports definitions from `Core.lean` and adds the
dimension-based wrapper theorem.
-/

noncomputable section
open Real

namespace MDL
namespace BornQuadratic

variable {V : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/--
Analytic boundary lemma: a continuous additive function on `[0,∞)` is linear.

This is kept separate because it isolates the only analytic input in the
`α = 2` route.
-/
lemma phi_linear_of_continuous_additive
    (φ : ℝ → ℝ)
    (hcont : Continuous φ)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → φ (s + t) = φ s + φ t) :
    ∃ c : ℝ, ∀ t, 0 ≤ t → φ t = c * t :=
  linear_of_continuous_additive_on_nonneg φ hcont hadd

/--
Dimension-based wrapper: once an orthonormal pair is extracted from `V`, apply
`exists_mul_sqNorm_of_pair`.
-/
theorem exists_mul_sqNorm_of_finrank_ge_two
    [FiniteDimensional ℝ V]
    (I : V → ℝ)
    (hdim : 2 ≤ Module.finrank ℝ V)
    (hcont : Continuous I)
    (hrad : Radial I)
    (horth : OrthAdd I) :
    ∃ c : ℝ, ∀ v, I v = c * sqNorm v := by
  let b := stdOrthonormalBasis ℝ V
  have hb := b.orthonormal
  have hne : (⟨0, by omega⟩ : Fin (Module.finrank ℝ V)) ≠ ⟨1, by omega⟩ := by
    intro heq; exact absurd (Fin.mk.inj heq) (by omega)
  let hp : OrthonormalPair (V := V) := {
    e₀ := b ⟨0, by omega⟩
    e₁ := b ⟨1, by omega⟩
    norm_e₀ := hb.1 ⟨0, by omega⟩
    norm_e₁ := hb.1 ⟨1, by omega⟩
    orth := hb.2 hne
  }
  exact exists_mul_sqNorm_of_pair I hp hcont hrad horth

end BornQuadratic
end MDL
