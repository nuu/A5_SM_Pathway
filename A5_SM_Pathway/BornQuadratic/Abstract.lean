import A5_SM_Pathway.BornQuadratic.Core
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# BornQuadraticAbstract.lean

An abstract layer above `BornQuadraticCore.lean`.

This file does **not** yet attempt a full proof. Instead it isolates the
minimal theorem-shape that should be provable once the `ℝ²` core is finished.
The point is to separate:

1. the genuinely geometric part (`radial + orthogonal additivity => quadratic`),
2. the scaling/exponent corollary (`=> α = 2`), and
3. the future representation-theoretic bridge.

Because a full general proof needs access to a 2-dimensional orthogonal plane,
we phrase the main transfer theorem with two explicit orthogonal unit vectors.
This is usually easier to formalize than arguing from finite dimension first.
-/

noncomputable section
open scoped BigOperators
open Real

namespace MDL
namespace BornQuadratic

variable {V : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]

variable (I : V → ℝ)

/--
The abstract geometric theorem expected from the `ℝ²` core.

Once an orthonormal pair is chosen, the function `I` should restrict to the
plane they span, and the `ℝ²` proof should imply that `I` is quadratic on that
plane. Radiality should then upgrade this to all of `V`.
-/
theorem exists_mul_sqNorm_of_radial_orthAdd_of_pair
    (hp : OrthonormalPair (V := V))
    (hcont : Continuous I)
    (hrad : Radial I)
    (horth : OrthAdd I) :
    ∃ c : ℝ, ∀ v, I v = c * sqNorm v := by
  exact exists_mul_sqNorm_of_pair I hp hcont hrad horth

/--
Once the quadratic form is established, the homogeneity exponent is forced to
be `2`.
-/
theorem exponent_two_of_homogeneous_of_pair_abs
    (hp : OrthonormalPair (V := V))
    (α : ℝ)
    (hcont : Continuous I)
    (hrad : Radial I)
    (horth : OrthAdd I)
    (hhom : Homogeneous I α)
    (hnontriv : ∃ v, I v ≠ 0) :
    α = 2 := by
  exact exponent_two_of_homogeneous_of_pair I hp α hcont hrad horth hhom hnontriv

/--
A version with an explicit dimension hypothesis should later be derived by
constructing an orthonormal pair. The statement is recorded here so the next
bridge file can target it directly.
-/
theorem exists_mul_sqNorm_of_radial_orthAdd_finrank
    [FiniteDimensional ℝ V]
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
