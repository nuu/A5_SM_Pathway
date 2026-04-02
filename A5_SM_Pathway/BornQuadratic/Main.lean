import A5_SM_Pathway.BornQuadratic.Bundle
import A5_SM_Pathway.BornQuadratic.OneVariable
import A5_SM_Pathway.BornQuadratic.Exponent

/-!
# BornQuadraticMainRoute.lean

A single summary file stating the current "best route" theorem chain.

This file is not meant to be the final polished version.  Its role is to keep
one canonical place where the logical dependency is visible:

* geometry (`radial + orthAdd`) gives additivity of `φ`,
* one-variable analysis gives linearity of `φ`,
* radial transport gives quadraticity of `I`,
* homogeneity then forces exponent `2`.
-/

noncomputable section
open Real

namespace MDL
namespace BornQuadratic

variable {V : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/--
Current best-form summary theorem.

Once the geometric core is quadratic and the intensity is also homogeneous of
some degree `α`, the degree is forced to be `2`.
-/
theorem exponent_two_current_best
    (I : V → ℝ)
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
A summary statement for the quadratic stage alone.
-/
theorem quadratic_current_best
    (I : V → ℝ)
    (hp : OrthonormalPair (V := V))
    (hcont : Continuous I)
    (hrad : Radial I)
    (horth : OrthAdd I) :
    ∃ c : ℝ, ∀ v, I v = c * sqNorm v := by
  exact exists_mul_sqNorm_of_pair I hp hcont hrad horth

/--
Conceptual bridge statement:
Schur is not the place where exponent `2` is proved.
Schur is the place where the underlying invariant quadratic form is fixed up to
scale; exponent `2` comes later from the geometric-analytic core.
-/
theorem schur_role_summary
    (I : V → ℝ)
    (hp : OrthonormalPair (V := V))
    (hcont : Continuous I)
    (hrad : Radial I)
    (horth : OrthAdd I) :
    ∃ c : ℝ, ∀ v, I v = c * sqNorm v := by
  exact quadratic_current_best I hp hcont hrad horth

end BornQuadratic
end MDL
