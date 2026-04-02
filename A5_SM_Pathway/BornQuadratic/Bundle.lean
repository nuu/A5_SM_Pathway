import A5_SM_Pathway.BornQuadratic.Core
import A5_SM_Pathway.BornQuadratic.Reduction
import A5_SM_Pathway.BornQuadratic.AnalyticHelpers
import A5_SM_Pathway.BornQuadratic.Abstract
import A5_SM_Pathway.BornQuadratic.SchurBridge
import A5_SM_Pathway.BornQuadratic.PairCore
import A5_SM_Pathway.BornQuadratic.GeometryHelpers

/-!
# BornQuadraticBundle.lean

Convenience import file for the current Born-quadratic formalization skeleton.

Suggested build order:

1. `BornQuadraticGeometryHelpers.lean`
2. `BornQuadraticAnalyticHelpers.lean`
3. `BornQuadraticCore_v2.lean`
4. `BornQuadraticReduction.lean`
5. `BornQuadraticAbstract.lean`
6. `BornQuadraticSchurBridge.lean`

Logical dependency order:

* geometry  -> `phi_add`
* analysis  -> linearity of `φ` + injectivity of `2^x`
* reduction -> quadratic intensity theorem
* bridge    -> Schur uniqueness + exponent `2`
-/
