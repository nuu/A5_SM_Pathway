import A5_SM_Pathway.Auxiliary
import A5_SM_Pathway.SolvabilityBelow60
import A5_SM_Pathway.BornFromA5Opacity
import A5_SM_Pathway.BornFromA5Opacity_Bridge
import A5_SM_Pathway.ObservationLimits
import A5_SM_Pathway.BornFromDiscreteness
import A5_SM_Pathway.TranslationLayer
import A5_SM_Pathway.BornQuadratic
import A5_SM_Pathway.DoubleCover
import A5_SM_Pathway.BranchSign
import A5_SM_Pathway.ReadoutTriviality
import A5_SM_Pathway.FourStateCycle
import A5_SM_Pathway.SpectralCoupling
import A5_SM_Pathway.GateArithmetic
import A5_SM_Pathway.AddressPrinciple
import A5_SM_Pathway.WeightedComposition

import A5_SM_Pathway.G1SelCore
import A5_SM_Pathway.QSqrt5
import A5_SM_Pathway.FlavorCore
import A5_SM_Pathway.FlavorCharTable
import A5_SM_Pathway.E8MaxSub
import A5_SM_Pathway.A5CP
import A5_SM_Pathway.E8BlowUp
import A5_SM_Pathway.E8Cartan
import A5_SM_Pathway.E6Trinification
import A5_SM_Pathway.E6Complex
import A5_SM_Pathway.FlavorGalois

/-!
# A₅ Paper III — Weight Law and Readout Law from the Non-Solvability of A₅

Lean 4 formal verification for:
"Forced Probability and Phase Readout from a Common Algebraic Root:
 The Born Weight P(i)=n_i²/60 and the (ε,s) Structure of the Double Cover of A₅"

## Module structure (matching paper sections)

### Part A — Weight Law (§2–§4)
- `Auxiliary`                : Basic A₅ properties, Sylow toolkit (§2)
- `SolvabilityBelow60`      : All groups below order 60 are solvable (§2)
- `BornFromA5Opacity`       : Solvable-probe opacity, resolution zero (§3, Thm 3.1)
- `ObservationLimits`       : Resolution-zero theorem, observation limits (§3)
- `BornFromDiscreteness`    : Invariant weight is constant, counting measure forced (§3, Thm 3.2, Cor 3.3)
- `BornFromA5Opacity_Bridge`: Quadratic channel measure P(i)=n_i²/60, k=2 uniqueness (§4, Def 4.1, Thm 4.3)
- `BornQuadratic`           : Born quadraticity — continuous extension chain (§4 extended)

### Part B — Readout Law (§5–§6)
- `DoubleCover`             : SL(2,F₅) = 2I, spin-descent bit ε (§5, Def 5.1)
- `BranchSign`              : C₅⁺/C₅⁻ splitting, branch sign s, swap-odd (§5, Def 5.2)
- `ReadoutTriviality`       : ε = 0 readout triviality Φ(0,s) = 0 (§6, Prop 6.1)
- `FourStateCycle`          : McKay Ê₈ bipartiteness, 4-state cycle (§6, Prop 6.1, Thm 6.2)
- `SpectralCoupling`        : McKay spectral face-coupling (e₂ = 20, C = 20φ⁴)

### Composition and Spatial Embedding (§7–§8)
- `WeightedComposition`     : P_{Σ,P}(a) = Σ μ(i)K(a|i), signal profile (§7)
- `AddressPrinciple`        : Coarse address (ε,s) forcing, Lemma 8.1 (§8)
- `GateArithmetic`          : Gate truth tables as M-layer arithmetic (supplementary)
- `TranslationLayer`        : Three observation modes (supplementary)

### G1' Programme — Emergence Path (Appendix G)
- `G1SelCore`               : 2I ↪ E₈ embedding class selection, n₁ ≥ 8 ⟺ SU(3)-class (App. G)

### Flavor Structure — A₅ Clebsch-Gordan and Galois (WS-A/E)
- `QSqrt5`                  : Q(√5) arithmetic, Galois automorphism σ
- `FlavorCore`              : Traceless 3×3 matrix identities (M22, M24, M24')
- `FlavorCharTable`         : A₅ character table, singlet counts, FS indicators (M01–M03, M11, M28)

### McKay-CP Programme — E₈ Selection and CP Structure (WS-C/D)
- `E8MaxSub`                : E₈ maximal subalgebra selection theorem (M58)
- `A5CP`                    : CP impossibility (M50), σ involution on 2I (M54), McKay-CP (M53, M56, M57)
-/
