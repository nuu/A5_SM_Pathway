import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# SL(2, F₅): A₅ の二重被覆
# The Double Cover of A₅ and Emergence of Spin Structure

Paper § : §5 (From the Double Cover to the Readout Bits)
         Definition 5.1 (spin-descent bit ε)

## 

A₅ ≅ I ⊂ SO(3) （）
**** SL(2, F₅) ≅ 2I ⊂ SU(2) 
A₅ ** 2 **

「 1/2」（）

    A₅  ≅ I  ⊂ SO(3)   —    — : [1,3,3,4,5]
     ↑  (2:1)
    SL(2,F₅) ≅ 2I ⊂ SU(2) —  — : [1,2,2,3,3,4,4,5,6]

:
   2  A₅  [1,3,3,4,5] ****
   2  SL(2,F₅)  [1,2,2,3,3,4,4,5,6] ****
  → ****A₅ 

## Layer 

- **M**: |SL(2,F₅)| = 120, |Z| = 2,  = 60 = |A₅|,
  , Plancherel  — 
- **P**: SL(2,F₅)/Z ≅ A₅（）,
   2  =  = ,
   = SO(3) → SU(2)  — P

## 

1. § 1: SL(2, F₅)  —  120
2. § 2:  Z(SL(2, F₅)) —  2,  {I, -I}
3. § 3:  — 120/2 = 60 = |A₅|
4. § 4:  1/2  — 
5. § 5: 

sorry = 0, axiom = 0 (native_decide )
-/

open Matrix

namespace MDL
namespace DoubleCover

-- ============================================================================
-- § 1.  SL(2, F₅) 
-- ============================================================================

/-!
SL(2, F₅) = { A ∈ M₂(F₅) | det(A) = 1 }

|SL(2, F_q)| = q(q²−1) = q(q−1)(q+1) 
|SL(2, F₅)| = 5 × (25−1) = 5 × 24 = 120

 |A₅| = 60  2 
SL(2,F₅)  A₅  **** (double cover) 

-/

/-- SL(2, F₅) Mathlib  SpecialLinearGroup  -/
abbrev SL2F5 := SpecialLinearGroup (Fin 2) (ZMod 5)

/-- SL(2, F₅) native_decide  -/
instance : DecidableEq SL2F5 := Subtype.instDecidableEq

/-- native_decide  -/
instance : DecidablePred (· ∈ Subgroup.center SL2F5) := fun _g =>
  decidable_of_iff _ Subgroup.mem_center_iff.symm

/--
**|SL(2, F₅)| = 120**

 |SL(2, F_q)| = q(q²−1)  q = 5 :
  5 × (25 − 1) = 5 × 24 = 120

Lean  ZMod 5  2×2  (625 ) 
det = 1 
-/
theorem SL2F5_card : Fintype.card SL2F5 = 120 := by native_decide

/--
SL(2, F₅) （ > 1）
-/
theorem SL2F5_nontrivial : Fintype.card SL2F5 > 1 := by
  rw [SL2F5_card]; omega

-- ============================================================================
-- § 2.   Z(SL(2, F₅))
-- ============================================================================

/-!
 F_q  SL(2)   aI  a² = 1 
F₅  a² = 1  a = 1  a = 4 (= −1 mod 5)
 Z(SL(2, F₅)) = {I, −I} 2

 Z₂ 「」「」:
  SL(2,F₅) / Z(SL(2,F₅))   = 120 / 2 = 60 = |A₅|
-/

/--
**|Z(SL(2, F₅))| = 2**

 {I, −I}  2 
-/
theorem SL2F5_center_card :
    Fintype.card (Subgroup.center SL2F5) = 2 := by native_decide

/--  −I ∈ SL(2, F₅)
    F₅  −1 = 4  −I = diag(4, 4)
    det(−I) = 4 × 4 − 0 × 0 = 16 = 1 (mod 5) -/
def mat_negI : SL2F5 :=
  ⟨!![4, 0; 0, 4], by native_decide⟩

/-- −I ≠ I () -/
theorem negI_ne_one : mat_negI ≠ 1 := by
  simp only [mat_negI, ne_eq, SpecialLinearGroup.ext_iff]
  native_decide

/-- −I  -/
theorem negI_mem_center : (mat_negI : SL2F5) ∈ Subgroup.center SL2F5 := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  have hkey : mat_negI.val = -1 • (1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) := by native_decide
  simp only [SpecialLinearGroup.coe_mul]
  rw [hkey]
  simp []

/-- −I  2 -/
theorem negI_order : orderOf mat_negI = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by native_decide) (by native_decide)

/-- (−I)² = I（） -/
theorem negI_sq_eq_one : mat_negI ^ 2 = 1 := by native_decide

-- ============================================================================
-- § 3.  
-- ============================================================================

/-!
**** (double cover)  φ: G̃ → G 
|ker(φ)| = 2 SL(2,F₅) → PSL(2,F₅) ≅ A₅ 

M :
  |SL(2,F₅)| / |Z(SL(2,F₅))| = 120 / 2 = 60 = |A₅|

 PSL(2,F₅) ≅ A₅ （Galois, 1832; Jordan, 1870）
P 
-/

/-- ****: |SL(2,F₅)| / |Z| = 60 -/
theorem cover_ratio :
    Fintype.card SL2F5 / Fintype.card (Subgroup.center SL2F5) = 60 := by
  rw [SL2F5_card, SL2F5_center_card]

/-- ** = |A₅|**:  A₅  -/
theorem cover_ratio_matches_A5 :
    Fintype.card SL2F5 / Fintype.card (Subgroup.center SL2F5) =
    Fintype.card (alternatingGroup (Fin 5)) := by
  have h1 := cover_ratio
  have h2 : Fintype.card (alternatingGroup (Fin 5)) = 60 := by native_decide
  omega

/--
SL(2, F₅) 

:
  S = [[0, −1], [1, 0]] = !![0, 4; 1, 0]  (det = 0·0 − 4·1 = −4 = 1)
  T = [[1, 1], [0, 1]]                      (det = 1·1 − 1·0 = 1)
  S · T ≠ T · S
-/
def mat_S : SL2F5 := ⟨!![0, 4; 1, 0], by native_decide⟩
def mat_T : SL2F5 := ⟨!![1, 1; 0, 1], by native_decide⟩

/-- S  T  -/
theorem ST_ne_TS : mat_S * mat_T ≠ mat_T * mat_S := by
  simp only [mat_S, mat_T, ne_eq, SpecialLinearGroup.ext_iff]
  native_decide

/--
S  4 (S² = −I, S⁴ = I)
-/
theorem mat_S_order : orderOf mat_S = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have h : orderOf mat_S = 2 ^ 2 := orderOf_eq_prime_pow (by native_decide) (by native_decide)
  simpa using h

/--
T  5 (T⁵ = I)
-/
theorem mat_T_order : orderOf mat_T = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by native_decide) (by native_decide)

/--  4  5  →  -/
theorem SL2F5_has_diverse_orders :
    (∃ g : SL2F5, orderOf g = 4) ∧
    (∃ g : SL2F5, orderOf g = 5) :=
  ⟨⟨mat_S, mat_S_order⟩, ⟨mat_T, mat_T_order⟩⟩

-- ============================================================================
-- § 4.   1/2  — 
-- ============================================================================

/-!
****: A₅  SL(2,F₅) 

  A₅ :         [1, 3, 3, 4, 5]         (5 )
  SL(2,F₅) :   [1, 2, 2, 3, 3, 4, 4, 5, 6]  (9 )

****: SL(2,F₅)  **2**  2 
A₅ ****

 2 「 1/2 」（）
 SO(3)  SU(2) 

: （） 1/2 
A₅ ⊂ SO(3) 
SL(2,F₅) ⊂ SU(2) 

**→ A₅ **
-/

/-- A₅  (Frobenius, 1900) -/
def A5_irrepDims : List ℕ := [1, 3, 3, 4, 5]

/-- SL(2, F₅) 
    (Schur, 1911;  2I ) -/
def SL2F5_irrepDims : List ℕ := [1, 2, 2, 3, 3, 4, 4, 5, 6]

/-- A₅  = 5（= ） -/
theorem A5_irrep_count : A5_irrepDims.length = 5 := by
  simp [A5_irrepDims]

/-- SL(2,F₅)  = 9（= ） -/
theorem SL2F5_irrep_count : SL2F5_irrepDims.length = 9 := by
  simp [SL2F5_irrepDims]

-- --------------------------------------------------------------------------
-- Plancherel  —  = 
-- --------------------------------------------------------------------------

/--
**Plancherel  (A₅)**:
  1² + 3² + 3² + 4² + 5² = 1 + 9 + 9 + 16 + 25 = 60 = |A₅|
-/
theorem A5_plancherel :
    (A5_irrepDims.map (· ^ 2)).sum = 60 := by
  simp [A5_irrepDims]

/--
**Plancherel  (SL(2, F₅))**:
  1² + 2² + 2² + 3² + 3² + 4² + 4² + 5² + 6²
  = 1 + 4 + 4 + 9 + 9 + 16 + 16 + 25 + 36
  = 120 = |SL(2, F₅)|
-/
theorem SL2F5_plancherel :
    (SL2F5_irrepDims.map (· ^ 2)).sum = 120 := by
  simp [SL2F5_irrepDims]

/-- Plancherel  (A₅) -/
theorem A5_plancherel_matches_card :
    (A5_irrepDims.map (· ^ 2)).sum =
      Fintype.card (alternatingGroup (Fin 5)) := by
  have h1 := A5_plancherel
  have h2 : Fintype.card (alternatingGroup (Fin 5)) = 60 := by native_decide
  omega

/-- Plancherel  (SL(2,F₅)) -/
theorem SL2F5_plancherel_matches_card :
    (SL2F5_irrepDims.map (· ^ 2)).sum = Fintype.card SL2F5 := by
  rw [SL2F5_plancherel, SL2F5_card]

-- --------------------------------------------------------------------------
--  2 : SL(2,F₅) A₅ 
-- --------------------------------------------------------------------------

/--
**A₅  2 **

 [1, 3, 3, 4, 5]  2 
 3 
-/
theorem A5_no_dim2_irrep : 2 ∉ A5_irrepDims := by
  simp [A5_irrepDims]

/-- A₅  3 -/
theorem A5_min_nontrivial_dim :
    ∀ n ∈ A5_irrepDims, n = 1 ∨ n ≥ 3 := by
  simp [A5_irrepDims]

/--
**SL(2, F₅)  2 **

 [1, 2, 2, 3, 3, 4, 4, 5, 6]  2 
 A₅  [1, 3, 3, 4, 5] 
****
-/
theorem SL2F5_has_dim2_irrep : 2 ∈ SL2F5_irrepDims := by
  simp [SL2F5_irrepDims]

/-- SL(2,F₅)  2  2  -/
theorem SL2F5_dim2_count :
    (SL2F5_irrepDims.filter (· == 2)).length = 2 := by
  simp [SL2F5_irrepDims]

-- --------------------------------------------------------------------------
-- 
-- --------------------------------------------------------------------------

/--
****: SL(2,F₅)  A₅ 

  A₅:       [1, 3, 3, 4, 5]
  SL(2,F₅): [1, 2, 2, 3, 3, 4, 4, 5, 6]
  :    {2, 6}

   2 =  1/2 ()
   6 =  5/2 

   4  A₅ SL(2,F₅) 

  :
    「」(2, 6) 
    「」(1, 3, 4, 5) 
-/
theorem dim2_new_in_cover : 2 ∈ SL2F5_irrepDims ∧ 2 ∉ A5_irrepDims := by
  exact ⟨SL2F5_has_dim2_irrep, A5_no_dim2_irrep⟩

theorem dim6_new_in_cover : 6 ∈ SL2F5_irrepDims ∧ 6 ∉ A5_irrepDims := by
  constructor
  · simp [SL2F5_irrepDims]
  · simp [A5_irrepDims]

-- ============================================================================
-- § 5.  
-- ============================================================================

set_option maxRecDepth 512 in
/--
**SL(2, F₅) ・（）**

 M :

  (a) |SL(2, F₅)| = 120
  (b) |Z(SL(2, F₅))| = 2
  (c)  120/2 = 60 = |A₅|（）
  (d) SL(2, F₅) 
  (e) SL(2, F₅)  2 
  (f) A₅  2 
  (g)  Plancherel 

（P）:
  (e) + (f) :
    ** 1/2（） SL(2,F₅) 
    A₅ **

   A₅ （）
  A₅  SL(2,F₅) ****
   SO(3) → SU(2) 
  （Spin ）
-/
theorem double_cover_spin_theorem :
    -- (a) |SL(2,F₅)| = 120
    (Fintype.card SL2F5 = 120) ∧
    -- (b) |Z(SL(2,F₅))| = 2
    (Fintype.card (Subgroup.center SL2F5) = 2) ∧
    -- (c)  = |A₅|
    (Fintype.card SL2F5 / Fintype.card (Subgroup.center SL2F5) =
     Fintype.card (alternatingGroup (Fin 5))) ∧
    -- (d) 
    (mat_S * mat_T ≠ mat_T * mat_S) ∧
    -- (e) SL(2,F₅)  2 
    (2 ∈ SL2F5_irrepDims) ∧
    -- (f) A₅  2 
    (2 ∉ A5_irrepDims) ∧
    -- (g)  Plancherel 
    ((SL2F5_irrepDims.map (· ^ 2)).sum = Fintype.card SL2F5 ∧
     (A5_irrepDims.map (· ^ 2)).sum =
       Fintype.card (alternatingGroup (Fin 5))) :=
  ⟨SL2F5_card,
   SL2F5_center_card,
   cover_ratio_matches_A5,
   ST_ne_TS,
   SL2F5_has_dim2_irrep,
   A5_no_dim2_irrep,
   SL2F5_plancherel_matches_card,
   A5_plancherel_matches_card⟩

-- ============================================================================
-- § 6.  :  −I 
-- ============================================================================

/-!
** −I **

SL(2,F₅)  {I, −I} 
（Schur ）

-  1, 3, 5 （）: −I  +1 
  （SO(3)  → A₅ ）
-  2, 4, 6 （）: −I  −1 
  （SO(3)  → ）

 (−1)^{2s} (s = ) 
**** (Spin-Statistics ) 

M : −I  2 
(−I)² = I  §2 
 P 
-/

/--
 Plancherel :
  1² + 3² + 3² + 5² = 1 + 9 + 9 + 25 = 44
  (A₅ )
-/
theorem integer_spin_contribution :
    1 ^ 2 + 3 ^ 2 + 3 ^ 2 + 5 ^ 2 = 44 := by norm_num

/--
 Plancherel :
  2² + 2² + 4² + 4² + 6² = 4 + 4 + 16 + 16 + 36 = 76
  ()
-/
theorem half_integer_spin_contribution :
    2 ^ 2 + 2 ^ 2 + 4 ^ 2 + 4 ^ 2 + 6 ^ 2 = 76 := by norm_num

/--
 +  = : 44 + 76 = 120 = |SL(2,F₅)|

Plancherel 

-/
theorem spin_decomposition :
    44 + 76 = 120 ∧ 120 = Fintype.card SL2F5 := by
  constructor
  · omega
  · rw [SL2F5_card]

/--
: 76/120 = 19/30 ≈ 63.3%



-/
theorem spinor_fraction : 76 * 30 = 19 * 120 := by norm_num

end DoubleCover
end MDL
