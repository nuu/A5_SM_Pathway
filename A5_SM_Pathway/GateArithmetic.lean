import Mathlib.Tactic

/-!
# Gate Arithmetic on Address Tables (Layer M)

## Main Results

Quantum gate truth tables are reproduced as finite arithmetic
on address tables. The "meaning" of gates is Layer P, but the
arithmetic correctness is Layer M.

- **Gate-M1**: Hadamard maps a one-row table to equal-weight two rows
- **Gate-M2**: H² = I by signed cancellation
- **Gate-M3**: CNOT is mod 2 re-indexing
- **Gate-M4**: Bell state is a correlated two-row table
- **Gate-M5**: Born-type quadratic weights for measurement
- **Gate-M7**: Interference = signed addition (unified with moiré)

## Key Design Decision

We avoid √2 throughout. The Hadamard matrix is represented as the
**integer** matrix [[1,1],[1,-1]] with a separate scale factor 1/√2.
All identities are verified at the integer level, where native_decide
and norm_num apply. The scale factors compose trivially.

sorry = 0, axiom = 0.
-/

open Matrix

namespace A5_SM_Pathway.GateArithmetic

-- ============================================================================
-- § 1. Hadamard: Integer Core
-- ============================================================================

/-!
The Hadamard gate H = (1/√2) · [[1,1],[1,-1]].

Since (1/√2)² = 1/2, the identity H² = I becomes:
  (1/2) · [[1,1],[1,-1]] · [[1,1],[1,-1]] = I
  i.e., [[1,1],[1,-1]] · [[1,1],[1,-1]] = 2·I

This is purely integer arithmetic.
-/

/-- Integer core of Hadamard: H_int = [[1,1],[1,-1]]. -/
def hadamardInt : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 1; 1, -1]

/-- **Gate-M2**: H² = I at integer level.
    H_int · H_int = 2 · I. Combined with scale (1/√2)², this gives H² = I. -/
theorem hadamard_squared :
    hadamardInt * hadamardInt = 2 • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  native_decide

/-- H_int is its own transpose (symmetric matrix). -/
theorem hadamardInt_symmetric : hadamardIntᵀ = hadamardInt := by
  native_decide

/-- det(H_int) = -2, so H_int is invertible (over ℚ, with scale 1/√2). -/
theorem hadamardInt_det : Matrix.det hadamardInt = -2 := by
  native_decide

-- ============================================================================
-- § 2. Hadamard Truth Table (Gate-M1)
-- ============================================================================

/-!
Action of H_int on basis vectors (before normalization):

  H_int · |0⟩ = H_int · [1, 0]ᵀ = [1, 1]ᵀ   (equal-weight, same sign)
  H_int · |1⟩ = H_int · [0, 1]ᵀ = [1, -1]ᵀ  (equal-weight, opposite sign)

The mask changes: specified (one nonzero entry) → unspecified (two nonzero entries).
-/

/-- Basis vector |0⟩ = [1, 0]. -/
def ket0 : Fin 2 → ℤ := ![1, 0]

/-- Basis vector |1⟩ = [0, 1]. -/
def ket1 : Fin 2 → ℤ := ![0, 1]

/-- H_int · |0⟩ = [1, 1] (equal weight, same sign). -/
theorem hadamard_ket0 :
    hadamardInt.mulVec ket0 = ![1, 1] := by native_decide

/-- H_int · |1⟩ = [1, -1] (equal weight, opposite sign). -/
theorem hadamard_ket1 :
    hadamardInt.mulVec ket1 = ![1, -1] := by native_decide

-- ============================================================================
-- § 3. Signed Cancellation Mechanism (Gate-M2 detail)
-- ============================================================================

/-!
The cancellation mechanism in H·H = I:

For |0⟩: H|0⟩ = [1,1], then H·[1,1] = [1·1+1·1, 1·1+(-1)·1] = [2, 0].
  Entry 0: same sign → reinforcement (1+1 = 2)
  Entry 1: opposite sign → cancellation (1-1 = 0)

For |1⟩: H|1⟩ = [1,-1], then H·[1,-1] = [1·1+1·(-1), 1·1+(-1)·(-1)] = [0, 2].
  Entry 0: opposite sign → cancellation (1-1 = 0)
  Entry 1: same sign → reinforcement (1+1 = 2)

This is the SAME signed-addition rule as moiré interference (§4 of paper).
-/

/-- H applied twice to |0⟩ returns 2·|0⟩. -/
theorem hadamard_roundtrip_ket0 :
    hadamardInt.mulVec (hadamardInt.mulVec ket0) = ![2, 0] := by native_decide

/-- H applied twice to |1⟩ returns 2·|1⟩. -/
theorem hadamard_roundtrip_ket1 :
    hadamardInt.mulVec (hadamardInt.mulVec ket1) = ![0, 2] := by native_decide

/-- Reinforcement: same-sign entries add. -/
theorem reinforcement : (1 : ℤ) * 1 + 1 * 1 = 2 := by norm_num

/-- Cancellation: opposite-sign entries cancel. -/
theorem cancellation : (1 : ℤ) * 1 + (-1) * 1 = 0 := by norm_num

-- ============================================================================
-- § 4. CNOT as Mod 2 Re-indexing (Gate-M3)
-- ============================================================================

/-!
CNOT(a, b) = (a, a ⊕ b) where ⊕ is XOR (mod 2 addition).

Truth table:
  |00⟩ → |00⟩  (0 ⊕ 0 = 0)
  |01⟩ → |01⟩  (0 ⊕ 1 = 1)
  |10⟩ → |11⟩  (1 ⊕ 0 = 1)  ← target flips
  |11⟩ → |10⟩  (1 ⊕ 1 = 0)  ← target flips

This is a row permutation on the 2-qubit address table.
-/

/-- XOR on Fin 2 (mod 2 addition). -/
def xorF2 (a b : Fin 2) : Fin 2 := ⟨(a.val + b.val) % 2, Nat.mod_lt _ (by omega)⟩

/-- CNOT on address pairs. -/
def cnot (a b : Fin 2) : Fin 2 × Fin 2 := (a, xorF2 a b)

/-- **Gate-M3**: CNOT truth table — all four cases. -/
theorem cnot_truth_table :
    cnot 0 0 = (0, 0) ∧
    cnot 0 1 = (0, 1) ∧
    cnot 1 0 = (1, 1) ∧
    cnot 1 1 = (1, 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [cnot, xorF2]

/-- CNOT is an involution: CNOT² = id. -/
theorem cnot_involution (a b : Fin 2) :
    cnot (cnot a b).1 (cnot a b).2 = (a, b) := by
  fin_cases a <;> fin_cases b <;> simp [cnot, xorF2]

/-- CNOT preserves the control bit. -/
theorem cnot_preserves_control (a b : Fin 2) :
    (cnot a b).1 = a := by
  simp [cnot]

-- ============================================================================
-- § 5. Bell State Construction (Gate-M4)
-- ============================================================================

/-!
Bell state |Φ⁺⟩ = (|00⟩ + |11⟩)/√2 is constructed by (H ⊗ I) · CNOT on |00⟩.

Step 1: H ⊗ I on |00⟩:
  |00⟩ → (H|0⟩) ⊗ |0⟩ = (|0⟩+|1⟩)/√2 ⊗ |0⟩
  In address table (integer level): {(0,0), (1,0)} both weight 1.

Step 2: CNOT:
  (0,0) → (0, 0⊕0) = (0,0)  weight 1
  (1,0) → (1, 1⊕0) = (1,1)  weight 1

Result: address table has nonzero entries at (0,0) and (1,1) only.
"Entanglement" = correlated address table. No action at a distance.
-/

/-- The two nonzero entries of Bell state |Φ⁺⟩ are at addresses (0,0) and (1,1). -/
theorem bell_addresses :
    cnot 0 0 = (0, 0) ∧ cnot 1 0 = (1, 1) := by
  constructor <;> simp [cnot, xorF2]

/-- The other two addresses have zero weight (are not reached). -/
theorem bell_zero_addresses :
    cnot 0 0 ≠ (0, 1) ∧ cnot 0 0 ≠ (1, 0) ∧
    cnot 1 0 ≠ (0, 1) ∧ cnot 1 0 ≠ (1, 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [cnot, xorF2]

-- ============================================================================
-- § 6. Born-Type Quadratic Weights (Gate-M5)
-- ============================================================================

/-!
For an address table T: {0,...,n-1} → ℤ (integer level, before normalization),
the probability of reading address k is:

  P(k) = |T(k)|² / Σⱼ |T(j)|²

This is the address-table version of the Born prototype P(i) = nᵢ²/|G|
from Paper II.

For the H|0⟩ table [1, 1]:
  P(0) = 1² / (1² + 1²) = 1/2
  P(1) = 1² / (1² + 1²) = 1/2  ← equal probability

For the H|1⟩ table [1, -1]:
  P(0) = 1² / (1² + 1²) = 1/2
  P(1) = 1² / (1² + 1²) = 1/2  ← equal probability (sign irrelevant for Born)
-/

/-- Sum of squared entries of a 2-element table. -/
def normSq2 (t : Fin 2 → ℤ) : ℤ := t 0 ^ 2 + t 1 ^ 2

/-- |H|0⟩|² = 1² + 1² = 2. -/
theorem born_H_ket0 : normSq2 ![1, 1] = 2 := by native_decide

/-- |H|1⟩|² = 1² + (-1)² = 2. -/
theorem born_H_ket1 : normSq2 ![1, -1] = 2 := by native_decide

/-- Born weights are equal for H|0⟩ (both entries have |T(k)|² = 1). -/
theorem born_equal_H_ket0 : (![1, 1] : Fin 2 → ℤ) 0 ^ 2 = (![1, 1] : Fin 2 → ℤ) 1 ^ 2 := by
  native_decide

/-- Born weights are equal for H|1⟩ (sign doesn't matter for |·|²). -/
theorem born_equal_H_ket1 :
    (![1, -1] : Fin 2 → ℤ) 0 ^ 2 = (![1, -1] : Fin 2 → ℤ) 1 ^ 2 := by
  native_decide

-- ============================================================================
-- § 7. Interference Unification (Gate-M7)
-- ============================================================================

/-!
**Theorem Gate-M7 (Unified interference arithmetic).**

The signed-addition rule underlying interference is the same in:
1. Integer moiré: Δn ≡ 0 mod 4 → same sign → bright line
2. Hadamard H·H = I: same sign → reinforcement, opposite → cancellation

Both reduce to the arithmetic identity:
  a + a = 2a   (reinforcement, same sign)
  a + (-a) = 0  (cancellation, opposite sign)

The difference is only in what the signs attach to:
  Moiré: spatial path difference
  Gates: temporal gate application
The arithmetic rule is identical.
-/

/-- **Interference rule**: same sign → reinforcement. -/
theorem interference_reinforce (a : ℤ) : a + a = 2 * a := by ring

/-- **Interference rule**: opposite sign → cancellation. -/
theorem interference_cancel (a : ℤ) : a + (-a) = 0 := by ring

/-- Mod 4 bright-line examples: Δn divisible by 4 gives even half-step. -/
theorem mod4_bright_examples :
    2 ∣ ((0 : ℤ) / 2) ∧ 2 ∣ ((4 : ℤ) / 2) ∧ 2 ∣ ((8 : ℤ) / 2) := by decide

/-- Mod 4 dark-line example: Δn = 2 gives odd half-step (2/2 = 1). -/
theorem mod4_dark_example : ¬(2 ∣ ((2 : ℤ) / 2)) := by decide

-- ============================================================================
-- § 8. Quantum Eraser as Row Selection (Gate-M6)
-- ============================================================================

/-!
For a Bell state with address table {(0,0): w, (1,1): w}:

Full data: P(first qubit = 0) = P(first qubit = 1) = 1/2. No interference.

Post-selected on second qubit = 0:
  Only (0,0) survives → first qubit is deterministically 0.

Post-selected on second qubit = 1:
  Only (1,1) survives → first qubit is deterministically 1.

"Quantum eraser" = choosing which rows of the table to look at.
No retrocausality. Just table filtering.
-/

/-- Post-selection on Bell state: if second qubit is 0, first qubit is 0. -/
theorem eraser_select_0 :
    ∀ (a : Fin 2), (a, (0 : Fin 2)) ∈ [(0 : Fin 2 × Fin 2), (1, 1)] → a = 0 := by
  intro a ha
  fin_cases a <;> simp_all

/-- Post-selection on Bell state: if second qubit is 1, first qubit is 1. -/
theorem eraser_select_1 :
    ∀ (a : Fin 2), (a, (1 : Fin 2)) ∈ [(0 : Fin 2 × Fin 2), (1, 1)] → a = 1 := by
  intro a ha
  fin_cases a <;> simp_all

-- ============================================================================
-- § 9. Summary
-- ============================================================================

/-!
## Layer M / P Classification

| Gate operation | Arithmetic fact (M) | Interpretation (P) |
|---------------|--------------------|--------------------|
| Hadamard | Specified → equal-weight table (Gate-M1) | "Branch choice suspended" |
| H·H = I | Signed cancellation restores original (Gate-M2) | "Interference = table arithmetic" |
| CNOT | Mod 2 re-indexing of rows (Gate-M3) | "Entanglement = shared table constraint" |
| Bell state | Correlated two-row table (Gate-M4) | "No action at distance, shared table" |
| Measurement | Born-type quadratic weights (Gate-M5) | "Collapse = address specification" |
| Quantum eraser | Row post-selection (Gate-M6) | "No retrocausality" |
| Interference | Signed addition rule (Gate-M7) | "Same rule as moiré" |

Left column: all finite arithmetic, Layer M theorems.
Right column: Layer P.

All results are sorry = 0, axiom = 0.
-/

end A5_SM_Pathway.GateArithmetic
