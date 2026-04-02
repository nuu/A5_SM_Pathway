import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# A₅ 
# Three Observation Modes for A₅

## 

A₅ （ker(π) = A₅）「」
A₅ 「」2:

  **Mode 1: ** (A₅ → Q, )
    ker(π) = A₅（§3 ）

  **Mode 2: ** ()
    Plancherel C₅± 
    （IndirectObservation.lean （Paper I ））

  **Mode 3: ** ( → A₅ → , Barrington )
    Boolean  A₅ 
    A₅ 
    （1 or ≠1）

 Mode 3 —  — 

## 

「A₅ → 」
 Barrington ****:

     → [] → A₅  → [] → 

A₅ 「」****
A₅ 

:
  （）
  
  
  

## Layer 

- **M**:  ≠ 1 AND ↔ 
   — 
- **P**: 「 A₅ 」
   P

STATUS: sorry = 0, axiom = 0
-/

noncomputable section

namespace MDL
namespace TranslationLayer

-- ============================================================================
-- § 1.  : A₅ 
-- ============================================================================

/-- A₅ （Galois, 1832） -/
theorem A5_not_solvable : ¬ IsSolvable (alternatingGroup (Fin 5)) := by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup_five
  rw [← IsSimpleGroup.comm_iff_isSolvable]
  intro h_comm
  let σ : alternatingGroup (Fin 5) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 2 3,
     Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩
  let τ : alternatingGroup (Fin 5) :=
    ⟨Equiv.swap 1 2 * Equiv.swap 3 4,
     Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩
  exact (show σ * τ ≠ τ * σ by
    rw [Ne, Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_mul]; decide)
    (h_comm σ τ)

-- ============================================================================
-- § 2.   AND 
-- ============================================================================

abbrev S5 := Equiv.Perm (Fin 5)

/-- : [a, b] = a⁻¹ b⁻¹ a b -/
def comm (a b : S5) : S5 := a⁻¹ * b⁻¹ * a * b

/--  σ, τ
    σ = (01)(23), τ = (12)(34) -/
def σ : S5 := Equiv.swap 0 1 * Equiv.swap 2 3
def τ : S5 := Equiv.swap 1 2 * Equiv.swap 3 4

/-- σ, τ : [σ, τ] ≠ 1
     -/
theorem comm_σ_τ_ne_one : comm σ τ ≠ 1 := by
  simp [comm, σ, τ]; decide

/--
**AND ↔ **

  [σ, τ] ≠ 1   (AND: true  ∧ true  = true)
  [σ, 1] = 1   (AND: true  ∧ false = false)
  [1, τ] = 1   (AND: false ∧ true  = false)
  [1, 1] = 1   (AND: false ∧ false = false)

Boolean  AND A₅（ S₅）
 Barrington 
-/
theorem and_commutator_table :
    comm σ τ ≠ 1 ∧
    comm σ 1 = 1 ∧
    comm 1 τ = 1 ∧
    comm (1 : S5) 1 = 1 := by
  refine ⟨comm_σ_τ_ne_one, ?_, ?_, ?_⟩
  all_goals simp [comm]

-- ============================================================================
-- § 3.  
-- ============================================================================

/--
**** (Translation Layer)

Boolean  A₅/S₅ 

  encode : （Boolean ）→ S₅ 
  execute :  → S₅ 
  decode :  1  → Boolean 

:
  encode/decode （Boolean）
  execute （A₅ ）
  「」 decode 
  A₅ 
-/
structure TransLayer where
  /-- （） -/
  inputBits : ℕ
  /-- S₅  -/
  program : (Fin inputBits → Bool) → List S5
  /-- :  -/
  execute (inputs : Fin inputBits → Bool) : S5 :=
    (program inputs).foldl (· * ·) 1
  /-- :  ≠ 1 -/
  nontrivial : ∃ inputs : Fin inputBits → Bool,
    (program inputs).foldl (· * ·) 1 ≠ 1

/--
****: decode 

「g = 1 」
 S₅ A₅ 

-/
def decode (g : S5) : Bool := g = 1

/-- decode （） -/
theorem decode_decidable : ∀ g : S5, g = 1 ∨ g ≠ 1 := by
  intro g; exact eq_or_ne g 1

-- ============================================================================
-- § 4.  AND 
-- ============================================================================

/--
**: 2 AND**

 (b₁, b₂) :
  b₁ = true  → σ,  b₁ = false → 1
  b₂ = true  → τ,  b₂ = false → 1

 = [σ or 1]⁻¹ ++ [τ or 1]⁻¹ ++ [σ or 1] ++ [τ or 1]
（）

: [encode(b₁), encode(b₂)] = 1 ⟺ b₁ ∧ b₂ = false
-/
def encodebit1 (b : Bool) : S5 := if b then σ else 1
def encodebit2 (b : Bool) : S5 := if b then τ else 1

/-- AND  =  -/
def andProgram (b₁ b₂ : Bool) : S5 :=
  comm (encodebit1 b₁) (encodebit2 b₂)

/--
**AND **

  andProgram true  true  ≠ 1   (= AND true)
  andProgram true  false = 1   (= AND false)
  andProgram false true  = 1   (= AND false)
  andProgram false false = 1   (= AND false)
-/
theorem andProgram_correct :
    andProgram true true ≠ 1 ∧
    andProgram true false = 1 ∧
    andProgram false true = 1 ∧
    andProgram false false = 1 := by
  simp [andProgram, encodebit1, encodebit2]
  exact and_commutator_table

/-- AND  decode : decode(andProgram b₁ b₂) = ¬(b₁ ∧ b₂) -/
theorem andProgram_decode (b₁ b₂ : Bool) :
    decode (andProgram b₁ b₂) = !(b₁ && b₂) := by
  rcases b₁ with _ | _ <;> rcases b₂ with _ | _ <;>
    simp [decode, andProgram, encodebit1, encodebit2, comm, σ, τ] <;> decide

-- ============================================================================
-- § 5.  
-- ============================================================================

/--
**A₅ （）**

  Mode 1 (): A₅ →  Q 
    （;  §3 ）

  Mode 2 (): 
    （IndirectObservation.lean （Paper I ））

  Mode 3 ():  AND 
    A₅ 
    （Bool）

  :
    Mode 1  = 
    Mode 2 = （ = ）
    Mode 3 = （ →  → ）
-/
theorem three_observation_modes :
    -- Mode 1: A₅ （）
    (¬ IsSolvable (alternatingGroup (Fin 5))) ∧
    -- Mode 3a: （）
    (comm σ τ ≠ 1) ∧
    -- Mode 3b: AND （ →  → ）
    (andProgram true true ≠ 1 ∧
     andProgram true false = 1 ∧
     andProgram false true = 1 ∧
     andProgram false false = 1) ∧
    -- Mode 3c: （）
    (∀ g : S5, g = 1 ∨ g ≠ 1) :=
  ⟨A5_not_solvable,
   comm_σ_τ_ne_one,
   andProgram_correct,
   decode_decidable⟩

-- ============================================================================
-- § 6.  
-- ============================================================================

/--
****

:

  (Opacity)  A₅ →  Q 
  (Barrington)  → A₅ →  

: 「A₅ 」
「 A₅ 」

:
  Opacity:    A₅ ──→ Q    （: ）
  Barrington: Bool ──→ A₅ ──→ Bool  （: ）

:  decode(g) = (g = 1) 
（decode(a * b) ≠ decode(a) ∧ decode(b) in general）

-/
theorem opacity_and_translation_compatible :
    -- : A₅ 
    (¬ IsSolvable (alternatingGroup (Fin 5))) ∧
    -- : AND 
    (comm σ τ ≠ 1) ∧
    -- :
    --   decode(σ * σ⁻¹) = true    decode(σ) = false
    --    decode  decode(a*b) = decode(a) ∧ decode(b) 
    --    true ≠ false ∧ ()
    (decode (σ * σ⁻¹) = true ∧ decode σ = false) := by
  refine ⟨A5_not_solvable, comm_σ_τ_ne_one, ?_⟩
  constructor
  · -- σ * σ⁻¹ = 1, so decode = true
    simp [decode]
  · -- σ ≠ 1
    simp [decode, σ]; decide

end TranslationLayer
end MDL
