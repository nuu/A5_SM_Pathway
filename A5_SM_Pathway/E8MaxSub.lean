/-
  A5_SM_Pathway/E8MaxSub.lean

  M58: E₈ maximal subalgebra selection theorem.

  Among all maximal subalgebras of E₈, the only one satisfying:
    (i)   product structure (family × gauge separation)
    (ii)  complex-type representation in 248 branching
    (iii) family factor fundamental representation dim = 3
  is E₆ × A₂.

  Method: Finite enumeration, closed by `cases` + `simp`.

  sorry = 0, axiom = 0.
-/

import Mathlib.Tactic

-- ============================================================
-- Maximal subalgebra enumeration
-- ============================================================

/-- The 8 maximal subalgebras of E₈ (Dynkin classification).
    Regular: D₈, A₈, A₄A₄, E₆A₂, E₇A₁
    Special: G₂F₄, A₁sp, B₂sp -/
inductive E8MaxSub where
  | D8      -- SO(16),         node 1 removal, mark 2
  | A8      -- SU(9),          node 2 removal, mark 3
  | A4A4    -- SU(5)×SU(5),    node 5 removal, mark 6
  | E6A2    -- E₆×SU(3),       node 7 removal, mark 3
  | E7A1    -- E₇×SU(2),       node 8 removal, mark 2
  | G2F4    -- G₂×F₄,          special maximal
  | A1sp    -- A₁,             special (index 1240)
  | B2sp    -- B₂ = SO(5),     special (index 340)
  deriving Repr, DecidableEq

-- ============================================================
-- Selection criteria
-- ============================================================

/-- C1: Product structure (at least 2 simple factors). -/
def E8MaxSub.hasProductStructure : E8MaxSub → Bool
  | .D8   => false   -- single factor SO(16)
  | .A8   => false   -- single factor SU(9)
  | .A4A4 => true    -- SU(5) × SU(5)
  | .E6A2 => true    -- E₆ × SU(3)
  | .E7A1 => true    -- E₇ × SU(2)
  | .G2F4 => true    -- G₂ × F₄
  | .A1sp => false   -- single factor
  | .B2sp => false   -- single factor

/-- C2: 248 branching contains a complex-type representation (R ≇ R̄).
    D₈:   120(adj,real) + 128_s(real, D_{4k})       → no complex
    A₈:   80(adj) + 84(Λ³,complex) + 84̄            → complex, but no product
    A₄²:  adjs(real) + (5,10)+(5̄,10̄)+(10,5)+(10̄,5̄) → complex
    E₆A₂: adjs(real) + (27,3)+(27̄,3̄)               → complex [M51]
    E₇A₁: adjs(real) + (56,2)(pseudo-real)           → no complex
    G₂F₄: all real (no Dynkin diagram automorphism)   → no complex
    A₁,B₂: single factor, all reps real               → no complex -/
def E8MaxSub.hasComplexRep : E8MaxSub → Bool
  | .D8   => false
  | .A8   => true
  | .A4A4 => true
  | .E6A2 => true
  | .E7A1 => false
  | .G2F4 => false
  | .A1sp => false
  | .B2sp => false

/-- C3: Family factor fundamental representation dimension.
    0 if no well-defined family factor. -/
def E8MaxSub.familyDim : E8MaxSub → Nat
  | .D8   => 0
  | .A8   => 0
  | .A4A4 => 5   -- SU(5) fund = 5
  | .E6A2 => 3   -- SU(3) fund = 3
  | .E7A1 => 2   -- SU(2) fund = 2
  | .G2F4 => 0
  | .A1sp => 0
  | .B2sp => 0

/-- All three selection criteria simultaneously. -/
def E8MaxSub.satisfiesSelection (h : E8MaxSub) : Bool :=
  h.hasProductStructure && h.hasComplexRep && (h.familyDim == 3)

-- ============================================================
-- M58: Selection theorem
-- ============================================================

/-- M58: E₆ × A₂ is the unique maximal subalgebra of E₈
    satisfying C1 (product) ∧ C2 (complex rep) ∧ C3 (family dim = 3). -/
theorem M58_E6A2_unique_selection :
    ∀ h : E8MaxSub, h.satisfiesSelection = true → h = E8MaxSub.E6A2 := by
  intro h; cases h <;> simp [E8MaxSub.satisfiesSelection,
    E8MaxSub.hasProductStructure, E8MaxSub.hasComplexRep, E8MaxSub.familyDim]

/-- M58 converse: E₆ × A₂ does satisfy all selection criteria. -/
theorem M58_E6A2_satisfies :
    E8MaxSub.E6A2.satisfiesSelection = true := by rfl

/-- M58 combined (iff). -/
theorem M58_iff :
    ∀ h : E8MaxSub, h.satisfiesSelection = true ↔ h = E8MaxSub.E6A2 := by
  intro h; constructor
  · exact M58_E6A2_unique_selection h
  · intro heq; subst heq; rfl

-- ============================================================
-- Supporting: individual condition checks
-- ============================================================

/-- C1 eliminates D₈, A₈, A₁, B₂. -/
theorem M58_C1_eliminates :
    E8MaxSub.D8.hasProductStructure = false ∧
    E8MaxSub.A8.hasProductStructure = false ∧
    E8MaxSub.A1sp.hasProductStructure = false ∧
    E8MaxSub.B2sp.hasProductStructure = false := ⟨rfl, rfl, rfl, rfl⟩

/-- C2 eliminates E₇×A₁ and G₂×F₄. -/
theorem M58_C2_eliminates :
    E8MaxSub.E7A1.hasComplexRep = false ∧
    E8MaxSub.G2F4.hasComplexRep = false := ⟨rfl, rfl⟩

/-- C3 eliminates A₄×A₄ (family dim = 5 ≠ 3). -/
theorem M58_C3_eliminates :
    E8MaxSub.A4A4.familyDim = 5 := rfl

-- ============================================================
-- Dimension checks (248 branching)
-- ============================================================

/-- 248 branching dimensions for each maximal subalgebra. -/
def E8MaxSub.branchDims : E8MaxSub → List Nat
  | .D8   => [120, 128]
  | .A8   => [80, 84, 84]
  | .A4A4 => [24, 24, 50, 50, 50, 50]
  | .E6A2 => [78, 8, 81, 81]
  | .E7A1 => [133, 3, 112]
  | .G2F4 => [14, 52, 182]
  | .A1sp => [248]
  | .B2sp => [248]

/-- All branchings sum to 248. -/
theorem M58_dims_sum_248 :
    ∀ h : E8MaxSub, h.branchDims.sum = 248 := by
  intro h; cases h <;> native_decide

-- ============================================================
-- Affine Ê₈ marks and node removal
-- ============================================================

/-- Affine Ê₈ marks for each node (0-indexed). -/
def affineE8Mark : Fin 9 → Nat
  | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 6
  | 5 => 5 | 6 => 4 | 7 => 3 | 8 => 2

/-- Marks sum to h = 30 (Coxeter number of E₈). -/
theorem marks_sum_30 :
    affineE8Mark 0 + affineE8Mark 1 + affineE8Mark 2 +
    affineE8Mark 3 + affineE8Mark 4 + affineE8Mark 5 +
    affineE8Mark 6 + affineE8Mark 7 + affineE8Mark 8 = 30 := by native_decide

/-- Only nodes 2 and 7 have mark = 3. -/
theorem mark3_nodes :
    ∀ i : Fin 9, affineE8Mark i = 3 ↔ (i = 2 ∨ i = 7) := by
  intro i; fin_cases i <;> simp [affineE8Mark]

/-- Node removal result (regular maximal subalgebra). -/
inductive NodeRemovalResult where
  | E8 | D8 | A8 | A7A1 | A5A2A1 | A4A4 | D5A3 | E6A2 | E7A1
  deriving Repr, DecidableEq

/-- Which subalgebra results from removing each affine node. -/
def nodeRemoval : Fin 9 → NodeRemovalResult
  | 0 => .E8 | 1 => .D8 | 2 => .A8 | 3 => .A7A1 | 4 => .A5A2A1
  | 5 => .A4A4 | 6 => .D5A3 | 7 => .E6A2 | 8 => .E7A1

/-- Mark-3 node 7 → E₆×A₂ (product), mark-3 node 2 → A₈ (non-product). -/
theorem mark3_node7_gives_E6A2 : nodeRemoval 7 = .E6A2 := rfl
theorem mark3_node2_gives_A8 : nodeRemoval 2 = .A8 := rfl

/-- Node 7 is the ONLY mark-3 removal giving a product structure. -/
theorem mark3_product_unique :
    ∀ i : Fin 9, affineE8Mark i = 3 →
    (nodeRemoval i = .E6A2 ∨ nodeRemoval i = .A8) := by
  intro i; fin_cases i <;> simp [affineE8Mark, nodeRemoval]
