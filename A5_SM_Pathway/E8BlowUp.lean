import Mathlib.Tactic

/-!
# E8BlowUp: Affine Ê₈ Node Removal and Breaking Chains

  M59: Complete classification of single-node removal from affine Ê₈.
  M60: E₆ factor uniqueness (node 7 only).
  M61: Mark-3 dichotomy (node 7 → E₆×A₂, node 2 → A₈).

  Additional: E₆ internal node removal toward trinification analysis.

  Date: 2026-03-29
  sorry = 0, axiom = 0
-/

-- ============================================================
-- §1. Affine Ê₈ McKay graph structure
-- ============================================================

/-- The 9 nodes of the affine Ê₈ McKay graph (= 2I irreps).
    Numbering follows the standard McKay convention.

    Graph topology:
      0 — 8 — 7 — 6 — 5 — 4 — 3 — 1
                              |
                              2
-/
inductive AffE8Node where
  | n0 | n1 | n2 | n3 | n4 | n5 | n6 | n7 | n8
  deriving Repr, DecidableEq, Fintype, Inhabited

/-- Mark of each node (= dimension of 2I irrep). -/
def AffE8Node.mark : AffE8Node → Nat
  | .n0 => 1  -- ρ₁ (trivial, affine node)
  | .n1 => 2  -- spinorial
  | .n2 => 3  -- ρ₃
  | .n3 => 4  -- ρ₄
  | .n4 => 6  -- spinorial (branch point)
  | .n5 => 5  -- ρ₅
  | .n6 => 4  -- spinorial
  | .n7 => 3  -- ρ₃'
  | .n8 => 2  -- spinorial

/-- Marks sum to h = 30 (Coxeter number of E₈). -/
theorem marks_sum_coxeter :
    AffE8Node.n0.mark + AffE8Node.n1.mark + AffE8Node.n2.mark +
    AffE8Node.n3.mark + AffE8Node.n4.mark + AffE8Node.n5.mark +
    AffE8Node.n6.mark + AffE8Node.n7.mark + AffE8Node.n8.mark = 30 := by
  decide

/-- Parity classification: A₅ type (EVEN) vs spinorial (ODD).
    A₅-type nodes carry irreps of A₅; spinorial nodes carry
    the remaining 2I irreps. -/
def AffE8Node.isA5type : AffE8Node → Bool
  | .n0 => true   -- ρ₁
  | .n1 => false   -- spinorial
  | .n2 => true   -- ρ₃
  | .n3 => true   -- ρ₄
  | .n4 => false   -- spinorial (branch point)
  | .n5 => true   -- ρ₅
  | .n6 => false   -- spinorial
  | .n7 => true   -- ρ₃'
  | .n8 => false   -- spinorial

/-- Sum of A₅-type marks squared = |A₅| = 60. -/
theorem A5type_marks_sq_sum :
    AffE8Node.n0.mark ^ 2 + AffE8Node.n2.mark ^ 2 +
    AffE8Node.n3.mark ^ 2 + AffE8Node.n5.mark ^ 2 +
    AffE8Node.n7.mark ^ 2 = 60 := by decide

/-- Sum of spinorial marks squared = 60. -/
theorem spinorial_marks_sq_sum :
    AffE8Node.n1.mark ^ 2 + AffE8Node.n4.mark ^ 2 +
    AffE8Node.n6.mark ^ 2 + AffE8Node.n8.mark ^ 2 = 60 := by decide

/-- A₅-type mark-square sum + spinorial mark-square sum = 120 = |2I|. -/
theorem total_marks_sq_sum_2I :
    (AffE8Node.n0.mark ^ 2 + AffE8Node.n2.mark ^ 2 +
     AffE8Node.n3.mark ^ 2 + AffE8Node.n5.mark ^ 2 +
     AffE8Node.n7.mark ^ 2) +
    (AffE8Node.n1.mark ^ 2 + AffE8Node.n4.mark ^ 2 +
     AffE8Node.n6.mark ^ 2 + AffE8Node.n8.mark ^ 2) = 120 := by decide

-- ============================================================
-- §2. Adjacency structure
-- ============================================================

/-- Adjacency relation of the affine Ê₈ McKay graph.
    Encoded as: node i is adjacent to node j. -/
def AffE8Node.adj : AffE8Node → AffE8Node → Bool
  | .n0, .n8 => true | .n8, .n0 => true
  | .n8, .n7 => true | .n7, .n8 => true
  | .n7, .n6 => true | .n6, .n7 => true
  | .n6, .n5 => true | .n5, .n6 => true
  | .n5, .n4 => true | .n4, .n5 => true
  | .n4, .n3 => true | .n3, .n4 => true
  | .n3, .n1 => true | .n1, .n3 => true
  | .n4, .n2 => true | .n2, .n4 => true
  | _, _ => false

/-- Adjacency is symmetric. -/
theorem adj_symm : ∀ a b : AffE8Node, a.adj b = b.adj a := by decide

/-- No self-loops. -/
theorem adj_irrefl : ∀ a : AffE8Node, a.adj a = false := by decide

/-- Degree of each node (number of neighbors). -/
def AffE8Node.degree : AffE8Node → Nat
  | .n0 => 1  -- connected to n8 only
  | .n1 => 1  -- connected to n3 only
  | .n2 => 1  -- connected to n4 only
  | .n3 => 2  -- connected to n4, n1
  | .n4 => 3  -- connected to n5, n3, n2  (branch point)
  | .n5 => 2  -- connected to n6, n4
  | .n6 => 2  -- connected to n7, n5
  | .n7 => 2  -- connected to n8, n6
  | .n8 => 2  -- connected to n0, n7

/-- Node 4 is the unique trivalent (branch) node. -/
theorem branch_point_unique :
    ∀ a : AffE8Node, a.degree = 3 ↔ a = .n4 := by decide

-- ============================================================
-- §3. M59: Single-node removal — complete classification
-- ============================================================

/-- Dynkin type of a simple Lie algebra component. -/
inductive SimpleDynkinType where
  | A : Nat → SimpleDynkinType  -- A_n (n ≥ 1), i.e., SU(n+1)
  | D : Nat → SimpleDynkinType  -- D_n (n ≥ 4), i.e., SO(2n)
  | E6 | E7 | E8
  deriving Repr, DecidableEq

/-- Residual Dynkin type = list of simple components (direct sum). -/
abbrev ResidualDynkin := List SimpleDynkinType

/-- M59: Complete classification of single-node removal from affine Ê₈.

    Removing node k gives the residual Dynkin type shown.
    This determines the unbroken gauge group after partial resolution. -/
def nodeRemovalResult : AffE8Node → ResidualDynkin
  | .n0 => [.E8]                              -- remove affine → finite E₈
  | .n1 => [.D 8]                             -- SO(16)
  | .n2 => [.A 8]                             -- SU(9)
  | .n3 => [.A 7, .A 1]                       -- SU(8) × SU(2)
  | .n4 => [.A 5, .A 2, .A 1]                 -- SU(6) × SU(3) × SU(2)
  | .n5 => [.A 4, .A 4]                       -- SU(5) × SU(5)
  | .n6 => [.D 5, .A 3]                       -- SO(10) × SU(4)
  | .n7 => [.E6, .A 2]                        -- E₆ × SU(3)  ★
  | .n8 => [.E7, .A 1]                        -- E₇ × SU(2)

-- ─── Rank verification ───

/-- Rank of a simple Dynkin type. -/
def SimpleDynkinType.rank : SimpleDynkinType → Nat
  | .A n => n
  | .D n => n
  | .E6 => 6 | .E7 => 7 | .E8 => 8

/-- Total rank of the residual type should be 8 (= rank E₈). -/
def totalRank (l : ResidualDynkin) : Nat :=
  l.map SimpleDynkinType.rank |>.sum

/-- All 9 removals give total rank 8. -/
theorem M59_rank_check :
    ∀ k : AffE8Node, totalRank (nodeRemovalResult k) = 8 := by decide

-- ─── Component count ───

/-- Number of connected components in the residual. -/
def numComponents (k : AffE8Node) : Nat :=
  (nodeRemovalResult k).length

/-- Node 4 is the only removal giving 3 components. -/
theorem three_components_unique :
    ∀ k : AffE8Node, numComponents k = 3 ↔ k = .n4 := by decide

/-- Nodes 0, 1, 2 give connected residuals (1 component). -/
theorem connected_residuals :
    numComponents .n0 = 1 ∧ numComponents .n1 = 1 ∧ numComponents .n2 = 1 := by
  decide

-- ============================================================
-- §4. M60: E₆ factor uniqueness
-- ============================================================

/-- Does a residual Dynkin type contain an E₆ factor? -/
def hasE6Factor (l : ResidualDynkin) : Bool :=
  l.any (· == .E6)

/-- M60: The only single-node removal giving an E₆ factor is node 7. -/
theorem M60_E6_factor_unique :
    ∀ k : AffE8Node, hasE6Factor (nodeRemovalResult k) = true ↔ k = .n7 := by
  decide

/-- Similarly: E₇ factor appears only from node 8 removal. -/
theorem E7_factor_unique :
    ∀ k : AffE8Node,
      (nodeRemovalResult k).any (· == .E7) = true ↔ k = .n8 := by
  decide

/-- E₈ factor appears only from node 0 (affine) removal. -/
theorem E8_factor_unique :
    ∀ k : AffE8Node,
      (nodeRemovalResult k).any (· == .E8) = true ↔ k = .n0 := by
  decide

-- ============================================================
-- §5. M61: Mark-3 dichotomy
-- ============================================================

/-- Mark-3 nodes are exactly {n2, n7}. -/
theorem mark3_nodes_are :
    ∀ k : AffE8Node, k.mark = 3 ↔ (k = .n2 ∨ k = .n7) := by decide

/-- Mark-3 A₅-type nodes are exactly {n2, n7}
    (both mark-3 nodes happen to be A₅-type). -/
theorem mark3_A5type :
    ∀ k : AffE8Node, k.mark = 3 → k.isA5type = true := by decide

/-- M61: Mark-3 dichotomy.
    Node 7 (ρ₃') → E₆ × A₂ (trinification possible).
    Node 2 (ρ₃)  → A₈ = SU(9) (trinification impossible). -/
theorem M61_mark3_dichotomy :
    nodeRemovalResult .n7 = [.E6, .A 2] ∧
    nodeRemovalResult .n2 = [.A 8] := by decide

/-- Does a residual type contain an A₂ = SU(3) factor? -/
def hasA2Factor (l : ResidualDynkin) : Bool :=
  l.any (· == .A 2)

/-- A₂ factor appears from removing nodes 4 or 7. -/
theorem A2_factor_nodes :
    ∀ k : AffE8Node,
      hasA2Factor (nodeRemovalResult k) = true ↔ (k = .n4 ∨ k = .n7) := by
  decide

/-- M61 corollary: Among mark-3 removals, only node 7 gives product structure. -/
theorem M61_mark3_product :
    ∀ k : AffE8Node, k.mark = 3 →
      ((nodeRemovalResult k).length ≥ 2 ↔ k = .n7) := by
  decide

-- ============================================================
-- §6. E₆ internal node removal (toward trinification)
-- ============================================================

/-- The 6 nodes of the E₆ subgraph (after removing node 7 from Ê₈).
    These are McKay nodes {1, 2, 3, 4, 5, 6}.

    E₆ graph:
      6 — 5 — 4 — 3 — 1
                  |
                  2
-/
inductive E6Node where
  | e1 | e2 | e3 | e4 | e5 | e6
  deriving Repr, DecidableEq, Fintype, Inhabited

/-- E₆ node → corresponding McKay node index. -/
def E6Node.toMcKay : E6Node → AffE8Node
  | .e1 => .n1  -- mark 2, spinorial
  | .e2 => .n2  -- mark 3, ρ₃
  | .e3 => .n3  -- mark 4, ρ₄
  | .e4 => .n4  -- mark 6, spinorial (branch)
  | .e5 => .n5  -- mark 5, ρ₅
  | .e6 => .n6  -- mark 4, spinorial

/-- E₆ internal adjacency. -/
def E6Node.adj : E6Node → E6Node → Bool
  | .e6, .e5 => true | .e5, .e6 => true
  | .e5, .e4 => true | .e4, .e5 => true
  | .e4, .e3 => true | .e3, .e4 => true
  | .e3, .e1 => true | .e1, .e3 => true
  | .e4, .e2 => true | .e2, .e4 => true
  | _, _ => false

/-- Mark of each E₆ node (inherited from McKay). -/
def E6Node.mark : E6Node → Nat :=
  fun n => n.toMcKay.mark

/-- Marks within E₆ sum to 24 (= 30 − 3 − 3, removing nodes 0,7,8). -/
theorem E6_marks_sum :
    E6Node.e1.mark + E6Node.e2.mark + E6Node.e3.mark +
    E6Node.e4.mark + E6Node.e5.mark + E6Node.e6.mark = 24 := by decide

/-- E₆ internal single-node removal.
    E₆ graph:  e6 — e5 — e4 — e3 — e1
                          |
                          e2

    Derivation for each case:
    e1: {e2,e3,e4,e5,e6}, branch at e4, arms [1,1,2] → D₅
    e2: {e1,e3,e4,e5,e6}, chain e6-e5-e4-e3-e1 → A₅
    e3: {e2,e4,e5,e6} ∪ {e1}, chain e6-e5-e4-e2 → A₄, isolated → A₁
    e4: {e5,e6} ∪ {e1,e3} ∪ {e2}, → A₂ + A₂ + A₁
    e5: {e6} ∪ {e1,e2,e3,e4}, isolated e6 → A₁, chain e1-e3-e4-e2 → A₄
    e6: {e1,e2,e3,e4,e5}, branch at e4, arms [1,1,2] → D₅
-/
def e6InternalRemoval : E6Node → ResidualDynkin
  | .e1 => [.D 5]              -- {e2,e3,e4,e5,e6}: branch at e4, arms [1,1,2] → D₅
  | .e2 => [.A 5]              -- {e1,e3,e4,e5,e6}: chain e6-e5-e4-e3-e1 → A₅
  | .e3 => [.A 4, .A 1]        -- {e2,e4,e5,e6} ∪ {e1}: chain e6-e5-e4-e2 → A₄, {e1} → A₁
  | .e4 => [.A 2, .A 2, .A 1]  -- {e5,e6} ∪ {e1,e3} ∪ {e2}: A₂ + A₂ + A₁
  | .e5 => [.A 4, .A 1]        -- {e1,e2,e3,e4} ∪ {e6}: chain e1-e3-e4-e2 → A₄, {e6} → A₁
  | .e6 => [.D 5]              -- {e1,e2,e3,e4,e5}: branch at e4, arms [1,1,2] → D₅

/-- E₆ internal node removal: rank check (each sums to 5). -/
theorem e6_internal_rank :
    ∀ k : E6Node, totalRank (e6InternalRemoval k) = 5 := by decide

/-- Removing the branch point e4 gives three components including two A₂'s. -/
theorem e4_removal_three_components :
    e6InternalRemoval .e4 = [.A 2, .A 2, .A 1] := by decide

/-- Branch point removal is the only E₆-internal removal giving multiple A₂ factors. -/
def countA2 (l : ResidualDynkin) : Nat :=
  l.filter (· == .A 2) |>.length

theorem e4_unique_double_A2 :
    ∀ k : E6Node, countA2 (e6InternalRemoval k) ≥ 2 ↔ k = .e4 := by decide

/-- E₆ node removals giving SO(10) (D₅ factor): nodes e1 and e6. -/
theorem D5_from_E6 :
    ∀ k : E6Node,
      (e6InternalRemoval k).any (· == .D 5) = true ↔ (k = .e1 ∨ k = .e6) := by
  decide

-- ============================================================
-- §7. Breaking chain analysis
-- ============================================================

/-- Does a residual type admit trinification SU(3)³?
    This requires at least two A₂ factors in the residual,
    or enough structure to embed SU(3)³.
    
    Conservative criterion: the residual type, when decomposed into
    simple factors, contains at least one E₆ or three A₂'s. -/
def admitsTrinification (l : ResidualDynkin) : Bool :=
  l.any (· == .E6) || ((l.filter (· == .A 2)).length ≥ 3)

/-- Only the node 7 removal from Ê₈ admits trinification
    (via E₆ → SU(3)³ further breaking). -/
theorem trinification_requires_node7 :
    ∀ k : AffE8Node,
      admitsTrinification (nodeRemovalResult k) = true ↔ k = .n7 := by
  decide

/-- The two-step chain: Ê₈ → (remove n7) → E₆ × A₂ → (remove e4 from E₆) → A₂ × A₂ × A₁ × A₂.
    This gives three SU(3) factors plus an SU(2), which is the closest
    to trinification achievable by sequential node removal. -/
theorem two_step_trinification_chain :
    nodeRemovalResult .n7 = [.E6, .A 2] ∧
    e6InternalRemoval .e4 = [.A 2, .A 2, .A 1] := by decide

-- ============================================================
-- §8. Physical selection theorems
-- ============================================================

/-- Does the removal give a product structure
    (more than one simple factor)? -/
def givesProduct (k : AffE8Node) : Bool :=
  (nodeRemovalResult k).length ≥ 2

/-- Product structure from single-node removal: nodes 3,4,5,6,7,8. -/
theorem product_nodes :
    ∀ k : AffE8Node,
      givesProduct k = true ↔
        (k = .n3 ∨ k = .n4 ∨ k = .n5 ∨ k = .n6 ∨ k = .n7 ∨ k = .n8) := by
  decide

/-- Selection by E₆ + SU(3)_family:
    The unique removal giving E₆ × A₂ = E₆ × SU(3)_family. -/
theorem E6_A2_unique_removal :
    ∀ k : AffE8Node,
      (hasE6Factor (nodeRemovalResult k) = true ∧
       hasA2Factor (nodeRemovalResult k) = true) ↔ k = .n7 := by
  decide

/-- Physical summary: requiring
    (i)   product structure (family × gauge separation)
    (ii)  E₆ gauge factor (for trinification pathway)
    (iii) 3-dimensional family factor (for 3 generations)
    selects node 7 removal uniquely.
    
    This is the node-removal counterpart of M58. -/
theorem node7_physical_selection :
    ∀ k : AffE8Node,
      (givesProduct k = true ∧
       hasE6Factor (nodeRemovalResult k) = true ∧
       k.mark = 3) ↔ k = .n7 := by
  decide

-- ============================================================
-- §9. Galois pair structure (connection to M49)
-- ============================================================

/-- The two mark-3 A₅-type nodes form a Galois pair. -/
theorem galois_pair_mark3 :
    ∀ k : AffE8Node,
      (k.mark = 3 ∧ k.isA5type = true) ↔ (k = .n2 ∨ k = .n7) := by decide

/-- Galois pair dichotomy: their removals give completely different structures.
    - Node 7 (ρ₃'): removal gives E₆ × A₂ (product, trinification possible)
    - Node 2 (ρ₃):  removal gives A₈ = SU(9) (single factor, no trinification) -/
theorem galois_pair_asymmetry :
    (nodeRemovalResult .n7).length = 2 ∧
    (nodeRemovalResult .n2).length = 1 := by decide

/-- The Galois pair separates: ρ₃ stays in E₆, ρ₃' is removed to become family. -/
theorem galois_separation :
    hasE6Factor (nodeRemovalResult .n7) = true ∧  -- ρ₃' removed → E₆ remains (containing ρ₃)
    hasE6Factor (nodeRemovalResult .n2) = false    -- ρ₃ removed → no E₆
    := by decide

-- ============================================================
-- §10. Summary theorem
-- ============================================================

/-- Grand summary of B4 analysis.
    The unique breaking chain from Ê₈ to SM-like structure via E₆:
    
    Step 0: Ê₈ (affine, 9 nodes)
    Step 1: Remove node 7 (ρ₃', mark 3) → E₆ × A₂  [M59/M60]
    Step 2: Inside E₆, remove branch node e4 → A₂ × A₂ × A₁  [E₆ internal]
    
    Combined: A₂_family × A₂ × A₂ × A₁
            = SU(3)_fam × SU(3) × SU(3) × SU(2)
    
    This is the closest achievable to SU(3)_fam × SU(3)³ via node removal.
    The extra SU(2) vs third SU(3) reflects that trinification
    E₆ → SU(3)³ is a regular subalgebra embedding, not a node removal. -/
theorem B4_grand_summary :
    -- M59: node 7 gives E₆ × A₂
    nodeRemovalResult .n7 = [.E6, .A 2] ∧
    -- M60: this is the unique E₆ removal
    (∀ k : AffE8Node, hasE6Factor (nodeRemovalResult k) = true → k = .n7) ∧
    -- M61: the other mark-3 node gives A₈ (no product)
    nodeRemovalResult .n2 = [.A 8] ∧
    -- E₆ internal: branch point gives best trinification approximation
    e6InternalRemoval .e4 = [.A 2, .A 2, .A 1] := by
  refine ⟨by decide, ?_, by decide, by decide⟩
  intro k hk; revert hk; cases k <;> simp_all [hasE6Factor, nodeRemovalResult, List.any]
