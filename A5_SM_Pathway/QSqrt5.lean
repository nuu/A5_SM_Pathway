/-
  A5_SM_Pathway/QSqrt5.lean
  
  Q(√5) as a lightweight commutative ring for A₅ character computations.
  Not a full AdjoinRoot — just enough structure for native_decide + simp.
-/

import Mathlib.Tactic

/-- Elements of Q(√5): a + b√5 with a, b ∈ ℚ. -/
@[ext]
structure QSqrt5 where
  rat : ℚ
  surd : ℚ
  deriving Repr, DecidableEq, BEq

namespace QSqrt5

-- ============================================================
-- Ring operations
-- ============================================================

instance : Zero QSqrt5 := ⟨⟨0, 0⟩⟩
instance : One QSqrt5 := ⟨⟨1, 0⟩⟩

def add (x y : QSqrt5) : QSqrt5 := ⟨x.rat + y.rat, x.surd + y.surd⟩
def mul (x y : QSqrt5) : QSqrt5 :=
  ⟨x.rat * y.rat + 5 * x.surd * y.surd, x.rat * y.surd + x.surd * y.rat⟩
def neg (x : QSqrt5) : QSqrt5 := ⟨-x.rat, -x.surd⟩
def sub (x y : QSqrt5) : QSqrt5 := add x (neg y)

instance : Add QSqrt5 := ⟨add⟩
instance : Mul QSqrt5 := ⟨mul⟩
instance : Neg QSqrt5 := ⟨neg⟩
instance : Sub QSqrt5 := ⟨sub⟩

/-- Scalar multiplication by ℚ. -/
def smulQ (c : ℚ) (x : QSqrt5) : QSqrt5 := ⟨c * x.rat, c * x.surd⟩

/-- Natural number scalar multiplication. -/
def nsmul : ℕ → QSqrt5 → QSqrt5
  | 0, _ => 0
  | n + 1, x => add x (nsmul n x)

/-- Integer scalar multiplication. -/
def zsmul : ℤ → QSqrt5 → QSqrt5
  | .ofNat n, x => nsmul n x
  | .negSucc n, x => neg (nsmul (n + 1) x)

/-- Power. -/
def pow : QSqrt5 → ℕ → QSqrt5
  | _, 0 => 1
  | x, n + 1 => mul x (pow x n)

instance : Pow QSqrt5 ℕ := ⟨pow⟩

/-- OfNat for small literals. -/
instance : OfNat QSqrt5 (nat_lit 0) := ⟨⟨0, 0⟩⟩
instance : OfNat QSqrt5 (nat_lit 1) := ⟨⟨1, 0⟩⟩
instance (n : ℕ) : OfNat QSqrt5 (n + 2) := ⟨⟨↑(n + 2), 0⟩⟩

-- ============================================================
-- Distinguished elements
-- ============================================================

/-- φ = (1+√5)/2 -/
def phi : QSqrt5 := ⟨1/2, 1/2⟩

/-- 1/φ = (-1+√5)/2 -/
def phiInv : QSqrt5 := ⟨-1/2, 1/2⟩

/-- √5 as element -/
def sqrt5 : QSqrt5 := ⟨0, 1⟩

-- ============================================================
-- Galois automorphism σ: √5 → -√5
-- ============================================================

def galois (x : QSqrt5) : QSqrt5 := ⟨x.rat, -x.surd⟩

-- ============================================================
-- simp lemmas
-- ============================================================

@[simp] theorem add_rat (x y : QSqrt5) : (x + y).rat = x.rat + y.rat := rfl
@[simp] theorem add_surd (x y : QSqrt5) : (x + y).surd = x.surd + y.surd := rfl
@[simp] theorem mul_rat (x y : QSqrt5) :
    (x * y).rat = x.rat * y.rat + 5 * x.surd * y.surd := rfl
@[simp] theorem mul_surd (x y : QSqrt5) :
    (x * y).surd = x.rat * y.surd + x.surd * y.rat := rfl
@[simp] theorem neg_rat (x : QSqrt5) : (-x).rat = -x.rat := rfl
@[simp] theorem neg_surd (x : QSqrt5) : (-x).surd = -x.surd := rfl
@[simp] theorem zero_rat : (0 : QSqrt5).rat = 0 := rfl
@[simp] theorem zero_surd : (0 : QSqrt5).surd = 0 := rfl
@[simp] theorem one_rat : (1 : QSqrt5).rat = 1 := rfl
@[simp] theorem one_surd : (1 : QSqrt5).surd = 0 := rfl

@[simp] theorem galois_rat (x : QSqrt5) : (galois x).rat = x.rat := rfl
@[simp] theorem galois_surd (x : QSqrt5) : (galois x).surd = -x.surd := rfl
@[simp] theorem galois_galois (x : QSqrt5) : galois (galois x) = x := by
  ext <;> simp [galois]
@[simp] theorem galois_add (x y : QSqrt5) : galois (x + y) = galois x + galois y := by
  ext <;> simp [galois]; ring
@[simp] theorem galois_mul (x y : QSqrt5) : galois (x * y) = galois x * galois y := by
  ext <;> simp [galois]; ring
@[simp] theorem galois_neg (x : QSqrt5) : galois (-x) = -galois x := by
  ext <;> simp [galois]

theorem phi_mul_phiInv : phi * phiInv = 1 := by
  ext <;> simp [phi, phiInv] <;> ring

theorem phi_add_phiInv : phi + phiInv = sqrt5 := by
  ext <;> simp [phi, phiInv, sqrt5] <;> ring

theorem galois_phi : galois phi = neg phiInv := by
  ext <;> simp [galois, phi, phiInv, neg]; ring

/-- Embedding of ℚ into QSqrt5. -/
def ofRat (q : ℚ) : QSqrt5 := ⟨q, 0⟩

@[simp] theorem galois_ofRat (q : ℚ) : galois (ofRat q) = ofRat q := by
  ext <;> simp [galois, ofRat]

/-- An element is rational iff surd = 0. -/
def isRational (x : QSqrt5) : Prop := x.surd = 0

theorem galois_fixed_iff_rational (x : QSqrt5) : galois x = x ↔ isRational x := by
  unfold isRational
  constructor
  · intro h
    have := congr_arg QSqrt5.surd h
    simp [galois] at this
    linarith
  · intro h
    ext
    · simp [galois]
    · simp [galois, h]

end QSqrt5
