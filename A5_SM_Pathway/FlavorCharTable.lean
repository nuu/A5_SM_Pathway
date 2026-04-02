/-
  A5_SM_Pathway/FlavorCharTable.lean  (v2)
  
  A₅ character table with Finset.univ.sum-based inner products.
  All computations over QSqrt5 with native_decide.
  
  Theorems: M01–M03, M11, M28, plus supporting decompositions.
-/

import A5_SM_Pathway.QSqrt5
import Mathlib.Tactic

open QSqrt5

-- ============================================================
-- A₅ conjugacy class data
-- ============================================================

/-- Class sizes. -/
def A5_classSize : Fin 5 → ℚ
  | 0 => 1 | 1 => 15 | 2 => 20 | 3 => 12 | 4 => 12

/-- Squaring map: class of g² given class of g. -/
def A5_sq : Fin 5 → Fin 5
  | 0 => 0 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3

/-- Cubing map: class of g³ given class of g.
    Orders: e→e, C₂→C₂, C₃→e, C₅⁺→C₅⁻, C₅⁻→C₅⁺.
    (For order 5: g³ = g⁻² and g² swaps C₅ classes, g⁻ stays in same class,
     so g⁻² = g³ swaps.) -/
def A5_cube : Fin 5 → Fin 5
  | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 4 | 4 => 3

-- ============================================================
-- Character table
-- ============================================================

/-- Rows: ρ₁(0), ρ₃(1), ρ₃'(2), ρ₄(3), ρ₅(4)
    Cols: {e}(0), C₂(1), C₃(2), C₅⁺(3), C₅⁻(4) -/
def A5_chi : Fin 5 → Fin 5 → QSqrt5
  | 0, _ => ⟨1, 0⟩
  | 1, 0 => ⟨3, 0⟩ | 1, 1 => ⟨-1, 0⟩ | 1, 2 => ⟨0, 0⟩
  | 1, 3 => phi      | 1, 4 => ⟨1/2, -1/2⟩
  | 2, 0 => ⟨3, 0⟩ | 2, 1 => ⟨-1, 0⟩ | 2, 2 => ⟨0, 0⟩
  | 2, 3 => ⟨1/2, -1/2⟩ | 2, 4 => phi
  | 3, 0 => ⟨4, 0⟩ | 3, 1 => ⟨0, 0⟩ | 3, 2 => ⟨1, 0⟩
  | 3, 3 => ⟨-1, 0⟩ | 3, 4 => ⟨-1, 0⟩
  | 4, 0 => ⟨5, 0⟩ | 4, 1 => ⟨1, 0⟩ | 4, 2 => ⟨-1, 0⟩
  | 4, 3 => ⟨0, 0⟩ | 4, 4 => ⟨0, 0⟩

-- ============================================================
-- Inner product (Finset.univ.sum version)
-- ============================================================

/-- (1/60) Σ_C |C| · f(C) · g(C)  over the 5 conjugacy classes.
    Returns a QSqrt5 value. For real characters f* = f. -/
def charIP (f g : Fin 5 → QSqrt5) : QSqrt5 :=
  let weighted := fun c => smulQ (A5_classSize c / 60) (f c * g c)
  -- Finset.univ.sum would be ideal; for native_decide we expand:
  weighted 0 + weighted 1 + weighted 2 + weighted 3 + weighted 4

/-- Product character of three representations. -/
def chi3 (i j k : Fin 5) (c : Fin 5) : QSqrt5 := A5_chi i c * A5_chi j c * A5_chi k c

/-- dim Inv(ρ_i ⊗ ρ_j ⊗ ρ_k) = ⟨χ_i χ_j χ_k, 1⟩. -/
def dimInv3 (i j k : Fin 5) : QSqrt5 := charIP (chi3 i j k) (fun _ => ⟨1, 0⟩)

-- ============================================================
-- M01–M03: Singlet uniqueness
-- ============================================================

theorem M01_singlet_rho3_rho3_rho5 :
    dimInv3 1 1 4 = ⟨1, 0⟩ := by native_decide

theorem M02_singlet_rho3_rho3p_rho5 :
    dimInv3 1 2 4 = ⟨1, 0⟩ := by native_decide

theorem M03_singlet_rho3_rho3p_rho4 :
    dimInv3 1 2 3 = ⟨1, 0⟩ := by native_decide

-- ============================================================
-- M28: Frobenius-Schur indicators
-- ============================================================

/-- FS indicator: (1/60) Σ_C |C| χ(C²). -/
def fsIndicator (rep : Fin 5) : QSqrt5 :=
  let weighted := fun c => smulQ (A5_classSize c / 60) (A5_chi rep (A5_sq c))
  weighted 0 + weighted 1 + weighted 2 + weighted 3 + weighted 4

theorem M28_all_real :
    fsIndicator 0 = ⟨1, 0⟩ ∧
    fsIndicator 1 = ⟨1, 0⟩ ∧
    fsIndicator 2 = ⟨1, 0⟩ ∧
    fsIndicator 3 = ⟨1, 0⟩ ∧
    fsIndicator 4 = ⟨1, 0⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

-- ============================================================
-- M11: dim Inv(Sym³(ρ₅)) = 2
-- ============================================================

/-- Character of Sym³(V):
    χ_{S³}(g) = (χ(g)³ + 3χ(g)χ(g²) + 2χ(g³)) / 6 -/
def chiSym3 (rep : Fin 5) (c : Fin 5) : QSqrt5 :=
  let chi_g := A5_chi rep c
  let chi_g2 := A5_chi rep (A5_sq c)
  let chi_g3 := A5_chi rep (A5_cube c)
  smulQ (1/6) (chi_g * chi_g * chi_g + smulQ 3 (chi_g * chi_g2) + smulQ 2 chi_g3)

/-- Multiplicity of trivial in Sym³(ρ₅). -/
def dimInvSym3 (rep : Fin 5) : QSqrt5 :=
  charIP (chiSym3 rep) (fun _ => ⟨1, 0⟩)

theorem M11_cubic_invariants_rho5 :
    dimInvSym3 4 = ⟨2, 0⟩ := by native_decide

-- ============================================================
-- Supporting: Galois action on characters
-- ============================================================

/-- σ(χ_ρ₃(C)) = χ_ρ₃'(C) for all C. -/
theorem galois_chi_rho3 :
    ∀ c : Fin 5, galois (A5_chi 1 c) = A5_chi 2 c := by
  intro c; fin_cases c <;> native_decide

/-- σ fixes ρ₄ characters. -/
theorem galois_chi_rho4 :
    ∀ c : Fin 5, galois (A5_chi 3 c) = A5_chi 3 c := by
  intro c; fin_cases c <;> simp [A5_chi, galois]

/-- σ fixes ρ₅ characters. -/
theorem galois_chi_rho5 :
    ∀ c : Fin 5, galois (A5_chi 4 c) = A5_chi 4 c := by
  intro c; fin_cases c <;> simp [A5_chi, galois]

/-- ρ₃ ⊗ ρ₃' has no trivial component (no invariant bilinear). -/
theorem no_singlet_rho3_rho3p :
    charIP (fun c => A5_chi 1 c * A5_chi 2 c) (fun _ => ⟨1, 0⟩) = ⟨0, 0⟩ := by
  native_decide

/-- dim Inv(ρ₃³) = 1 (Levi-Civita singlet, supports M40). -/
theorem singlet_rho3_cubed :
    dimInv3 1 1 1 = ⟨1, 0⟩ := by native_decide
