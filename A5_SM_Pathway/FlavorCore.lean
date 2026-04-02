/-
  A5_SM_Pathway/FlavorCore.lean  (v2)
  
  M22: det(zeroBg) = 0
  M24: tr(S³) = 3·det(S) for traceless 3×3
  M24': tr(S⁴) = (tr(S²))²/2 — via Cayley-Hamilton, NO SORRY
  M41-support: det(antisymmetric 3×3) = 0
  
  Strategy for M24':
    Step 1: Prove Cayley-Hamilton for traceless 3×3:
            S³ = (tr(S²)/2)·S + det(S)·I
    Step 2: Multiply by S: S⁴ = (tr(S²)/2)·S² + det(S)·S
    Step 3: Take trace: tr(S⁴) = (tr(S²)/2)·tr(S²) + det(S)·tr(S)
                                = (tr(S²))²/2 + 0
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

open Matrix

variable {R : Type*} [CommRing R]

-- ============================================================
-- Basic definitions
-- ============================================================

def zeroBgMatrix (p q : R) : Matrix (Fin 3) (Fin 3) R :=
  !![0, p, q; p, 0, 0; q, 0, 0]

def tracelessMat (a b p q f : R) : Matrix (Fin 3) (Fin 3) R :=
  !![a, p, q; p, b, f; q, f, -(a + b)]

-- ============================================================
-- M22: det(zeroBg) = 0
-- ============================================================

theorem M22_det_zeroBg (p q : R) : det (zeroBgMatrix p q) = 0 := by
  simp [zeroBgMatrix, det_fin_three, mul_comm]

-- ============================================================
-- M24: tr(S³) = 3·det(S) for traceless S
-- ============================================================

theorem M24_trCube_eq_3det (a b p q f : R) :
    trace (tracelessMat a b p q f * tracelessMat a b p q f * tracelessMat a b p q f)
    = 3 * det (tracelessMat a b p q f) := by
  simp [tracelessMat, trace, det_fin_three,
        Fin.sum_univ_three]; ring

-- ============================================================
-- Cayley-Hamilton for traceless 3×3
-- ============================================================

/-- The key identity: 2·S³ = tr(S²)·S + 2·det(S)·1
    for a traceless 3×3 matrix.
    This is the Cayley-Hamilton theorem specialized to tr(S)=0,
    multiplied through by 2 to avoid division in CommRing. -/
theorem cayleyHamilton_traceless (a b p q f : R) :
    let S := tracelessMat a b p q f
    let trS2 := trace (S * S)
    S * S * S + S * S * S = trS2 • S + (2 * det S) • (1 : Matrix (Fin 3) (Fin 3) R) := by
  ext i j
  simp [tracelessMat, trace, det_fin_three,
        Fin.sum_univ_three, Matrix.smul_apply, Matrix.one_apply, Matrix.add_apply]
  fin_cases i <;> fin_cases j <;> simp <;> ring

-- ============================================================
-- M24': tr(S⁴) = (tr(S²))²/2  — NO SORRY
-- ============================================================

/-- From Cayley-Hamilton:
    S⁴ = S·S³ = S·[(tr(S²)/2)·S + det(S)·I]
       = (tr(S²)/2)·S² + det(S)·S
    tr(S⁴) = (tr(S²)/2)·tr(S²) + det(S)·tr(S)
           = (tr(S²))²/2 + 0
    Stated as 2·tr(S⁴) = tr(S²)² to avoid division in CommRing. -/
theorem M24'_trQuart_eq_half_trSq_sq (a b p q f : R) :
    let S := tracelessMat a b p q f
    2 * trace (S * S * S * S) = trace (S * S) * trace (S * S) := by
  simp [tracelessMat, trace, Fin.sum_univ_three]; ring

-- ============================================================
-- Antisymmetric det = 0 (supports M41)
-- ============================================================

theorem det_antisymm_three (a b c : R) :
    det (!![0, a, b; -a, 0, c; -b, -c, 0] : Matrix (Fin 3) (Fin 3) R) = 0 := by
  simp [det_fin_three]; ring

-- ============================================================
-- Trace of traceless matrix = 0
-- ============================================================

theorem trace_traceless (a b p q f : R) :
    trace (tracelessMat a b p q f) = 0 := by
  simp [tracelessMat, trace, Fin.sum_univ_three, add_neg_cancel]
