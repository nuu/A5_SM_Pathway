import A5_SM_Pathway.BornQuadratic.Core
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# BornQuadraticReduction.lean

This file isolates the **reduction lemmas** behind the Born-quadratic program.

The purpose is to make explicit that the global theorem

`radial + orthAdd + continuous  =>  I(v) = c * sqNorm v`

breaks into two logically separate steps:

1. a one-variable statement about the profile `φ(t) = I(√t • e₀)` on `t ≥ 0`,
2. a purely radial transport from the axis back to arbitrary vectors.

This separation is useful for Lean formalization because it localizes the hard
points:

* geometry: `phi_add_of_radial_orthAdd`,
* analysis: `linear_of_continuous_additive_on_nonneg`,
* exponent extraction: `eq_two_of_two_rpow_eq_four`.
-/

noncomputable section
open Real

namespace MDL
namespace BornQuadratic

variable {V : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace OrthonormalPair

variable (hp : OrthonormalPair (V := V))

/--
If the one-variable profile `φ` is already known to be linear on `ℝ≥0`, then
`I` is globally quadratic.

This is the cleanest reduction lemma in the development: the only real input is
radiality, which transports the axis formula to arbitrary vectors.
-/
theorem quadratic_of_phi_linear
    (I : V → ℝ)
    (hrad : Radial I)
    {c : ℝ}
    (hc : ∀ t, 0 ≤ t → hp.phi I t = c * t) :
    ∀ v, I v = c * sqNorm v := by
  intro v
  have hvnn : 0 ≤ sqNorm v := sqNorm_nonneg v
  have haxis : I v = hp.phi I (sqNorm v) := by
    unfold OrthonormalPair.phi
    apply hrad
    rw [hp.sqNorm_smul_e₀ hvnn]
  calc
    I v = hp.phi I (sqNorm v) := haxis
    _ = c * sqNorm v := hc _ hvnn

/--
Packaging version of `quadratic_of_phi_linear`.
-/
theorem exists_mul_sqNorm_of_phi_linear
    (I : V → ℝ)
    (hrad : Radial I)
    (hlin : ∃ c : ℝ, ∀ t, 0 ≤ t → hp.phi I t = c * t) :
    ∃ c : ℝ, ∀ v, I v = c * sqNorm v := by
  rcases hlin with ⟨c, hc⟩
  exact ⟨c, hp.quadratic_of_phi_linear I hrad hc⟩

/--
A direct reduction of the main theorem to the geometric lemma `phi_add` and the
analytic lemma `linear_of_continuous_additive_on_nonneg`.

This theorem is intentionally almost identical to
`exists_mul_sqNorm_of_pair`, but phrased to emphasize the proof pipeline.
-/
theorem exists_mul_sqNorm_of_pair_via_phi
    (hp' : OrthonormalPair (V := V))
    (I : V → ℝ)
    (hcont : Continuous I)
    (hrad : Radial I)
    (horth : OrthAdd I) :
    ∃ c : ℝ, ∀ v, I v = c * sqNorm v := by
  let φ : ℝ → ℝ := hp'.phi I
  have hφadd : ∀ s t, 0 ≤ s → 0 ≤ t → φ (s + t) = φ s + φ t := by
    intro s t hs ht
    simpa [φ] using hp'.phi_add_of_radial_orthAdd I hrad horth hs ht
  have hφcont : Continuous φ := by
    show Continuous (fun t => I ((Real.sqrt t) • hp'.e₀))
    exact hcont.comp (Real.continuous_sqrt.smul continuous_const)
  rcases linear_of_continuous_additive_on_nonneg φ hφcont hφadd with ⟨c, hc⟩
  exact hp'.exists_mul_sqNorm_of_phi_linear I hrad ⟨c, hc⟩

end OrthonormalPair

/--
A tiny algebraic lemma isolating the nontrivial final step in the exponent
argument.

The geometric part yields `(2:ℝ)^α = 4`; the only remaining issue is to deduce
`α = 2` from this identity.
-/
private lemma eq_two_of_two_rpow_eq_four_local {α : ℝ} (h : (2 : ℝ)^α = 4) : α = 2 := by
  have h' : (2 : ℝ) ^ α = (2 : ℝ) ^ (2 : ℝ) := by rw [h]; norm_num
  have h_pos : (0 : ℝ) < 2 := by norm_num
  have h_log_ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have : α * Real.log 2 = 2 * Real.log 2 := by
    calc α * Real.log 2 = Real.log ((2 : ℝ) ^ α) := (Real.log_rpow h_pos α).symm
      _ = Real.log ((2 : ℝ) ^ (2 : ℝ)) := by rw [h']
      _ = 2 * Real.log 2 := Real.log_rpow h_pos 2
  exact mul_right_cancel₀ h_log_ne this

/--
Pure algebraic reduction: once `I` is known to be quadratic, homogeneity forces
exponent `2`.

This theorem is independent of the geometric proof of quadraticity.
-/
theorem exponent_two_of_quadratic
    (I : V → ℝ)
    (α : ℝ)
    (hquad : ∃ c : ℝ, ∀ v, I v = c * sqNorm v)
    (hhom : Homogeneous I α)
    (hnontriv : ∃ v, I v ≠ 0) :
    α = 2 := by
  rcases hquad with ⟨c, hc⟩
  rcases hnontriv with ⟨v, hv⟩
  have hcv : c * sqNorm v ≠ 0 := by
    simpa [hc v] using hv
  have hsqv : sqNorm v ≠ 0 := by
    intro hs
    apply hcv
    simp [hs]
  have hc_ne : c ≠ 0 := by
    intro hc0
    apply hcv
    simp [hc0]
  have h2hom : I ((2 : ℝ) • v) = (2 : ℝ)^α * I v := hhom 2 (by positivity) v
  have h2quad : I ((2 : ℝ) • v) = c * sqNorm ((2 : ℝ) • v) := hc ((2 : ℝ) • v)
  have hsqs : sqNorm ((2 : ℝ) • v) = 4 * sqNorm v := by
    unfold sqNorm
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    ring
  have hpow : (2 : ℝ)^α = 4 := by
    -- Rewrite both sides using the quadratic formula and cancel `c * sqNorm v`.
    have hmain : c * (4 * sqNorm v) = (2 : ℝ)^α * (c * sqNorm v) := by
      calc
        c * (4 * sqNorm v)
            = c * sqNorm ((2 : ℝ) • v) := by rw [hsqs]
        _ = I ((2 : ℝ) • v) := by symm; exact h2quad
        _ = (2 : ℝ)^α * I v := h2hom
        _ = (2 : ℝ)^α * (c * sqNorm v) := by rw [hc v]
    have hmain' : 4 * (c * sqNorm v) = (2 : ℝ)^α * (c * sqNorm v) := by linarith
    exact (mul_right_cancel₀ hcv hmain').symm
  exact eq_two_of_two_rpow_eq_four_local hpow

/--
Final reduction theorem.

To prove exponent `2`, it is enough to prove the quadratic form theorem first;
all exponent information is then a purely algebraic corollary.
-/
theorem exponent_two_of_pair_via_quadratic
    (I : V → ℝ)
    (hp : OrthonormalPair (V := V))
    (α : ℝ)
    (hcont : Continuous I)
    (hrad : Radial I)
    (horth : OrthAdd I)
    (hhom : Homogeneous I α)
    (hnontriv : ∃ v, I v ≠ 0) :
    α = 2 := by
  apply exponent_two_of_quadratic (I := I)
    (hquad := hp.exists_mul_sqNorm_of_pair_via_phi I hcont hrad horth)
    (hhom := hhom)
    (hnontriv := hnontriv)

end BornQuadratic
end MDL
