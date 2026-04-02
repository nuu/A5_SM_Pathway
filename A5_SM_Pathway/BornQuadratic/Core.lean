import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Order.DenselyOrdered

open scoped InnerProductSpace

/-!
# BornQuadraticCore_v2.lean

A compile-oriented reorganization of the Born-quadratic core.

The main change relative to the earlier skeleton is that we use

`sqNorm v := ‖v‖ * ‖v‖`

instead of `‖v‖ ^ (2 : ℕ)`.

This is mathematically equivalent, but in practice it tends to reduce friction
in geometric rewrites such as

* `sqNorm ((Real.sqrt t) • e) = t`,
* `sqNorm (u + v) = sqNorm u + sqNorm v` when `u ⟂ v`,
* `sqNorm (r • v) = r*r * sqNorm v` for `0 ≤ r`.

The actual difficult analytic step remains isolated in the placeholder lemma
`linear_of_continuous_additive_on_nonneg`.
-/

noncomputable section
open Real

namespace MDL
namespace BornQuadratic

variable {V : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Squared norm, written multiplicatively to simplify rewrites. -/
def sqNorm (v : V) : ℝ := ‖v‖ * ‖v‖

omit [InnerProductSpace ℝ V] in
lemma sqNorm_nonneg (v : V) : 0 ≤ sqNorm v := by
  unfold sqNorm
  positivity

/-- Radiality with respect to `sqNorm`. -/
def Radial (I : V → ℝ) : Prop :=
  ∀ u v, sqNorm u = sqNorm v → I u = I v

/-- Orthogonal additivity of the intensity. -/
def OrthAdd (I : V → ℝ) : Prop :=
  ∀ u v, ⟪u, v⟫_ℝ = 0 → I (u + v) = I u + I v

/-- Homogeneity of degree `α` for nonnegative real scalars. -/
def Homogeneous (I : V → ℝ) (α : ℝ) : Prop :=
  ∀ (r : ℝ), 0 ≤ r → ∀ v, I (r • v) = r^α * I v

/-- An explicit orthonormal pair. -/
structure OrthonormalPair where
  e₀ : V
  e₁ : V
  norm_e₀ : ‖e₀‖ = 1
  norm_e₁ : ‖e₁‖ = 1
  orth : ⟪e₀, e₁⟫_ℝ = 0

namespace OrthonormalPair

variable (hp : OrthonormalPair (V := V))

/-- The 1-variable profile of `I` along `e₀`. -/
def phi (I : V → ℝ) (t : ℝ) : ℝ :=
  I ((Real.sqrt t) • hp.e₀)

lemma sqNorm_smul_e₀ {t : ℝ} (ht : 0 ≤ t) :
    sqNorm ((Real.sqrt t) • hp.e₀) = t := by
  unfold sqNorm
  rw [norm_smul, hp.norm_e₀, mul_one]
  have hs : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
  rw [Real.norm_of_nonneg hs, mul_self_sqrt ht]

lemma sqNorm_smul_e₁ {t : ℝ} (ht : 0 ≤ t) :
    sqNorm ((Real.sqrt t) • hp.e₁) = t := by
  unfold sqNorm
  rw [norm_smul, hp.norm_e₁, mul_one]
  have hs : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
  rw [Real.norm_of_nonneg hs, mul_self_sqrt ht]

lemma orth_scaled (s t : ℝ) :
    ⟪(Real.sqrt s) • hp.e₀, (Real.sqrt t) • hp.e₁⟫_ℝ = 0 := by
  rw [inner_smul_left, inner_smul_right]
  simp [hp.orth]

/--
Pythagoras in the specific orthonormal-pair situation.

This is the geometric lemma that should be filled first once the exact mathlib
identity for `‖u+v‖^2` under orthogonality is settled.
-/
lemma sqNorm_sum_scaled {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    sqNorm ((Real.sqrt s) • hp.e₀ + (Real.sqrt t) • hp.e₁) = s + t := by
  set u := (Real.sqrt s) • hp.e₀
  set v := (Real.sqrt t) • hp.e₁
  have huv : ⟪u, v⟫_ℝ = 0 := hp.orth_scaled s t
  have hpyth : ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
    have := @norm_add_sq_real V _ _ u v; rw [huv, mul_zero, add_zero] at this; exact this
  unfold sqNorm
  have hsq : ‖u + v‖ * ‖u + v‖ = ‖u‖ * ‖u‖ + ‖v‖ * ‖v‖ := by
    have h1 : ‖u + v‖ ^ 2 = ‖u + v‖ * ‖u + v‖ := by ring
    have h2 : ‖u‖ ^ 2 = ‖u‖ * ‖u‖ := by ring
    have h3 : ‖v‖ ^ 2 = ‖v‖ * ‖v‖ := by ring
    linarith
  rw [hsq]
  have h_u : ‖u‖ * ‖u‖ = s := hp.sqNorm_smul_e₀ hs
  have h_v : ‖v‖ * ‖v‖ = t := hp.sqNorm_smul_e₁ ht
  linarith

lemma sqNorm_axis_eq_sum {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    sqNorm ((Real.sqrt (s + t)) • hp.e₀)
      = sqNorm ((Real.sqrt s) • hp.e₀ + (Real.sqrt t) • hp.e₁) := by
  rw [hp.sqNorm_smul_e₀ (add_nonneg hs ht), hp.sqNorm_sum_scaled hs ht]

lemma radial_rewrite_e₁
    (I : V → ℝ)
    (hrad : Radial I)
    {t : ℝ} (ht : 0 ≤ t) :
    I ((Real.sqrt t) • hp.e₁) = I ((Real.sqrt t) • hp.e₀) := by
  apply hrad
  rw [hp.sqNorm_smul_e₁ ht, hp.sqNorm_smul_e₀ ht]

lemma phi_add_of_radial_orthAdd
    (I : V → ℝ)
    (hrad : Radial I)
    (horth : OrthAdd I)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    hp.phi I (s + t) = hp.phi I s + hp.phi I t := by
  let u : V := (Real.sqrt s) • hp.e₀
  let v : V := (Real.sqrt t) • hp.e₁
  have huv : ⟪u, v⟫_ℝ = 0 := by
    simpa [u, v] using hp.orth_scaled s t
  have hsum : I (u + v) = I u + I v := horth u v huv
  have hrad_sum : I ((Real.sqrt (s + t)) • hp.e₀) = I (u + v) := by
    apply hrad
    simpa [u, v] using hp.sqNorm_axis_eq_sum hs ht
  have hrad_right : I v = I ((Real.sqrt t) • hp.e₀) := by
    simpa [v] using hp.radial_rewrite_e₁ I hrad ht
  calc
    hp.phi I (s + t)
        = I ((Real.sqrt (s + t)) • hp.e₀) := rfl
    _ = I (u + v) := hrad_sum
    _ = I u + I v := hsum
    _ = hp.phi I s + hp.phi I t := by
          simp [OrthonormalPair.phi, u, v, hrad_right]

end OrthonormalPair

/--
Analytic boundary lemma.

A continuous function additive on the nonnegative reals is linear there.
This is deliberately isolated as the only genuinely analytic input.
-/
lemma linear_of_continuous_additive_on_nonneg
    (φ : ℝ → ℝ)
    (hcont : Continuous φ)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → φ (s + t) = φ s + φ t) :
    ∃ c : ℝ, ∀ t, 0 ≤ t → φ t = c * t := by
  refine ⟨φ 1, ?_⟩
  /- Proof: φ(0)=0 → natural scaling → rational scaling → density + continuity -/
  -- Step 0: φ(0) = 0
  have h0 : φ 0 = 0 := by have := hadd 0 0 le_rfl le_rfl; rw [zero_add] at this; linarith
  -- Step 1: φ(n * t) = n * φ(t) for n : ℕ, t ≥ 0
  have hscale : ∀ (n : ℕ) (t : ℝ), 0 ≤ t → φ (↑n * t) = ↑n * φ t := by
    intro n
    induction n with
    | zero => intro t _; simp [h0]
    | succ n ih =>
      intro t ht
      have hnt : 0 ≤ (↑n : ℝ) * t := mul_nonneg (Nat.cast_nonneg n) ht
      have h := hadd (↑n * t) t hnt ht
      rw [ih t ht] at h
      convert h using 1 <;> push_cast <;> ring
  -- Step 2: φ(n) = n * φ(1) for n : ℕ
  have hnat : ∀ n : ℕ, φ ↑n = ↑n * φ 1 := by
    intro n; have := hscale n 1 zero_le_one; simp at this; linarith
  -- Step 3: φ(↑m / ↑n) = φ 1 * (↑m / ↑n) for m n : ℕ, n > 0
  have hdiv : ∀ (m n : ℕ), 0 < n → φ (↑m / ↑n) = φ 1 * (↑m / ↑n) := by
    intro m n hn
    have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
    have hn_ne : (↑n : ℝ) ≠ 0 := ne_of_gt hn_pos
    have hmn_nn : 0 ≤ (↑m / ↑n : ℝ) := div_nonneg (Nat.cast_nonneg m) hn_pos.le
    -- n * φ(m/n) = φ(n * (m/n)) = φ(m) = m * φ(1)
    have h1 := hscale n (↑m / ↑n) hmn_nn
    rw [show (↑n : ℝ) * (↑m / ↑n) = ↑m from by field_simp, hnat m] at h1
    -- h1 : ↑m * φ 1 = ↑n * φ (↑m / ↑n)
    have : φ (↑m / ↑n) = ↑m / ↑n * φ 1 := by
      rw [div_mul_eq_mul_div, eq_div_iff hn_ne]; linarith
    rw [this]; ring
  -- Step 4: φ(q) = φ 1 * q for q : ℚ, q ≥ 0
  have hrat : ∀ q : ℚ, 0 ≤ (q : ℝ) → φ ↑q = φ 1 * ↑q := by
    intro q hq
    have hnum_nn : 0 ≤ q.num := Rat.num_nonneg.mpr (by exact_mod_cast hq)
    have hq_eq : (q : ℝ) = ↑q.num.toNat / ↑q.den := by
      have h1 : (q.num.toNat : ℤ) = q.num := Int.toNat_of_nonneg hnum_nn
      rw [Rat.cast_def]
      congr 1
      exact_mod_cast h1.symm
    rw [hq_eq]
    exact hdiv q.num.toNat q.den q.pos
  -- Step 5: {x | φ x = φ 1 * x} is closed; it contains all nonneg rationals;
  --         every nonneg real is in the closure of nonneg rationals; done.
  have hcl : IsClosed {x : ℝ | φ x = φ 1 * x} :=
    isClosed_eq hcont (continuous_const.mul continuous_id')
  intro t ht
  -- t ∈ closure of nonneg rationals, and nonneg rationals ⊆ closed equalizer
  have hmem : t ∈ closure {x : ℝ | ∃ q : ℚ, 0 ≤ (q : ℝ) ∧ x = ↑q} := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    rcases exists_rat_btwn (show max 0 (t - ε / 2) < t + ε / 2 by
      apply max_lt <;> linarith) with ⟨q, hq_lo, hq_hi⟩
    refine ⟨↑q, ⟨q, le_of_lt (lt_of_le_of_lt (le_max_left 0 _) hq_lo), rfl⟩, ?_⟩
    rw [Real.dist_eq, abs_lt]
    have hq_lo' : t - ε / 2 < ↑q := lt_of_le_of_lt (le_max_right 0 _) hq_lo
    exact ⟨by linarith, by linarith⟩
  exact closure_minimal (fun x hx => by obtain ⟨q, hq_nn, hxq⟩ := hx; exact hxq ▸ hrat q hq_nn) hcl hmem

/--
Main geometric theorem from an explicit orthonormal pair.
-/
theorem exists_mul_sqNorm_of_pair
    (I : V → ℝ)
    (hp : OrthonormalPair (V := V))
    (hcont : Continuous I)
    (hrad : Radial I)
    (horth : OrthAdd I) :
    ∃ c : ℝ, ∀ v, I v = c * sqNorm v := by
  let φ : ℝ → ℝ := hp.phi I
  have hφadd : ∀ s t, 0 ≤ s → 0 ≤ t → φ (s + t) = φ s + φ t := by
    intro s t hs ht
    simpa [φ] using hp.phi_add_of_radial_orthAdd I hrad horth hs ht
  have hφcont : Continuous φ := by
    show Continuous (fun t => I ((Real.sqrt t) • hp.e₀))
    exact hcont.comp (Real.continuous_sqrt.smul continuous_const)
  rcases linear_of_continuous_additive_on_nonneg φ hφcont hφadd with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro v
  have hvnn : 0 ≤ sqNorm v := sqNorm_nonneg v
  have hrad_axis : I v = φ (sqNorm v) := by
    unfold φ OrthonormalPair.phi
    apply hrad
    rw [hp.sqNorm_smul_e₀ hvnn]
  calc
    I v = φ (sqNorm v) := hrad_axis
    _ = c * sqNorm v := hc _ hvnn

/--
Pure algebraic corollary: once the intensity is quadratic, the homogeneity
exponent is forced to be `2`.
-/
theorem exponent_two_of_homogeneous_of_pair
    (I : V → ℝ)
    (hp : OrthonormalPair (V := V))
    (α : ℝ)
    (hcont : Continuous I)
    (hrad : Radial I)
    (horth : OrthAdd I)
    (hhom : Homogeneous I α)
    (hnontriv : ∃ v, I v ≠ 0) :
    α = 2 := by
  rcases exists_mul_sqNorm_of_pair I hp hcont hrad horth with ⟨c, hc⟩
  rcases hnontriv with ⟨v, hv⟩
  have hcv : c * sqNorm v ≠ 0 := by simpa [hc v] using hv
  have h2 : I ((2 : ℝ) • v) = (2 : ℝ)^α * I v := hhom 2 (by positivity) v
  have h2' : I ((2 : ℝ) • v) = c * sqNorm ((2 : ℝ) • v) := hc ((2 : ℝ) • v)
  have hsqs : sqNorm ((2 : ℝ) • v) = 4 * sqNorm v := by
    unfold sqNorm
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    ring
  -- From the two expressions for I(2•v):
  have h_left : I ((2 : ℝ) • v) = 4 * (c * sqNorm v) := by rw [h2', hsqs]; ring
  have h_right : I ((2 : ℝ) • v) = (2 : ℝ) ^ α * (c * sqNorm v) := by rw [h2, hc v]
  have h_eq : (2 : ℝ) ^ α * (c * sqNorm v) = 4 * (c * sqNorm v) := by linarith
  have h_pow : (2 : ℝ) ^ α = 4 := mul_right_cancel₀ hcv h_eq
  -- 2^α = 4 = 2^2 → α = 2 by injectivity of x ↦ 2^x
  have h_final : (2 : ℝ) ^ α = (2 : ℝ) ^ (2 : ℝ) := by rw [h_pow]; norm_num
  have h_pos : (0 : ℝ) < 2 := by norm_num
  have h_log_ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have : α * Real.log 2 = 2 * Real.log 2 := by
    calc α * Real.log 2 = Real.log ((2 : ℝ) ^ α) := (Real.log_rpow h_pos α).symm
      _ = Real.log ((2 : ℝ) ^ (2 : ℝ)) := by rw [h_final]
      _ = 2 * Real.log 2 := Real.log_rpow h_pos 2
  exact mul_right_cancel₀ h_log_ne this

end BornQuadratic
end MDL
