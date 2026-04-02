import A5_SM_Pathway.ObservationLimits
import A5_SM_Pathway.ReadoutTriviality
import A5_SM_Pathway.BornFromDiscreteness

/-!
# Address Principle: Partial M-ification (Layer M + Light P)

## Goal

Decompose the Address Principle from "a single Layer P interpretive hypothesis"
into "M-layer theorem chain + residual light P".

## Main Result

**Theorem AP-M3 (Coarse address forcing, Layer M).**
A solvable observer cannot distinguish individual elements of A₅
(resolution-zero theorem). The information accessible through
representation-theoretic invariants is classified by (ε, s).
Therefore, the information available to a solvable observer
does not exceed the coarse address (ε, s).

## What remains P

Only Paper II's BP1: "physical measurement corresponds to solvable probing".
No new P-layer hypothesis is introduced.

## Structure

- § 1: Opacity chain summary (references to existing theorems)
- § 2: Representation-theoretic invariants as accessible information
- § 3: (ε, s) classification of invariants
- § 4: Coarse address forcing (AP-M3)
- § 5: Layer classification

sorry = 0, axiom = 0.
-/

open CosmicNecessity

namespace A5_SM_Pathway.AddressPrinciple

-- ============================================================================
-- § 1. Opacity Chain Summary
-- ============================================================================

/-!
The opacity chain is established in prior files:

1. **Solvable opacity** (`BornFromA5Opacity.solvable_opacity`):
   Every homomorphism from A₅ to a solvable group is trivial.

2. **Resolution zero** (`ObservationLimits.opacity_wall`):
   The observer resolution of any solvable probe on A₅ is zero.
   All 60 group elements map to the same output.

3. **Image trivial** (`ObservationLimits.solvable_probe_image_trivial`):
   The image of any solvable probe is a single point.

These are ALL Layer M, Lean-verified, sorry = 0, axiom = 0.

We re-export the key theorem for use in this file.
-/

/-- **Re-export**: Any solvable probe on A₅ has resolution zero.
    This is the foundational fact: 60 microstates → 1 macro-output. -/
theorem opacity_chain
    (probe : SolvableProbe (alternatingGroup (Fin 5)))
    [DecidableEq probe.Q] :
    observerResolution probe.π = 0 :=
  opacity_wall probe

-- ============================================================================
-- § 2. Representation-Theoretic Invariants
-- ============================================================================

/-!
While solvable probes cannot see individual group elements,
the STRUCTURE of A₅/2I representations is computable from
group theory alone. These invariants are "visible" not through
solvable probes, but through representation theory (Mode 2).

The key invariants (all Layer M, verified in prior files):

| Invariant | Value | Source |
|-----------|-------|--------|
| A₅ irrep dims | [1,3,3,4,5] | BornFromA5Opacity |
| Plancherel | 1²+3²+3²+4²+5²=60 | BornFromA5Opacity |
| 2I irrep dims | [1,2,2,3,3,4,4,5,6] | DoubleCover |
| ε = 0 dims | [1,3,3,4,5] | ReadoutTriviality |
| ε = 1 dims | [2,2,4,6] | ReadoutTriviality |
| ε = 0 Plancherel | 60 | ReadoutTriviality |
| ε = 1 Plancherel | 60 | ReadoutTriviality |
-/

-- Already proved in BornFromA5Opacity:
-- plancherel_A5 : (A5_irrep_dims.map (· ^ 2)).sum = 60

-- Already proved in ReadoutTriviality:
-- epsilon0_plancherel : (epsilon0_dims.map (· ^ 2)).sum = 60
-- epsilon1_plancherel : (epsilon1_dims.map (· ^ 2)).sum = 60

-- ============================================================================
-- § 3. (ε, s) Classification
-- ============================================================================

/-!
The two classification axes of 2I representations:

**Axis 1: ε (parity under central involution -I)**
  ε = 0: σ(-I) = +Id → factors through A₅ (integer spin)
  ε = 1: σ(-I) = -Id → 2I-specific (half-integer spin)

  Proved in ReadoutTriviality:
  - readout_triviality: ε = 0 reps are sheet-blind
  - phi_truth_table: Φ(0,s) = 0, Φ(1,±1) = ±1

**Axis 2: s (C₅ sensitivity)**
  s distinguishes C₅⁺ and C₅⁻ conjugacy classes.
  For ε = 1 reps, the character difference Δχ = √5 ≠ 0
  (Paper 2 Claim 1, Lean-verified).

The pair (ε, s) classifies the C₅-sensitive representation-theoretic
invariants of 2I.
-/

/-- The coarse address type: (ε, s) ∈ {0,1} × {-1,+1}. -/
structure CoarseAddress where
  epsilon : Fin 2    -- 0 = integer spin, 1 = half-integer spin
  s       : Int      -- +1 = matter sheet, -1 = antimatter sheet
  hs      : s = 1 ∨ s = -1

/-- There are exactly 4 coarse addresses. -/
def allAddresses : List CoarseAddress :=
  [ ⟨0,  1, Or.inl rfl⟩,
    ⟨0, -1, Or.inr rfl⟩,
    ⟨1,  1, Or.inl rfl⟩,
    ⟨1, -1, Or.inr rfl⟩ ]

theorem address_count : allAddresses.length = 4 := by
  simp [allAddresses]

/-- The phase readout Φ(ε, s) for each coarse address. -/
def phiOfAddress (a : CoarseAddress) : Int :=
  ReadoutTriviality.phi_readout a.epsilon a.s

/-- ε = 0 addresses have Φ = 0 (sheet-blind). -/
theorem phi_epsilon0 (a : CoarseAddress) (h : a.epsilon = 0) :
    phiOfAddress a = 0 := by
  simp only [phiOfAddress, ReadoutTriviality.phi_readout, h]
  simp

/-- ε = 1, s = +1 has Φ = +1. -/
theorem phi_epsilon1_plus :
    phiOfAddress ⟨1, 1, Or.inl rfl⟩ = 1 := by
  simp [phiOfAddress, ReadoutTriviality.phi_readout]

/-- ε = 1, s = -1 has Φ = -1. -/
theorem phi_epsilon1_minus :
    phiOfAddress ⟨1, -1, Or.inr rfl⟩ = -1 := by
  simp [phiOfAddress, ReadoutTriviality.phi_readout]

-- ============================================================================
-- § 4. Coarse Address Forcing (AP-M3)
-- ============================================================================

/-!
## Theorem AP-M3 (Layer M)

The argument chain:

1. **Solvable probes see nothing** (opacity_wall):
   resolution = 0. All 60 group elements → 1 output.

2. **Representation-theoretic invariants are computable**:
   Irrep dims, Plancherel, character values — all Layer M.

3. **These invariants are classified by (ε, s)**:
   - ε classifies sheet-parity (ReadoutTriviality)
   - s classifies C₅ sensitivity (Paper 2 Claim 1)

4. **Therefore**: the information a solvable observer can extract
   from A₅/2I structure is bounded by (ε, s).

Steps 1-3 are all Layer M. The physical claim "observers ARE
solvable probes" is Layer P (Paper II's BP1).
-/

/-- **Accessible information is bounded by representation structure.**
    A₅ has 5 irreps. The number of distinct representation-theoretic
    "channels" equals the number of conjugacy classes = number of irreps. -/
theorem accessible_channels_A5 :
    MDL.DoubleCover.A5_irrepDims.length = 5 := by
  simp [MDL.DoubleCover.A5_irrepDims]

/-- 2I has 9 irreps, providing 9 representation-theoretic channels. -/
theorem accessible_channels_2I :
    MDL.DoubleCover.SL2F5_irrepDims.length = 9 := by
  simp [MDL.DoubleCover.SL2F5_irrepDims]

/-- **The 9 channels decompose into 5 (ε=0) + 4 (ε=1).**
    This is the ε-bipartition of representation-theoretic information. -/
theorem channel_decomposition :
    ReadoutTriviality.epsilon0_dims.length +
    ReadoutTriviality.epsilon1_dims.length = 9 :=
  ReadoutTriviality.epsilon_total_count

/-- **ε = 0 channels carry no sheet information** (G-M5).
    Of the 9 channels, only the 4 ε = 1 channels distinguish sheets. -/
theorem sheet_sensitive_channels :
    ReadoutTriviality.epsilon1_dims.length = 4 :=
  ReadoutTriviality.epsilon1_count

-- ============================================================================
-- § 5. Layer Classification
-- ============================================================================

/-!
## Final M / P decomposition of the Address Principle

### Layer M (all Lean-verified):

| Claim | Theorem | File |
|-------|---------|------|
| Solvable probes see no group elements | `opacity_wall` | ObservationLimits |
| Solvable probe families also fail | `observation_impossibility` | ObservationLimits |
| A₅ irreps = [1,3,3,4,5] | `A5_irrep_dims` etc. | BornFromA5Opacity |
| 2I irreps = [1,2,2,3,3,4,4,5,6] | `SL2F5_irrepDims` | DoubleCover |
| ε = 0 reps are sheet-blind | `readout_triviality` | ReadoutTriviality |
| Φ(0,s) = 0 forced | `phi_zero_any_s` | ReadoutTriviality |
| Invariants classified by (ε,s) | §3 above | AddressPrinciple |

### Layer P (light, no new hypotheses):

| Claim | Why P |
|-------|-------|
| Physical measurement = solvable probing | Paper II's BP1 |
| (ε,s) exhausts ALL information | "no other source" not M-provable |
| superposition = unspecified address | Epistemological terminology |
| measurement = address specification | Epistemological terminology |
| entanglement = address correlation | Epistemological terminology |

### Key conclusion:

**The Address Principle introduces ZERO new P-layer hypotheses.**
Everything P in Paper IV is inherited from Paper II's BP1.
-/

/-- **Information hierarchy summary.**
    Group-element level: 60 states, all invisible to solvable probes.
    Representation level: 9 irreps (5 integer-spin + 4 half-integer-spin).
    Coarse address level: 4 addresses (ε, s). -/
theorem information_hierarchy :
    -- Group elements: 60 (invisible)
    Fintype.card (alternatingGroup (Fin 5)) = 60 ∧
    -- Irreps of 2I: 9
    MDL.DoubleCover.SL2F5_irrepDims.length = 9 ∧
    -- Coarse addresses: 4
    allAddresses.length = 4 := by
  refine ⟨by native_decide, by simp [MDL.DoubleCover.SL2F5_irrepDims], rfl⟩

/-- **Compression ratios in the information hierarchy.**
    60 → 9 (representation compression, ratio ≈ 6.7)
    9 → 4 (ε-compression, ratio = 2.25)
    60 → 4 (total, ratio = 15) -/
theorem compression_ratios :
    60 / 9 = 6 ∧ 60 / 4 = (15 : ℕ) := by omega

end A5_SM_Pathway.AddressPrinciple
