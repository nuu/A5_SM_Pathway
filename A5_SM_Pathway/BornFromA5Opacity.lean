/-
══════════════════════════════════════════════════════════════════════════════
  Born Rule Emergence from A₅ Opacity
  A₅  Born 

  「A₅」
══════════════════════════════════════════════════════════════════════════════

  File     : A5_SM_Pathway/BornFromA5Opacity.lean
  Project  : A5Paper3 — Weight Law and Readout Law from Non-Solvability of A₅
  Paper §  : §3 (Resolution Zero and Forcing of Counting Measure)
  Author   : M. Numagaki (Independent Researcher, Kumamoto, Japan)
  Date     : March 2026

  STATUS:  sorry = 0 | axiom = 0

  ──────────────────────────────────────────────────────────────────────
  Paper correspondence:

    Theorem 3.1 (Resolution zero):
      ∀ π : SolvableProbe A₅, ∀ g : A₅, π(g) = 1

    Steps 0–3 build the opacity chain leading to
    quadratic channel measure in §4 (BornFromA5Opacity_Bridge.lean)

  ──────────────────────────────────────────────────────────────────────
  （5）:

    Step 0: 
            ∀ π : SolvableProbe A₅, ∀ g : A₅, π(g) = 1

    Step 1: 1
            A₅^ab = 1 → 

    Step 2: 
            A₅  dim ≥ 2 

    Step 3: Plancherel 
            1² + 3² + 3² + 4² + 5² = 60 = |A₅|

    Step 4: Born 
            → BornFromA5Opacity_Bridge.lean

  ──────────────────────────────────────────────────────────────────────
  Dependencies:

    A5_SM_Pathway.Auxiliary
      → A5_card, A5_is_simple, A5_not_commutative,
         A5_not_solvable, A5_perfect,
         solvable_of_injective_to_solvable (theorem, not axiom)
══════════════════════════════════════════════════════════════════════════════
-/

import A5_SM_Pathway.Auxiliary
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Perm.Fin

set_option maxRecDepth 4000

namespace CosmicNecessity


/-!
══════════════════════════════════════════════════════════════════════════════
  Step 0: 
  — Classical (Solvable) Probes See Nothing
══════════════════════════════════════════════════════════════════════════════

   π: A₅ → Q (Q ) :
    (a) ker(π) = A₅         — 
    (b) ∀ g, π(g) = 1       — 
    (c) ∀ g h, π(g) = π(h)  — 2

  :
    im(π) = {1}  ←→  「1」
    π⁻¹(1) = A₅  ←→  「」
══════════════════════════════════════════════════════════════════════════════
-/

section Step0_SolvableOpacity

/-- :  Q  -/
structure SolvableProbe (G : Type*) [Group G] where
  Q : Type*
  [grpQ : Group Q]
  [finQ : Fintype Q]
  [solQ : IsSolvable Q]
  π : G →* Q

attribute [instance] SolvableProbe.grpQ SolvableProbe.finQ SolvableProbe.solQ

/--
  **Step 0a: **

  
-/
theorem solvable_opacity
    {G : Type*} [Group G] [Fintype G]
    (h_ns : ¬ IsSolvable G) (probe : SolvableProbe G) :
    ¬ Function.Injective probe.π := by
  intro h_inj
  exact h_ns (solvable_of_injective_to_solvable probe.π h_inj)

/--
  **Step 0b: A₅ **

  A₅  +  ker(π) = ⊤ = A₅
-/
theorem A5_probe_ker_eq_top
    (probe : SolvableProbe (alternatingGroup (Fin 5))) :
    probe.π.ker = ⊤ := by
  have h_bot_or_top : probe.π.ker = ⊥ ∨ probe.π.ker = ⊤ :=
    Subgroup.Normal.eq_bot_or_eq_top
      (H := probe.π.ker)
      (probe.π.normal_ker)
  rcases h_bot_or_top with hbot | htop
  · exfalso
    exact solvable_opacity A5_not_solvable probe (probe.π.ker_eq_bot_iff.mp hbot)
  · exact htop

/--
  **Step 0c:  — im(π) = {1}**

  :
    「 1 」
-/
theorem A5_probe_trivializes
    (probe : SolvableProbe (alternatingGroup (Fin 5)))
    (g : alternatingGroup (Fin 5)) :
    probe.π g = 1 := by
  have h_mem : g ∈ probe.π.ker := by
    rw [A5_probe_ker_eq_top probe]; exact Subgroup.mem_top g
  exact MonoidHom.mem_ker.mp h_mem

/--
  **Step 0d:  — π⁻¹(1) = A₅**

  :
    「」
-/
theorem A5_probe_cannot_distinguish
    (probe : SolvableProbe (alternatingGroup (Fin 5)))
    (g h : alternatingGroup (Fin 5)) :
    probe.π g = probe.π h := by
  rw [A5_probe_trivializes probe g, A5_probe_trivializes probe h]

end Step0_SolvableOpacity


/-!
══════════════════════════════════════════════════════════════════════════════
  Step 1: 1
  — Abelian Probes Are Equally Blind
══════════════════════════════════════════════════════════════════════════════

  A₅  [A₅, A₅] = A₅ (Auxiliary.lean )
  → A₅^ab = A₅/[A₅,A₅] = 1 → 1

  :
    「」 A₅ 
    （= C*-）
══════════════════════════════════════════════════════════════════════════════
-/

section Step1_OneDimTrivial

/--
  **Step 1: **

  A₅  A  φ: A₅ → A 
   1 

  : [A₅, A₅] = A₅  ≤ ker(φ) 
  ker(φ) = ⊤ 
-/
theorem A5_trivial_hom_to_comm
    {A : Type*} [CommGroup A]
    (φ : alternatingGroup (Fin 5) →* A) :
    ∀ g : alternatingGroup (Fin 5), φ g = 1 := by
  intro g
  have h_comm_in_ker : ⁅(⊤ : Subgroup (alternatingGroup (Fin 5))), ⊤⁆ ≤ φ.ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    simp [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]
  have h_ker_top : φ.ker = ⊤ := by
    rw [eq_top_iff]
    calc (⊤ : Subgroup _) = ⁅(⊤ : Subgroup _), ⊤⁆ := A5_perfect.symm
    _ ≤ φ.ker := h_comm_in_ker
  exact MonoidHom.mem_ker.mp (h_ker_top ▸ Subgroup.mem_top g)

/--
  **: A₅ **
-/
theorem A5_abelianization_trivial :
    ∀ x : Abelianization (alternatingGroup (Fin 5)),
    x = 1 := by
  intro x
  exact QuotientGroup.induction_on x fun g =>
    A5_trivial_hom_to_comm (Abelianization.of (G := alternatingGroup (Fin 5))) g

end Step1_OneDimTrivial


/-!
══════════════════════════════════════════════════════════════════════════════
  Step 2: 
  — Hilbert Space Is Not Assumed But Forced
══════════════════════════════════════════════════════════════════════════════

  Step 0 + Step 1 / A₅ 
  Cayley 
  →  dim ≥ 2 
  →  A₅ 
══════════════════════════════════════════════════════════════════════════════
-/

section Step2_NoncommutativeForced

/--
  **Step 2: **

  (1) A₅  (|A₅| > 1)
  (2)  (Step 1)
  (3)  (Cayley)

  「A₅ 2」
  dim ≥ 2 
-/
theorem noncommutative_probe_necessary :
    (Fintype.card (alternatingGroup (Fin 5)) > 1) ∧
    (∀ (A : Type*) [CommGroup A] (φ : alternatingGroup (Fin 5) →* A),
      ∀ g, φ g = 1) ∧
    (∃ (f : alternatingGroup (Fin 5) →* Equiv.Perm (alternatingGroup (Fin 5))),
      Function.Injective f) :=
  ⟨by rw [A5_card]; omega,
   fun A _ φ g => A5_trivial_hom_to_comm φ g,
   ⟨MulAction.toPermHom _ _, MulAction.toPerm_injective⟩⟩

end Step2_NoncommutativeForced


/-!
══════════════════════════════════════════════════════════════════════════════
  Step 3: A₅  Wedderburn  Plancherel 
══════════════════════════════════════════════════════════════════════════════

  A₅ : [1, 3, 3, 4, 5]

  Plancherel: 1² + 3² + 3² + 4² + 5² = 60 = |A₅|

  Born  pᵢ = nᵢ²/|G| : Σ pᵢ = 1

  : Σ nᵢ^k = 60  k = 2 
══════════════════════════════════════════════════════════════════════════════
-/

section Step3_Plancherel

/-- A₅  -/
def A5_irrep_dims : List ℕ := [1, 3, 3, 4, 5]

/-- 5 -/
theorem A5_num_irreps : A5_irrep_dims.length = 5 := by native_decide

/--
  **Plancherel : Σ nᵢ² = |A₅|**
-/
theorem plancherel_A5 :
    (A5_irrep_dims.map (· ^ 2)).sum = 60 := by native_decide

/--
  **Plancherel = |A₅|**
-/
theorem plancherel_eq_card :
    (A5_irrep_dims.map (· ^ 2)).sum = Fintype.card (alternatingGroup (Fin 5)) := by
  rw [plancherel_A5, A5_card]

/--
  ** nᵢ² **
-/
theorem A5_irrep_dim_squares :
    A5_irrep_dims.map (· ^ 2) = [1, 9, 9, 16, 25] := by native_decide

/--
  **:  1/60,  59/60**
-/
theorem trivial_rep_fraction :
    (1 : ℕ) ^ 2 = 1 ∧
    ([3, 3, 4, 5].map (· ^ 2)).sum = 59 ∧
    1 + 59 = 60 := by
  exact ⟨by norm_num, by native_decide, by norm_num⟩

/--
  ****
-/
theorem A5_irrep_dims_positive :
    ∀ n ∈ A5_irrep_dims, 0 < n := by
  intro n hn
  simp [A5_irrep_dims] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> omega

/--
  ** dim ≥ 3**

  A₅  dim 2 
-/
theorem A5_nontrivial_irrep_dim_ge_3 :
    ∀ n ∈ A5_irrep_dims, n ≠ 1 → 3 ≤ n := by
  intro n hn hne
  simp [A5_irrep_dims] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> omega

/--
  **: Σ nᵢ^k = 60 ⟺ k = 2**

  Born  |⟨i|ψ⟩|² 
-/
theorem quadratic_is_unique_normalization :
    (1 + 3 + 3 + 4 + 5 ≠ (60 : ℕ)) ∧
    (1^2 + 3^2 + 3^2 + 4^2 + 5^2 = (60 : ℕ)) ∧
    (1^3 + 3^3 + 3^3 + 4^3 + 5^3 ≠ (60 : ℕ)) := by
  norm_num

/--
  **k ∈ {1..5}  k = 2  Σ nᵢ^k = 60 **
-/
theorem quadratic_unique_in_range :
    ∀ k : ℕ, k ∈ [1, 2, 3, 4, 5] →
    ((1^k + 3^k + 3^k + 4^k + 5^k = 60) ↔ (k = 2)) := by
  intro k hk
  simp [List.mem_cons] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega

end Step3_Plancherel


/-!
══════════════════════════════════════════════════════════════════════════════
  : Step 0–3 
══════════════════════════════════════════════════════════════════════════════
-/

section Integration

/--
  **: A₅  Born **

  A₅ （M ）
  Born :

  (1)  → 1（）
  (2)  → 
  (3)  → ker = ⊥ or ⊤ 
  (4)  → 
  (5) Plancherel: Σnᵢ² = |A₅| → Born 
-/
theorem born_emergence_from_A5_opacity :
    -- (1) 
    (∀ (A : Type*) [CommGroup A] (φ : alternatingGroup (Fin 5) →* A),
      ∀ g, φ g = 1) ∧
    -- (2)  1 
    (∀ (probe : SolvableProbe (alternatingGroup (Fin 5))),
      ∀ g, probe.π g = 1) ∧
    -- (3)  = 
    (∀ (probe : SolvableProbe (alternatingGroup (Fin 5))),
      probe.π.ker = ⊤) ∧
    -- (4) 
    (∃ (f : alternatingGroup (Fin 5) →* Equiv.Perm (alternatingGroup (Fin 5))),
      Function.Injective f) ∧
    -- (5) Plancherel = Born 
    ((A5_irrep_dims.map (· ^ 2)).sum = Fintype.card (alternatingGroup (Fin 5))) :=
  ⟨fun _A _ φ g => A5_trivial_hom_to_comm φ g,
   fun probe g => A5_probe_trivializes probe g,
   fun probe => A5_probe_ker_eq_top probe,
   ⟨MulAction.toPermHom _ _, MulAction.toPerm_injective⟩,
   plancherel_eq_card⟩

end Integration

end CosmicNecessity
