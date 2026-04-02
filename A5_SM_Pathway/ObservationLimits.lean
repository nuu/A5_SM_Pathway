/-
══════════════════════════════════════════════════════════════════════════════
  Observation Limits: The Algebraic Impossibility of Non-Solvable Measurement
  ：
══════════════════════════════════════════════════════════════════════════════

  File     : A5_SM_Pathway/ObservationLimits.lean
  Project  : A5Paper3 — Weight Law and Readout Law from Non-Solvability of A₅
  Paper §  : §3 (Resolution Zero and Forcing of Counting Measure)
  Author   : M. Numagaki (Independent Researcher, Kumamoto, Japan)
  Date     : March 2026

  STATUS:  sorry = 0 | axiom = 0

  ──────────────────────────────────────────────────────────────────────
  :

    「・」
    「」
    「」

  5:

    §1.  — 
    §2.  — 
    §3.  — 
    §4.  — 60 → 1 
    §5.  — 

  Layer :
    §1–§4: Layer M（）
    §5: Layer M（）+ Layer P（）

  Dependencies:
    A5_SM_Pathway.Auxiliary       → A5_card, A5_is_simple, A5_perfect, ...
    A5_SM_Pathway.BornFromA5Opacity → SolvableProbe, A5_probe_trivializes, ...
══════════════════════════════════════════════════════════════════════════════
-/

import A5_SM_Pathway.BornFromA5Opacity
import A5_SM_Pathway.SolvabilityBelow60

set_option maxRecDepth 4000

namespace CosmicNecessity


/-!
══════════════════════════════════════════════════════════════════════════════
  §1.  — Observer as Solvable Homomorphism
══════════════════════════════════════════════════════════════════════════════

  々「」
  （）

  :「 Q  π」

  （BornFromA5Opacity.lean ）:
    SolvableProbe G := { Q : Type*, [IsSolvable Q], π : G →* Q }

  SolvableProbe  BornFromA5Opacity.lean 
  「」
══════════════════════════════════════════════════════════════════════════════
-/


/-!
══════════════════════════════════════════════════════════════════════════════
  §2.  — Resolution of an Observer
══════════════════════════════════════════════════════════════════════════════

   π: G → Q 「」:= π 

  π(g) ≠ π(h)  (g, h) 
   = 0 「」

   = |G| × (|G| - 1) / 2（）
══════════════════════════════════════════════════════════════════════════════
-/

section Resolution

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/--
  ****:  π 

  resolution(π) := |{ (g, h) : G × G | π(g) ≠ π(h) }|

  - resolution = 0: （）
  - resolution = |G|² - |G|: （）
-/
def observerResolution {Q : Type*} [Group Q] [Fintype Q] [DecidableEq Q]
    (π : G →* Q) : ℕ :=
  Finset.card (Finset.filter
    (fun p : G × G => π p.1 ≠ π p.2)
    Finset.univ)

/--
  ****: 

  |im(π)| = 1 
  |im(π)| = |G| （π ）
-/
def observerImageSize {Q : Type*} [Group Q] [Fintype Q] [DecidableEq Q]
    (π : G →* Q) : ℕ :=
  Finset.card (Finset.image π Finset.univ)

omit [DecidableEq G] in
/--
  ****

  resolution(π) = 0 ⟺ ∀ g h, π(g) = π(h)
-/
theorem resolution_zero_iff_all_equal
    {Q : Type*} [Group Q] [Fintype Q] [DecidableEq Q]
    (π : G →* Q) :
    observerResolution π = 0 ↔ ∀ g h : G, π g = π h := by
  constructor
  · intro hres g h
    by_contra hne
    have : (g, h) ∈ Finset.filter (fun p : G × G => π p.1 ≠ π p.2) Finset.univ := by
      simp [Finset.mem_filter]; exact hne
    have hpos : 0 < Finset.card (Finset.filter
        (fun p : G × G => π p.1 ≠ π p.2) Finset.univ) :=
      Finset.card_pos.mpr ⟨(g, h), this⟩
    simp only [observerResolution] at hres; linarith
  · intro hall
    apply Finset.card_eq_zero.mpr
    rw [Finset.filter_eq_empty_iff]
    intro ⟨g, h⟩ _
    simp; exact hall g h

end Resolution


/-!
══════════════════════════════════════════════════════════════════════════════
  §3.  — The Opacity Wall
══════════════════════════════════════════════════════════════════════════════

  A₅ 

   Paper I (BornFromA5Opacity.lean) 
  A5_probe_cannot_distinguish 

  :
    「々（）
     A₅ 」

  :
    - 
    - 
    - 
══════════════════════════════════════════════════════════════════════════════
-/

section OpacityWall

/--
  ** (The Opacity Wall)**

  A₅ 

  「」
  A₅ 60
-/
theorem opacity_wall
    (probe : SolvableProbe (alternatingGroup (Fin 5)))
    [DecidableEq probe.Q] :
    observerResolution probe.π = 0 := by
  rw [resolution_zero_iff_all_equal]
  exact A5_probe_cannot_distinguish probe

/--
  ****: 1

  60
  :「1」
-/
theorem solvable_probe_image_trivial
    (probe : SolvableProbe (alternatingGroup (Fin 5)))
    [DecidableEq probe.Q] :
    observerImageSize probe.π = 1 := by
  unfold observerImageSize
  rw [show Finset.image probe.π Finset.univ = {1} from ?_]
  · simp
  · ext q
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨g, rfl⟩; exact A5_probe_trivializes probe g
    · intro hq; exact ⟨1, by simp [map_one, hq]⟩

/--
  ****:

  （60）
  1 = 60 : 1
-/
theorem opacity_quantitative :
    --  = 
    (∀ probe : SolvableProbe (alternatingGroup (Fin 5)),
      probe.π.ker = ⊤) ∧
    --  = 60（）
    (Fintype.card (alternatingGroup (Fin 5)) = 60) := by
  exact ⟨A5_probe_ker_eq_top, A5_card⟩

end OpacityWall


/-!
══════════════════════════════════════════════════════════════════════════════
  §4. 
══════════════════════════════════════════════════════════════════════════════

  （） |G|² - |G| 
   0

  :
    （） / （） = 0 / (60²-60) = 0

  :
    : |im(π_solvable)| / |im(π_regular)| = 1/60
══════════════════════════════════════════════════════════════════════════════
-/

section InformationLoss

/--
  **（）**

   ρ_reg: A₅ → Perm(A₅) 
  

   Cayley 
-/
theorem full_resolution_exists :
    ∃ (f : alternatingGroup (Fin 5) →* Equiv.Perm (alternatingGroup (Fin 5))),
    Function.Injective f :=
  ⟨MulAction.toPermHom _ _, MulAction.toPerm_injective⟩

/--
  ****

   |G|
-/
theorem faithful_probe_image_full
    {G Q : Type*} [Group G] [Fintype G] [Group Q] [Fintype Q] [DecidableEq Q]
    (f : G →* Q) (hf : Function.Injective f) :
    Finset.card (Finset.image f Finset.univ) = Fintype.card G := by
  rw [Finset.card_image_of_injective _ hf, Finset.card_univ]

/--
  ****

  :  = 1 ()
  :  = 60 ()

   1 : 60
-/
theorem information_contrast :
    --  = 60
    (∃ (f : alternatingGroup (Fin 5) →* Equiv.Perm (alternatingGroup (Fin 5))),
      Function.Injective f ∧
      Fintype.card (alternatingGroup (Fin 5)) = 60) ∧
    --  = 1 ()
    (∀ probe : SolvableProbe (alternatingGroup (Fin 5)),
      ∀ g h, probe.π g = probe.π h) := by
  exact ⟨⟨MulAction.toPermHom _ _, MulAction.toPerm_injective, A5_card⟩,
         fun probe g h => A5_probe_cannot_distinguish probe g h⟩

end InformationLoss


/-!
══════════════════════════════════════════════════════════════════════════════
  §5.  — Probability Emerges from Blindness
══════════════════════════════════════════════════════════════════════════════

  60 →  1/60 
  「」

   BornFromDiscreteness.lean 
  invariant_prob_is_counting_measure :

     G- G-
     1/|S| 

  

  :
     (§3)
      ↓
     ( = 0)
      ↓
     ()
      ↓
     1/|S|  (BornFromDiscreteness)
      ↓
    「」
══════════════════════════════════════════════════════════════════════════════
-/

section ProbabilityEmergence

/--
  **: **

   π 
  → π  f: G → ℚ 
  → 「」
  →  1/|G|
-/
theorem indistinguishability_forces_symmetry
    (probe : SolvableProbe (alternatingGroup (Fin 5)))
    (f : probe.Q → ℚ) :
    ∀ g h : alternatingGroup (Fin 5),
    f (probe.π g) = f (probe.π h) := by
  intro g h
  rw [A5_probe_cannot_distinguish probe g h]

/--
  **「」1**

  A₅ 60
  11「」

  :
    
    「」= 
-/
theorem classical_state_is_single_point
    (probe : SolvableProbe (alternatingGroup (Fin 5))) :
    ∀ g : alternatingGroup (Fin 5), probe.π g = 1 :=
  A5_probe_trivializes probe

/--
  ****

  A₅  M :

  (1)  = 0（）
  (2) 601（）
  (3) 
  (4)  1/60 
  (5) （）

  
  「」
-/
theorem probability_emergence_theorem :
    -- (1) 1
    (∀ probe : SolvableProbe (alternatingGroup (Fin 5)),
      ∀ g, probe.π g = 1) ∧
    -- (2) |A₅| = 60 ()
    (Fintype.card (alternatingGroup (Fin 5)) = 60) ∧
    -- (3) （）
    (∃ (f : alternatingGroup (Fin 5) →* Equiv.Perm (alternatingGroup (Fin 5))),
      Function.Injective f) ∧
    -- (4) Born : 1² + 3² + 3² + 4² + 5² = 60
    (1^2 + 3^2 + 3^2 + 4^2 + 5^2 = (60 : ℕ)) ∧
    -- (5) 
    (1 + 3 + 3 + 4 + 5 ≠ (60 : ℕ)) := by
  exact ⟨fun probe g => A5_probe_trivializes probe g,
         A5_card,
         ⟨MulAction.toPermHom _ _, MulAction.toPerm_injective⟩,
         by norm_num,
         by norm_num⟩

end ProbabilityEmergence


/-!
══════════════════════════════════════════════════════════════════════════════
  §6. ：
══════════════════════════════════════════════════════════════════════════════

  「」:

    
    「」
    

    々
     A₅ 
    

  :
    - 「」= （）
    - 「」= （）
    - 「」= （sorry=0）
    - 「」= 60:1 （sorry=0）
    - 「」= →（sorry=0）
══════════════════════════════════════════════════════════════════════════════
-/

section Conclusion

/--
  **: **

   A₅ （Layer M）:

  「（A₅）
   
    Born  P(i) = nᵢ²/|G| 
    Plancherel 」
-/
theorem observation_impossibility :
    -- :  A₅ 
    (∀ probe : SolvableProbe (alternatingGroup (Fin 5)),
      ∀ g h : alternatingGroup (Fin 5),
      probe.π g = probe.π h) ∧
    -- : A₅ 
    (¬ IsSolvable (alternatingGroup (Fin 5))) ∧
    -- : |G| < 60 （）
    (∀ (G : Type*) [Group G] [Fintype G],
      Fintype.card G < 60 → IsSolvable G) ∧
    -- : 
    (∃ (f : alternatingGroup (Fin 5) →* Equiv.Perm (alternatingGroup (Fin 5))),
      Function.Injective f) :=
  ⟨fun probe g h => A5_probe_cannot_distinguish probe g h,
   A5_not_solvable,
   fun _G _ _ h => groups_below_60_solvable h,
   ⟨MulAction.toPermHom _ _, MulAction.toPerm_injective⟩⟩

end Conclusion

end CosmicNecessity
