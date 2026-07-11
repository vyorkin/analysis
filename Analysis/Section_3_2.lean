import Mathlib.Tactic
import Analysis.Section_3_1

/-!
# Analysis I, Section 3.2: Russell's paradox

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

This section is mostly optional, though it does make explicit the axiom of foundation which is
used in a minor role in an exercise in Section 3.5.

Main constructions and results of this section:

- Russell's paradox (ruling out the axiom of universal specification).
- The axiom of regularity (foundation) - an axiom designed to avoid Russell's paradox.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

--/

namespace Chapter3

export SetTheory (Set Object)

variable [SetTheory]

/-- Axiom 3.8 (Universal specification) -/
abbrev axiom_of_universal_specification : Prop :=
  ∀ P : Object → Prop, ∃ A : Set, ∀ x : Object, x ∈ A ↔ P x

theorem Russells_paradox : ¬ axiom_of_universal_specification := by
  -- This proof is written to follow the structure of the original text.
  intro hus
  unfold axiom_of_universal_specification at hus
  -- P x: "x — это (некоторое) множество, не содержащее самого себя"
  set P : Object → Prop := fun x ↦ ∃ X : Set, x = X ∧ x ∉ X -- let P : ...
  -- x = X -- мн-во элементов, которые являются этим же множеством (самим сабими)
  -- x ∉ X -- не содержит само себя
  -- по аксиоме универсальной спецификации применённой к P, получаем:
  obtain ⟨Ω, hΩ⟩ := hus P
  -- Рассмотрим оба случая:
  -- когда омега содержит само себя и когда не содержит
  by_cases h' : (Ω : Object) ∈ Ω
  -- случай Ω ∈ Ω: тогда P Ω верно, то есть Ω совпадает с каким-то X ∉ X
  . have hiff : (Ω : Object) ∈ Ω ↔ P (Ω : Object) := hΩ Ω
    have hP : P (Ω : Object) := hiff.mp h'
    obtain ⟨Ω', ⟨hΩ1, hΩ2⟩⟩ := hP
    -- simp сводит равенство образов (↑Ω = ↑Ω') к равенству множеств Ω = Ω'
    simp at hΩ1
    rw [←hΩ1] at hΩ2
    contradiction  -- hΩ2 : Ω ∉ Ω, а h' : Ω ∈ Ω
  -- случай Ω ∉ Ω: тогда X := Ω сам свидетельствует, что P Ω верно
  · have : P (Ω : Object) := by use Ω
    rw [←hΩ] at this  -- получаем Ω ∈ Ω, что противоречит h'
    contradiction

/-- Axiom 3.9 (Regularity) -/
theorem SetTheory.Set.axiom_of_regularity {A : Set} (h : A ≠ ∅) :
    ∃ x : A, ∀ S : Set, x.val = S → Disjoint S A := by
  have hA : ∃ x, x ∈ A := nonempty_def h
  -- regularity_axiom
  --   (A : Set)
  --   (hA : ∃ x, mem x A)
  --   :
  --   ∃ x, x ∈ A ∧ ∀ (S : Set), x = S → ¬∃ y, y ∈ A ∧ y ∈ S
  obtain ⟨x, h, h'⟩ := regularity_axiom A hA
  use ⟨x, h⟩
  intro S hS; specialize h' S hS
  rw [disjoint_iff, eq_empty_iff_forall_notMem]
  contrapose! h'; simp at h'
  aesop

/--
  Exercise 3.2.1.  The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the empty set.
-/
theorem SetTheory.Set.emptyset_exists (h : axiom_of_universal_specification) :
    ∃ (X : Set), ∀ x, x ∉ X := by
  sorry

/--
  Exercise 3.2.1.  The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the singleton set.
-/
theorem SetTheory.Set.singleton_exists (h : axiom_of_universal_specification) (x : Object) :
    ∃ (X : Set), ∀ y, y ∈ X ↔ y = x := by
  sorry

/--
  Exercise 3.2.1.  The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the pair set.
-/
theorem SetTheory.Set.pair_exists (h : axiom_of_universal_specification) (x₁ x₂ : Object) :
    ∃ (X : Set), ∀ y, y ∈ X ↔ y = x₁ ∨ y = x₂ := by
  sorry

/--
  Exercise 3.2.1. The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the union operation.
-/
theorem SetTheory.Set.union_exists (h : axiom_of_universal_specification) (A B : Set) :
    ∃ (Z : Set), ∀ z, z ∈ Z ↔ z ∈ A ∨ z ∈ B := by
  sorry

/--
  Exercise 3.2.1. The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the specify operation.
-/
theorem SetTheory.Set.specify_exists (h : axiom_of_universal_specification) (A : Set) (P : A → Prop) :
    ∃ (Z : Set), ∀ z, z ∈ Z ↔ ∃ h : z ∈ A, P ⟨ z, h ⟩ := by
  sorry

/--
  Exercise 3.2.1. The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the replace operation.
-/
theorem SetTheory.Set.replace_exists (h : axiom_of_universal_specification) (A : Set)
  (P : A → Object → Prop) (hP : ∀ x y y', P x y ∧ P x y' → y = y') :
    ∃ (Z : Set), ∀ y, y ∈ Z ↔ ∃ a : A, P a y := by
  sorry

/-- Exercise 3.2.2 -/
theorem SetTheory.Set.not_mem_self (A : Set) : (A : Object) ∉ A := by sorry

/-- Exercise 3.2.2 -/
theorem SetTheory.Set.not_mem_mem (A B : Set) : (A : Object) ∉ B ∨ (B : Object) ∉ A := by sorry

/-- Exercise 3.2.3 -/
theorem SetTheory.Set.univ_iff : axiom_of_universal_specification ↔
  ∃ (U : Set), ∀ x, x ∈ U := by sorry

/-- Exercise 3.2.3 -/
theorem SetTheory.Set.no_univ : ¬ ∃ (U : Set), ∀ (x : Object), x ∈ U := by sorry


end Chapter3
