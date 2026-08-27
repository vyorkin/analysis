import Mathlib.Tactic
import Analysis.Section_3_1

/-!
# Analysis I, раздел 3.2: Парадокс Рассела

Я старался сделать перевод максимально точным перефразированием оригинального текста. Когда
приходилось выбирать между более идиоматичным Lean-решением и более точным переводом, я, как
правило, выбирал второе. В частности, местами Lean-код можно было бы "заголфить", сделав его более
элегантным и идиоматичным, но я сознательно этого избегал.

Этот раздел по большей части необязателен, хотя в нём явно формулируется аксиома фундирования,
которая играет второстепенную роль в одном из упражнений раздела 3.5.

Основные конструкции и результаты этого раздела:

- Парадокс Рассела (исключающий аксиому универсальной спецификации).
- Аксиома регулярности (фундирования) — аксиома, призванная избежать парадокса Рассела.

## Советы от прошлых пользователей

Пользователи, прошедшие упражнения этого раздела, могут присылать свои советы для будущих пользователей в виде PR.

- (Добавьте совет сюда)

-/

namespace Chapter3

export SetTheory (Set Object)

variable [SetTheory]

/-- Axiom 3.8 (универсальная спецификация) -/
abbrev axiom_of_universal_specification : Prop :=
  ∀ P : Object → Prop, ∃ A : Set, ∀ x : Object, x ∈ A ↔ P x

theorem Russells_paradox : ¬ axiom_of_universal_specification := by
  -- Это доказательство написано так, чтобы следовать структуре оригинального текста.
  intro hus
  unfold axiom_of_universal_specification at hus
  -- P x: "x — это (некоторое) множество, не содержащее самого себя"
  set P : Object → Prop := fun x ↦ ∃ X : Set, x = X ∧ x ∉ X -- let P : ...
  -- x = X -- мн-во элементов, которые являются этим же множеством (самими собой)
  -- x ∉ X -- и не входят в это множество
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

/-- Axiom 3.9 (регулярность) -/
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
  Exercise 3.2.1. Суть упражнения — установить эти результаты, не используя ни парадокс
  Рассела, ни пустое множество.
-/
theorem SetTheory.Set.emptyset_exists (h : axiom_of_universal_specification) :
    ∃ (X : Set), ∀ x, x ∉ X := by
  sorry

/--
  Exercise 3.2.1. Суть упражнения — установить эти результаты,
  не используя ни парадокс Рассела, ни одноэлементное множество.
-/
theorem SetTheory.Set.singleton_exists (h : axiom_of_universal_specification) (x : Object) :
    ∃ (X : Set), ∀ y, y ∈ X ↔ y = x := by
  sorry

/--
  Exercise 3.2.1. Суть упражнения — установить эти результаты,
  не используя ни парадокс Рассела, ни пару.
-/
theorem SetTheory.Set.pair_exists (h : axiom_of_universal_specification) (x₁ x₂ : Object) :
    ∃ (X : Set), ∀ y, y ∈ X ↔ y = x₁ ∨ y = x₂ := by
  sorry

/--
  Exercise 3.2.1. Суть упражнения — установить эти результаты,
  не используя ни парадокс Рассела, ни операцию объединения.
-/
theorem SetTheory.Set.union_exists (h : axiom_of_universal_specification) (A B : Set) :
    ∃ (Z : Set), ∀ z, z ∈ Z ↔ z ∈ A ∨ z ∈ B := by
  sorry

/--
  Exercise 3.2.1. Суть упражнения — установить эти результаты,
  не используя ни парадокс Рассела, ни операцию спецификации.
-/
theorem SetTheory.Set.specify_exists (h : axiom_of_universal_specification) (A : Set) (P : A → Prop) :
    ∃ (Z : Set), ∀ z, z ∈ Z ↔ ∃ h : z ∈ A, P ⟨ z, h ⟩ := by
  sorry

/--
  Exercise 3.2.1. Суть упражнения — установить эти результаты,
  не используя ни парадокс Рассела, ни операцию замены.
-/
theorem SetTheory.Set.replace_exists (h : axiom_of_universal_specification) (A : Set)
  (P : A → Object → Prop) (hP : ∀ x y y', P x y ∧ P x y' → y = y') :
    ∃ (Z : Set), ∀ y, y ∈ Z ↔ ∃ a : A, P a y := by
  sorry

/-- Exercise 3.2.2 (no set contains itself) -/
theorem SetTheory.Set.not_mem_self (A : Set) : (A : Object) ∉ A := by sorry

/-- Exercise 3.2.2 (no two sets contain each other) -/
theorem SetTheory.Set.not_mem_mem (A B : Set) : (A : Object) ∉ B ∨ (B : Object) ∉ A := by sorry

/-- Exercise 3.2.3 (universal specification) -/
theorem SetTheory.Set.univ_iff : axiom_of_universal_specification ↔
  ∃ (U : Set), ∀ x, x ∈ U := by sorry

/-- Exercise 3.2.3 (there is no universal set) -/
theorem SetTheory.Set.no_univ : ¬ ∃ (U : Set), ∀ (x : Object), x ∈ U := by sorry


end Chapter3
