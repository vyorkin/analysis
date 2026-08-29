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

/--
Axiom 3.8 (универсальная спецификация):

Для любого утверждения {lit}`P` существует множество {lit}`A` такое,
что если элемент {lit}`x` принадлежит этому множеству ({lit}`x ∈ A`),
то для него выполняется {lit}`P x`.
-/
abbrev axiom_of_universal_specification : Prop :=
  ∀ P : Object → Prop, ∃ A : Set, ∀ x : Object, x ∈ A ↔ P x

/--
Аксиома универсальной спецификации противоречива:

Не существует объекта, задающего множество всех {lit}`x`,
для которых верно произвольное {lit}`P x`
-/
theorem Russells_paradox : ¬ axiom_of_universal_specification := by
  -- Это доказательство написано так,
  -- чтобы следовать структуре оригинального текста
  unfold axiom_of_universal_specification
  -- Нужно прийти к противоречию
  intro hus
  -- В качестве `P` берём следующее утверждение:
  -- "x/X — это (некоторое) множество, не содержащее само себя"
  set P : Object → Prop := fun x ↦
    ∃ X : Set, x = X ∧ x ∉ X -- let P : ...
  -- x = X -- мн-во элементов, которые являются этим же множеством (самими сабими)
  -- x ∉ X -- и не входят в это множество
  -- По аксиоме универсальной спецификации применённой к P, получаем,
  -- что существуюет некоторое множество Ω:
  have husP : ∃ Ω, ∀ (x : Object), x ∈ Ω ↔ P x := hus P
  -- Разберём полученное утверждение на 2 отдельные гипотезы
  obtain ⟨Ω, hΩ⟩ := husP
  -- Итак, у нас есть Ω и утверждение hΩ, которое должно для него выполняться.
  -- А теперь покажем, что этого вызывает парадокс.
  -- Для этого рассмотрим оба случая:
  -- 1) когда Ω содержит само себя и 2) когда не содержит
  by_cases h' : (Ω : Object) ∈ Ω
  -- Случай `Ω ∈ Ω`:
  -- тогда `P Ω` верно, то есть `Ω` совпадает с каким-то `X ∉ X`
  . -- Утверждение `P` верно для любого элемента Ω,
    -- тогда давай возьмём в качестве такого элемента само Ω.
    specialize hΩ Ω
    -- Теперь: `hΩ : Ω ∈ Ω ↔ P Ω` и у нас есть `h' : Ω ∈ Ω`
    have hP : P (Ω : Object) := hΩ.mp h'
    -- Разворачиваем определённую выше P, чтобы было понятнее что происходит
    unfold P at hP
    -- В роли `x` мы использовали `Ω`, поэтому `hP : P` сейчас имеет вид:
    -- `hP : ∃ X, Ω = X ∧ Ω ∉ X`
    -- Разбираем её на составляющие её утверждения:
    -- 1) ∃ X     => Ω'
    -- 2) Ω = X   => hΩ1 : Ω = Ω'
    -- 3) Ω ∉ X   => hΩ2 : Ω ∉ Ω'
    obtain ⟨Ω', ⟨hΩ1, hΩ2⟩⟩ := hP
    -- simp сводит равенство образов (↑Ω = ↑Ω') к равенству множеств Ω = Ω'
    simp at hΩ1
    rw [←hΩ1] at hΩ2
    -- Пришли к противоречию
    contradiction -- hΩ2 : Ω ∉ Ω, а h' : Ω ∈ Ω
  -- Случай Ω ∉ Ω:
  -- тогда X := Ω сам свидетельствует, что P Ω верно
  · have hPΩ: P (Ω : Object) := by use Ω
    rw [←hΩ] at hPΩ -- получаем Ω ∈ Ω, что противоречит h'
    contradiction

/--
Axiom 3.9 (регулярность):

То же утверждение, что и {lit}`regularity_axiom` из раздела 3.1,
но переформулированное в терминах {lit}`Set`/{lit}`∈` вместо {lit}`Object`/{lit}`mem`,
и с {lit}`Disjoint S A` вместо {lit}`¬∃ y, y ∈ A ∧ y ∈ S`.

Любое непустое множество {lit}`A` содержит элемент {lit}`x`,
который либо сам не является множеством, либо, будучи множеством {lit}`S`,
не пересекается с {lit}`A`.

Это исключает бесконечный спуск по цепочке принадлежности и,
в частности, запрещает множеству содержать само себя.
-/
theorem SetTheory.Set.axiom_of_regularity {A : Set} (h : A ≠ ∅) :
  ∃ x : A, ∀ S : Set, x.val = S → Disjoint S A := by
    -- Раз `A ≠ ∅`, у него есть хотя бы один элемент
    have hA : ∃ x, x ∈ A := nonempty_def h
    -- Применяем сырую аксиому регулярности к этому элементу —
    --
    -- (A : Set) (hA : ∃ x, x ∈ A) :
    --   ∃ x, x ∈ A ∧ ∀ (S : Set), x = S → ¬∃ y, y ∈ A ∧ y ∈ S
    obtain ⟨x, hxA, h'⟩ := regularity_axiom A hA
    -- Она даёт `hxA : x ∈ A` и условие `h'`, гарантирующее
    -- отсутствие общих элементов у `A` и `S` (когда `x = S`)
    --
    -- Тип переменной в `∃ x, …` это `A.toSubtype = {x : Object // x ∈ A}`.
    -- Он написан явно в формулировке теоремы (`∃ x : A, …` выше),
    -- а если бы не был виден – `use x` без пары выдал бы ошибку с ожидаемым типом:
    --
    -- Type mismatch
    --   x
    -- has type
    --   Object
    -- but is expected to have type
    --   A.toSubtype
    --
    use ⟨x, hxA⟩
    intro S hS
    specialize h' S hS
    -- Осталось перевести `h' : ¬∃ y, y ∈ A ∧ y ∈ S` в цель `Disjoint S A`
    rw [disjoint_iff] -- Disjoint A B ↔ A ∩ B = ∅
    rw [eq_empty_iff_forall_notMem] -- X = ∅ ↔ ∀ (x : Object), x ∉ X
    -- Контрапозиция + push_neg:
    -- 1) Трансформирует цель P → Q в ¬Q → ¬P
    -- 2) Применяет push_neg к цели и гипотезе
    contrapose! h'
    -- x ∈ S ∩ A, которое надо переписать, находится под ∃ x,
    -- a `rw` ищет паттерн через kabstract, который не спускается внутрь ∃,
    -- поэтому применяем тактику simp
    simp only [mem_inter'] at h' -- x ∈ X ∩ Y ↔ x ∈ X ∧ x ∈ Y
    obtain ⟨x1, hx1⟩ := hA
    obtain ⟨x2, ⟨hx2inS, hx2inA⟩⟩ := h'
    exact ⟨x2, ⟨hx2inA, hx2inS⟩⟩

/--
Exercise 3.2.1.
Суть упражнения — установить эти результаты,
не используя ни парадокс Рассела, ни пустое множество.
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
theorem SetTheory.Set.not_mem_self (A : Set) : (A : Object) ∉ A := by
  sorry

/-- Exercise 3.2.2 (no two sets contain each other) -/
theorem SetTheory.Set.not_mem_mem (A B : Set) : (A : Object) ∉ B ∨ (B : Object) ∉ A := by
  sorry

/-- Exercise 3.2.3 (universal specification) -/
theorem SetTheory.Set.univ_iff : axiom_of_universal_specification ↔
  ∃ (U : Set), ∀ x, x ∈ U := by sorry

/-- Exercise 3.2.3 (there is no universal set) -/
theorem SetTheory.Set.no_univ : ¬ ∃ (U : Set), ∀ (x : Object), x ∈ U := by sorry


end Chapter3
