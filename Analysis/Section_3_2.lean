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

Здесь необходимо показать, что из аксиомы универсальной спецификации
вытекают аксиомы 3.3, 3.4, 3.5, 3.6 и 3.7.
Суть упражнения — установить эти результаты,
не используя ни парадокс Рассела, ни пустое множество.

Если предположить, что все натуральные числа являются объектами,
то мы также получим аксиому 3.8. Таким образом, эта аксиома,
если бы она была принята, то значительно упростила бы основу теории множеств.
Она может рассматриваться как одна из основ интуитивной модели теории множеств,
известной как наивная теория множеств. К сожалению, мы убедились,
что аксиома 3.9 слишком хороша, чтобы быть правдой.
-/
theorem SetTheory.Set.emptyset_exists (h : axiom_of_universal_specification) :
  -- Существует такое множество, что никакой элемент в него не входит.
  ∃ (X : Set), ∀ x, x ∉ X := by
    -- Развернём определение универсальной спецификации для наглядности.
    unfold axiom_of_universal_specification at h
    -- Универсальная спецификация говорит нам о том,
    -- что всегда найдётся такое множество `A` для которого верно следующее:
    -- Если какой‑то элемент входит в множество,
    -- то утверждение `P` для этого элемента выполняется (и наоборот).
    --
    -- В качестве `P` берём заведомо ложное утверждение:
    -- тогда никакой `x` не может ему удовлетворять,
    -- и построенное по спецификации множество автоматически окажется пустым.
    set P : Object → Prop := fun _ ↦ False
    specialize h P
    unfold P at h
    obtain ⟨A, hA⟩ := h
    -- Никакой элемент `x` не является элементом множества `A`.
    guard_hyp hA : ∀ (x : Object), x ∈ A ↔ False
    -- Вот такое множество и будем использовать для доказательства.
    use A
    intro x hx
    exact (hA x).mp hx

/-- Exercise 3.2.1 -/
theorem SetTheory.Set.singleton_exists
  (h : axiom_of_universal_specification) (x : Object) :
    -- Существование одноэлементного множества.
    ∃ (X : Set), ∀ y, y ∈ X ↔ y = x := by
      -- Развернём определение универсальной спецификации для наглядности.
      unfold axiom_of_universal_specification at h
      set P : Object → Prop := fun y ↦ y = x
      specialize h P
      obtain ⟨A, h⟩ := h
      unfold P at h; replace h : ∀ y, y ∈ A ↔ y = x := h
      use A, h

/-- Exercise 3.2.1 -/
theorem SetTheory.Set.pair_exists
  (h : axiom_of_universal_specification) (x₁ x₂ : Object) :
    -- Существование множества-пары.
    ∃ (X : Set), ∀ y, y ∈ X ↔ y = x₁ ∨ y = x₂ := by
      unfold axiom_of_universal_specification at h
      set P : Object → Prop := fun y ↦ y = x₁ ∨ y = x₂
      specialize h P
      obtain ⟨A, h⟩ := h
      unfold P at h
      use A

/-- Exercise 3.2.1 -/
theorem SetTheory.Set.union_exists
  (h : axiom_of_universal_specification) (A B : Set) :
    -- Существованиe объединения.
    ∃ (Z : Set), ∀ z, z ∈ Z ↔ z ∈ A ∨ z ∈ B := by
      unfold axiom_of_universal_specification at h
      -- Для фиксированных множеств `A, B` возьмём `P (z) : ⇐⇒ (z ∈ A ∨ z ∈ B)`.
      set P : Object → Prop := fun z ↦ z ∈ A ∨ z ∈ B
      -- По аксиоме универсальной спецификации найдётся множество `Z` такое,
      -- что для всякого `z` выполняется `z ∈ Z ⇐⇒ (z ∈ A ∨ z ∈ B)`.
      specialize h P
      obtain ⟨Z, h⟩ := h
      unfold P at h
      -- Это и есть искомое объединение `A ∪ B`.
      exact ⟨Z, h⟩

/--
Exercise 3.2.1

```
theorem SetTheory.Set.specification_axiom''
  {A : Set} (P : A → Prop) (x : Object) :
    x ∈ A.specify P ↔ ∃ h : x ∈ A, P ⟨x, h⟩ := by
```
-/
theorem SetTheory.Set.specify_exists
  (h : axiom_of_universal_specification) (A : Set) (P : A → Prop) :
    ∃ (Z : Set), ∀ z, z ∈ Z ↔ ∃ h : z ∈ A, P ⟨z, h⟩ := by
      unfold axiom_of_universal_specification at h
      -- Для фиксированных `A, P` возьмём `Q z := ∃ h : z ∈ A, P ⟨z, h⟩`.
      set Q : Object → Prop := fun z ↦ ∃ h : z ∈ A, P ⟨z, h⟩
      specialize h Q
      obtain ⟨Z, hZ⟩ := h
      unfold Q at hZ
      exact ⟨Z, hZ⟩

/-- Exercise 3.2.1 -/
theorem SetTheory.Set.replace_exists (h : axiom_of_universal_specification) (A : Set)
  (P : A → Object → Prop) (_hP : ∀ x y y', P x y ∧ P x y' → y = y') :
    ∃ (Z : Set), ∀ y, y ∈ Z ↔ ∃ a : A, P a y := by
      unfold axiom_of_universal_specification at h
      set Q : Object → Prop := fun y ↦ ∃ (a : A), P a y
      -- Ну значит существует и такое множество `A`,
      -- для которого выполняется `x ∈ A ↔ Q x`
      specialize h Q
      obtain ⟨Z, hz⟩ := h
      unfold Q at hz
      use Z

/--
Exercise 3.2.2 (no set contains itself).

Используйте аксиому регулярности и аксиому одноэлементного множества,
чтобы показать, что если A — множество, то A ∉ A.

Из‑за отсутствия аннотаций, доказательствo и контекст
читается и понимается сложнее, чем обычно.
-/
theorem SetTheory.Set.not_mem_self (A : Set) : (A : Object) ∉ A := by
  intro h
  -- Строим одноэлементное множество `SA = {A}`,
  -- к которому применим аксиому регулярности.
  set SA : Set := {(A : Object)}
  -- mem_singleton : (x a : Object) : x ∈ {a} ↔ x = a
  have hsa := (mem_singleton A A).mpr -- : A = A → A ∈ {A}
  -- `SA` непусто: оно содержит сам `A` (это следует из `A = A` по `rfl`).
  have hmemA : (A : Object) ∈ SA := hsa /- A = A -/ rfl -- A ∈ {A}
  -- regularity_axiom
  --   (A : Set) (hA : ∃ x, x ∈ A) :
  --     ∃ x, x ∈ A ∧ ∀ (S : Set), x = S → ¬∃ y, y ∈ A ∧ y ∈ S
  have hr := regularity_axiom SA ⟨(A : Object), hmemA⟩
  -- Аксиома регулярности к непустому `SA` даёт элемент `x ∈ SA`, для которого,
  -- если `x` — само множество `S`, то `S` и `SA` не имеют общих элементов.
  obtain ⟨x, ⟨hxa, h'⟩⟩ := hr
  -- Единственный элемент `SA` — это `A`, поэтому `x = A`.
  have hxA : x = (A : Object) := (mem_singleton x A).mp hxa
  -- Подставляем `S := A` (пользуясь `x = A`): получаем, что `A` и `SA` не пересекаются.
  specialize h' A hxA
  -- Но `A` лежит и в `SA` (это `hmemA`), и в самом себе (это исходное `h`) —
  -- значит, `A` является их общим элементом, что противоречит предыдущему шагу.
  have hcommon : ∃ y, y ∈ SA ∧ y ∈ A := ⟨(A : Object), hmemA, h⟩
  -- exact h' hcommon
  contradiction

/--
Exercise 3.2.2 (no two sets contain each other).

Кроме того, покажите, что если A и B — два множества,
то либо A ∉ B, либо B ∉ A, либо оба условия одновременно.
-/
theorem SetTheory.Set.not_mem_mem (A B : Set) : (A : Object) ∉ B ∨ (B : Object) ∉ A := by
  -- От противного: предполагаем, что оба условия нарушены сразу,
  -- т.е. `A ∈ B` и `B ∈ A` одновременно (`by_contra!` сразу протаскивает `push_neg`).
  by_contra! h
  obtain ⟨hAB, hBA⟩ := h
  -- Строим пару `P = {A, B}`, к которой применим аксиому регулярности.
  set P : Set := {(A : Object), (B : Object)}
  -- mem_pair : (x a b : Object) : x ∈ {a, b} ↔ x = a ∨ x = b
  have hmemA : (A : Object) ∈ P := (mem_pair A A B).mpr (Or.inl rfl)
  have hmemB : (B : Object) ∈ P := (mem_pair B A B).mpr (Or.inr rfl)
  -- `P` непусто: оно содержит `A`. Аксиома регулярности даёт элемент `x ∈ P`, для которого,
  -- если `x` — само множество `S`, то `S` и `P` не имеют общих элементов.
  -- (A : Set) (hA : ∃ x, x ∈ A) :
  --   ∃ x, x ∈ A ∧ ∀ (S : Set), x = S → ¬∃ y, y ∈ A ∧ y ∈ S
  have hr := regularity_axiom P ⟨(A : Object), hmemA⟩
  obtain ⟨x, hxP, h'⟩ := hr
  -- Единственные элементы `P` — это `A` и `B`, значит `x = A` или `x = B`.
  rcases (mem_pair x A B).mp hxP with hxA | hxB
  · -- Случай `x = A`: подставляем `S := A` и получаем, что `A` и `P` не пересекаются.
    specialize h' A hxA
    -- Но `B` лежит и в `A` (это `hBA`), и в `P` (это `hmemB`) —
    -- значит, `B` является их общим элементом, что противоречит предыдущему шагу.
    exact h' ⟨(B : Object), hmemB, hBA⟩
  · -- Случай `x = B`: подставляем `S := B` и получаем, что `B` и `P` не пересекаются.
    specialize h' B hxB
    -- Но `A` лежит и в `B` (это `hAB`), и в `P` (это `hmemA`) —
    -- значит, `A` является их общим элементом, что противоречит предыдущему шагу.
    exact h' ⟨(A : Object), hmemA, hAB⟩

/-- Exercise 3.2.3 (universal specification) -/
theorem SetTheory.Set.univ_iff : axiom_of_universal_specification ↔
  ∃ (U : Set), ∀ x, x ∈ U := by sorry

/-- Exercise 3.2.3 (there is no universal set) -/
theorem SetTheory.Set.no_univ : ¬ ∃ (U : Set), ∀ (x : Object), x ∈ U := by sorry


end Chapter3
