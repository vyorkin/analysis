import Mathlib.Tactic
import Analysis.Section_3_1

/-!
# Analysis I, раздел 3.4: Образы и прообразы

Я старался сделать перевод максимально точным перефразированием оригинального текста. Когда
приходилось выбирать между более идиоматичным Lean-решением и более точным переводом, я, как
правило, выбирал второе. В частности, местами Lean-код можно было бы "заголфить", сделав его более
элегантным и идиоматичным, но я сознательно этого избегал.

Основные конструкции и результаты этого раздела:

- Образы и прообразы функций (из Mathlib) в рамках теории множеств из раздела 3.1.
  (Функции из раздела 3.3 теперь устарели и далее использоваться не будут.)
- Связь с понятиями образа {syntax term}`f '' S` и прообраза {syntax term}`f ⁻¹' S` из Mathlib.

## Советы от прошлых пользователей

Пользователи, прошедшие упражнения этого раздела, могут присылать свои советы для будущих
пользователей в виде PR.

- (Добавьте совет сюда)

-/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

/--
Определение 3.4.1:
Формулируется определение образа через аксиому замены с предикатом вот такого вида.
Не требует, чтобы {lean}`S` было подмножеством {lean}`X`.
-/
-- Определение не требует `S ⊆ X`.
-- В образ попадают только те `x ∈ S`, которые заодно лежат и в `X`.
-- В этом легко убедиться, посмотрев на определение
-- аксиомы замены/подстановки (`SetTheory.replace`):
--
-- `replace X (P : Subtype (mem . X) → Object → Prop) (hp : ...) : Set`
--                          ^^^^^^^
-- Элементы `S` вне области определения `f` в построении образа не участвуют.
abbrev SetTheory.Set.image {X Y : Set} (f : X → Y) (S : Set) : Set :=
  X.replace (P := fun x y ↦ f x = y ∧ x.val ∈ S) (by
    -- Чтобы "доказать" эту подстановку с таким предикатом `P`
    -- требуется просто показать функциональность/однозначность этого отношения:
    -- `hp: ∀ x y y', P x y ∧ P x y' → y = y'`
    -- (каждому `x` он сопоставляет не более одного `y`).
    -- Итак требуется доказать посылку аксиомы замены/подстановки.
    -- Можно было бы сделать просто вот так:
    -- simp_all
    -- Но это не наш способ %)
    intro x y y' h
    obtain ⟨h₁, h₂⟩ := h
    -- Надо показать, что это один и тот же `y`:
    show y = y'
    guard_hyp h₁ : ↑(f x) = y  ∧ ↑x ∈ S
    guard_hyp h₂ : ↑(f x) = y' ∧ ↑x ∈ S
    -- Обе части конъюнкции в гипотезах говорят,
    -- что соответствующий `y` — это `f x`.
    obtain ⟨hy,  _⟩ := h₁
    obtain ⟨hy', _⟩ := h₂
    -- Поэтому оба значения совпадают с `f x`, а значит и друг с другом.
    rw [← hy, ← hy'])

/-- Определение 3.4.1 -/
-- По сути, здесь с двух сторон написано ровно одно и то же,
-- лишь конъюнкты поменены местами.
theorem SetTheory.Set.mem_image {X Y : Set} (f : X → Y) (S : Set) (y : Object) :
  y ∈ image f S ↔ ∃ x : X, x.val ∈ S ∧ f x = y := by
    grind [replacement_axiom]

-- Тот же результат, что и `mem_image`,
-- но доказан явно через `rw` и `constructor`.
theorem SetTheory.Set.mem_image' {X Y : Set} (f : X → Y) (S : Set) (y : Object) :
  y ∈ image f S ↔ ∃ x : X, x.val ∈ S ∧ f x = y := by
    rw [image]
    -- (hP : ∀ (x : A.toSubtype)
    -- (y y' : Object), P x y ∧ P x y' → y = y')
    -- (y : Object)
    -- : y ∈ A.replace hP ↔ ∃ x, P x y
    rw [replacement_axiom]
    constructor
    · rintro ⟨x, hx, hS⟩
      exact ⟨x, hS, hx⟩
    · rintro ⟨x, hS, hx⟩
      exact ⟨x, hx, hS⟩

/-- Альтернативное определение образа через аксиому спецификации. -/
theorem SetTheory.Set.image_eq_specify {X Y : Set} (f : X → Y) (S : Set) :
  image f S = Y.specify (fun y ↦ ∃ x : X, x.val ∈ S ∧ f x = y) := by
    ext y
    -- `x ∈ A.specify P ↔ ∃ (h : x ∈ A), P ⟨x, h⟩`,
    -- а `Subtype.coe_eq_iff` как раз превращает равенство
    -- `↑(f x) = y` (в `Object`) в такую же экзистенцию по `h`
    rw [specification_axiom'', mem_image]
    simp only [Subtype.coe_eq_iff]
    tauto

-- Моё странное доказательство.
theorem SetTheory.Set.image_eq_specify' {X Y : Set} (f : X → Y) (S : Set) :
  image f S = Y.specify (fun y ↦ ∃ x : X, x.val ∈ S ∧ f x = y) := by
    ext y
    rw [specification_axiom''] -- x ∈ A.specify P ↔ ∃ (h : x ∈ A), P ⟨x, h⟩
    constructor
    · unfold image
      rw [replacement_axiom] -- y ∈ A.replace hP ↔ ∃ x, P x y
      rintro ⟨x, ⟨hfx, hsx⟩⟩
      refine ⟨?_, x, hsx, ?_⟩
      · subst hfx
        have ⟨y, hy⟩ := f x
        exact hy
      · subst hfx
        rfl
    · unfold image
      rw [replacement_axiom]
      rintro ⟨y', ⟨x, hx⟩⟩
      obtain ⟨hxs, hfx⟩ := hx
      refine ⟨x, ⟨?_, hxs⟩⟩
      rw [hfx]

/--
  Связь с понятием образа из Mathlib.
  Обратите внимание на необходимость приведения {name}`Subtype.val`,
  чтобы согласовать типы.
-/
-- Здесь `X → Y` на самом деле означает `X.toSubtype → Y.toSubtype`
-- (это работает через инстанс `CoeSort Set (Type v)`),
-- то есть `f: X → Y` действует не на `Object`, а на подтипах
-- `{x : Object // x ∈ X}` и `{y : Object // y ∈ Y}`.
--
-- `S : Set` — произвольное множество, необязательно подмножество `X`.
-- Элементы `S`, не лежащие в `X`, просто не участвуют в образе,
-- так как `f` к ним неприменима.
--
-- `image f S` (левая часть) — это наш образ из Определения 3.4.1,
-- построенный через аксиому замены. Он сам имеет тип `Set`,
-- поэтому, чтобы сравнить его с Mathlib-множеством,
-- его нужно явно привести к `_root_.Set Object` —
-- это и делает аннотация `(image f S : _root_.Set Object)`
-- (через инстанс `Coe Set (_root_.Set Object)`).
--
-- Правая часть строится целиком средствами Mathlib:
-- `{x | x.val ∈ S}` — это те `x : X.toSubtype`, чьё значение `x.val` лежит в `S`
-- (по сути пересечение `S` с `X`, выраженное как подмножество подтипа `X.toSubtype`)
-- `f '' (...)` — обычный Mathlib-образ этого множества,
-- лежащий уже в `_root_.Set Y.toSubtype`,
-- то есть это множество пар `⟨y, доказательство того что y ∈ Y⟩`.
--
-- `Subtype.val '' (...)` берёт каждую такую пару и оставляет только `y`,
-- выбрасывая доказательство. По определению:
-- `Set.image`, `g '' T = {b | ∃ a ∈ T, g a = b}`,
-- поэтому при `g := Subtype.val` это разворачивается в
-- `b ∈ Subtype.val '' T ↔ ∃ (h : b ∈ Y), ⟨b, h⟩ ∈ T`.
-- Так множество пар `_root_.Set Y.toSubtype` превращается в множество голых объектов
-- `_root_.Set Object`, с которым уже можно сравнивать левую часть.
--
-- Итак:
-- Теорема говорит, что наш образ (после приведения к Mathlib-множеству) —
-- это то же самое, что образ, вычисленный целиком в терминах Mathlib,
-- если предварительно ограничить `S` элементами, которые вообще лежат в `X`.
theorem SetTheory.Set.image_eq_image {X Y : Set} (f : X → Y) (S : Set) :
  (image f S : _root_.Set Object) = Subtype.val '' (f '' {x | x.val ∈ S}) := by
    ext
    simp
    grind

/--
  Образ {lean}`image f S` (при любом {lean}`S`) лежит
  в области значений {lean}`f`, то есть {lean}`image f S ⊆ Y`.
-/
theorem SetTheory.Set.image_in_codomain {X Y : Set}
  (f : X → Y) (S : Set) : image f S ⊆ Y := by
    intro _ h
    rw [mem_image] at h
    grind

-- Тот же результат, что и `image_in_codomain`, но доказан явно, без `grind`
theorem SetTheory.Set.image_in_codomain' {X Y : Set}
  (f : X → Y) (S : Set) : image f S ⊆ Y := by
    intro y h
    rw [mem_image] at h
    -- `h : ∃ x : X, x.val ∈ S ∧ f x = y` — раскрываем существование
    obtain ⟨x, _, hfx⟩ := h
    -- `hfx : ↑(f x) = y`, поэтому цель `y ∈ Y` переписывается в `↑(f x) ∈ Y`
    rw [← hfx]
    -- А это в точности то, что утверждает
    -- второй компонент подтипа `f x : Y.toSubtype`
    obtain ⟨y, hy⟩ := f x
    exact hy

/-- Пример 3.4.2 -/
abbrev f_3_4_2 : nat → nat := fun n ↦ (2*n : ℕ)

-- Конкретное вычисление:
-- образ `{1,2,3}` под удвоением `f_3_4_2` — это `{2,4,6}`.
theorem SetTheory.Set.image_f_3_4_2 : image f_3_4_2 {1,2,3} = {2,4,6} := by
  ext y
  rw [mem_image] -- y ∈ image f S ↔ ∃ x, ↑x ∈ S ∧ ↑(f x) = y
  unfold f_3_4_2
  simp only [mem_triple]
  constructor
  · -- `rfl` в паттерне сразу подставляет равенство `f x₁ = y`
    rintro ⟨_, (_ | _ | _), rfl⟩ <;> simp_all
  · rintro (_ | _ | _)
    -- в отличие от `<;>`, `map_tacs` применяет
    -- к каждой из трёх целей свою тактику по порядку
    map_tacs [use 1; use 2; use 3]
    all_goals simp_all

-- Та же теорема, что и `image_f_3_4_2`,
-- но без комбинаторов вроде `rintro (_ | _ | _)` и `map_tacs`:
-- все шесть случаев (три в каждую сторону) расписаны отдельно, для наглядности
theorem SetTheory.Set.image_f_3_4_2' : image f_3_4_2 {1,2,3} = {2,4,6} := by
  ext y
  rw [mem_image]
  unfold f_3_4_2
  simp only [mem_triple]
  constructor
  · intro h
    obtain ⟨x, hx, hfx⟩ := h
    rcases hx with hx | hx | hx
    · simp_all
    · simp_all
    · simp_all
  · intro h
    rcases h with h | h | h
    · exact ⟨1, by simp_all, by simp_all⟩
    · exact ⟨2, by simp_all, by simp_all⟩
    · exact ⟨3, by simp_all, by simp_all⟩

-- И ещё более подробно тоже самое.
theorem SetTheory.Set.image_f_3_4_2'' : image f_3_4_2 {1,2,3} = {2,4,6} := by
  ext y
  rw [mem_image]
  unfold f_3_4_2
  simp only [mem_triple]
  constructor
  · intro h
    obtain ⟨x, hx, hfx⟩ := h
    rcases hx with hx | hx | hx
    · -- `nat_coe_eq_iff'` переводит равенство объектов `↑x = 1`
      -- в равенство обычных чисел `(x : ℕ) = 1`
      have hx' : nat_equiv.symm x = 1 := nat_coe_eq_iff'.mp hx
      rw [hx'] at hfx
      left
      -- `norm_num` сворачивает `2 * 1` до `2`
      -- и снимает двойное приведение `↑↑` до `↑2`
      norm_num at hfx
      exact hfx.symm
    · have hx' : nat_equiv.symm x = 2 := nat_coe_eq_iff'.mp hx
      rw [hx'] at hfx
      right; left
      norm_num at hfx
      exact hfx.symm
    · have hx' : nat_equiv.symm x = 3 := nat_coe_eq_iff'.mp hx
      rw [hx'] at hfx
      right; right
      norm_num at hfx
      exact hfx.symm
  · intro h
    rcases h with h | h | h
    · exact ⟨1, Or.inl rfl, by rw [h]; norm_num⟩
    · exact ⟨2, Or.inr (Or.inl rfl), by rw [h]; norm_num⟩
    · exact ⟨3, Or.inr (Or.inr rfl), by rw [h]; norm_num⟩

/-- Пример 3.4.3 записан с использованием понятия образа из Mathlib. -/
-- Пусть ℤ – множество целых чисел (которое мы определим строго в следующем разделе).
-- И пусть `f : ℤ → ℤ` – отображение `f(x) = x^2`,
-- тогда `f({-1, 0, 1, 2}) = {0, 1, 4}`
--
-- Заметим, что `f` не является инъекцией, так как `f(-1) = f(1)`, но `-1 ≠ 1`.
--
example : (fun n : ℤ ↦ n^2) '' {-1,0,1,2} = {0,1,4} := by
  -- aesop
  ext y
  constructor
  · rw [Set.mem_image] -- y ∈ f '' s ↔ ∃ x ∈ s, f x = y
    rintro ⟨x, hx, rfl⟩
    rcases hx with rfl | rfl | rfl | rfl
    · right; left; norm_num
    · left; norm_num
    · right; left; norm_num
    · right; right; norm_num
  · rw [Set.mem_image]
    intro hy
    rcases hy with rfl | rfl | rfl
    · use 0
      constructor
      · right; left; rfl
      · ring
    · use 1
      constructor
      · right; right; left; rfl
      · ring
    · use 2
      constructor
      · right; right; right; rfl
      · ring

-- Прямое направление `mem_image`:
-- если `x ∈ S`, то `f x` лежит в образе `image f S`.
theorem SetTheory.Set.mem_image_of_eval {X Y : Set} (f : X → Y) (S : Set) (x : X) :
  x.val ∈ S → (f x).val ∈ image f S := by
    intro hxs
    rw [mem_image] -- y ∈ image f S ↔ ∃ x, ↑x ∈ S ∧ ↑(f x) = y
    use x

-- Понятно, что теорема выше вернa: `x ∈ S → f(x) ∈ f(S)`
-- А вот уже такая импликация в общем случае не верна:
-- `f(x) ∈ f(S) → x ∈ S`
-- Ровно это и написано в формулировке теоремы ниже:
-- `¬((f x).val ∈ image f S → x.val ∈ S)`
--
-- Область значений (образ) функции, может быть уже,
-- чем область определения.
--
-- Например для `f : X → Y`:
-- `X = {-1, 0, 1, 2}`
-- `Y = {0, 1, 4}` (заметь, что здесь на один элемент меньше)
-- `4 = f(-2)` лежит в `Y`, но
-- `-2` не лежит в `X`

/--
Контрпример к обратному направлению:
{lit}`f x ∈ image f S` не гарантирует {lit}`x ∈ S`.
-/
theorem SetTheory.Set.mem_image_of_eval_counter :
  ∃ (X Y : Set) (f : X → Y) (S : Set) (x : X),
    ¬((f x).val ∈ image f S → x.val ∈ S) := by
      -- Чтобы это показать, подойдет любая неинъективная функция.
      -- Она-то уж точно гарантирует, что образ
      -- будет содержать меньшее количество элементов,
      -- чем прообраз (по определению (не)инъективности).
      --
      -- Пусть образ будет содержать ровно один элемент,
      -- а для области определения возьмем множество из двух элементов.
      --
      -- Короче, построим такую функцию:
      -- f : {1, 2} → {1}
      set X : Set := {1, 2}
      set Y : Set := {1}
      -- Какое-то подмножество X: S ⊆ X : {2} ⊆ {1, 2}
      set S : Set := {2}
      --
      have hx : 1 ∈ X := by simp [X]
      have hy : 1 ∈ Y := by simp [Y]
      -- Константная неинъективная функция:
      -- Отображает все в один элемент – `1`.
      set f : X → Y := fun _ ↦ (⟨1, hy⟩ : Y)
      -- В качестве исходного элемента `x ∈ X` возьмем `1`.
      set x : X := ⟨1, hx⟩
      --
      -- Теперь покажем, что для этих выбранных нами `X, Y, S, f`:
      --
      -- если `f x ∈ image f S`,     то `x ∉ S`    (`x := 1, S := {2}`)
      -- т.е. `f 1 ∈ image f ({2})`, то `1 ∉ {2}`  (`f _ := 1`)
      --        `1 ∈ {1}`,           то `1 ∉ {2}`
      --
      use X, Y, f, S, x
      --
      -- Попробуем прийти к противоречию:
      --
      -- Раскроем определение образa.
      rw [mem_image] -- y ∈ image f S ↔ ∃ x, ↑x ∈ S ∧ ↑(f x) = y
      -- Сразу же переименуем `x_1` в `s` – так будет легче читаться.
      intro h; rename_bvar x → s at h
      unfold S at h
      --
      -- Смысл `h`:
      -- если найдётся элемент `s`, лежащий в `S = {2}`
      -- и дающий то же значение, что и `f x`,
      -- то `x ∈ {2} → x = 2`, но `x = 1`.
      -- То есть мы знаем, что это ложно: `(x.val = 1) ∉ {2}`).
      -- Значит нужно предъявить такого свидетеля.
      --
      rw [mem_singleton] at h
      -- Свидетель — сам элемент `2`: он лежит и в `X`, и в `S`,
      have hx2 : 2 ∈ X := by simp [X]
      have hs2 : 2 ∈ S := by simp [S]
      -- `f` – константнaя функция,
      -- так что `f 2` = `f x` по `rfl`.
      have heq : (f ⟨2, hx2⟩).val = (f x).val := rfl
      have hex : ∃ s, s.val ∈ S ∧ (f s).val = (f x).val :=
        ⟨⟨2, hx2⟩, hs2, heq⟩
      have hcontra : x.val = 2 := h hex
      -- Имеем hcontra : x = 2, но x = 1 по предположению выше.
      -- Противоречие.
      simp [x] at hcontra

/--
  Определение 3.4.4 (прообраз функции).
  Здесь также не требуется, чтобы {lean}`U` было подмножеством {lean}`Y`.
-/
abbrev SetTheory.Set.preimage {X Y : Set} (f : X → Y) (U : Set) : Set :=
  X.specify (P := fun x ↦ (f x).val ∈ U)

/--
Элемент {lit}`x : X` попадает в прообраз {lit}`preimage f U`
тогда и только тогда, когда {lit}`f x ∈ U`.
-/
@[simp]
theorem SetTheory.Set.mem_preimage {X Y : Set}
  (f : X → Y) (U : Set) (x : X) :
    x.val ∈ preimage f U ↔ (f x).val ∈ U :=
      by rw [specification_axiom'] -- ↑x ∈ A.specify P ↔ P x

/--
  Версия {name}`mem_preimage` для произвольного {lean}`x : Object`:
  принадлежность {lean}`x` множеству {lean}`X` не предполагается заранее
  (в отличие от {name}`mem_preimage`, где это указано в параметрe {lean}`x : X`),
  а выражена внутри самого утверждения через {lean}`∃ x' : X, x'.val = x`.
-/
theorem SetTheory.Set.mem_preimage'
    {X Y : Set} (f : X → Y) (U : Set) (x : Object) :
  x ∈ preimage f U ↔ ∃ x' : X, x'.val = x ∧ (f x').val ∈ U := by
    constructor
    . intro h
      by_cases hx : x ∈ X
      . use ⟨x, hx⟩
        have := mem_preimage f U ⟨_, hx⟩
        simp_all
      . grind [specification_axiom]
    . rintro ⟨x', rfl, hfx'⟩
      rwa [mem_preimage]

-- Тот же результат, что и `mem_preimage'`, но доказан без `simp_all`/`grind`
theorem SetTheory.Set.mem_preimage''
    {X Y : Set} (f : X → Y) (U : Set) (x : Object) :
  x ∈ preimage f U ↔ ∃ x' : X, x'.val = x ∧ (f x').val ∈ U := by
    constructor
    · intro h
      -- `preimage f U` — это `X.specify P`
      unfold preimage at h
      --
      -- `specification_axiom` говорит, что
      -- специфицированнoe/отфильтрованнoe/выделенное множество
      -- всегда является подмножеством исходного множества.
      --
      -- Значит из `h : x ∈ preimage f U` сразу следует `x ∈ X`.
      -- (h : x ∈ A.specify P) : x ∈ A
      have hx : x ∈ X := specification_axiom h
      -- Раз есть доказательство `hx`, можно собрать элемент `⟨x, hx⟩ : X`
      -- и предъявить его как свидетеля для `∃ x' : X, ...`.
      use ⟨x, hx⟩
      use rfl -- x = x → (↑⟨x, hx⟩ = x)
      --
      -- Осталось показать `(f ⟨x, hx⟩).val ∈ U`.
      --
      -- Это в точности `mem_preimage`, применённая к `⟨x, hx⟩ : X`.
      have hfxu := mem_preimage f U ⟨x, hx⟩ -- ↑x ∈ preimage f U ↔ ↑(f x) ∈ U
      --
      unfold preimage at hfxu
      exact hfxu.mp h
    · rintro ⟨x', rfl, hfx'⟩
      -- Здесь `rfl` в паттерне уже заменил `x` на `x'.val`,
      -- поэтому осталось применить `mem_preimage` в обратную сторону.
      have hfxu := mem_preimage f U x'
      exact hfxu.mpr hfx'

/-- Связь с понятием прообраза из Mathlib. -/
theorem SetTheory.Set.preimage_eq {X Y : Set} (f : X → Y) (U : Set) :
  ((preimage f U) : _root_.Set Object) = Subtype.val '' (f⁻¹' {y | y.val ∈ U}) := by
    -- Слева — наш `preimage f U : Set`, приведённый к Mathlib-множеству через
    -- `inst_coe_set` (по определению `(X : _root_.Set Object) = {x | x ∈ X}`).
    -- Справа — Mathlib-прообраз `{y | y.val ∈ U}` под `f : X.toSubtype → Y.toSubtype`,
    -- перенесённый обратно из подтипа `X.toSubtype` в `Object` через `Subtype.val ''`.
    --
    -- Обе стороны — множества элементов типа `Object`, поэтому `ext` сводит
    -- равенство множеств к поэлементной эквивалентности для произвольного `x : Object`:
    --   x ∈ preimage f U  ↔  x ∈ Subtype.val '' (f⁻¹' {y | y.val ∈ U})
    ext
    -- `simp` разворачивает обе стороны до одной и той же экзистенциальной формы:
    --  * слева `specification_axiom''` превращает `x ∈ preimage f U`
    --    в `∃ h : x ∈ X, (f ⟨x, h⟩).val ∈ U`;
    --  * справа `Set.preimage_setOf_eq` и `Set.mem_image` превращают
    --    `x ∈ Subtype.val '' (f⁻¹' {y | y.val ∈ U})`
    --    в `∃ x' : X, (f x').val ∈ U ∧ x'.val = x`;
    --  * `Subtype.exists` расщепляет свидетеля `x' : X` на пару
    --    `(a : Object, h : a ∈ X)`, а `exists_and_right`/`exists_eq_right`
    --    используют равенство `a = x`, чтобы подставить `a := x`
    --    и убрать лишний экзистенциал.
    -- После этого обе стороны буквально совпадают: `∃ h : x ∈ X, (f ⟨x, h⟩).val ∈ U`,
    -- и `simp` закрывает цель через `Iff.rfl`.
    simp

/-- Прообраз {lit}`preimage f U` целиком лежит в области определения {lit}`X`. -/
-- Это верно просто по определению прообраза и спецификации:
-- `preimage f U` это все такие `х ∈ Х`, что `(f x) ∈ U`.
-- Отсюда можно получить доказательствo `х ∈ Х`.
theorem SetTheory.Set.preimage_in_domain {X Y : Set} (f : X → Y) (U : Set) :
  (preimage f U) ⊆ X := by
    intro x h
    unfold preimage at h
    -- x ∈ A.specify P ↔ ∃ (h : x ∈ A), P ⟨x, h⟩
    simp_all only [specification_axiom'']
    obtain ⟨hx, _⟩ := h
    exact hx

/-- Пример 3.4.6. -/
-- Если `f : ℕ → ℕ` отображение `f(x) = 2*x`, то `f({1,2,3}) = {2,4,6}`.
theorem SetTheory.Set.preimage_f_3_4_2 : preimage f_3_4_2 {2,4,6} = {1,2,3} := by
  ext
  simp only [mem_preimage', mem_triple, f_3_4_2]
  constructor
  · rintro ⟨x, rfl, (_ | _ | _)⟩ <;> simp_all <;> omega
  · rintro (rfl | rfl | rfl)
    map_tacs [use 1; use 2; use 3]
    all_goals simp

-- Для `f(x) = 2*x` мы видим, что `f⁻¹({1, 2, 3}) = {1}`.
--
-- Прообраз `f⁻¹({1,2,3})` — это все такие `x`,
-- для которых `f(x) ∈ {1,2,3}`,
-- то есть все `x`, для которых `2*x ∈ {1,2,3}`:
-- `2*x = 1` — нет решения среди натуральных чисел;
-- `2*x = 2` — `x = 1`;
-- `2*x = 3` — нет решения (3 нечётно).
--
-- Единственный подходящий `x` — это 1, поэтому `f⁻¹({1,2,3}) = {1}`.
--
-- Таким образом образ и прообраз это два совершенно разных множества.
--
-- Конкретный пример: `f_3_4_2 : n ↦ 2*n`.
-- Образ прообраза `{1,2,3}` под `f_3_4_2` не восстанавливает `{1,2,3}`,
-- поскольку `f_3_4_2` не сюръективна.
theorem SetTheory.Set.image_preimage_f_3_4_2 :
  image f_3_4_2 (preimage f_3_4_2 {1,2,3}) ≠ {1,2,3} := by
    -- `f_3_4_2 : n ↦ 2*n`
    -- Достаточно предъявить число `3`.
    -- Оно лежит в `{1,2,3}`, но не может лежать в образе,
    -- потому что `f_3_4_2 x = 2*x` всегда чётно, а `3` нечётно.
    intro h
    rw [Set.ext_iff] at h
    obtain ⟨h₀, h₁⟩ := h 3
    have hmem : 3 ∈ ({1,2,3} : Set) := by simp
    specialize h₁ hmem
    -- (f : X.toSubtype → Y.toSubtype)
    -- (S : Set)
    -- (y : Object)
    -- : y ∈ image f S ↔ ∃ x, ↑x ∈ S ∧ ↑(f x) = y
    obtain ⟨x, hx, hfx⟩ := (mem_image f_3_4_2 _ 3).mp h₁
    -- где _ := (preimage f_3_4_2 {1,2,3})
    unfold f_3_4_2 at hfx
    -- Снимаем коэрции:
    -- `hfx` превращается в чистое `2 * nat_equiv.symm x = 3`.
    simp at hfx
    -- Можно использовать `omega` - она сразу увидит,
    -- что такого `x` не существует.
    --
    -- Альтернативный (более ясный) способ:
    -- Любое кратное 2 даёт остаток 0 при делении на 2.
    have heven : (2 * nat_equiv.symm x) % 2 = 0 :=
      -- Nat.mul_mod_right (m n : ℕ) : m * n % m = 0
      Nat.mul_mod_right 2 x
    -- У нас есть утверждение, что "3 кратно 2".
    -- Значит и остаток от деления 3 на 2 равен 0.
    -- Подставляет `hfx : 2 * nat_equiv.symm x = 3`,
    -- превращая `heven` в `3 % 2 = 0`.
    rw [hfx] at heven
    -- Но `3` даёт остаток `1` при делении на `2`, то есть не `0`.
    have hodd : (3 : ℕ) % 2 ≠ 0 := by norm_num
    -- `heven : 3 % 2 = 0` противоречит `hodd: 3 % 2 ≠ 0`.
    contradiction

/-- Пример 3.4.7 (с использованием понятия прообраза из Mathlib) -/
-- Нотация ⁻¹' это preimage (прообраз)
example : (fun n : ℤ ↦ n^2) ⁻¹' {0,1,4} = {-2,-1,0,1,2} := by
  ext x
  -- Цель — эквивалентность `x ∈ f⁻¹'{0,1,4} ↔ x ∈ {-2,-1,0,1,2}`.
  -- `Iff` — это структура из двух полей (`mp` и `mpr`), поэтому анонимный
  -- конструктор `⟨_, _⟩` даёт по отдельному доказательству на каждое направление.
  -- Второе поле (обратное направление, `mpr`) сразу же закрывается вложенным
  -- `by aesop` — эта часть доказательства не видна в состоянии цели, так как
  -- решается целиком внутри самого `refine`.
  -- Первое поле оставлено как `?_` — именно оно становится новой целью,
  -- поэтому кажется, что `refine` просто заменил `↔` на `→`
  -- (на самом деле было два доказательства, но одно из них скрыто).
  refine ⟨?_, by aesop⟩
  -- Гипотеза `x ∈ {0,1,4}` разворачивается в `x=0 ∨ x=1 ∨ x=4`,
  -- `rintro (_ | _ | h)` вводит её и сразу разбирает на 3 случая.
  -- Имя `h` даём только третьему случаю (`x^2 = 4`) — он единственный,
  -- где явное рассуждение понадобится ниже; остальные два `aesop`
  -- закрывает сам, используя `pow_eq_zero_iff`/`sq_eq_one_iff_of_ne_neg_one`
  -- (или аналогичные simp-леммы) из своего набора.
  rintro (_ | _ | h)
  on_goal 3 =>
    -- `4` не распознаётся автоматически как `2^2`,
    -- поэтому нужный simp-факт вручную не сработает — приходится
    -- явно подставить `2^2 = 4`, чтобы применить `sq_eq_sq_iff_eq_or_eq_neg`.
    have : 2 ^ 2 = (4 : ℤ) := (by norm_num)
    rw [←h, sq_eq_sq_iff_eq_or_eq_neg] at this
  -- `all_goals aesop` закрывает все 3 оставшиеся цели:
  -- в первых двух случаях (`x^2=0`, `x^2=1`) — как и раньше, за счёт simp-лемм,
  -- в третьем — используя `this : 2 = x ∨ 2 = -x`, добавленное выше.
  all_goals aesop

/-- То же утверждение, но без тактики {lit}`aesop` — каждый шаг сделан явным. -/
example : (fun n : ℤ ↦ n^2) ⁻¹' {0,1,4} = {-2,-1,0,1,2} := by
  ext x
  constructor
  · rintro (h | h | h)
    · -- x^2 = 0 ⇒ x = 0
      have h0 : (0 : ℤ) ^ 2 = 0 := by ring
      have hsq : x ^ 2 = 0 ^ 2 := by rw [h0]; exact h
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h' | h' <;> tauto
    · -- x^2 = 1 ⇒ x = 1 ∨ x = -1
      have h1 : (1 : ℤ) ^ 2 = 1 := by ring
      have hsq : x ^ 2 = 1 ^ 2 := by rw [h1]; exact h
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h' | h' <;> tauto
    · -- x^2 = 4 ⇒ x = 2 ∨ x = -2
      have h2 : (2 : ℤ) ^ 2 = 4 := by ring
      have hsq : x ^ 2 = 2 ^ 2 := by rw [h2]; exact h
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h' | h' <;> tauto
  · -- Обратное направление:
    -- подставляем каждое конкретное значение и считаем квадрат.
    rintro (h | h | h | h | h) <;> rw [h] <;> norm_num

example : (fun n : ℤ ↦ n^2) ⁻¹' ((fun n : ℤ ↦ n^2) '' {-1,0,1,2}) ≠ {-1,0,1,2} := by
  sorry

-- Делает нотацию степени доступной и задает для нее интерпретацию.
instance SetTheory.Set.inst_pow : Pow Set Set where
  -- Наше `pow X Y` — это множество, обозначаемое в книге `X^Y`,
  -- состоящее из ВСЕХ функций из `Y` в `X`.
  pow := pow

@[coe]
def SetTheory.Set.coe_of_fun {X Y : Set} (f : X → Y) : Object :=
  function_to_object X Y f

/--
Это приведение должно быть {name}`CoeOut`, а не {name}`Coe`,
потому что входной тип {lean}`X → Y` содержит параметры,
отсутствующие в выходном типе {name}`Object`.
-/
instance SetTheory.Set.inst_coe_of_fun {X Y : Set} : CoeOut (X → Y) Object where
  coe := coe_of_fun

-- Приведение функции `X → Y` к `Object` инъективно:
-- `f` и `g` совпадают как объекты тогда и только тогда,
-- когда они равны как функции.
@[simp]
theorem SetTheory.Set.coe_of_fun_inj
  {X Y : Set} (f g : X → Y) : (f : Object) = (g : Object) ↔ f = g := by
    simp [coe_of_fun]

/-- Аксиома 3.11:
Аксиома множества отображений или аксиома степенного множества.
-/
--
-- Элемент `F` (именно элемент типа `Object`) входит в
-- множество отображений `X^Y` (множество функций `Y → X`),
-- если существует функция `f : Y → X` (именно функция) "равная" объекту `F`.
-- Здесь приведение `f : X → Y` к `F : Object` происходит автоматически,
-- потому что выше мы определили соответствующий инстанс и функцию `function_to_object`.
@[simp]
theorem SetTheory.Set.powerset_axiom {X Y : Set} (F : Object) :
  F ∈ (X ^ Y) ↔ ∃ f : Y → X, f = F :=
    SetTheory.powerset_axiom X Y F

-- SetTheory.powerset_axiom
-- (X : Set) (Y : Set) (F : Object) :
--   mem F (pow X Y) ↔
--     ∃ f : (Subtype (mem . Y) → Subtype (mem . X)),
--     function_to_object Y X f = F

/-- Пример 3.4.9 -/
abbrev f_3_4_9_a : ({4,7} : Set) → ({0,1} : Set) := fun x ↦ ⟨0, by simp⟩

open Classical in
noncomputable abbrev f_3_4_9_b : ({4,7} : Set) → ({0,1} : Set) :=
  fun x ↦ if x.val = 4 then ⟨ 0, by simp ⟩ else ⟨ 1, by simp ⟩

open Classical in
noncomputable abbrev f_3_4_9_c : ({4,7} : Set) → ({0,1} : Set) :=
  fun x ↦ if x.val = 4 then ⟨ 1, by simp ⟩ else ⟨ 0, by simp ⟩

abbrev f_3_4_9_d : ({4,7} : Set) → ({0,1} : Set) := fun x ↦ ⟨ 1, by simp ⟩

-- объект `F ∈ {0,1}^{4,7}` — это ровно одна из четырёх функций `{4,7} → {0,1}`, перечисленных выше
theorem SetTheory.Set.example_3_4_9 (F : Object) :
  F ∈ ({0,1} : Set) ^ ({4,7} : Set) ↔
    F = f_3_4_9_a ∨ F = f_3_4_9_b ∨ F = f_3_4_9_c ∨ F = f_3_4_9_d := by
      rw [powerset_axiom]
      refine ⟨?_, by aesop ⟩
      rintro ⟨f, rfl⟩
      have h1 := (f ⟨4, by simp⟩).property
      have h2 := (f ⟨7, by simp⟩).property
      simp [coe_of_fun_inj] at *
      obtain _ | _ := h1 <;> obtain _ | _ := h2
      map_tacs [left; (right;left); (right;right;left); (right;right;right)]
      all_goals
        ext ⟨_, hx⟩
        simp at hx
        grind

/-- Упражнение 3.4.6 (i). Здесь нужно дать подходящее определение степенного множества. -/
--
-- Множество `{0,1} ^ X` — это множество всех функций из `X` в двухэлементное множество `{0,1}`.
-- Такие функции называются индикаторными (или характеристическими):
-- для любого `x : X` значение `f(x)` равно `1` тогда и только тогда,
-- когда `x` принадлежит некоторому подмножеству, которое эта функция описывает.
-- Иными словами, каждая функция `f : X → {0,1}` однозначно
-- задаёт подмножество `{ x : X | f(x) = 1 }` (прообраз единицы).
--
-- Чтобы построить степенное множество `{0,1} ^ X` как множество всех таких подмножеств,
-- мы используем аксиому замены (3.11). Её формулировка говорит,
-- что для любого множества `A` и любого предиката `P(x,y)` (определённого для объектов),
-- если для каждого `x ∈ A` существует единственное `y` с `P(x,y)`,
-- то можно образовать множество всех таких `y`.
-- В нашем случае исходное множество `A = {0,1} ^ X`,
-- а `y = Y` — это то подмножество `X`, которое соответствует функции `f : X → {0,1}`
-- (или, что то же самое, элементу `F` этого множества функций).
--
-- Предикат `P(F, Y)` должен связать каждый элемент `F` из множества функций
-- (представленный как объект типа `Object`) с результирующим множеством `Y` (тоже типа `Object`).
-- Внутри теории множеств функция `f : X → {0,1}` и её представление как объект `F` —
-- это одно и то же, но для формальных манипуляций нам нужна коэрция `(f : Object)`.
-- Тогда условие `(f : Object) = F` гарантирует, что `f` — это именно та функция,
-- которую кодирует элемент `F` из исходного множества.
-- А условие `Y = preimage f {1}` утверждает,
-- что `Y` есть в точности множество тех элементов `X`,
-- которые отображаются в `1`, т.е. характеристическое множество, соответствующее `f`.
--
-- Таким образом, применяя замену ко всем `F ∈ {0,1}^X`,
-- мы собираем все возможные прообразы единицы,
-- и получаем в точности множество всех подмножеств `X`.
-- Это и есть искомое степенное множество.
--
-- Формально:
--   powerset X = { Y | ∃ f : X → {0,1}, (f : Object) ∈ ({0,1}^X) ∧ Y = f⁻¹({1}) }.
--
-- В коде ниже это реализовано через `replace` с предикатом `P`, как описано выше.
--
def SetTheory.Set.powerset (X : Set) : Set :=
  (({0,1} ^ X) : Set).replace
    (P := fun F Y ↦
      -- `F` – элемент (типа `Object`) множества функций вида `X → {0,1}`;
      -- `Y` – элемент результирующего множества, который мы строим
      -- Связь: существует функция `f`, представляемая объектом `F`,
      -- и `Y` является её прообразом `{1}`.
      -- Нас интересуют только те подмножества `X`,
      -- на которых функция f принимает значение `1`.
      ∃ f : X → ({0,1} : Set), (f : Object) = F ∧ Y = (preimage f {1})
    ) (by
        -- aesop
        intro x y y' h
        obtain ⟨⟨f, hf, hy⟩, ⟨f', hf', hy'⟩⟩ := h
        -- `f` и `f'` кодируются одним и тем же объектом `F`,
        -- поэтому их коэрции в `Object` совпадают.
        have hcoe : (f : Object) = (f' : Object) := hf.trans hf'.symm
        have hff' : f = f' := (coe_of_fun_inj f f').mp hcoe
        rw [hy, hy', hff']
    )

open Classical in
/-- Упражнение 3.4.6 (i) -/
@[simp]
theorem SetTheory.Set.mem_powerset {X : Set} (x : Object) :
    x ∈ powerset X ↔ ∃ Y : Set, x = Y ∧ Y ⊆ X := by sorry

/-- Лемма 3.4.10 -/
theorem SetTheory.Set.exists_powerset (X : Set) :
   ∃ (Z : Set), ∀ x, x ∈ Z ↔ ∃ Y : Set, x = Y ∧ Y ⊆ X := by
  use powerset X; apply mem_powerset

/- Как отмечено в списке опечаток, Упражнение 3.4.6 (ii) заменено на Упражнение 3.5.11. -/

/-- Замечание 3.4.11 -/
theorem SetTheory.Set.powerset_of_triple (a b c x : Object) :
    x ∈ powerset {a,b,c}
    ↔ x = (∅ : Set)
    ∨ x = ({a} : Set)
    ∨ x = ({b} : Set)
    ∨ x = ({c} : Set)
    ∨ x = ({a,b} : Set)
    ∨ x = ({a,c} : Set)
    ∨ x = ({b,c} : Set)
    ∨ x = ({a,b,c} : Set) := by
  simp only [mem_powerset, subset_def, mem_triple]
  refine ⟨ ?_, by aesop ⟩
  rintro ⟨Y, rfl, hY⟩; by_cases a ∈ Y <;> by_cases b ∈ Y <;> by_cases c ∈ Y
  on_goal 8 => left
  on_goal 4 => right; left
  on_goal 6 => right; right; left
  on_goal 7 => right; right; right; left
  on_goal 2 => right; right; right; right; left
  on_goal 3 => right; right; right; right; right; left
  on_goal 5 => right; right; right; right; right; right; left
  on_goal 1 => right; right; right; right; right; right; right
  all_goals congr; ext; simp; grind

/-- Аксиома 3.12 (Объединение) -/
theorem SetTheory.Set.union_axiom (A : Set) (x : Object) :
    x ∈ union A ↔ ∃ (S : Set), x ∈ S ∧ (S : Object) ∈ A := SetTheory.union_axiom A x

/-- Пример 3.4.12 -/
theorem SetTheory.Set.example_3_4_12 :
    union { (({2,3} : Set) : Object), (({3,4} : Set) : Object), (({4,5} : Set) : Object) } = {2,3,4,5} := by
  sorry

/-- Связь с объединением из Mathlib -/
theorem SetTheory.Set.union_eq (A : Set) :
    (union A : _root_.Set Object) =
    ⋃₀ { S : _root_.Set Object | ∃ S' : Set, S = S' ∧ (S' : Object) ∈ A } := by
  ext; simp [union_axiom, Set.mem_sUnion]; aesop

/-- Индексированное объединение -/
abbrev SetTheory.Set.iUnion (I : Set) (A : I → Set) : Set :=
  union (I.replace (P := fun α S ↦ S = A α) (by intro _ _ _ ⟨h1, h2⟩; exact h1.trans h2.symm))

-- `x` лежит в индексированном объединении `iUnion I A` тогда и только тогда,
-- когда `x` принадлежит хотя бы одному из множеств `A α`
theorem SetTheory.Set.mem_iUnion {I : Set} (A : I → Set) (x : Object) :
    x ∈ iUnion I A ↔ ∃ α : I, x ∈ A α := by
  rw [union_axiom]; constructor
  . simp_all [replacement_axiom]
  grind [replacement_axiom]

open Classical in
noncomputable abbrev SetTheory.Set.index_example : ({1,2,3} : Set) → Set :=
  fun i ↦ if i.val = 1 then {2,3} else if i.val = 2 then {3,4} else {4,5}

-- конкретное вычисление: объединение `index_example` по индексам `{1,2,3}` даёт `{2,3,4,5}`
theorem SetTheory.Set.iUnion_example : iUnion {1,2,3} index_example = {2,3,4,5} := by
  apply ext; intros; simp [mem_iUnion, index_example, Insert.insert]
  refine ⟨ by aesop, ?_ ⟩; rintro (_ | _ | _); map_tacs [use 1; use 2; use 3]
  all_goals aesop

/-- Связь с индексированным объединением из Mathlib -/
theorem SetTheory.Set.iUnion_eq (I : Set) (A : I → Set) :
    (iUnion I A : _root_.Set Object) = ⋃ α, (A α : _root_.Set Object) := by
  ext; simp [mem_iUnion]

-- объединение по пустому семейству индексов пусто
theorem SetTheory.Set.iUnion_of_empty (A : (∅ : Set) → Set) : iUnion (∅ : Set) A = ∅ := by sorry

/-- Индексированное пересечение -/
noncomputable abbrev SetTheory.Set.nonempty_choose {I : Set} (hI : I ≠ ∅) : I :=
  ⟨(nonempty_def hI).choose, (nonempty_def hI).choose_spec⟩

abbrev SetTheory.Set.iInter' (I : Set) (β : I) (A : I → Set) : Set :=
  (A β).specify (P := fun x ↦ ∀ α : I, x.val ∈ A α)

noncomputable abbrev SetTheory.Set.iInter (I : Set) (hI : I ≠ ∅) (A : I → Set) : Set :=
  iInter' I (nonempty_choose hI) A

-- `x` лежит в индексированном пересечении `iInter I hI A` тогда и только тогда,
-- когда `x` принадлежит каждому из множеств `A α`
theorem SetTheory.Set.mem_iInter {I : Set} (hI : I ≠ ∅) (A : I → Set) (x : Object) :
    x ∈ iInter I hI A ↔ ∀ α : I, x ∈ A α := by
  sorry

/-- Упражнение 3.4.1 -/
theorem SetTheory.Set.preimage_eq_image_of_inv {X Y V : Set} (f : X → Y) (f_inv : Y → X)
  (hf : Function.LeftInverse f_inv f ∧ Function.RightInverse f_inv f) (hV : V ⊆ Y) :
    image f_inv V = preimage f V := by sorry

/- Упражнение 3.4.2.  Сформулируйте и докажите утверждение, связывающее `preimage f (image f S)` и `S`. -/
-- theorem SetTheory.Set.preimage_of_image {X Y:Set} (f:X → Y) (S: Set) (hS: S ⊆ X) : sorry := by sorry

/- Упражнение 3.4.2.  Сформулируйте и докажите утверждение, связывающее `image f (preimage f U)` и `U`.
Интересно, что здесь не требуется, чтобы U было подмножеством Y. -/
-- theorem SetTheory.Set.image_of_preimage {X Y:Set} (f:X → Y) (U: Set) : sorry := by sorry

/- Упражнение 3.4.2.  Сформулируйте и докажите утверждение, связывающее `preimage f (image f (preimage f U))` и `preimage f U`.
Интересно, что здесь не требуется, чтобы U было подмножеством Y. -/
-- theorem SetTheory.Set.preimage_of_image_of_preimage {X Y:Set} (f:X → Y) (U: Set) : sorry := by sorry

/--
  Упражнение 3.4.3.
-/
theorem SetTheory.Set.image_of_inter {X Y : Set} (f : X → Y) (A B : Set) :
    image f (A ∩ B) ⊆ (image f A) ∩ (image f B) := by sorry

-- разность образов содержится в образе разности: `(image f A) \ (image f B) ⊆ image f (A \ B)`
theorem SetTheory.Set.image_of_diff {X Y : Set} (f : X → Y) (A B : Set) :
    (image f A) \ (image f B) ⊆ image f (A \ B) := by sorry

-- образ объединения равен объединению образов
theorem SetTheory.Set.image_of_union {X Y : Set} (f : X → Y) (A B : Set) :
    image f (A ∪ B) = (image f A) ∪ (image f B) := by sorry

def SetTheory.Set.image_of_inter' : Decidable (∀ X Y : Set, ∀ f : X → Y, ∀ A B : Set, image f (A ∩ B) = (image f A) ∩ (image f B)) := by
  -- первой строкой этой конструкции должно быть либо `apply isTrue`, либо `apply isFalse`
  sorry

def SetTheory.Set.image_of_diff' : Decidable (∀ X Y : Set, ∀ f : X → Y, ∀ A B : Set, image f (A \ B) = (image f A) \ (image f B)) := by
  -- первой строкой этой конструкции должно быть либо `apply isTrue`, либо `apply isFalse`
  sorry

/-- Упражнение 3.4.4 -/
theorem SetTheory.Set.preimage_of_inter {X Y : Set} (f : X → Y) (A B : Set) :
    preimage f (A ∩ B) = (preimage f A) ∩ (preimage f B) := by sorry

-- прообраз объединения равен объединению прообразов
theorem SetTheory.Set.preimage_of_union {X Y : Set} (f : X → Y) (A B : Set) :
    preimage f (A ∪ B) = (preimage f A) ∪ (preimage f B) := by sorry

-- прообраз разности равен разности прообразов
theorem SetTheory.Set.preimage_of_diff {X Y : Set} (f : X → Y) (A B : Set) :
    preimage f (A \ B) = (preimage f A) \ (preimage f B)  := by sorry

/-- Упражнение 3.4.5 (image of a preimage) -/
theorem SetTheory.Set.image_preimage_of_surj {X Y : Set} (f : X → Y) :
    (∀ S, S ⊆ Y → image f (preimage f S) = S) ↔ Function.Surjective f := by sorry

/-- Упражнение 3.4.5 (preimage of an image) -/
theorem SetTheory.Set.preimage_image_of_inj {X Y : Set} (f : X → Y) :
    (∀ S, S ⊆ X → preimage f (image f S) = S) ↔ Function.Injective f := by sorry

/-- Вспомогательная лемма для Упражнения 3.4.7. -/
@[simp]
lemma SetTheory.Set.mem_powerset' {S S' : Set} : (S' : Object) ∈ S.powerset ↔ S' ⊆ S := by
  simp [mem_powerset]

/-- Ещё одна вспомогательная лемма для Упражнения 3.4.7. -/
lemma SetTheory.Set.mem_union_powerset_replace_iff {S : Set} {P : S.powerset → Object → Prop} {hP : _} {x : Object} :
    x ∈ union (S.powerset.replace (P := P) hP) ↔
    ∃ (S' : S.powerset) (U : Set), P S' U ∧ x ∈ U := by
  grind [union_axiom, replacement_axiom]

/-- Упражнение 3.4.7 -/
theorem SetTheory.Set.partial_functions {X Y : Set} :
    ∃ Z : Set, ∀ F : Object, F ∈ Z ↔ ∃ X' Y' : Set, X' ⊆ X ∧ Y' ⊆ Y ∧ ∃ f : X' → Y', F = f := by
  sorry

/--
  Упражнение 3.4.8. Суть этого упражнения — доказать утверждение, не используя
  операцию попарного объединения {kw (of := «term_∪_»)}`∪`.
-/
theorem SetTheory.Set.union_pair_exists (X Y : Set) : ∃ Z : Set, ∀ x, x ∈ Z ↔ (x ∈ X ∨ x ∈ Y) := by
  sorry

/-- Упражнение 3.4.9 -/
theorem SetTheory.Set.iInter'_insensitive {I : Set} (β β' : I) (A : I → Set) :
    iInter' I β A = iInter' I β' A := by sorry

/-- Упражнение 3.4.10 (union over a union of index sets) -/
theorem SetTheory.Set.union_iUnion {I J : Set} (A : (I ∪ J : Set) → Set) :
    iUnion I (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    ∪ iUnion J (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    = iUnion (I ∪ J) A := by sorry

/-- Упражнение 3.4.10 (a union of nonempty index sets is nonempty) -/
theorem SetTheory.Set.union_of_nonempty {I J : Set} (hI : I ≠ ∅) (hJ : J ≠ ∅) : I ∪ J ≠ ∅ := by sorry

/-- Упражнение 3.4.10 (intersection over a union of index sets) -/
theorem SetTheory.Set.inter_iInter {I J : Set} (hI : I ≠ ∅) (hJ : J ≠ ∅) (A : (I ∪ J : Set) → Set) :
    iInter I hI (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    ∩ iInter J hJ (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    = iInter (I ∪ J) (union_of_nonempty hI hJ) A := by sorry

/-- Упражнение 3.4.11 (complement of a union) -/
theorem SetTheory.Set.compl_iUnion {X I : Set} (hI : I ≠ ∅) (A : I → Set) :
    X \ iUnion I A = iInter I hI (fun α ↦ X \ A α) := by sorry

/-- Упражнение 3.4.11 (complement of an intersection) -/
theorem SetTheory.Set.compl_iInter {X I : Set} (hI : I ≠ ∅) (A : I → Set) :
    X \ iInter I hI A = iUnion I (fun α ↦ X \ A α) := by sorry

end Chapter3
