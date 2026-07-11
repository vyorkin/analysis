import Mathlib.Tactic

set_option doc.verso.suggestions false

/-!
# Analysis I, Section 3.1: Fundamentals (of set theory)

In this section we set up a version of Zermelo-Frankel set theory (with atoms) that tries to be
as faithful as possible to the original text of Analysis I, Section 3.1. All numbering refers to
the original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- A type `Chapter3.SetTheory.Set` of sets
- A type `Chapter3.SetTheory.Object` of objects
- An axiom that every set is (or can be coerced into) an object
- The empty set {syntax term}`∅`, singletons {syntax term}`{y}`, and pairs {syntax term}`{y,z}`
  (and more general finite tuples), with their attendant axioms
- Pairwise union {syntax term}`X ∪ Y`, and their attendant axioms
- Coercion of a set `A` to its associated type `A.toSubtype`, which is a subtype of `Object`, and
  basic API.  (This is a technical construction needed to make the Zermelo-Frankel set theory
  compatible with the dependent type theory of Lean.)
- The specification `A.specify P` of a set `A` and a predicate `P: A.toSubtype → Prop` to the
  subset of elements of `A` obeying `P`, and the axiom of specification.
  TODO: somehow implement set builder elaboration for this.
- The replacement `A.replace hP` of a set `A` via a predicate
  `P: A.toSubtype → Object → Prop` obeying a uniqueness condition
  `∀ x y y', P x y ∧ P x y' → y = y'`, and the axiom of replacement.
- A bijective correspondence between the Mathlib natural numbers `ℕ` and a set
  `Chapter3.Nat : Chapter3.Set` (the axiom of infinity).
- Axioms of regularity, power set, and union (used in later sections of this chapter, but not
  required here)
- Connections with Mathlib's notion of a {name}`Set`

The other axioms of Zermelo-Frankel set theory are discussed in later sections.

Some technical notes:
- Mathlib of course has its own notion of a {name}`Set` (or more precisely, a type `Set X` associated to
  each type `X`), which is not compatible with the notion `Chapter3.Set` defined here,
  though we will try to make the notations match as much as possible.  This causes some notational
  conflict: for instance, one may need to explicitly specify `(∅:Chapter3.Set)` instead of just {syntax term}`∅`
  to indicate that one is using the `Chapter3.Set` version of the empty set, rather than the
  Mathlib version of the empty set, and similarly for other notation defined here.
- In Analysis I, we chose to work with an "impure" set theory, in which there could be more
  `Object`s than just `Set`s.  In the type theory of Lean, this requires treating `Chapter3.Set`
  and `Chapter3.Object` as distinct types. Occasionally this means we have to use a coercion
  `(X: Chapter3.Object)` of a `Chapter3.Set` `X` to make into a `Chapter3.Object`: this is
  mostly needed when manipulating sets of sets.
- Strictly speaking, a set `X:Set` is not a type; however, we will coerce sets to types, and
  specifically to a subtype of `Object`.  A similar coercion is in place for Mathlib's
  formalization of sets.
- After this chapter is concluded, the notion of a `Chapter3.SetTheory.Set` will be deprecated in
  favor of the standard Mathlib notion of a {name}`Set` (or more precisely of the type `Set X` of a set
  in a given type `X`).  However, due to various technical incompatibilities between set theory
  and type theory, we will not attempt to create a full equivalence between these two
  notions of sets. (As such, this makes this entire chapter optional from the point of view of
  the rest of the book, though we retain it for pedagogical purposes.)


## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)
-/

namespace Chapter3

/- The ability to work in multiple universe is not relevant immediately, but
becomes relevant when constructing models of set theory in the Chapter 3 epilogue. -/
universe u v

/-- The axioms of Zermelo-Frankel theory with atoms. -/
class SetTheory where
  -- Ниже в аксиомах 3.6/3.7 встречается запись `Subtype (mem . A)`.
  -- Точка здесь — это плейсхолдер-синтаксис Lean (аналог `·`) для анонимной функции:
  -- `mem . A` разворачивается в `fun x => mem x A`.
  -- Ну фактически, это безточечная аннотация неэквивалентной функциональной композиции.
  -- То есть в предикат «x принадлежит A».
  -- Тогда `Subtype (fun x => mem x A)` — это подтип `Object`,
  -- состоящий ровно из элементов, принадлежащих A (пары `⟨x, доказательство mem x A⟩`).
  -- Именно по такому подтипу и должен пробегать предикат `P` в `specify`/`replace`.
  Set : Type u -- Axiom 3.1
  Object : Type v -- Axiom 3.1
  -- `↪` — тип `Function.Embedding`: пара (функция + доказательство инъективности).
  --
  -- structure Embedding (α : Sort*) (β : Sort*) where
  --   toFun : α → β
  --   inj' : Injective toFun
  --
  -- Метод `.inj'` извлекает инъективность: `∀ a b, f a = f b → a = b`.
  --
  set_to_object : Set ↪ Object -- Axiom 3.1
  -- Утверждение о том, что элемент входит в множество (принадлежит множеству).
  mem : Object → Set → Prop -- Axiom 3.1
  extensionality X Y : (∀ x, mem x X ↔ mem x Y) → X = Y -- Axiom 3.2
  emptyset : Set -- Axiom 3.3
  emptyset_mem x : ¬ mem x emptyset -- Axiom 3.3
  singleton : Object → Set -- Axiom 3.4
  singleton_axiom x y : mem x (singleton y) ↔ x = y -- Axiom 3.4
  union_pair : Set → Set → Set -- Axiom 3.5
  union_pair_axiom X Y x : mem x (union_pair X Y) ↔ (mem x X ∨ mem x Y) -- Axiom 3.5
  -- Спецификация/выделение: `specify A P` — подмножество A из тех x, для
  -- которых P x истинно. По сути `{x ∈ A | P(x)}`, результат всегда есть подможество A.
  specify A (P : Subtype (mem . A) → Prop) : Set -- Axiom 3.6
  specification_axiom A (P : Subtype (mem . A) → Prop) :
    (∀ x, mem x (specify A P) → mem x A) ∧ ∀ x, mem x.val (specify A P) ↔ P x -- Axiom 3.6
  --
  -- replace A P hP — это множество всех y, для которых найдётся x ∈ A для
  -- которых выполнено `P x y`, т.е. аналог {f(x) | x ∈ A}.
  -- В отличие от specify, результат не обязан быть подмножеством A.
  --
  -- Тождество Лейбница. Тождество неразличимых:
  replace A (P : Subtype (mem . A) → Object → Prop)
    (hP : ∀ x y y', P x y ∧ P x y' → y = y') : Set -- Axiom 3.7
  -- Образ/отображение: P x y читается как «x переходит в y» — функциональное отношение
  -- (условие hP требует однозначности образа).
  replacement_axiom A (P : Subtype (mem . A) → Object → Prop)
    (hP : ∀ x y y', P x y ∧ P x y' → y = y') : ∀ y, mem y (replace A P hP) ↔ ∃ x, P x y -- Axiom 3.7
  nat : Set -- Axiom 3.8
  nat_equiv : ℕ ≃ Subtype (mem . nat) -- Axiom 3.8
  regularity_axiom A (hA : ∃ x, mem x A) :
    ∃ x, mem x A ∧ ∀ S, x = set_to_object S → ¬ ∃ y, mem y A ∧ mem y S -- Axiom 3.9
  pow : Set → Set → Set -- Axiom 3.11
  function_to_object (X : Set) (Y : Set) :
    (Subtype (mem . X) → Subtype (mem . Y)) ↪ Object -- Axiom 3.11
  powerset_axiom (X : Set) (Y : Set) (F : Object) :
    mem F (pow X Y) ↔ ∃ f : Subtype (mem . Y) → Subtype (mem . X),
    function_to_object Y X f = F -- Axiom 3.11
  union : Set → Set -- Axiom 3.12
  union_axiom A x : mem x (union A) ↔ ∃ S, mem x S ∧ mem (set_to_object S) A -- Axiom 3.12

-- This enables one to use `Set` and `Object` instead of `SetTheory.Set` and `SetTheory.Object`.
export SetTheory (Set Object)

-- Делает экземпляр класса типов SetTheory неявным параметром всех последующих
-- определений и теорем — то есть любая теорема ниже автоматически предполагает, что аксиомы
-- теории Цермело–Френкеля с "атомами" выполнены, без явного указания этого в каждом объявлении.
--
-- "Атомы" — это объекты (Object), которые не являются множествами:
-- у них нет элементов, но пустым множеством они тоже не являются.
-- В стандартной ЗФ всё суть множества; здесь Object шире Set,
-- и разность — это атомы (числа, точки и т.п. как примитивные объекты).
--
-- This instance implicitly imposes the axioms of Zermelo-Frankel set theory with atoms.
variable [SetTheory]

/-- Definition 3.1.1 (objects can be elements of sets) -/
instance SetTheory.objects_mem_sets : Membership Object Set where
  mem X x := mem x X

-- Now we can use the `∈` notation between our `Object` and `Set`.
example (X : Set) (x : Object) : x ∈ X ↔ SetTheory.mem x X := by rfl

/-- Axiom 3.1 (Sets are objects)-/
instance SetTheory.sets_are_objects : Coe Set Object where
  coe X := set_to_object X

-- Now we can treat a `Set` as an `Object` when needed.
example (X : Set) : (X : Object) = SetTheory.set_to_object X := rfl

/-- Axiom 3.1 (Sets are objects)-/
-- `set_to_object : Set ↪ Object` — инъективное вложение; `.inj'` достаёт инъективность
-- (т.е. `f a = f b → a = b`), поэтому равенство в `Object` поднимается до равенства в `Set`.
theorem SetTheory.Set.coe_eq {X Y : Set} (h : (X : Object) = (Y : Object)) : X = Y :=
  set_to_object.inj' h

/-- Axiom 3.1 (Sets are objects)-/
-- `⟨coe_eq, …⟩` строит `↔` из двух направлений:
-- `→` — это `coe_eq`, уже доказанный выше.
-- `←` — если `X = Y`, то `rintro rfl` подставляет `Y := X` повсюду,
--       и цель `(X : Object) = (X : Object)` закрывается `rfl`.
--
-- @[simp] позволяет тактите `simp` автоматически
-- убирать приведение типов в равенствах множеств.
@[simp]
theorem SetTheory.Set.coe_eq_iff (X Y : Set) : (X : Object) = (Y : Object) ↔ X = Y :=
  ⟨coe_eq, by rintro rfl; rfl⟩

/-- Axiom 3.2 (Equality of sets).
The {attr}`@[ext]` tag allows the {tactic}`ext` tactic to work for sets. -/
@[ext]
theorem SetTheory.Set.ext {X Y : Set} (h : ∀ x, x ∈ X ↔ x ∈ Y) : X = Y :=
  extensionality X Y h

/- Axiom 3.2 (Equality of sets)-/
#check SetTheory.Set.ext_iff -- {X Y : Set} : X = Y ↔ ∀ (x : Object), x ∈ X ↔ x ∈ Y

instance SetTheory.Set.instEmpty : EmptyCollection Set where
  emptyCollection := emptyset

-- Now we can use the `∅` notation to refer to `SetTheory.emptyset`.
example : ∅ = SetTheory.emptyset := rfl

-- Make everything we define in `SetTheory.Set.*` accessible directly.
open SetTheory.Set

/--
  Axiom 3.3 (empty set).
  Note: in some applications one may have to explicitly cast {lean}`(∅ : Set)` to {name}`Set` due to
  Mathlib's existing set theory notation.
-/
@[simp]
theorem SetTheory.Set.not_mem_empty : ∀ x, x ∉ (∅ : Set) :=
  emptyset_mem

/-- Empty set has no elements -/
theorem SetTheory.Set.eq_empty_iff_forall_notMem {X : Set} : X = ∅ ↔ (∀ x, x ∉ X) := by
  constructor
  · intro h
    rw [h]
    exact not_mem_empty -- ∀ x, x ∉ (∅ : Set)
  · intro h
    -- ext x
    -- ^^^ Использование тактики ext эквивалентно следующему:
    rw [Set.ext_iff] -- (h : ∀ x, x ∈ X ↔ x ∈ Y) : X = Y
    intro x
    constructor
    · intro hx
      specialize h x
      contradiction
    · intro he
      have hc := not_mem_empty x -- ∀ x, x ∉ (∅ : Set)
      contradiction

/-- Empty set is unique -/
theorem SetTheory.Set.empty_unique : ∃! (X : Set), ∀ x, x ∉ X := by
  -- Существование уникального = существование ∧ уникальность
  -- Существование: ∃ x, p x
  --  Уникальность: ∀ (y₁ y₂ : α), p y₁ → p y₂ → y₁ = y₂
  apply existsUnique_of_exists_of_unique
  · use ∅
    exact not_mem_empty -- ∀ x, x ∉ (∅ : Set)
  · intro X Y hx hy
    ext x
    specialize hx x
    specialize hy x
    constructor
    · intro hx'; contradiction
    · intro hy'; contradiction

/-- Lemma 3.1.5 (Single choice) -/
-- Единственный выбор.
-- Если есть непустое мн-во, то можно выбрать хотя бы один его элемент,
-- т.е. оно состоит хотя бы из одного элемента.
lemma SetTheory.Set.nonempty_def {X : Set} (h : X ≠ ∅) : ∃ x, x ∈ X := by
  -- This proof is written to follow the structure of the original text.
  -- Докажем от противного, предположим обратное.
  by_contra! h
  have claim (x : Object) : x ∈ X ↔ x ∈ (∅ : Set) := by
    simp [h, not_mem_empty]
  apply ext at claim
  contradiction

-- Вот это самое понятное доказательство, основанное на
-- введении промежуточной гипотезы, которая доказывается при помощи двух противоречий.
lemma SetTheory.Set.nonempty_def' {X : Set} (h : X ≠ ∅) : ∃ x, x ∈ X := by
  -- This proof is written to follow the structure of the original text.
  by_contra! h
  have claim (x : Object) : x ∈ X ↔ x ∈ (∅ : Set) := by
    specialize h x
    constructor
    · intro h'
      contradiction
    · intro h'
      have hc := not_mem_empty x -- ∀ x, x ∉ (∅ : Set)
      contradiction
  apply ext at claim -- (h : ∀ x, x ∈ X ↔ x ∈ Y) : X = Y
  contradiction

-- Вот это менее интуитивно понятное док-во из-за apply h.
lemma SetTheory.Set.nonempty_def'' {X : Set} (h : X ≠ ∅) : ∃ x, x ∈ X := by
  by_contra! hc
  apply h
  rw [eq_empty_iff_forall_notMem] -- X = ∅ ↔ ∀ (x : Object), x ∉ X
  exact hc

theorem SetTheory.Set.nonempty_of_inhabited
  {X : Set} {x : Object} (h : x ∈ X) : X ≠ ∅ := by
    -- Предположим обратноe: что множество X пустое.
    contrapose! h -- Применим закон логической контрапозиции.
    rw [eq_empty_iff_forall_notMem] at h --  X = ∅ ↔ ∀ (x : Object), x ∉ X
    specialize h x
    exact h

instance SetTheory.Set.instSingleton : Singleton Object Set where
  singleton := singleton

-- Now we can use the `{x}` notation for a single element `Set`.
example (x : Object) : {x} = SetTheory.singleton x := rfl

/--
  Axiom 3.3(a) (singleton).
  Note: in some applications one may have to explicitly cast {lean (type := "Set")}`{a}` to {name}`Set` due to Mathlib's
  existing set theory notation.
-/
@[simp]
theorem SetTheory.Set.mem_singleton (x a : Object) : x ∈ ({a} : Set) ↔ x = a :=
  singleton_axiom x a

instance SetTheory.Set.instUnion : Union Set where
  union := union_pair

-- Now we can use the `X ∪ Y` notation for a union of two `Set`s.
example (X Y : Set) : X ∪ Y = SetTheory.union_pair X Y := rfl

/-- Axiom 3.4 (Pairwise union)-/
@[simp]
theorem SetTheory.Set.mem_union (x : Object) (X Y : Set) :
  x ∈ (X ∪ Y) ↔ (x ∈ X ∨ x ∈ Y) :=
    union_pair_axiom X Y x

instance SetTheory.Set.instInsert : Insert Object Set where
  insert x X := {x} ∪ X

@[simp]
theorem SetTheory.Set.mem_insert (a b : Object) (X : Set) :
  a ∈ insert b X ↔ a = b ∨ a ∈ X := by
    simp only [insert, Insert.insert, mem_union, mem_singleton]

/-- Axiom 3.3(b) (pair).  Note: in some applications one may have to
    cast {lean (type := "Set")}`{a,b}` to {name}`Set`. -/
theorem SetTheory.Set.pair_eq (a b : Object) : ({a,b} : Set) = {a} ∪ {b} := by rfl

/-- Axiom 3.3(b) (pair).  Note: in some applications one may have to
    cast {lean (type := "Set")}`{a,b}` to {name}`Set`. -/
@[simp]
theorem SetTheory.Set.mem_pair (x a b : Object) : x ∈ ({a,b} : Set) ↔ (x = a ∨ x = b) := by
  simp [pair_eq, mem_union, mem_singleton]

theorem SetTheory.Set.mem_pair' (x a b : Object) :
  x ∈ ({a,b} : Set) ↔ (x = a ∨ x = b) := by
    rw [pair_eq] -- {a, b} = {a} ∪ {b}
    rw [mem_union] -- x ∈ (X ∪ Y) ↔ (x ∈ X ∨ x ∈ Y)
    rw [mem_singleton, mem_singleton] -- x ∈ {a} ↔ x = a

@[simp]
theorem SetTheory.Set.mem_triple (x a b c : Object) :
  x ∈ ({a,b,c} : Set) ↔ (x = a ∨ x = b ∨ x = c) := by
    simp [Insert.insert, mem_union, mem_singleton]

theorem SetTheory.Set.mem_triple' (x a b c : Object) :
  x ∈ ({a,b,c} : Set) ↔ (x = a ∨ x = b ∨ x = c) := by
    repeat rw [Insert.insert]
    sorry

/-- Remark 3.1.9 -/
theorem SetTheory.Set.pair_uniq (a b : Object) :
  ∃! (X : Set), ∀ x, x ∈ X ↔ x = a ∨ x = b := by
    apply existsUnique_of_exists_of_unique
    · use {a, b}
      intro x
      exact mem_pair x a b
    · intro s₁ s₂ h₁ h₂
      ext x
      -- rw [h₁ x, h₂ x]
      specialize h₁ x
      specialize h₂ x
      rw [h₁, h₂]

/-- Remark 3.1.9 -/
theorem SetTheory.Set.singleton_uniq (a : Object) :
  ∃! (X : Set), ∀ x, x ∈ X ↔ x = a := by
    -- have haa : ∃! X, ∀ (x : Object), x ∈ X ↔ x = a ∨ x = a := pair_uniq a a
    -- simp only [or_self] at haa
    -- exact haa
    --
    -- Докажем существование уникального множества, доказав отдельно
    -- 1. Существование этого множества
    -- 2. Уникальность этого множества
    apply existsUnique_of_exists_of_unique
    · use {a}
      intro x
      exact mem_singleton x a
    · intro s₁ s₂ h₁ h₂
      ext x
      -- rw [h₁ x, h₂ x]
      specialize h₁ x
      specialize h₂ x
      rw [h₁, h₂]


/-- Remark 3.1.9 -/
theorem SetTheory.Set.pair_comm (a b : Object) : ({a,b} : Set) = {b,a} := by
  ext x
  rw [mem_pair, mem_pair]
  rw [or_comm] -- a ∨ b ↔ b ∨ a

/-- Remark 3.1.9 -/
@[simp]
theorem SetTheory.Set.pair_self (a : Object) : ({a,a} : Set) = {a} := by
  ext x
  rw [mem_pair]
  rw [or_self] -- (p ∨ p) = p
  rw [mem_singleton]

/-- Exercise 3.1.1 -/
theorem SetTheory.Set.pair_eq_pair {a b c d : Object}
  (h : ({a,b} : Set) = {c,d}) : (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
    rw [Set.ext_iff] at h
    have ha := h a
    have hb := h b
    have hc := h c
    have hd := h d
    rw [mem_pair, mem_pair] at ha hb hc hd
    simp at ha hb hc hd
    -- hc : c = a ∨ c = b,  hd : d = a ∨ d = b
    -- Разбираем 4 комбинации для ha и hb.
    -- Вырожденные случаи (a=c,b=c) и (a=d,b=d) требуют hd/hc,
    -- чтобы установить, что второй элемент пары тоже совпадает
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rcases hd with rfl | rfl <;> left <;> exact ⟨rfl, rfl⟩
    · left; exact ⟨rfl, rfl⟩
    · right; exact ⟨rfl, rfl⟩
    · rcases hc with rfl | rfl <;> right <;> exact ⟨rfl, rfl⟩

abbrev SetTheory.Set.empty : Set := ∅
abbrev SetTheory.Set.singleton_empty : Set := {(empty : Object)}
abbrev SetTheory.Set.pair_empty : Set := {(empty : Object), (singleton_empty : Object)}

-- Пустое множество не равно одноэлементному множеству из пустого.
/-- Exercise 3.1.2 -/
theorem SetTheory.Set.emptyset_neq_singleton : empty ≠ singleton_empty := by
  intro h
  -- ^ По сути, рассуждаем от противного таким образом.
  rw [Set.ext_iff] at h
  specialize h empty
  obtain ⟨h₀, h₁⟩ := h
  --
  -- singleton_empty = {(empty : Object)} по определению
  -- mem_singleton: x ∈ {a} ↔ x = a
  -- После rw [mem_singleton]: (empty : Object) = (empty : Object),
  -- которая закрывается rfl автоматически
  -- Это верно просто по аксиоме 3.3:
  have hmem : (empty : Object) ∈ singleton_empty := by rw [mem_singleton]
  --
  have hh : (empty : Object) ∈ empty := h₁ hmem
  rw [show empty = ∅ by rfl] at hh
  have hc := not_mem_empty (∅ : Set) -- Axiom 3.3 : (x : Object) : x ∉ ∅
  contradiction

-- Более короткая версия доказательства теоремы выше.
theorem SetTheory.Set.emptyset_neq_singleton' : empty ≠ singleton_empty := by
  intro h
  -- Axiom 3.3: x ∈ {a} ↔ x = a
  have hmem : (empty : Object) ∈ singleton_empty := by rw [mem_singleton]
  rw [← h] at hmem
  exact not_mem_empty _ hmem -- ∀ x, x ∉ (∅ : Set)

/-- Exercise 3.1.2 -/
-- Пустое множество не равно 2-х элементному множеству из двух пустых.
theorem SetTheory.Set.emptyset_neq_pair : empty ≠ pair_empty := by
  intro h
  rw [Set.ext_iff] at h
  obtain ⟨h₀, h₁⟩ := h empty
  have hmem : (empty : Object) ∈ pair_empty := by
    rw [mem_pair]
    left
    rfl
  have hh : (empty : Object) ∈ empty := h₁ hmem
  rw [show empty = ∅ by rfl] at hh
  have hc := not_mem_empty (∅ : Set) -- Axiom 3.3 : (x : Object) : x ∉ ∅
  contradiction

theorem SetTheory.Set.emptyset_neq_pair' : empty ≠ pair_empty := by
  intro h
  -- Это утверждение получаем "бесплатно" из Axiom 3.3:
  have hmem : (empty : Object) ∈ pair_empty := by
    rw [mem_pair]
    tauto
  rw [← h, show empty = ∅ by rfl] at hmem
  have hnot := not_mem_empty (∅ : Set) -- Axiom 3.3 : (x : Object) : x ∉ ∅
  contradiction

-- Одноэлементное множество из пустого не равно двухэлементному множеству из пустых.
/-- Exercise 3.1.2 -/
theorem SetTheory.Set.singleton_empty_neq_pair : singleton_empty ≠ pair_empty := by
  intro h
  -- По аксиоме 3.3:
  have hmem : (singleton_empty : Object) ∈ pair_empty := by rw [mem_pair]; tauto
  rw [← h] at hmem
  rw [mem_singleton] at hmem -- x ∈ {a} ↔ x = a
  symm at hmem
  have heq : empty = singleton_empty := Set.coe_eq hmem
  have hnot := emptyset_neq_singleton
  contradiction

/--
  Remark 3.1.11.
  (These results can be proven either by a direct rewrite, or by using extensionality.)
-/
theorem SetTheory.Set.union_congr_left (A A' B : Set) (h : A = A') :
  A ∪ B = A' ∪ B := by rw [h]

/--
  Remark 3.1.11.
  (These results can be proven either by a direct rewrite, or by using extensionality.)
-/
theorem SetTheory.Set.union_congr_right (A B B' : Set) (h : B = B') :
  A ∪ B = A ∪ B' := by rw [h]

/-- Lemma 3.1.12 (Basic properties of unions) / Exercise 3.1.3 -/
theorem SetTheory.Set.singleton_union_singleton (a b : Object) :
  ({a} : Set) ∪ ({b} : Set) = {a,b} := by
    exact pair_eq a b

/-- Lemma 3.1.12 (Basic properties of unions) / Exercise 3.1.3 -/
theorem SetTheory.Set.union_comm (A B : Set) : A ∪ B = B ∪ A := by
  ext x
  rw [mem_union, mem_union]
  tauto

/-- Lemma 3.1.12 (Basic properties of unions) / Exercise 3.1.3 -/
theorem SetTheory.Set.union_assoc (A B C : Set) : (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
  -- this proof is written to follow the structure of the original text.
  ext x
  constructor
  . intro hx
    rw [mem_union] at hx
    obtain case1 | case2 := hx
    . rw [mem_union] at case1
      obtain case1a | case1b := case1
      . rw [mem_union]; tauto
      have : x ∈ B ∪ C := by rw [mem_union]; tauto
      rw [mem_union]; tauto
    · have : x ∈ B ∪ C := by rw [mem_union]; tauto
      rw [mem_union]; tauto
  · intro hx; rw [mem_union] at hx
    obtain case1 | case2 := hx
    · rw [mem_union, mem_union]
      tauto
    · rw [mem_union] at case2
      rw [mem_union, mem_union]
      tauto

/-- Proposition 3.1.27(c) -/
@[simp]
theorem SetTheory.Set.union_self (A : Set) : A ∪ A = A := by
  ext x
  rw [mem_union]
  tauto

/-- Proposition 3.1.27(a) -/
@[simp]
theorem SetTheory.Set.union_empty (A : Set) : A ∪ ∅ = A := by
  ext x
  rw [mem_union]
  constructor
  · rintro (h₀ | h₁)
    · assumption
    · have hnot := not_mem_empty x
      contradiction
  · tauto

/-- Proposition 3.1.27(a) -/
@[simp]
theorem SetTheory.Set.empty_union (A : Set) : ∅ ∪ A = A := by
  rw [union_comm]
  exact union_empty A

theorem SetTheory.Set.triple_eq (a b c : Object) : {a,b,c} = ({a} : Set) ∪ {b,c} := by
  -- {a,b,c} = insert a {b,c} = {a} ∪ {b,c} по определению instInsert, поэтому rfl
  rfl

/-- Example 3.1.10 -/
theorem SetTheory.Set.pair_union_pair (a b c : Object) : ({a,b} : Set) ∪ {b,c} = {a,b,c} := by
  ext x
  simp only [mem_union, mem_pair, mem_triple]
  tauto

theorem SetTheory.Set.pair_union_pair' (a b c : Object) : ({a,b} : Set) ∪ {b,c} = {a,b,c} := by
  ext x
  rw [mem_union]
  rw [mem_pair, mem_pair]
  rw [mem_triple]
  -- tauto
  constructor <;> (intro h; tauto)

/-- Definition 3.1.14.   -/
instance SetTheory.Set.instSubset : HasSubset Set where
  Subset X Y := ∀ x, x ∈ X → x ∈ Y

-- Now we can use `⊆` for a subset relationship between two `Set`s.
example (X Y : Set) : X ⊆ Y ↔ ∀ x, x ∈ X → x ∈ Y := by rfl

/--
  Definition 3.1.14.
  Note that the strict subset operation in Mathlib is denoted {kw (of := «term_⊂_»)}`⊂` rather than `⊊`.
-/
instance SetTheory.Set.instSSubset : HasSSubset Set where
  SSubset X Y := X ⊆ Y ∧ X ≠ Y

/-- Now we can use {kw (of := «term_⊂_»)}`⊂` for a strict subset relationship between two {name}`Set`s. -/
example (X Y : Set) : X ⊂ Y ↔ X ⊆ Y ∧ X ≠ Y := by rfl

/-- Definition 3.1.14. -/
theorem SetTheory.Set.subset_def (X Y : Set) :
  X ⊆ Y ↔ ∀ x, x ∈ X → x ∈ Y := by rfl

/--
  Definition 3.1.14.
  Note that the strict subset operation in Mathlib is denoted {kw (of := «term_⊂_»)}`⊂` rather than `⊊`.
-/
theorem SetTheory.Set.ssubset_def (X Y : Set) : X ⊂ Y ↔ (X ⊆ Y ∧ X ≠ Y) := by rfl

/-- Remark 3.1.15 -/
theorem SetTheory.Set.subset_congr_left
  {A A' B : Set} (hAA' : A = A') (hAB : A ⊆ B) : A' ⊆ B := by
    rw [← hAA']
    exact hAB

/-- Examples 3.1.16 -/
@[simp, refl]
theorem SetTheory.Set.subset_self (A : Set) : A ⊆ A := by
  -- tauto
  rw [subset_def]
  intro x h
  exact h

/-- Examples 3.1.16 -/
@[simp]
theorem SetTheory.Set.empty_subset (A : Set) : ∅ ⊆ A := by
  rw [subset_def]
  intro x h₀
  have h₁ := not_mem_empty x
  contradiction

/-- Proposition 3.1.17 (Partial ordering by set inclusion) -/
theorem SetTheory.Set.subset_trans
  {A B C : Set} (hAB : A ⊆ B) (hBC : B ⊆ C) : A ⊆ C := by
    -- This proof is written to follow the structure of the original text.
    rw [subset_def]
    intro x hx
    rw [subset_def] at hAB
    apply (hAB x) at hx -- Эквивалентно следующему: replace hx := hAB x hx
    apply hBC x at hx
    assumption

/-- Proposition 3.1.17 (Partial ordering by set inclusion) -/
theorem SetTheory.Set.subset_antisymm
  (A B : Set) (hAB : A ⊆ B) (hBA : B ⊆ A) : A = B := by
    ext x
    -- tauto
    rw [subset_def] at hAB hBA
    specialize hAB x
    specialize hBA x
    exact ⟨hAB, hBA⟩

/-- Proposition 3.1.17 (Partial ordering by set inclusion) -/
theorem SetTheory.Set.ssubset_trans
  (A B C : Set) (hAB : A ⊂ B) (hBC : B ⊂ C) : A ⊂ C := by
    rw [ssubset_def] at *
    constructor
    · exact subset_trans hAB.left hBC.left
    · intro h
      rw [← h] at hBC
      have ha₀ := subset_antisymm A B hAB.left hBC.left
      have ha₁ := hAB.right
      contradiction
/-
  ## Подтип как «тип элементов множества»

  В теории типов Lean множество `A : Set` само по себе не является типом —
  нельзя написать `(x : A)` напрямую. `toSubtype` решает эту проблему:
  оно превращает множество в подтип объектов.

  Формально: `A.toSubtype = { x : Object // x ∈ A }`, то есть тип пар `⟨x, hx⟩`,
  где `x : Object` и `hx : x ∈ A`. Это «зависимая пара»: значение несёт
  в себе объект вместе с доказательством его принадлежности множеству.

  Создание элемента подтипа:
  · `⟨x, hx⟩ : A.toSubtype`  — анонимный конструктор
  · `A.subtype_mk hx`        — именованная вспомогательная функция

  Извлечение компонентов:
  · `x'.val      : Object`     — сам объект
  · `x'.property : x'.val ∈ A` — доказательство принадлежности

  Сокращённая запись через `CoeSort`:
  После объявления `instance : CoeSort Set (Type v)` Lean умеет автоматически
  считать `A : Set` типом (разворачивая до `A.toSubtype`). Поэтому вместо
  `(x' : A.toSubtype)` можно писать просто `(x' : A)` — это та же самая вещь.

  Зачем это нужно:
  Аксиомы спецификации и замены принимают предикаты `P : A → Prop`
  (что означает `P : A.toSubtype → Prop`). Такой предикат получает
  не просто `Object`, а пару «объект + доказательство принадлежности»,
  что позволяет внутри `P` ссылаться на факт `x ∈ A` без лишних аргументов.
-/

/--
  This defines the subtype {lean}`A.toSubtype` for any {lean}`A:Set`.
  Note that {lean}`A.toSubtype` gives you a type, similar to
  how {name}`Object` or {name}`Set` are types.
  A value {given (type := "A.toSubtype")}`x'` of type {lean}`A.toSubtype` combines
  some {given}`x: Object` with a proof that {given}`hx: x ∈ A`.

  To produce an element {name}`x'` of this subtype, use
  {lean (type := "A.toSubtype")}`⟨ x, hx ⟩`, where {lean}`x: Object` and {lean}`hx: x ∈ A`.
  The object {name}`x` associated to a subtype element {name}`x'` is
  recovered as {lean}`x'.val`, and the property {name}`hx` that {name}`x` belongs to
  {name}`A` is recovered as {lean}`x'.property`.
-/
abbrev SetTheory.Set.toSubtype (A : Set) := Subtype (fun x ↦ x ∈ A)

example (A : Set) (x : Object) (hx : x ∈ A) : A.toSubtype := ⟨x, hx⟩
example (A : Set) (x' : A.toSubtype) : Object := x'.val
example (A : Set) (x' : A.toSubtype) : x'.val ∈ A := x'.property

-- На практике подтип позволяет упаковать объект вместе с
-- доказательством принадлежности в одно значение.
-- Сравни два доказательства: они эквивалентны, но второе упаковывает x и hx в x.
example (A B : Set) (x : Object) (hx : x ∈ A) : x ∈ A ∪ B := by simp; left; exact hx
example (A B : Set) (x' : A.toSubtype) : x'.val ∈ A ∪ B := by simp; left; exact x'.property

instance : CoeSort (Set) (Type v) where
  coe A := A.toSubtype

-- Теперь благодара инстансу CoeSort (Set) (Type v) вместо x : A.toSubtype можно писать просто x : A.
-- Сравни три доказательства: они эквивалентны, но последнее читается лаконичнее всего.
example (A B : Set) (x : Object) (hx : x ∈ A) : x ∈ A ∪ B := by simp; left; exact hx
example (A B : Set) (x' : A.toSubtype) : x'.val ∈ A ∪ B := by simp; left; exact x'.property
example (A B : Set) (x' : A) : x'.val ∈ A ∪ B := by simp; left; exact x'.property

/--
  Любой элемент множества (неявно приведённый к подтипу) принадлежит этому множеству
  в смысле отношения принадлежности данной теории множеств.
-/
lemma SetTheory.Set.subtype_property (A : Set) (x : A) : x.val ∈ A := x.property
lemma SetTheory.Set.subtype_coe (A : Set) (x : A) : x.val = x := rfl
lemma SetTheory.Set.coe_inj (A : Set) (x y : A) : x.val = y.val ↔ x = y := Subtype.coe_inj

/--
  If one has a proof {name}`hx` of {lean}`x ∈ A`, then {lean}`A.subtype_mk hx` will
  then make the element of {name}`A` (viewed as a subtype) corresponding to {name}`x`.
-/
def SetTheory.Set.subtype_mk (A : Set) {x : Object} (hx : x ∈ A) : A := ⟨x, hx⟩

@[simp]
lemma SetTheory.Set.subtype_mk_coe {A : Set} {x : Object} (hx : x ∈ A) :
  A.subtype_mk hx = x := by rfl

/-
  ## Аксиома спецификации (Axiom 3.6): `A.specify P`

  `A.specify P` задумана как аналог `{ x ∈ A | P(x) }`, но в Lean она объявлена
  в классе `SetTheory` как **аксиома** — то есть `specify` создаёт некое непрозрачное
  множество, и Lean сам по себе не знает, что в нём лежит.

  Именно поэтому нужны три леммы ниже: они составляют API, который сообщает Lean'у
  правила принадлежности `A.specify P`. Без них о содержимом этого множества
  нельзя доказать ничего.

  Тип предиката: `P : A → Prop`, то есть `P : A.toSubtype → Prop`.
  Предикат принимает не просто `x : Object`, а элемент подтипа — пару ⟨x, hx⟩,
  где `hx : x ∈ A`. Благодаря этому внутри `P` автоматически известно,
  что аргумент принадлежит `A`.
-/
abbrev SetTheory.Set.specify (A : Set) (P : A → Prop) : Set := SetTheory.specify A P

-- Три леммы покрывают три разных ситуации в доказательствах:
-- specification_axiom   — имеем `x : Object` и `x ∈ A.specify P`; извлекает `x ∈ A`.
-- specification_axiom'  — имеем `x : A` (элемент подтипа); даёт `↔` с `P x` напрямую.
-- specification_axiom'' — имеем `x : Object`; даёт `↔` через `∃ h : x ∈ A, P ⟨x, h⟩`.

-- Вот эти три теоремы просто являются
-- спецификой реализации аксиомы спецификации (выделения) в Lean4.
-- Они нужны для инструментального удобства, скажем так :)

-- Направление «→»: принадлежность спецификации влечёт принадлежность исходному множеству.
-- Используй, когда имеешь `h : x ∈ A.specify P` и нужно получить `x ∈ A`.
/-- Axiom 3.6 (axiom of specification) -/
theorem SetTheory.Set.specification_axiom
  {A : Set} {P : A → Prop} {x : Object} (h : x ∈ A.specify P) :
    x ∈ A := (SetTheory.specification_axiom A P).1 x h

-- Двустороннее ↔, когда x уже является элементом подтипа `x : A`.
-- Используй, когда уже держишь в руках элемент подтипа и хочешь переключиться
-- между `x.val ∈ A.specify P` и `P x`.
/-- Axiom 3.6 (axiom of specification) -/
theorem SetTheory.Set.specification_axiom'
  {A : Set} (P : A → Prop) (x : A) : x.val ∈ A.specify P ↔ P x :=
    (SetTheory.specification_axiom A P).2 x

-- Двустороннее ↔ для сырого объекта `x : Object`.
-- Правая часть `∃ h : x ∈ A, P ⟨x, h⟩` читается так:
--   «существует доказательство h того, что x ∈ A,
--   при котором P выполняется на паре ⟨x, h⟩ : A».
-- Это эквивалентно «x ∈ A ∧ P(x)», но записанное через ∃ — так, чтобы
-- можно было построить элемент подтипа и передать его в P.
-- Это основной вариант для работы в доказательствах с `x : Object`.
/-- Axiom 3.6 (axiom of specification) -/
@[simp]
theorem SetTheory.Set.specification_axiom'' {A : Set} (P : A → Prop) (x : Object) :
  x ∈ A.specify P ↔ ∃ h : x ∈ A, P ⟨x, h⟩ := by
    constructor
    . intro h; use specification_axiom h
      simp [←specification_axiom' P, h]
    intro ⟨ h, hP ⟩
    simpa [←specification_axiom' P] using hP

-- Непосредственное следствие specification_axiom: спецификация есть подмножество A.
-- Ну, по сути, это и есть выделение некоторого подмножества при помощи фильтрации.
theorem SetTheory.Set.specify_subset {A : Set} (P : A → Prop) : A.specify P ⊆ A := by
  rw [subset_def]
  intro x hx
  exact specification_axiom hx -- (h : x ∈ A.specify P) : x ∈ A

/-- This exercise may require some understanding of how subtypes are implemented in Lean. -/
theorem SetTheory.Set.specify_congr
  {A A' : Set} (hAA' : A = A') {P : A → Prop} {P' : A' → Prop}
    (hPP' : (x : Object) → (h : x ∈ A) → (h' : x ∈ A') → (P ⟨x, h⟩ ↔ P' ⟨x, h'⟩)) :
      A.specify P = A'.specify P' := by
        -- Равенство множеств доказывается через экстенсиональность
        ext x
        have h₀ := specification_axiom'' P  x -- (x : Object) : x ∈ A.specify P ↔ ∃ (h : x ∈ A), P ⟨x, h⟩
        have h₁ := specification_axiom'' P' x -- (x : Object) : x ∈ A.specify P ↔ ∃ (h : x ∈ A), P ⟨x, h⟩
        subst hAA' -- Заменим везде A' = A
        rw [h₀, h₁]
        constructor
        · rintro ⟨h, hP⟩
          have heq := hPP' x h h
          have hP' := heq.mp hP
          exact ⟨h, hP'⟩
        · rintro ⟨h, hP'⟩
          have heq := hPP' x h h
          have hP := heq.mpr hP'
          exact ⟨h, hP⟩

theorem SetTheory.Set.specify_congr'
  {A A' : Set} (hAA' : A = A') {P : A → Prop} {P' : A' → Prop}
    (hPP' : (x : Object) → (h : x ∈ A) → (h' : x ∈ A') → P ⟨x, h⟩ ↔ P' ⟨x, h'⟩) :
      A.specify P = A'.specify P' := by
        -- Можно было бы сразу везде выполнить замену: A' = A
        subst hAA'
        -- Затем рассмотреть равенство множеств по экстенсиональности
        ext x
        -- simp only [specification_axiom'']
        -- (x : Object) : x ∈ A.specify P ↔ ∃ (h : x ∈ A), P ⟨x, h⟩
        rw [specification_axiom'', specification_axiom'']
        -- exists_congr (h : ∀ (a : α), p a ↔ q a) : (∃ a, p a) ↔ ∃ a, q a
        exact exists_congr fun h => hPP' x h h
        --
        -- exists_congr словами: если для любого из одного следует другое, то
        -- найдется хотя бы один, для которого это верно.
        -- constructor
        -- · rintro ⟨h, hP⟩
        --   have heq := hPP' x h h
        --   have hP' := heq.mp hP
        --   exact ⟨h, hP'⟩
        -- · rintro ⟨h, hP'⟩
        --   have heq := hPP' x h h
        --   have hP := heq.mpr hP'
        --   exact ⟨h, hP⟩

-- Определение пересечения с помощью инстанса класса типов Inter.
-- Нужно, чтобы иметь возможность использовать нотацию пересечения X ∩ Y.
instance SetTheory.Set.instIntersection : Inter Set where
  -- Любой элемент из X является также элементом из Y.
  -- Используем аксиому спецификации (выделения) для выделения такого подмножества из множества X.
  inter X Y := X.specify (fun x ↦ x.val ∈ Y)

-- Now we can use the `X ∩ Y` notation for an intersection of two `Set`s.
example (X Y : Set) : X ∩ Y = X.specify (fun x ↦ x.val ∈ Y) := rfl

/-- Definition 3.1.22 (Intersections) -/
@[simp]
theorem SetTheory.Set.mem_inter (x : Object) (X Y : Set) :
  x ∈ (X ∩ Y) ↔ (x ∈ X ∧ x ∈ Y) := by
    constructor
    · intro h
      -- (h : x ∈ A.specify (P : X ∩ Y)) : x ∈ A
      have hX : x ∈ X := specification_axiom h
      -- (P : A.toSubtype → Prop) (x : A.toSubtype) : ↑x ∈ A.specify P ↔ P x
      have hiff := specification_axiom' (fun z ↦ z.val ∈ Y) ⟨x, hX⟩
      have hY : x ∈ Y := hiff.mp h
      exact ⟨hX, hY⟩
    · rintro ⟨hX, hY⟩
      have hiff := specification_axiom' (fun z ↦ z.val ∈ Y) ⟨x, hX⟩
      exact hiff.mpr hY

/-- Definition 3.1.22 (Intersections) -/
@[simp]
theorem SetTheory.Set.mem_inter' (x : Object) (X Y : Set) :
  x ∈ (X ∩ Y) ↔ (x ∈ X ∧ x ∈ Y) := by
    constructor
    . intro h
      have h' := specification_axiom h
      simp [h']
      exact (specification_axiom' _ ⟨x, h'⟩).mp h
    · intro ⟨ hX, hY ⟩
      exact (specification_axiom' (fun x ↦ x.val ∈ Y) ⟨x, hX⟩).mpr hY

instance SetTheory.Set.instSDiff : SDiff Set where
  sdiff X Y := X.specify (fun x ↦ x.val ∉ Y)

-- Now we can use the `X \ Y` notation for a difference of two `Set`s.
example (X Y : Set) : X \ Y = X.specify (fun x ↦ x.val ∉ Y) := rfl

/-- Definition 3.1.26 (Difference sets) -/
@[simp]
theorem SetTheory.Set.mem_sdiff (x : Object) (X Y : Set) :
  x ∈ (X \ Y) ↔ (x ∈ X ∧ x ∉ Y) := by
    constructor
    . intro h
      have h' := specification_axiom h -- (h : x ∈ A.specify P) : x ∈ A
      simp [h']
      exact (specification_axiom' _ ⟨x, h'⟩).mp h
    · intro ⟨hX, hY⟩
      exact (specification_axiom' (fun x ↦ x.val ∉ Y) ⟨x, hX⟩).mpr hY

/-- Proposition 3.1.27(d) / Exercise 3.1.6 -/
theorem SetTheory.Set.inter_comm (A B : Set) : A ∩ B = B ∩ A := by
  ext x
  constructor
  · intro h
    rw [mem_inter] at *
    exact ⟨h.right, h.left⟩
  · intro h
    rw [mem_inter] at *
    exact ⟨h.right, h.left⟩

/-- Proposition 3.1.27(d) / Exercise 3.1.6 — идиоматичная версия -/
theorem SetTheory.Set.inter_comm' (A B : Set) : A ∩ B = B ∩ A := by
  ext x
  simp only [mem_inter]
  rw [And.comm]

/-- Proposition 3.1.27(b) -/
theorem SetTheory.Set.subset_union {A X : Set} (hAX : A ⊆ X) : A ∪ X = X := by
  ext x
  rw [mem_union]
  rw [subset_def] at hAX
  rw [or_iff_right_iff_imp] -- (a ∨ b ↔ b) ↔ a → b
  apply hAX

/-- Proposition 3.1.27(b) -/
theorem SetTheory.Set.union_subset {A X : Set} (hAX : A ⊆ X) : X ∪ A = X := by
  rw [union_comm]
  exact subset_union hAX

/-- Proposition 3.1.27(c) -/
@[simp]
theorem SetTheory.Set.inter_self (A : Set) : A ∩ A = A := by
  ext x
  rw [mem_inter]
  rw [and_self]

/-- Proposition 3.1.27(e) -/
theorem SetTheory.Set.inter_assoc (A B C : Set) :
  (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
    ext x
    repeat rw [mem_inter]
    tauto

/-- Proposition 3.1.27(f) -/
theorem  SetTheory.Set.inter_union_distrib_left (A B C : Set) :
  A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
    ext x
    -- simp only [mem_inter, mem_union]
    rw [mem_union]
    repeat rw [mem_inter]
    rw [mem_union]
    -- tauto
    constructor
    · rintro ⟨ha, hb | hc⟩
      · left;  exact ⟨ha, hb⟩
      · right; exact ⟨ha, hc⟩
    · rintro (⟨ha, hb⟩ | ⟨ha, hc⟩)
      · exact ⟨ha, Or.inl hb⟩
      · exact ⟨ha, Or.inr hc⟩

/-- Proposition 3.1.27(f) -/
theorem  SetTheory.Set.union_inter_distrib_left (A B C : Set) :
  A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
    ext x
    simp only [mem_inter, mem_union]
    -- rw [mem_inter]
    -- repeat rw [mem_union]
    -- rw [mem_inter]
    tauto

/-- Proposition 3.1.27(f) -/
theorem SetTheory.Set.union_compl {A X : Set} (hAX : A ⊆ X) : A ∪ (X \ A) = X := by
  ext x
  -- simp only [mem_union, mem_sdiff]
  rw [mem_union, mem_sdiff]
  rw [subset_def] at hAX -- X ⊆ Y ↔ ∀ x ∈ X, x ∈ Y
  specialize hAX x
  tauto

/-- Proposition 3.1.27(f) -/
theorem SetTheory.Set.inter_compl {A X : Set} : A ∩ (X \ A) = ∅ := by
  ext x
  rw [mem_inter, mem_sdiff]
  have hmem := not_mem_empty x -- ∀ x, x ∉ (∅ : Set)
  tauto

/-- Proposition 3.1.27(g) -/
theorem SetTheory.Set.compl_union {A B X : Set} : X \ (A ∪ B) = (X \ A) ∩ (X \ B) := by
  ext x
  rw [mem_inter]
  repeat rw [mem_sdiff]
  rw [mem_union]
  rw [not_or] -- ¬(p ∨ q) ↔ ¬p ∧ ¬q
  tauto

/-- Proposition 3.1.27(g) -/
theorem SetTheory.Set.compl_inter {A B X : Set} : X \ (A ∩ B) = (X \ A) ∪ (X \ B) := by
  ext x
  rw [mem_union]
  repeat rw [mem_sdiff]
  rw [mem_inter]
  rw [not_and] -- ¬(a ∧ b) ↔ a → ¬b
  tauto

-- Делаем множествa дистрибутивными решетками.
/-- Not from textbook: sets form a distributive lattice. -/
instance SetTheory.Set.instDistribLattice : DistribLattice Set where
  le := (· ⊆ ·)
  le_refl : ∀ (A : Set), A ⊆ A := subset_self
  le_trans : ∀ (X A B : Set), X ⊆ A → A ⊆ B → X ⊆ B := fun _ _ _ ↦ subset_trans
  le_antisymm : ∀ (A B : Set), A ⊆ B → B ⊆ A → A = B := subset_antisymm
  inf := (· ∩ ·)
  sup := (· ∪ ·)
  le_sup_left : ∀ (a b : Set), a ⊆ a ∪ b := by
    intro a b x hx
    rw [mem_union]
    left
    exact hx
  le_sup_right : ∀ (a b : Set), b ⊆ a ∪ b := by
    intro a b x hx
    rw [mem_union]
    right
    exact hx
  sup_le : ∀ (a b c : Set), a ⊆ c → b ⊆ c → a ∪ b ⊆ c := by
    intro a b c hac hbc x hx
    rw [mem_union] at hx
    -- tauto
    rcases hx with ha | hb
    · exact hac x ha
    · exact hbc x hb
  inf_le_left : ∀ (a b : Set), a ∩ b ⊆ a := by
    intro a b x hxab
    rw [mem_inter] at hxab
    exact hxab.1
  inf_le_right : ∀ (a b : Set), a ∩ b ⊆ b := by
    intro a b x hxab
    rw [mem_inter] at hxab
    exact hxab.2
  le_inf : ∀ (a b c : Set), a ⊆ b → a ⊆ c → a ⊆ b ∩ c := by
    intro a b c hab hac x hx
    rw [mem_inter]
    have hax := hab x hx
    have hcx := hac x hx
    exact ⟨hax, hcx⟩
  le_sup_inf : ∀ (x y z : Set), (x ∪ y) ∩ (x ∪ z) ⊆ x ∪ (y ∩ z) := by
    intro X Y Z
    rw [← union_inter_distrib_left] -- A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)

/-- Sets have a minimal element.  -/
-- Даём Set структуру решётки через ⊆ как ≤, и ∅ как ⊥.
instance SetTheory.Set.instOrderBot : OrderBot Set where
  bot := ∅
  bot_le : ∀ (A : Set), ∅ ⊆ A := empty_subset

-- Disjoint (что-либо "непересекающееся") в Mathlib — это
-- общее понятие из теории решёток, а не специфичное для множеств.
-- Оно определено для любого типа с частичным порядком ≤ и наименьшим элементом ⊥:
--    Disjoint a b ↔ ∀ c, c ≤ a → c ≤ b → c ≤ ⊥
--
-- то есть единственный элемент, который лежит "ниже" одновременно a и b это ⊥.
-- Нам это нужно, чтобы не изобретать своё собственное определение непересекающихся множеств:
-- вместо этого мы даём Set структуру решётки (через ⊆ как ≤, и ∅ как ⊥, см. instOrderBot выше),
-- и тогда Mathlib-евское общее определение Disjoint автоматически
-- применимо к нашим множествам и совпадает с привычным A ∩ B = ∅
-- (это показано ниже в disjoint_iff).
--
-- Now we've defined `A ≤ B` to mean `A ⊆ B`, and set `⊥` to `∅`.
-- This makes the `Disjoint` definition from Mathlib work with our `Set`.
example (A B : Set) : (A ≤ B) ↔ (A ⊆ B) := by rfl
example : ⊥ = (∅ : Set) := by rfl
example (A B : Set) : Prop := Disjoint A B

/-- Definition of disjointness (using the previous instances) -/
theorem SetTheory.Set.disjoint_iff (A B : Set) : Disjoint A B ↔ A ∩ B = ∅ := by
  convert _root_.disjoint_iff

-- Тождество неразличимых по Лейбницу.
abbrev SetTheory.Set.replace (A : Set) {P : A → Object → Prop}
  (hP : ∀ x y y', P x y ∧ P x y' → y = y') : Set := SetTheory.replace A P hP

/-- Axiom 3.7 (Axiom of replacement) -/
-- Позволяет задавать отображения типа таких {3,4,5} → {3++,4++,5++}
@[simp]
theorem SetTheory.Set.replacement_axiom {A : Set} {P : A → Object → Prop}
  (hP : ∀ x y y', P x y ∧ P x y' → y = y') (y : Object) :
    y ∈ A.replace hP ↔ ∃ x, P x y :=
      SetTheory.replacement_axiom A P hP y

abbrev Nat := SetTheory.nat

-- Going forward, we'll use `Nat` as a type.
-- However, notice we've set `Nat` to `SetTheory.nat` which is a `Set` and not a type.
-- The only reason we can write `x: Nat` is because we've previously defined a `CoeSort`
-- coercion that lets us write `x: A` (when `A` is a `Set`) as a shortcut for `x: A.toSubtype`.
-- This is why, whenever you see `x: Nat`, you're really looking at `x: Nat.toSubtype`.
example (x : Nat) : Nat.toSubtype := x
example (x : Nat) : Object := x.val
example (x : Nat) : (x.val ∈ Nat) := x.property
example (o : Object) (ho : o ∈ Nat) : Nat := ⟨o, ho⟩

/-- Axiom 3.8 (Axiom of infinity) -/
def SetTheory.Set.nat_equiv : ℕ ≃ Nat := SetTheory.nat_equiv

-- Below are some API for handling coercions. This may not be the optimal way to set things up.
instance SetTheory.Set.instOfNat {n : ℕ} : OfNat Nat n where
  ofNat := nat_equiv n

-- Now we can define `Nat` with a natural literal.
example : Nat := 5
example : (5 : Nat).val ∈ Nat := (5 : Nat).property

instance SetTheory.Set.instNatCast : NatCast Nat where
  natCast n := nat_equiv n

-- Now we can turn `ℕ` into `Nat`.
example (n : ℕ) : Nat := n
example (n : ℕ) : (n : Nat).val ∈ Nat := (n : Nat).property

instance SetTheory.Set.toNat : Coe Nat ℕ where
  coe n := nat_equiv.symm n

-- Now we can turn `Nat` into `ℕ`.
example (n : Nat) : ℕ := n

instance SetTheory.Object.instNatCast : NatCast Object where
  natCast n := (n : Nat).val

-- Now we can turn `ℕ` into an `Object`.
example (n : ℕ) : Object := n
example (n : ℕ) : Set := {(n : Object)}

instance SetTheory.Object.instOfNat {n : ℕ} : OfNat Object n where
  ofNat := ((n : Nat) : Object)

-- Now we can define `Object` with a natural literal.
example : Object := 1
example : Set := {1, 2, 3}

@[simp]
lemma SetTheory.Object.ofnat_eq {n : ℕ} : ((n : Nat) : Object) = (n : Object) := rfl

lemma SetTheory.Object.ofnat_eq' {n : ℕ} : (ofNat(n) : Object) = (n : Object) := rfl

@[simp]
lemma SetTheory.Object.ofnat_eq'' {n : Nat} : ((n : ℕ) : Object) = (n : Object) := by
  simp [Nat.cast, NatCast.natCast, Equiv.apply_symm_apply]

@[simp]
lemma SetTheory.Object.ofnat_eq''' {n : ℕ} {hn} : ((⟨(n : Object), hn⟩ : nat) : ℕ) = n := by
  simp [Nat.cast, NatCast.natCast, Equiv.symm_apply_apply]

lemma SetTheory.Set.nat_coe_eq {n : ℕ} : (n : Nat) = OfNat.ofNat n := rfl

@[simp]
lemma SetTheory.Set.nat_equiv_inj (n m : ℕ) : (n : Nat) = (m : Nat) ↔ n = m  :=
  Equiv.apply_eq_iff_eq nat_equiv

@[simp]
lemma SetTheory.Set.nat_equiv_symm_inj (n m : Nat) : (n : ℕ) = (m : ℕ) ↔ n = m :=
  Equiv.apply_eq_iff_eq nat_equiv.symm

@[simp]
theorem SetTheory.Set.ofNat_inj (n m : ℕ) :
    (ofNat(n) : Nat) = (ofNat(m) : Nat) ↔ ofNat(n) = ofNat(m) := by
      convert nat_equiv_inj _ _

example : (5 : Nat) ≠ (3 : Nat) := by
  simp

@[simp]
theorem SetTheory.Set.ofNat_inj' (n m : ℕ) :
    (ofNat(n) : Object) = (ofNat(m) : Object) ↔ ofNat(n) = ofNat(m) := by
      simp only [←Object.ofnat_eq, Object.ofnat_eq', Set.coe_inj, Set.nat_equiv_inj]
      rfl

example : (5 : Object) ≠ (3 : Object) := by
  simp

@[simp]
lemma SetTheory.Set.nat_coe_eq_iff {m n : ℕ} :
  (m : Object) = ofNat(n) ↔ m = n := by
    exact ofNat_inj' m n

example (n : ℕ) : (n : Object) = 2 ↔ n = 2 := by
  simp

@[simp]
theorem SetTheory.Object.natCast_inj (n m : ℕ) :
    (n : Object) = (m : Object) ↔ n = m := by
      simp [←ofnat_eq, Subtype.val_inj]

@[simp]
lemma SetTheory.Set.nat_equiv_coe_of_coe (n : ℕ) : ((n : Nat) : ℕ) = n :=
  Equiv.symm_apply_apply nat_equiv n

@[simp]
lemma SetTheory.Set.nat_equiv_coe_of_coe' (n : Nat) : ((n : ℕ) : Nat) = n :=
  Equiv.symm_apply_apply nat_equiv.symm n

@[simp]
lemma SetTheory.Set.nat_equiv_coe_of_coe'' (n : ℕ) : ((ofNat(n) : Nat) : ℕ) = n :=
  nat_equiv_coe_of_coe n

@[simp]
lemma SetTheory.Set.nat_coe_eq_iff' {m : Nat} {n : ℕ} :
  (m : Object) = (ofNat(n) : Object) ↔ (m : ℕ) = ofNat(n) := by
    constructor <;> intro h <;> rw [show m = n by aesop]
    apply nat_equiv_coe_of_coe; rfl

example : (2 : ℕ) ≠ (7 : Nat) := by
  simp

/-- Example 3.1.16 (simplified).  -/
example : ({3, 5} : Set) ⊆ {1, 3, 5} := by
  rw [subset_def]
  intro x
  rw [mem_pair]
  rw [mem_triple]
  tauto

/-- Example 3.1.17 (simplified). -/
example : ({3, 5} : Set).specify (fun x ↦ x.val ≠ 3) = ({5} : Set) := by
  ext x
  rw [mem_singleton]
  rw [specification_axiom'']
  constructor
  · rintro ⟨h1, h2⟩
    have h3 := (mem_pair x 3 5).mp h1 -- x ∈ {a, b} → x = a ∨ x = b
    rcases h3 with h3 | h5
    · have hx3 : x ≠ 3 := h2
      contradiction -- exact absurd h3 hx3
    · exact h5
  · rintro h
    rw [h]
    have hmem : (5 : Object) ∈ ({3, 5} : Set) :=
      (mem_pair 5 3 5).mpr (Or.inr rfl)
    use hmem
    show (5 : Object) ≠ 3
    norm_num

-- Пример использования norm_num, который мы будем использовать в упражнении ниже:
-- Ложная гипотеза о числовых литералах закрывает любую цель.
-- `norm_num at h` сводит `h` к `False` (через ofNat_inj'), и цель уже неважна.
example (h : (1 : Object) = 3) : (1 : Object) = 2 ∨ (1 : Object) = 4 := by
  norm_num at h

/-- Example 3.1.24 -/
example : ({1, 2, 4} : Set) ∩ {2, 3, 4} = {2, 4} := by
  ext x
  rw [mem_inter]
  rw [mem_pair, mem_triple, mem_triple]
  -- `tauto` сам по себе не видит, что разные числовые литералы (Object) различны,
  -- поэтому в прямую сторону перебираем все 3×3 варианта равенства x и подставляем (subst h1).
  --
  -- В противоречивых случаях, например:
  -- h2 : (1 : Object) = 3
  -- -| 1 = 2 ∨ 1 = 4
  -- norm_num at h2 переписывает h2 через @[simp]-лемму ofNat_inj' в
  -- ℕ-равенство (1 : ℕ) = 3, встроенным числовым движком видит, что оно ложно,
  -- и сводит h2 к `False`. Гипотеза `False` в контексте автоматически закрывает
  -- текущую цель — саму дизъюнкцию `1 = 2 ∨ 1 = 4` доказывать не нужно.
  constructor
  · rintro ⟨h1 | h1 | h1, h2 | h2 | h2⟩ <;> subst h1 <;> first | tauto | norm_num at h2
  · rintro (h | h) <;> tauto

/-- Example 3.1.24 -/
example : ({1, 2, 4} : Set) ∩ {2, 3, 4} = {2, 4} := by
  ext x
  -- Instead of unfolding repetitive branches by hand like earlier,
  -- you can use the `aesop` tactic which does this automatically.
  aesop -- Большой атом очевидности :)

/-- Example 3.1.24 -/
example : ({1, 2} : Set) ∩ {3, 4} = ∅ := by
  rw [eq_empty_iff_forall_notMem] -- X = ∅ ↔ ∀ (x : Object), x ∉ X
  aesop

-- Disjoint A B (см. пояснение выше про Mathlib-евское определение через решётки) —
-- это способ сказать «A и B не пересекаются», не привязываясь к
-- конкретным ∩ и ∅ (идее/операции пересечения и понятия пустоты или небытия).
--
-- Здесь мы хотим показать, что {1,2,3} и {2,3,4} пересекаются (у них общие элементы 2 и 3),
-- поэтому доказываем отрицание `¬ Disjoint ...`. Чтобы работать с этим определением,
-- сначала через `disjoint_iff` переписываем его в привычный вид `A ∩ B = ∅`, а дальше
-- `intro h` берёт это равенство как гипотезу (для доказательства отрицания) и приводит
-- к противоречию: `notMem`-форма показывает, что, например, 2 лежит
-- в обоих множествах, а значит не может лежать в пустом пересечении.
example : ¬ Disjoint ({1, 2, 3} : Set) {2, 3, 4} := by
  rw [disjoint_iff] -- Disjoint A B ↔ A ∩ B = ∅
  intro h
  rw [eq_empty_iff_forall_notMem] at h -- X = ∅ ↔ ∀ (x : Object), x ∉ X
  aesop -- norm_num at h

-- Методом очевидности.
example : Disjoint (∅ : Set) ∅ := by aesop

-- Методом "откуда это берётся?".
example : Disjoint (∅ : Set) ∅ := by
  rw [disjoint_iff] -- Disjoint A B ↔ A ∩ B = ∅
  rw [eq_empty_iff_forall_notMem] -- X = ∅ ↔ ∀ (x : Object), x ∉ X
  intro x hx
  rw [mem_inter] at hx -- x ∈ X ∩ Y ↔ x ∈ X ∧ x ∈ Y
  have h₀ := hx.1
  have h₁ := not_mem_empty x -- ∀ x, x ∉ (∅ : Set)
  contradiction

/-- Definition 3.1.26 example -/
example : ({1, 2, 3, 4} : Set) \ {2, 4, 6} = {1, 3} := by
  apply ext; aesop

example : ({1, 2, 3, 4} : Set) \ {2, 4, 6} = {1, 3} := by
  ext x
  rw [mem_sdiff]
  rw [mem_pair]
  rw [mem_insert, mem_triple, mem_triple]
  constructor
  · rintro ⟨h1 | h1 | h1 | h1, h2⟩ <;> subst h1 <;> tauto
  · rintro (h | h) <;> subst h <;> exact ⟨by tauto, by norm_num⟩

/-
  Мы уже накопили некоторое количество аксиом и результатов о множествах, но всё ещё есть много
  вещей, которые мы пока не можем делать. Одна из базовых вещей, которую мы хотим делать с
  множеством — это взять каждый объект этого множества и каким-то образом преобразовать каждый
  такой объект в новый объект; например, мы можем захотеть начать с множества чисел, скажем
  {3,5,9}, и увеличить каждое на единицу, получив новое множество {4,6,10}.

  Это не то, что мы можем сделать непосредственно, используя только уже имеющиеся аксиомы,
  поэтому нам нужна новая аксиома:

  Аксиома 3.6 (Замена):

  Пусть A — множество.
  Для любого объекта x ∈ A и любого объекта y предположим, что
  у нас есть утверждение P(x,y), относящееся к x и y, такое что
  для каждого x ∈ A существует не более одного y, для которого P(x,y) истинно.
  Тогда существует множество:
    {y : P(x,y) истинно для некоторого x ∈ A}, такое что для любого объекта z,
    z ∈ {y : P(x,y) истинно для некоторого x ∈ A} ⇐⇒ P(x,z) истинно для некоторого x ∈ A.
-/
/-- Example 3.1.30 -/
example : ({3, 5, 9} : Set).replace
  (P := fun x y ↦
    ∃ (n : ℕ), (x.val = n) ∧ (y = (n + 1 : ℕ))) (by aesop) = {4, 6, 10} := by
  ext x
  -- replacement_axiom:
  --   (hP : ∀ (x : A.toSubtype) (y y' : Object), P x y ∧ P x y' → y = y')
  --   (y : Object) :
  --   y ∈ A.replace hP ↔ ∃ x, P x y
  rw [replacement_axiom]
  rw [mem_triple]
  constructor
  · rintro ⟨x1, n, hn, hx⟩
    have h3 := x1.property
    rw [mem_triple] at h3
    rw [hn] at h3
    simp only [nat_coe_eq_iff] at h3
    rcases h3 with rfl | rfl | rfl
    · rw [hx]; left; norm_num
    · rw [hx]; right; left; norm_num
    · rw [hx]; right; right; norm_num
  · -- show x = 4 ∨ x = 6 ∨ x = 10 → ∃ x_1 n, ↑x_1 = ↑n ∧ x = ↑(n + 1)
    rintro (rfl | rfl | rfl)
    · have h3 : (3 : Object) ∈ ({3, 5, 9} : Set) := by
        -- simp
        rw [mem_triple]; left; rfl
      use ⟨3, h3⟩, 3
      simp
    · have h5 : (5 : Object) ∈ ({3, 5, 9} : Set) := by simp
      use ⟨5, h5⟩, 5
      simp
    · have h9 : (9 : Object) ∈ ({3, 5, 9} : Set) := by simp
      use ⟨9, h9⟩, 9
      simp

/-- Example 3.1.31 -/
example : ({3, 5, 9} : Set).replace (P := fun _ y ↦ y = 1) (by aesop) = {1} := by
  ext x
  -- aesop
  --
  -- replacement_axiom
  --   (hP : ∀ (x : A.toSubtype) (y y' : Object), P x y ∧ P x y' → y = y')
  --   (y : Object)
  --   :
  --   y ∈ A.replace hP ↔ ∃ x, P x y
  --
  -- replace: (hP : ∀ x y y', P x y ∧ P x y' → y = y') : Set
  --
  -- Фишка в том, что `{3, 5, 9}.replace` это и есть `hP`,
  -- то есть совпадает по типу с требуемой гипотезой для replacement_axiom.
  rw [replacement_axiom]
  --
  -- toSubtype это «зависимая пара»:
  -- значение несёт в себе объект вместе с доказательством его принадлежности множеству.
  --
  -- A.toSubtype = { x : Object // x ∈ A }, то есть тип пар ⟨x, hx⟩,
  -- где `x : Object` и `hx : x ∈ A`.
  constructor
  · rintro ⟨s, hx⟩
    rw [← mem_singleton] at hx
    exact hx
  · rintro hx
    have h3 : (3 : Object) ∈ ({3, 5, 9} : Set) := by
    -- mem_triple (x a b c : Object) : x ∈ ({a,b,c} : Set) ↔ (x = a ∨ x = b ∨ x = c)
      refine (mem_triple 3 3 5 9).mpr ?_
      left; rfl
    have hx1 : x = 1 := by
      rw [← mem_singleton]
      exact hx
    -- use ⟨3, h3⟩
    -- Не очевидно, что x_1 имеет тип {3, 5, 9} : Set
    show ∃ x_1 : ({3, 5, 9} : Set), x = 1
    -- тип x_1 нигде явно не печатается в цели — он берётся из домена `P` в
    -- `replacement_axiom {P : A → Object → Prop}`, где `A` через CoeSort означает `A.toSubtype`.
    -- Ниже разъяснено, как поступать в подобных ситуациях.
    refine ⟨?_, hx1⟩
    exact ⟨3, h3⟩

-- Заметка на будущее: если не понятно, что подставить в `∃ x_1, ...` —
-- не гадай по напечатанной цели (тип связанной переменной там всегда скрыт).
-- Вместо этого:
-- 1) refine ⟨?_, ...⟩, чтобы Lean показал точный тип дыры;
-- 2) если тип — это A.toSubtype, вспомни, что это снова пара ⟨val, proof⟩;
-- 3) при необходимости смотри исходную сигнатуру леммы (replacement_axiom),
--    откуда взялся экзистенциал, а не уже инстанцированную цель.

/-- Exercise 3.1.5.  One can use the {tactic}`tfae_have` and
    {tactic}`tfae_finish` tactics here.
    TFAE: The Following (propositions) Are Equivalent. -/
theorem SetTheory.Set.subset_tfae (A B : Set) :
  [A ⊆ B, A ∪ B = B, A ∩ B = A].TFAE := by
    tfae_have (h1iff2 : A ⊆ B ↔ A ∪ B = B) : 1 ↔ 2 := by
      constructor
      · rw [union_comm]
        exact union_subset -- (hAX : A ⊆ X) : X ∪ A = X
      · intro h
        rw [← h]
        intro x hx
        rw [mem_union] -- x ∈ X ∪ Y ↔ x ∈ X ∨ x ∈ Y
        left
        exact hx
    tfae_have (h2iff3 : A ∪ B = B ↔ A ∩ B = A) : 2 ↔ 3 := by
      constructor
      · intro h
        ext x
        rw [mem_inter]
        tauto
      · intro h
        rw [← h1iff2]
        rw [subset_def]
        intro x hx
        rw [← h] at hx
        rw [mem_inter] at hx
        exact hx.2
    tfae_finish

-- Это доказательство отличается от того, что я сделал на бумаге тем,
-- Что здесь мы показываем равносильности вместо импликаций,
-- поэтому нам не требуется зацикливать рассуждение:
--
-- A ⊆ B ↔ A ∪ B = B ↔ A ∩ B = A
--       ^           ^
--    h1iff2      h2iff3

-- Немного более подробная версия без применения тактики tauto
theorem SetTheory.Set.subset_tfae' (A B : Set) :
  [A ⊆ B, A ∪ B = B, A ∩ B = A].TFAE := by
    tfae_have (h1iff2 : A ⊆ B ↔ A ∪ B = B) : 1 ↔ 2 := by
      constructor
      · rw [union_comm]
        exact union_subset -- (hAX : A ⊆ X) : X ∪ A = X
      · intro h
        rw [← h]
        intro x hx
        rw [mem_union] -- x ∈ X ∪ Y ↔ x ∈ X ∨ x ∈ Y
        left
        exact hx
    tfae_have (h2iff3 : A ∪ B = B ↔ A ∩ B = A) : 2 ↔ 3 := by
      constructor
      · intro h
        apply subset_antisymm -- (hAB : A ⊆ B) (hBA : B ⊆ A) : A = B
        · intro x
          rw [mem_inter] -- x ∈ X ∩ Y ↔ x ∈ X ∧ x ∈ Y
          tauto
        · rw [subset_def] -- X ⊆ Y ↔ ∀ x ∈ X, x ∈ Y
          intro x
          rw [mem_inter]
          intro hx
          refine ⟨hx, ?_⟩
          rw [← h1iff2] at h
          exact h x hx
      · intro h
        rw [← h1iff2]
        rw [subset_def]
        intro x hx
        rw [← h] at hx
        rw [mem_inter] at hx
        exact hx.2
    -- Это уже не требуется делать, потому что
    -- мы доказывали равносильности вместо импликаций.
    -- tfae_have (h3iff1 : A ∩ B = A ↔ A ⊆ B) : 3 ↔ 1 := by
    --   constructor
    --   · sorry
    --   · sorry
    tfae_finish

/-- Exercise 3.1.7 -/
theorem SetTheory.Set.inter_subset_left (A B : Set) : A ∩ B ⊆ A := by
  rw [subset_def]
  intro x hx
  rw [mem_inter] at hx
  exact hx.1

/-- Exercise 3.1.7 -/
theorem SetTheory.Set.inter_subset_right (A B : Set) : A ∩ B ⊆ B := by
  rw [inter_comm]
  exact inter_subset_left B A

/-- Exercise 3.1.7 -/
@[simp]
theorem SetTheory.Set.subset_inter_iff (A B C : Set) : C ⊆ A ∩ B ↔ C ⊆ A ∧ C ⊆ B := by
  simp only [subset_def, mem_inter, forall_and]

#check forall_and -- (∀ (x : α), p x ∧ q x) ↔ (∀ (x : α), p x) ∧ ∀ (x : α), q x

/-- Exercise 3.1.7 -/
theorem SetTheory.Set.subset_inter_iff' (A B C : Set) : C ⊆ A ∩ B ↔ C ⊆ A ∧ C ⊆ B := by
  repeat rw [subset_def] -- simp only [subset_def]
  constructor
  · intro h
    constructor
    · intro x hxc
      specialize h x
      rw [mem_inter] at h
      exact (h hxc).1
    · intro x hxc
      specialize h x
      rw [mem_inter] at h
      exact (h hxc).2
  · intro h x hxc
    rw [mem_inter]
    -- Не буду тут повторять рассуждения, подобные тем, которые приведены выше.
    -- Следующая тактика вполне справится:
    tauto

/-- Exercise 3.1.7 -/
theorem SetTheory.Set.subset_union_left (A B : Set) : A ⊆ A ∪ B := by
  intro x hx
  rw [mem_union] -- x ∈ X ∪ Y ↔ x ∈ X ∨ x ∈ Y
  left
  exact hx

/-- Exercise 3.1.7 -/
theorem SetTheory.Set.subset_union_right (A B : Set) : B ⊆ A ∪ B := by
  rw [union_comm] -- A ∪ B = B ∪ A
  exact subset_union_left B A

/-- Exercise 3.1.7 -/
@[simp]
theorem SetTheory.Set.union_subset_iff (A B C : Set) : A ∪ B ⊆ C ↔ A ⊆ C ∧ B ⊆ C := by
  simp only [subset_def, mem_union, or_imp, forall_and]

#check or_imp -- a ∨ b → c ↔ (a → c) ∧ (b → c)

/-- Exercise 3.1.7 -/
theorem SetTheory.Set.union_subset_iff' (A B C : Set) : A ∪ B ⊆ C ↔ A ⊆ C ∧ B ⊆ C := by
  simp only [subset_def, mem_union]
  constructor
  · intro h
    split_ands
    · tauto
    · intro x hxb
      specialize h x
      tauto
  · intro h x hxab
    tauto

#check subset_antisymm -- (A B : Set), A ⊆ B → B ⊆ A → A = B

/-- Exercise 3.1.8 -/
@[simp]
theorem SetTheory.Set.inter_union_cancel (A B : Set) : A ∩ (A ∪ B) = A := by
  apply subset_antisymm
  · exact inter_subset_left A (A ∪ B) -- A ∩ B ⊆ A
  · rw [subset_inter_iff] -- C ⊆ A ∩ B ↔ C ⊆ A ∧ C ⊆ B
    have h₁ := subset_self A
    have h₂ := subset_union_left A B
    exact ⟨h₁, h₂⟩

-- Интересное наблюдение:
-- A ∩ (A ∪ B) = A  ~~  min(a, max(a, b)) = a
--                      max(a, b) = b => min(a, b) = a
--                      max(a, b) = a => min(a, a) = a
-- A ∪ (A ∩ B) = A  ~~  max(a, min(a, b)) = a

/-- Exercise 3.1.8 -/
@[simp]
theorem SetTheory.Set.union_inter_cancel (A B : Set) : A ∪ (A ∩ B) = A := by
  ext x
  simp only [mem_union, mem_inter]
  show (x ∈ A) ∨ (x ∈ A ∧ x ∈ B) ↔ x ∈ A
  tauto

/-- Exercise 3.1.9 -/
theorem SetTheory.Set.partition_left {A B X : Set}
  (h_union : A ∪ B = X) (h_inter : A ∩ B = ∅) : A = X \ B := by
    -- Лучше бы было начать вот так:
    -- ext x
    -- Но увы, я был упорот или начал вот так:
    apply subset_antisymm
    · rw [subset_def]
      intro x hxa
      rw [mem_sdiff]
      constructor
      · rw [← h_union]
        rw [mem_union]
        left
        exact hxa
      · intro hxb
        have hxab : x ∈ A ∧ x ∈ B := ⟨hxa, hxb⟩
        rw [← mem_inter, h_inter] at hxab
        have hmem := not_mem_empty x
        contradiction
    · rw [subset_def]
      intro x
      rw [mem_sdiff]
      intro ⟨hx, hnb⟩
      rw [← h_union] at hx
      rw [mem_union] at hx
      rcases hx with ha | hb
      · exact ha
      · contradiction

/-- Exercise 3.1.9 -/
-- ИИшное док-во: введение промежуточной гипотезы hnotab мне было неочевидно.
theorem SetTheory.Set.partition_left' {A B X : Set}
  (h_union : A ∪ B = X) (h_inter : A ∩ B = ∅) : A = X \ B := by
    ext x
    rw [mem_sdiff, ← h_union, mem_union]
    -- Цель `x ∈ A ↔ (x ∈ A ∨ x ∈ B) ∧ x ∉ B` не тавтология сама по себе:
    -- нужен ещё факт, что x не может лежать в A и B одновременно —
    -- это и даёт неиспользованная h_inter.
    have hnotab : ¬ (x ∈ A ∧ x ∈ B) := by
      rw [← mem_inter, h_inter]
      exact not_mem_empty x
    tauto

/-- Exercise 3.1.9 -/
theorem SetTheory.Set.partition_right {A B X : Set}
  (h_union : A ∪ B = X) (h_inter : A ∩ B = ∅) : B = X \ A := by
    ext x
    rw [mem_sdiff, ← h_union, mem_union]
    constructor
    · intro hxb
      constructor
      · right; exact hxb
      · intro hxa
        have h : x ∈ A ∧ x ∈ B := ⟨hxa, hxb⟩
        rw [← mem_inter, h_inter] at h
        have h' := not_mem_empty x
        contradiction
    · intro ⟨h, hxna⟩
      rcases h with hxa | hxb
      · contradiction
      · exact hxb

/--
  Exercise 3.1.10.
  You may find {name}`Function.onFun_apply` and the {tactic}`fin_cases` tactic useful.
-/
-- Disjoint X Y означает X ∩ Y = ∅.
-- Доказать, что три множества A \ B, A ∩ B, B \ A попарно не пересекаются.
theorem SetTheory.Set.pairwise_disjoint (A B : Set) :
  Pairwise (Function.onFun Disjoint ![A \ B, A ∩ B, B \ A]) := by
    -- Function.onFun_apply
    -- (f : β → β → γ) (g : α → β) (a b : α) :
    --   Function.onFun f g a b = f (g a) (g b)
    intro i j hij
    simp only [Function.onFun]
    rw [disjoint_iff]
    fin_cases i <;> fin_cases j
      <;> simp
      <;> (try contradiction)
      <;> (ext x; simp [mem_inter, mem_sdiff]; tauto)

-- Пример использования тактики fin_cases.
example (n : ℕ) (h : n ∈ ({0, 1, 4} : Finset ℕ)) :
    n = 0 ∨ ∃ k, n = k ^ 2 ∧ k > 0 := by
  fin_cases h
  · left; rfl
  · right; exact ⟨1, rfl, by norm_num⟩
  · right; exact ⟨2, rfl, by norm_num⟩

#check compl_inter -- X \ (A ∩ B) = X \ A ∪ X \ B
#check compl_union -- X \ (A ∪ B) = X \ A ∩ (X \ B)
#check inter_compl -- A ∩ (X \ A) = ∅
#check inter_union_cancel -- A ∩ (A ∪ B) = A
#check union_inter_cancel -- (A ∪ A) ∩ B = A

/-- Exercise 3.1.10 -/
theorem SetTheory.Set.union_eq_partition (A B : Set) :
  A ∪ B = (A \ B) ∪ (A ∩ B) ∪ (B \ A) := by
    ext x
    simp only [mem_union, mem_sdiff, mem_inter]
    -- Здесь без классической логики не обойтись,
    -- и тактика tauto как раз неявно использует
    -- Classical.em (x ∈ B) и Classical.em (x ∈ A)
    -- Ниже мы докажем один раз полностью "вручную".
    tauto

theorem SetTheory.Set.union_eq_partition' (A B : Set) :
  A ∪ B = (A \ B) ∪ (A ∩ B) ∪ (B \ A) := by
    ext x
    simp only [mem_union, mem_sdiff, mem_inter]
    constructor
    · intro h
      rcases h with hxa | hxb
      · -- x ∈ B неразрешимо конструктивно (нет Decidable-инстанса),
        -- поэтому явно применяем исключённое третье через by_cases
        by_cases hb : x ∈ B
        · left
          right
          exact ⟨hxa, hb⟩
        · left
          left
          exact ⟨hxa, hb⟩
      · by_cases ha : x ∈ A
        · left
          right
          exact ⟨ha, hxb⟩
        · right
          exact ⟨hxb, ha⟩
    · intro h
      guard_hyp h : ((x ∈ A ∧ x ∉ B) ∨ (x ∈ A ∧ x ∈ B)) ∨ (x ∈ B ∧ x ∉ A)
      -- Правый конъюнкт нас никогда не интересует,
      -- поэтому с помощью прочерка игнорируем его.
      rcases h with (⟨ha, -⟩ | ⟨ha, -⟩) | ⟨hb, -⟩
      · left
        exact ha
      · left
        exact ha
      · right
        exact hb

/--
  Exercise 3.1.11.
  The challenge is to prove this without using
  {name}`Set.specify`, {name}`Set.specification_axiom`, {name}`Set.specification_axiom'`, or
  anything built from them (like differences and intersections).
-/
-- У нас есть произвольное множество A и предикат P на его элементах.
-- Нужно построить множество B ⊆ A такое, что x.val ∈ B ↔ P x для всех x ∈ A —
-- то есть B = {x ∈ A | P x}, обычная теоретико-множественная вырезка.
-- Отличие от Set.specify в том, что здесь нельзя пользоваться аксиомой спецификации
-- (и всем, что из неё построено) — множество B нужно получить через аксиому замены (replacement_axiom).
theorem SetTheory.Set.specification_from_replacement {A : Set} {P : A → Prop} :
  ∃ B, B ⊆ A ∧ ∀ x, x.val ∈ B ↔ P x := by
    -- Двухместное отношение для аксиомы замены:
    -- y соответствует x, если P x выполнено и y — это как раз x.val
    let P' : A → Object → Prop := fun x y => P x ∧ y = x.val
    -- Однозначность:
    -- Если и y, и y' соответствуют одному x, то y = y' = x.val
    have hP : ∀ (x : A) (y y' : Object), P' x y ∧ P' x y' → y = y' := by
      rintro x y y' ⟨⟨_, hy⟩, _, hy'⟩
      rw [hy, hy']
    -- B — образ A относительно P' (аксиома замены).
    use (A.replace hP)
    constructor
    · -- B ⊆ A: всякий элемент B — это x.val для какого-то x ∈ A,
      -- а значит лежит в A
      intro y hy
      rw [replacement_axiom] at hy
      obtain ⟨x, _, hxy⟩ := hy
      rw [hxy]
      exact x.property
    · intro x
      rw [replacement_axiom]
      constructor
      · -- Если x.val = x'.val для некоторого x' с P x',
        -- то x = x' (подтипы равны по равенству val), значит P x.
        rintro ⟨x', hPx', hxx'⟩
        have hxx : x = x' := Subtype.ext hxx'
        rw [hxx]
        exact hPx'
      · -- Если P x, то сам x годится в качестве свидетеля.
        intro hPx
        exact ⟨x, hPx, rfl⟩

-- Тот же результат, но линейно: без промежуточных `let`/`have` для предиката P' и hP —
-- предикат передаём прямо в `A.replace`, а его однозначность доказываем
-- как первую цель в общем списке.
theorem SetTheory.Set.specification_from_replacement' {A : Set} {P : A → Prop} :
  ∃ B, B ⊆ A ∧ ∀ x, x.val ∈ B ↔ P x := by
  refine ⟨A.replace (P := fun x y => P x ∧ y = x.val) ?_, ?_, ?_⟩
  · -- Однозначность: y и y' оба равны x.val, значит равны друг другу.
    rintro x y y' ⟨⟨_, hy⟩, _, hy'⟩
    rw [hy, hy']
  · -- B ⊆ A.
    intro y hy
    rw [replacement_axiom] at hy
    obtain ⟨x, _, hxy⟩ := hy
    rw [hxy]
    exact x.property
  · -- x.val ∈ B ↔ P x.
    intro x
    rw [replacement_axiom]
    constructor
    · rintro ⟨x', hPx', hxx'⟩
      rw [Subtype.ext hxx']
      exact hPx'
    · intro hPx
      exact ⟨x, hPx, rfl⟩

/-- Exercise 3.1.12.-/
theorem SetTheory.Set.subset_union_subset {A B A' B' : Set}
  (hA'A : A' ⊆ A) (hB'B : B' ⊆ B) : A' ∪ B' ⊆ A ∪ B := by
      sorry

/-- Exercise 3.1.12.-/
theorem SetTheory.Set.subset_inter_subset {A B A' B' : Set}
  (hA'A : A' ⊆ A) (hB'B : B' ⊆ B) : A' ∩ B' ⊆ A ∩ B := by
    sorry

/-- Exercise 3.1.12.-/
theorem SetTheory.Set.subset_diff_subset_counter :
    ∃ (A B A' B' : Set), (A' ⊆ A) ∧ (B' ⊆ B) ∧ ¬ (A' \ B') ⊆ (A \ B) := by
      sorry

/-
  Final part of Exercise 3.1.12: state and prove a reasonable substitute positive result for the
  above theorem that involves set differences.
-/

/-- Exercise 3.1.13 -/
theorem SetTheory.Set.singleton_iff (A : Set) (hA : A ≠ ∅) :
  (¬∃ B ⊂ A, B ≠ ∅) ↔ ∃ x, A = {x} := by
    sorry

/-
  Now we introduce connections between this notion of a set, and Mathlib's notion.
  The exercise below will acquiant you with the API for Mathlib's sets.
-/

instance SetTheory.Set.inst_coe_set : Coe Set (_root_.Set Object) where
  coe X := { x | x ∈ X }

-- Now we can convert our `Set` into a Mathlib `_root_.Set`.
-- Notice that Mathlib sets are parameterized by the element type, in our case `Object`.
example (X : Set) : _root_.Set Object := X

/--
  Injectivity of the coercion. Note however that we do NOT assert that the coercion is surjective
  (and indeed Russell's paradox prevents this)
-/
@[simp]
theorem SetTheory.Set.coe_inj' (X Y : Set) :
    (X : _root_.Set Object) = (Y : _root_.Set Object) ↔ X = Y := by
  constructor
  . intro h; apply ext; intro x
    replace h := congr(x ∈ $h); simpa using h
  rintro rfl; rfl

/-- Compatibility of the membership operation {kw (of := «term_∈_»)}`∈` -/
theorem SetTheory.Set.mem_coe (X : Set) (x : Object) : x ∈ (X : _root_.Set Object) ↔ x ∈ X := by
  simp

/-- Compatibility of the emptyset -/
theorem SetTheory.Set.coe_empty : ((∅ : Set) : _root_.Set Object) = ∅ := by
  simp

/-- Compatibility of subset -/
theorem SetTheory.Set.coe_subset (X Y : Set) :
  (X : _root_.Set Object) ⊆ (Y : _root_.Set Object) ↔ X ⊆ Y := by
    simp only [Set.setOf_subset_setOf]
    rfl

theorem SetTheory.Set.coe_ssubset (X Y : Set) :
    (X : _root_.Set Object) ⊂ (Y : _root_.Set Object) ↔ X ⊂ Y := by sorry

/-- Compatibility of singleton -/
theorem SetTheory.Set.coe_singleton (x : Object) : (({x} : Set) : _root_.Set Object) = {x} := by sorry

/-- Compatibility of union -/
theorem SetTheory.Set.coe_union (X Y : Set) :
    ((X ∪ Y : Set) : _root_.Set Object) = (X : _root_.Set Object) ∪ (Y : _root_.Set Object) := by sorry

/-- Compatibility of pair -/
theorem SetTheory.Set.coe_pair (x y : Object) : (({x, y} : Set) : _root_.Set Object) = {x, y} := by sorry

/-- Compatibility of subtype -/
theorem SetTheory.Set.coe_subtype (X : Set) :  (X : _root_.Set Object) = X.toSubtype := by sorry

/-- Compatibility of intersection -/
theorem SetTheory.Set.coe_intersection (X Y : Set) :
    ((X ∩ Y : Set) : _root_.Set Object) = (X : _root_.Set Object) ∩ (Y : _root_.Set Object) := by sorry

/-- Compatibility of set difference-/
theorem SetTheory.Set.coe_diff (X Y : Set) :
    ((X \ Y : Set) : _root_.Set Object) = (X : _root_.Set Object) \ (Y : _root_.Set Object) := by sorry

/-- Compatibility of disjointness -/
theorem SetTheory.Set.coe_Disjoint (X Y : Set) :
    Disjoint (X : _root_.Set Object) (Y : _root_.Set Object) ↔ Disjoint X Y := by sorry

end Chapter3
