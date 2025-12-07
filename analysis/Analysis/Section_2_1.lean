import Mathlib.Tactic

/-!
# Analysis I, Section 2.1: The Peano Axioms

This file is a translation of Section 2.1 of Analysis I to Lean 4.  All numbering refers to the
original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing
so.

Main constructions and results of this section:

- Definition of the "Chapter 2" natural numbers, `Chapter2.Nat`, abbreviated as `Nat` within the
  Chapter2 namespace. (In the book, the natural numbers are treated in a purely axiomatic
  fashion, as a type that obeys the Peano axioms; but here we take advantage of Lean's native
  inductive types to explicitly construct a version of the natural numbers that obey those
  axioms.  One could also proceed more axiomatically, as is done in Section 3 for set theory:
  see the epilogue to this chapter.)
- Establishment of the Peano axioms for `Chapter2.Nat`.
- Recursive definitions for `Chapter2.Nat`.

Note: at the end of this chapter, the `Chapter2.Nat` class will be deprecated in favor of the
standard Mathlib class `_root_.Nat`, or `ℕ`.  However, we will develop the properties of
`Chapter2.Nat` "by hand" in the next few sections for pedagogical purposes.

-/

namespace Chapter2

/-
Это как бы предположение о существовании натуральной числовой системы ℕ.
Оно будет уточняться после введения понятий "множество" и "функция".

Т.е. просто из определения такого типа Nat ещё не следует то, что он
годится для определения натуральной числовой системы.
-/

/--
  Assumption 2.6 (Existence of natural numbers).  Here we use an explicit construction of the
  natural numbers (using an inductive type).  For a more axiomatic approach, see the epilogue to
  this chapter.
-/
inductive Nat where
| zero : Nat
| succ : Nat → Nat
deriving Repr, DecidableEq  -- this allows `decide` to work on `Nat`

/-- Axiom 2.1 (0 is a natural number) -/
instance Nat.instZero : Zero Nat := ⟨ zero ⟩
#check (0 : Nat)

/-- Axiom 2.2 (Successor of a natural number is a natural number) -/
postfix:100 "++" => Nat.succ
#check (fun n ↦ n++)
-- #check ((fun n ↦ n++) 0 : Nat)

#check ((0++)++ : Nat)

-- Единственная операция, которая у нас есть - операция увеличения на единицу.
-- Мы не говорим, что это такое за операция, и чем вообще являются натуральные числа.
-- Это типа философские вопросы. Для нас имеет значение только какие свойства имеют объекты,
-- а не то, что они из себя представляют и что означают.
--
-- Совсем не обязательно для построения натуральных чисел использовать тип, вроде
-- определённого выше Nat. Можно использовать и другие объекты, например множества и
-- понятие об их мощности. Идея в том, что все возможные натуральные числовые системы,
-- построенные из разных математических объектов/структур должны подчиняться всем
-- необходимым аксиомам и допускать необходимые действие.
-- Короче - первчина аксиоматическая система, а не выбранный объект/структура.
-- Вообще, одно из великих открытий 19 века в том, что числа можно понимать абстрактно,
-- через аксиомы, не нуждаясь в конкретной модели.

/--
  Definition 2.1.3 (Definition of the numerals 0, 1, 2, etc.). Note: to avoid ambiguity, one may
  need to use explicit casts such as (0:Nat), (1:Nat), etc. to refer to this chapter's version of
  the natural numbers.
-/
instance Nat.instOfNat {n:_root_.Nat} : OfNat Nat n where
  ofNat := _root_.Nat.rec 0 (fun _ n ↦ n++) n

instance Nat.instOne : One Nat := ⟨ 1 ⟩

lemma Nat.zero_succ : 0++ = 1 := by rfl
#check (1 : Nat)

lemma Nat.one_succ : 1++ = 2 := by rfl
#check (2 : Nat)

/-- Proposition 2.1.4 (3 is a natural number)-/
lemma Nat.two_succ : 2++ = 3 := by rfl
#check (3 : Nat)

/--
  Axiom 2.3 (0 is not the successor of any natural number).
  Compare with Lean's `Nat.succ_ne_zero`.
-/
theorem Nat.succ_ne (n : Nat) : n++ ≠ 0 := by
  by_contra h
  injection h

-- По определению тоже самое, что и Nat.succ_ne_zero

/-- Proposition 2.1.6 (4 is not equal to zero) -/
theorem Nat.four_ne : (4:Nat) ≠ 0 := by
  -- By definition, 4 = 3++.
  change 3++ ≠ 0
  -- By axiom 2.3, 3++ is not zero.
  exact succ_ne _

/-
Идея в том, чтобы начать с минимального набора аксиом.
Рассматривать различные конкретные примеры систем, построенных на
этой аксиоматической базе и врубаться насколько они противоречат
интуитивным представлениям. Если противоречат, то добавлять
минимально необходимые аксиомы, чтобы "залатать" косяки.
-/

/--
  Axiom 2.4 (Different natural numbers have different successors).
  Compare with Mathlib's `Nat.succ_inj`.
-/
theorem Nat.succ_cancel {n m:Nat} (hnm: n++ = m++) : n = m := by
  injection hnm

-- ^ Это следствие того, что ниже по закону контрапозиции:
-- https://ru.wikipedia.org/wiki/%D0%97%D0%B0%D0%BA%D0%BE%D0%BD_%D0%BA%D0%BE%D0%BD%D1%82%D1%80%D0%B0%D0%BF%D0%BE%D0%B7%D0%B8%D1%86%D0%B8%D0%B8

/--
  Axiom 2.4 (Different natural numbers have different successors).
  Compare with Mathlib's `Nat.succ_ne_succ`.
-/
theorem Nat.succ_ne_succ (n m : Nat) : n ≠ m → n++ ≠ m++ := by
  intro h
  contrapose! h
  exact succ_cancel h

/-- Proposition 2.1.8 (6 is not equal to 2) -/
theorem Nat.six_ne_two : (6 : Nat) ≠ 2 := by
-- this proof is written to follow the structure of the original text.
  by_contra h
  change 5++ = 1++ at h
  apply succ_cancel at h
  change 4++ = 0++ at h
  apply succ_cancel at h
  have := four_ne
  contradiction

/-- One can also prove this sort of result by the `decide` tactic -/
theorem Nat.six_ne_two' : (6:Nat) ≠ 2 := by
  decide

/-
Пока что всё ещё можно построить нат. числовую систему типа такой:
ℕ := {0, 0.5, 1, 1.5, 2, 2.5, 3, 3.5, ...}
Мы хотим исключить "не правильные" числа. Поэтому нам нужен какой-то способ
определять последовательности рекурсивно. Какая-то такая схема должна быть,
с помощью которой можно сказать, что существуют числа только определённого вида,
сконструированные только вот этим одним конкретным способом
(прибавлением едниницы в нашем случае).

Нужна аксиома, согласно которой все числа в ℕ могут быть получены из
нуля и операции добавления единицы, чтобы исключить любые другие элементы (типа 0.5).

И вот под "могут быть получены из" мы будем понимать принцип мат. индукции.
Это и будет нашей пятой аксиомой.
-/

/--
  Axiom 2.5 (Principle of mathematical induction). The `induction`
  (or `induction'`) tactic in Mathlib serves as a substitute for this axiom.
-/
theorem Nat.induction (P : Nat → Prop) (hbase : P 0) (hind : ∀ n, P n → P (n++)) :
    ∀ n, P n := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n hi => exact hind n hi

/-
Мы хотим построить последовательность вида {a₀, a₁, a₂, ...}. Суть в том,
что мы хотим сделать возможным переход от одного элемента последовательности к другому
только с помощью какой-то одной функциеи (у нас это операция прибавления единицы).

Используя мат. индукцию мы можем убедиться, что такая последовательность может
быть построена только одним способом, в котором переход от некоторого
предыдущего элемента aₙ к следующему aₙ++ возможен только с помощью функции fₙ:
aₙ++ := fₙ(aₙ). У нас каждая из этих функций, это операция добавления единицы (++).

c = a₀ -(f₀)→ a₁ -(f₁)→ a₂ ... aₙ -(fₙ)→ aₙ++
a₀ := c
a₁ := f₀(a₀)
a₂ := f₁(a₁)
...
aₙ++ := fₙ(aₙ)
-/

/-
Утверждение 2.1.16 (рекурсивные определения):

Для каждого n ∈ ℕ существует некоторая ф-ция fₙ : ℕ → ℕ,
которая сопоставляет этому n какое-то натуральное число.
Пусть c ∈ ℕ, тогда каждого n ∈ ℕ существует уникальное aₙ такое,
что a₀ = c и aₙ++ = f(aₙ).

Проще говоря: a₀ = c ∧ ∀ n ∈ ℕ, aₙ++ = fₙ(aₙ)

В книге написано, что мы каждому натуральному числу n сопоставляем
такую функцию перехода fₙ : ℕ → ℕ, но ведь операция у нас только одна - ++.
Поэтому имхо можно дать упрощённое определение вроде:

a₀ -(++)→ a₁ -(++)→ a₂ ... aₙ -(++)→ aₙ++
aₙ++ := (aₙ)++

Оринальное определение как будто бы позволяет иметь для каждого перехода от
одного элемента последовательности к другому какую-то свою уникальную операцию.
Т.е., например, пусть, чисто ради прикола
f₀ := (++)  - операция "прибавления" единицы
f₁ := (+++) - операция "добавления" едницицы
итд
-/

-- Вместе с индуктивным типом всегда автоматически определяется
-- принцип элиминации rec. Эту функцию также называют рекурсором,
-- и именно она делает тип индуктивным: онa позволяет определить функцию на
-- твоём индуктивном типе, присваивая значения, соответствующие каждому конструктору.
-- Интуитивно, индуктивный тип исчерпывающе порождается своими конструкторами и
-- не имеет элементов, кроме тех, которые они создают.
--
-- Вот ниже показано как раз как она выглядит для наших натуральных чисел.

/--
  Recursion. Analogous to the inbuilt Mathlib method `Nat.rec` associated to
  the Mathlib natural numbers
-/
abbrev Nat.recurse (f: Nat → Nat → Nat) (c : Nat) : Nat → Nat :=
  fun n ↦
    match n with
    | 0 => c
    | n++ => f n (recurse f c n)

/- Тут Nat.recurse это схема определения числовой последовательности рекурсивным способом.
   abbrev по сути эквивалентно def.

   Для каждого n ∈ ℕ она конструирует ф-цию fₙ : ℕ → ℕ, которая
   сопоставляет этому n какое-то натуральное число.

   c ∈ N - то, что она вернёт для n = 0
   f - ф-ция, которая для данного n ∈ ℕ и aₙ возвращает fₙ(aₙ),

       Во второй ветке паттерн-матчина, чтобы получить aₙ она рекурсивно
       вызывает сама себя (recurse f c n),
       где с n как бы "снимется" ещё одна единичка и "перекидывается наружу" и
       так до нуля (0 => c). Короче, она делает вот это: aₙ++ = fₙ(aₙ).

       Второй параметр, который мы передаём в f это предыдущее число,
       (которое мы должны сконструировать).

   Итак, используя аксиомы 2.1 и 2.2 мы можем конструировать числа.
   Благодаря аксиоме 2.3 мы знаем, что мы не зациклим такую числовую систему в 0.
   Аксиома 2.4 не допускает переопределение чисел.
   Ну а с помощью 2.5 мы можем определить нашу последовательность единственным способом
   (путём перехода между элементами только с помощью операции прибавления единички) и
   таким образом исключить "лишние числа" (вроде 0.5, 0.333...).
-/

/-- Proposition 2.1.16 (recursive definitions). Compare with Mathlib's `Nat.rec_zero`. -/
theorem Nat.recurse_zero (f: Nat → Nat → Nat) (c: Nat) : Nat.recurse f c 0 = c := by rfl
-- ^ c - нулевой эл. числ. посл. или
--   Nat.recurse натуральному числу 0 сопоставляет число c
--   По сути это базовый кейс паттер-матчинга определения Nat.recurse.

/-- Proposition 2.1.16 (recursive definitions). Compare with Mathlib's `Nat.rec_add_one`. -/
theorem Nat.recurse_succ (f: Nat → Nat → Nat) (c: Nat) (n: Nat) :
    recurse f c (n++) = f n (recurse f c n) := by rfl
-- ^ Это второй кейс паттерн-матчинга определения Nat.recurse

/-- Proposition 2.1.16 (recursive definitions). -/
theorem Nat.eq_recurse (f: Nat → Nat → Nat) (c: Nat) (a: Nat → Nat) :
    (a 0 = c ∧ ∀ n, a (n++) = f n (a n)) ↔ a = recurse f c := by
  constructor
  . intro ⟨ h0, hsucc ⟩
    -- this proof is written to follow the structure of the original text.
    apply funext
    apply induction
    . exact h0
    · intro n hn
      rw [hsucc n]
      rw [recurse_succ]
      rw [hn]
  · intro h
    rw [h]
    constructor -- could also use `split_ands` or `and_intros` here
    . exact recurse_zero _ _
    · exact recurse_succ _ _


/-- Proposition 2.1.16 (recursive definitions). -/
theorem Nat.recurse_uniq (f: Nat → Nat → Nat) (c: Nat) :
    ∃! (a: Nat → Nat), a 0 = c ∧ ∀ n, a (n++) = f n (a n) := by
  apply ExistsUnique.intro (recurse f c)
  . constructor -- could also use `split_ands` or `and_intros` here
    . exact recurse_zero _ _
    . exact recurse_succ _ _
  intro a
  exact (eq_recurse _ _ a).mp

end Chapter2
