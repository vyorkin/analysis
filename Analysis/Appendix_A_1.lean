import Mathlib.Tactic

/-!
# Analysis I, Appendix A.1: Математические утверждения

Введение в математические утверждения.
Демонстрирует некоторые базовые тактики и синтаксис Lean.
-/

-- Example A.1.1. То, что учебник называет "утверждениями" — это объекты
-- типа `Prop` в Lean. Кроме того, в Lean принято присваивать "мусорные" значения
-- выражениям, которые в обычной математике считались бы неопределёнными,
-- так что рассуждения об неопределённых термах в учебнике нужно корректировать соответственно.

/- Example A.1.1. То, что учебник называет "утверждениями" — это объекты типа `Prop` в Lean.
   Кроме того, в Lean принято присваивать "мусорные" значения выражениям, которые в обычной
   математике считались бы неопределёнными, так что рассуждения об неопределённых термах
   в учебнике нужно корректировать соответственно. -/
#check 2+2=4
#check 2+2=5

-- Здесь автор будет использовать не встречавшуюся мне ранее тактику tauto.
-- Рассмотрим как она работает.

-- tauto — это "финишная" тактика для пропозиционки:
-- она механически раскидывает (∧, ∨, ↔, ∃) в гипотезах и цели и пытается доказать
-- цель автоматически, пользуясь простыми тактиками вроде reflexivity и solve_by_elim.​

-- Что именно делает tauto:
--
-- В гипотезах tauto рекурсивно разбивает связки вида
-- p ∧ q, p ∨ q, p ↔ q, ∃ x, P x на более простые куски,
-- добавляя соответствующие гипотезы в контекcт.
--
-- В цели она аналогично разбивает цель вида p ∧ q, p ↔ q или
-- ∃ x, P x на подцели, которые проще автоматом решить.
-- Например, цель P ∧ Q превратится в две цели P и Q,
-- а ∃ x, P x — в задачу "подобрать терм" и доказать P для него.

-- Как она закрывает цель:
--
-- Когда структура уже максимально разложена, tauto пытается доказать
-- оставшиеся "атомарные" цели с помощью следующих тактик:
-- reflexivity   - Доказывает равенства вида p ↔ p, p = p
-- solve_by_elim - Подбирает подходящие гипотезы/леммы, возможно с небольшим углублением
--                 (ниже про эту тактику я подробнее расписал).
--
-- Если после всего этого всё ещё остаются не доказанные цели,
-- тактика падает с ошибкой, а если нет — полностью закрывает цель
-- (поэтому её и называют finishing tactic: либо всё, либо ничего).


/-- Всякое корректно построенное утверждение либо истинно, либо ложно... -/
example (P : Prop) : (P = true) ∨ (P = false) := by
  simp
  tauto

-- Замечание: `P = true` и `P = false` упрощаются до `P` и `¬P` соответственно.

/-- .. но не оба сразу. -/
example (P : Prop) : ¬((P = true) ∧ (P = false)) := by simp

/-- Чтобы доказать, что утверждение истинно,
    достаточно показать, что оно не ложно, -/
example {P : Prop} (h : P ≠ false) : P = true := by simp; tauto

/-- а чтобы показать, что утверждение ложно,
    достаточно показать, что оно не истинно. -/
example {P : Prop} (h : P ≠ true) : P = false := by simp; tauto

/-- Это утверждение истинно, но вряд ли особо полезно. -/
example : 2 = 2 := rfl

/-- Это утверждение тоже истинно, но не очень эффективно. -/
example : 4 ≤ 4 := by norm_num

/- Это выражение, а не утверждение. -/
#check 2 + 3 * 5 -- : ℕ

/- Это утверждение, а не выражение. -/
#check 2 + 3 * 5 = 17 -- : Prop

#check Prime (30 + 5)

#check 30 + 5 ≤ 42 - 7

/-- Конъюнкция -/
example {X Y : Prop} (hX : X) (hY : Y) : X ∧ Y := by
  constructor
  . exact hX
  · exact hY

example {X Y : Prop} (hXY : X ∧ Y) : X := by
  exact hXY.1

example {X Y : Prop} (hXY : X ∧ Y) : Y := by
  exact hXY.2

-- См.: https://en.wikipedia.org/wiki/Contraposition
example {X Y : Prop} (hX : ¬X) : ¬(X ∧ Y) := by
  contrapose! hX
  exact hX.1

example {X Y : Prop} (hY : ¬Y) : ¬(X ∧ Y) := by
  contrapose! hY
  exact hY.2

example : (2 + 2 = 4) ∧ (3 + 3 = 6) := by
  constructor
  . norm_num
  · norm_num

/-- Дизъюнкция -/
example {X Y : Prop} (hX : X) : X ∨ Y := by
  left
  exact hX

example {X Y : Prop} (hY : Y) : X ∨ Y := by
  right
  exact hY

example {X Y : Prop} (hX : ¬X) (hY : ¬Y) : ¬(X ∨ Y) := by
  simp
  constructor
  . exact hX
  · exact hY

example : (2 + 2 = 4) ∨ (3 + 3 = 5) := by
  left
  norm_num

example : ¬((2 + 2 = 5) ∨ (3 + 3 = 5)) := by
  simp

example : (2 + 2 = 4) ∨ (3 + 3 = 6) := by
  left
  norm_num

example : (2 + 2 = 4) ∧ (3 + 3 = 6) := by
  constructor
  . norm_num
  · norm_num

example : (2 + 2 = 4) ∨ (2353 + 5931 = 7284) := by
  left
  norm_num

#check Xor'

/-- Отрицание -/
example {X : Prop} : (¬X = true) ↔ (X = false) := by simp

example {X : Prop} : (¬X = false) ↔ (X = true) := by simp

example : ¬(2 + 2 = 5) := by simp

example : 2 + 2 ≠ 5 := by simp

example (Jane_black_hair Jane_blue_eyes : Prop) : 
  (¬(Jane_black_hair ∧ Jane_blue_eyes)) ↔ (¬Jane_black_hair ∨ ¬Jane_blue_eyes) := by
  simp; tauto

example (x : ℤ) : ¬(Even x ∧ x ≥ 0) ↔ (Odd x ∨ x < 0) := by
  have : ¬Odd x ↔ Even x := Int.not_odd_iff_even
  have : ¬(x ≥ 0) ↔ x < 0 := Int.not_le
  tauto

example (x : ℤ) : ¬(x ≥ 2 ∧ x ≤ 6) ↔ (x < 2 ∨ x > 6) := by
  have : ¬(x ≥ 2) ↔ (x < 2) := Int.not_le
  have : ¬(x ≤ 6) ↔ (x > 6) := Int.not_le
  tauto

example (John_brown_hair John_black_hair : Prop) : 
  (¬(John_brown_hair ∨ John_black_hair)) ↔ (¬John_brown_hair ∧ ¬John_black_hair) := by
  simp

example (x : ℝ) : ¬(x ≥ 1 ∧ x ≤ -1) ↔ (x < 1 ∨ x > -1) := by
  have : ¬ (x ≥ 1) ↔ (x < 1) := not_le
  have : ¬ (x ≤ -1) ↔ (x > -1) := not_le
  tauto

example (x : ℤ) : ¬(Even x ∨ Odd x) ↔ (¬Even x ∧ ¬Odd x) := by
  tauto

example (X : Prop) : ¬ (¬ X) ↔ X := by
  simp

/-- Тогда и только тогда (iff) -/
example {X Y : Prop} (hXY : X ↔ Y) (hX : X) : Y := by
  rw [hXY] at hX
  exact hX

example {X Y : Prop} (hXY : X ↔ Y) (hY : Y) : X := by
  rw [←hXY] at hY
  exact hY

example {X Y : Prop} (hXY : X ↔ Y) (hX : X) : Y := by
  exact hXY.mp hX

example {X Y : Prop} (hXY : X ↔ Y) (hY : Y) : X := by
  exact hXY.mpr hY

example {X Y : Prop} (hXY : X ↔ Y) : X=Y := by
  simp [hXY]

example (x : ℝ) : x = 3 ↔ 2 * x = 6 := by
  constructor
  . intro h
    linarith
  intro h
  linarith

example : ¬ (∀ x : ℝ, x = 3 ↔ x^2 = 9) := by
  simp
  use -3
  norm_cast

example {X Y : Prop} (hXY : X ↔ Y) (hX : ¬ X) : ¬ Y := by
  by_contra this
  rw [←hXY] at this
  contradiction

example : (2+2=5) ↔ (4+4=10) := by
  simp

example {X Y Z : Prop} (hXY : X ↔ Y) (hXZ : X ↔ Z) : [X,Y,Z].TFAE := by
  tfae_have 1 ↔ 2 := by exact hXY  -- Эта строка необязательна
  tfae_have 1 ↔ 3 := by exact hXZ  -- Эта строка необязательна
  tfae_finish

/-- Замечание: у метода {name (full := List.TFAE.out)}`out` индексация начинается с 0,
    в отличие от тактики {tactic}`tfae_have`. -/
example {X Y Z : Prop} (h : [X,Y,Z].TFAE) : X ↔ Y := by
  exact h.out 0 1

/-- Exercise A.1.1.  Заполните первый {syntax term}`sorry` чем-нибудь разумным. -/
example {X Y : Prop} : ¬ ((X ∨ Y) ∧ ¬ (X ∧ Y)) ↔ sorry := by sorry

/-- Exercise A.1.2.  Заполните первый {syntax term}`sorry` чем-нибудь разумным. -/
example {X Y : Prop} : ¬ (X ↔ Y) ↔ sorry := by sorry

/-- Exercise A.1.3. -/
def Exercise_A_1_3 : Decidable (∀ (X Y : Prop), (X → Y) → (¬X → ¬ Y) → (X ↔ Y)) := by
  -- первая строка этой конструкции должна быть либо `apply isTrue`, либо `apply isFalse`,
  -- в зависимости от того, считаете ли вы данное утверждение истинным или ложным.
  sorry

/-- Exercise A.1.4. -/
def Exercise_A_1_4 : Decidable (∀ (X Y : Prop), (X → Y) → (¬Y → ¬ X) → (X ↔ Y)) := by
  -- первая строка этой конструкции должна быть либо `apply isTrue`, либо `apply isFalse`.
  sorry

/-- Exercise A.1.5. -/
def Exercise_A_1_5 : Decidable (∀ (X Y Z : Prop), (X ↔ Y) → (Y ↔ Z) → [X,Y,Z].TFAE) := by
  -- первая строка этой конструкции должна быть либо `apply isTrue`, либо `apply isFalse`.
  sorry

/-- Exercise A.1.6. -/
def Exercise_A_1_6 : Decidable (∀ (X Y Z : Prop), (X → Y) → (Y → Z) → (Z → X) → [X,Y,Z].TFAE) := by
  -- первая строка этой конструкции должна быть либо `apply isTrue`, либо `apply isFalse`.
  sorry
