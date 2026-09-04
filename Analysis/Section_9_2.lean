import Mathlib.Tactic

/-!
# Analysis I, раздел 9.2: Алгебра вещественнозначных функций

Я старался сделать перевод максимально точным перефразированием оригинального текста. Когда
приходилось выбирать между более идиоматичным Lean-решением и более точным переводом, я, как
правило, выбирал второе. В частности, местами Lean-код можно было бы "заголфить", сделав его более
элегантным и идиоматичным, но я сознательно этого избегал.

Основные конструкции и результаты этого раздела:

- Напоминание базовых поточечных операций над функциями.

-/

namespace Chapter9

open Classical in
noncomputable abbrev function_example : ℝ → ℝ := fun x ↦ if x ∈ ((fun y : ℚ ↦ (y : ℝ)) '' .univ) then 1 else 0

/-- Определение 9.2.1 (Арифметические операции над функциями). -/
theorem add_func_eval (f g : ℝ → ℝ) (x : ℝ) : (f + g) x = f x + g x := rfl

-- Поточечное определение разности функций: `(f - g) x = f x - g x`
theorem sub_func_eval (f g : ℝ → ℝ) (x : ℝ) : (f - g) x = f x - g x := rfl

-- Поточечное определение максимума функций: `(max f g) x = max (f x) (g x)`
theorem max_func_eval (f g : ℝ → ℝ) (x : ℝ) : max f g x = max (f x) (g x) := rfl

-- Поточечное определение минимума функций: `(min f g) x = min (f x) (g x)`
theorem min_func_eval (f g : ℝ → ℝ) (x : ℝ) : min f g x = min (f x) (g x) := rfl

-- Поточечное определение произведения функций: `(f * g) x = f x * g x`
theorem mul_func_eval (f g : ℝ → ℝ) (x : ℝ) : (f * g) x = f x * g x := rfl

-- Поточечное определение частного функций: `(f / g) x = f x / g x`
theorem div_func_eval (f g : ℝ → ℝ) (x : ℝ) : (f / g) x = f x / g x := rfl

-- Поточечное определение скалярного умножения функции: `(c • f) x = c * f x`
theorem smul_func_eval (c : ℝ) (f : ℝ → ℝ) (x : ℝ) : (c • f) x = c * f x := rfl

abbrev f_9_2_2 : ℝ → ℝ := fun x ↦ x^2

abbrev g_9_2_2 : ℝ → ℝ := fun x ↦ 2*x

example : f_9_2_2 + g_9_2_2 = fun x ↦ x^2 + 2*x := rfl

example : f_9_2_2 * g_9_2_2 = fun x ↦ 2 * x^3 := by ext; simp; ring

example : f_9_2_2 - g_9_2_2 = fun x ↦ x^2 - 2*x := rfl

example : 6 • f_9_2_2 = fun x ↦ 6 * (x^2) := by ext; simp

example : f_9_2_2 ∘ g_9_2_2 = fun x ↦ 4*x^2 := by grind

example : g_9_2_2 ∘ f_9_2_2 = fun x ↦ 2*x^2 := by grind

/-- Упражнение 9.2.1 (a) -/
def Exercise_9_2_1a : Decidable (∀ (f g h : ℝ → ℝ), (f+g) ∘ h = f ∘ h + g ∘ h) := by
  -- Первой строкой этой конструкции должна быть `apply isTrue` или `apply isFalse`.
  sorry

/-- Упражнение 9.2.1 (b) -/
def Exercise_9_2_1b : Decidable (∀ (f g h : ℝ → ℝ), f ∘ (g + h) = f ∘ g + f ∘ h) := by
  -- Первой строкой этой конструкции должна быть `apply isTrue` или `apply isFalse`.
  sorry

/-- Упражнение 9.2.1 (c) -/
def Exercise_9_2_1c : Decidable (∀ (f g h : ℝ → ℝ), (f+g) * h = f * h + g * h) := by
  -- Первой строкой этой конструкции должна быть `apply isTrue` или `apply isFalse`.
  sorry

/-- Упражнение 9.2.1 (d) -/
def Exercise_9_2_1d : Decidable (∀ (f g h : ℝ → ℝ), f * (g+h) = f * g + f * h) := by
  -- Первой строкой этой конструкции должна быть `apply isTrue` или `apply isFalse`.
  sorry

end Chapter9
