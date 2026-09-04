import Mathlib.Tactic
import Mathlib.Data.Real.Sign
import Analysis.Section_9_1

set_option doc.verso.suggestions false

/-!
# Analysis I, раздел 9.3: Предельные значения функций

Я старался сделать перевод максимально точным перефразированием оригинального текста. Когда
приходилось выбирать между более идиоматичным Lean-решением и более точным переводом, я, как
правило, выбирал второе. В частности, местами Lean-код можно было бы "заголфить", сделав его более
элегантным и идиоматичным, но я сознательно этого избегал.

Основные конструкции и результаты этого раздела:

- Пределы непрерывных функций
- Связь с понятиями сходимости по фильтру из Mathlib
- Законы пределов для функций

Технический момент: в тексте книги изучаемые функции `f` определены только на подмножествах `X` из
{lean}`ℝ`, а вне этих подмножеств не определены. Однако в Lean это порождает возню с приведениями
типов при попытке ограничить `f` на различные подмножества `X` (которые, строго говоря, не являются
в точности подмножествами {lean}`ℝ`, хотя и приводятся к ним). Чтобы избежать этой проблемы, мы
отступим от текста книги и будем определять наши функции на всём {lean}`ℝ` (с пониманием того, что
вне интересующей нас области `X` им присваиваются "мусорные" значения).
-/

/-- Определение 9.3.1
Заметьте, что в книге используется ≤ вместо <, но < соответствует определению окрестности в mathlib.
-/
abbrev Real.CloseFn (ε : ℝ) (X : Set ℝ) (f : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ x ∈ X, |f x - L| < ε

/-- Определение 9.3.3 -/
abbrev Real.CloseNear (ε : ℝ) (X : Set ℝ) (f : ℝ → ℝ) (L : ℝ) (x₀ : ℝ) : Prop :=
  ∃ δ > 0, ε.CloseFn (X ∩ .Ioo (x₀-δ) (x₀+δ)) f L

namespace Chapter9

/-- Пример 9.3.2
Небольшое отличие от книги, связанное с изменением {lean}`Real.CloseFn`
-/
example : (5.1 : ℝ).CloseFn (.Icc 1 3) (fun x ↦ x^2) 4 := by sorry

/-- Пример 9.3.2
Небольшое отличие от книги, связанное с изменением {lean}`Real.CloseFn`
-/
example : (0.42 : ℝ).CloseFn (.Icc 1.9 2.1) (fun x ↦ x^2) 4 := by sorry

/-- Пример 9.3.4 -/
example : ¬(0.1 : ℝ).CloseFn (.Icc 1 3) (fun x ↦ x^2) 4 := by
  sorry

/-- Пример 9.3.4 -/
example : (0.1 : ℝ).CloseNear (.Icc 1 3) (fun x ↦ x^2) 4 2 := by
  sorry

/-- Пример 9.3.5 -/
example : ¬(0.1 : ℝ).CloseFn (.Icc 1 3) (fun x ↦ x^2) 9 := by
  sorry

/-- Пример 9.3.5 -/
example : (0.1 : ℝ).CloseNear (.Icc 1 3) (fun x ↦ x^2) 9 3 := by
  sorry

/-- Определение 9.3.6 (Сходимость функций в точке). -/
abbrev Convergesto (X : Set ℝ) (f : ℝ → ℝ) (L : ℝ) (x₀ : ℝ) : Prop := ∀ ε > (0 : ℝ), ε.CloseNear X f L x₀

/-- Связь с понятиями сходимости по фильтру из Mathlib -/
theorem Convergesto.iff (X : Set ℝ) (f : ℝ → ℝ) (L : ℝ) (x₀ : ℝ) : 
  Convergesto X f L x₀ ↔ (nhdsWithin x₀ X).Tendsto f (nhds L) := by
  unfold Convergesto Real.CloseNear Real.CloseFn nhdsWithin
  rw [LinearOrderedAddCommGroup.tendsto_nhds]
  peel with ε hε
  rw [Filter.eventually_inf_principal]
  simp [Filter.Eventually, mem_nhds_iff_exists_Ioo_subset]
  constructor
  . intro ⟨ δ, _, _ ⟩; use x₀-δ, x₀+δ, by grind
    intro _; simp; grind
  intro ⟨ l, u, ⟨ _, _ ⟩, h ⟩
  have h1 : 0 < x₀ - l := by linarith
  have h2 : 0 < u - x₀ := by linarith
  set δ := min (x₀ - l) (u - x₀)
  observe hδ1 : δ ≤ x₀ - l
  observe hδ2 : δ ≤ u - x₀
  use δ, (by positivity); intro x hxX _ _
  specialize h (show x ∈ .Ioo l u by simp; grind)
  simpa [hxX] using h

/-- Пример 9.3.8 -/
example : Convergesto (.Icc 1 3) (fun x ↦ x^2) 4 2 := by
  sorry

/-- Утверждение 9.3.9 / Упражнение 9.3.1 -/
theorem Convergesto.iff_conv {E : Set ℝ} (f : ℝ → ℝ) (L : ℝ) {x₀ : ℝ} : 
  Convergesto E f L x₀ ↔ ∀ a : ℕ → ℝ, (∀ n : ℕ, a n ∈ E) →
  Filter.atTop.Tendsto a (nhds x₀) →
  Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds L) := by
  sorry

-- Следствие `Convergesto.iff_conv`: если `f → L` в `x₀` по `E`, то `f(aₙ) → L` для любой последовательности `aₙ` в `E`, сходящейся к `x₀`
theorem Convergesto.comp {E : Set ℝ} {f : ℝ → ℝ} {L : ℝ} {x₀ : ℝ} (hf : Convergesto E f L x₀) {a : ℕ → ℝ}
  (ha : ∀ n : ℕ, a n ∈ E) (hconv : Filter.atTop.Tendsto a (nhds x₀)) : 
  Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds L) := by
  rw [iff_conv f L] at hf; solve_by_elim

-- Замечание 9.3.11 не вполне верно для Lean: гипотезу `AdherentPt x₀ E` можно безопасно убрать
-- из большинства теорем (за исключением Convergesto.uniq).

/-- Следствие 9.3.13 -/
theorem Convergesto.uniq {E : Set ℝ} {f : ℝ → ℝ} {L L' : ℝ} {x₀ : ℝ} (h : AdherentPt x₀ E)
  (hf : Convergesto E f L x₀) (hf' : Convergesto E f L' x₀) : L = L' := by
  -- Это доказательство написано так, чтобы следовать структуре оригинального текста.
  let ⟨ a, ha, hconv ⟩ := (limit_of_AdherentPt _ _).mp h
  exact tendsto_nhds_unique (hf.comp ha hconv) (hf'.comp ha hconv)

/-- Утверждение 9.3.14 (Законы пределов для функций, сложение) -/
theorem Convergesto.add {E : Set ℝ} {f g : ℝ → ℝ} {L M : ℝ} {x₀ : ℝ}
  (hf : Convergesto E f L x₀) (hg : Convergesto E g M x₀) : 
  Convergesto E (f + g) (L + M) x₀ := by
    -- Это доказательство написано так, чтобы следовать структуре оригинального текста.
    rw [iff_conv _ _] at hf hg ⊢
    intro a ha hconv; specialize hf a ha hconv; specialize hg a ha hconv
    convert hf.add hg using 1

/-- Утверждение 9.3.14 (Законы пределов для функций, вычитание) / Упражнение 9.3.2 -/
theorem Convergesto.sub {E : Set ℝ} {f g : ℝ → ℝ} {L M : ℝ} {x₀ : ℝ}
  (hf : Convergesto E f L x₀) (hg : Convergesto E g M x₀) : 
  Convergesto E (f - g) (L - M) x₀ := by
    sorry

/-- Утверждение 9.3.14 (Законы пределов для функций, максимум) / Упражнение 9.3.2 -/
theorem Convergesto.max {E : Set ℝ} {f g : ℝ → ℝ} {L M : ℝ} {x₀ : ℝ}
  (hf : Convergesto E f L x₀) (hg : Convergesto E g M x₀) : 
  Convergesto E (max f g) (max L M) x₀ := by
    sorry

/-- Утверждение 9.3.14 (Законы пределов для функций, минимум) / Упражнение 9.3.2 -/
theorem Convergesto.min {E : Set ℝ} {f g : ℝ → ℝ} {L M : ℝ} {x₀ : ℝ}
  (hf : Convergesto E f L x₀) (hg : Convergesto E g M x₀) : 
  Convergesto E (min f g) (min L M) x₀ := by
    sorry

/-- Утверждение 9.3.14 (Законы пределов для функций, умножение на скаляр) / Упражнение 9.3.2 -/
theorem Convergesto.smul {E : Set ℝ} {f : ℝ → ℝ} {L : ℝ} {x₀ : ℝ}
  (hf : Convergesto E f L x₀) (c : ℝ) : 
  Convergesto E (c • f) (c * L) x₀ := by
    sorry

/-- Утверждение 9.3.14 (Законы пределов для функций, умножение) / Упражнение 9.3.2 -/
theorem Convergesto.mul {E : Set ℝ} {f g : ℝ → ℝ} {L M : ℝ} {x₀ : ℝ}
  (hf : Convergesto E f L x₀) (hg : Convergesto E g M x₀) : 
  Convergesto E (f * g) (L * M) x₀ := by
    sorry

/-- Утверждение 9.3.14 (Законы пределов для функций, деление) / Упражнение 9.3.2. Гипотезу из книги о том, что g не обращается в ноль на E, можно опустить. -/
theorem Convergesto.div {E : Set ℝ} {f g : ℝ → ℝ} {L M : ℝ} {x₀ : ℝ} (hM : M ≠ 0)
  (hf : Convergesto E f L x₀) (hg : Convergesto E g M x₀) : 
  Convergesto E (f / g) (L / M) x₀ := by
    sorry

-- Постоянная функция `x ↦ c` сходится к `c` в любой точке `x₀`
theorem Convergesto.const (E : Set ℝ) (x₀ : ℝ) (c : ℝ)
  : Convergesto E (fun _ ↦ c) c x₀ := by
  sorry

-- Тождественная функция `x ↦ x` сходится к `x₀` в точке `x₀`
theorem Convergesto.id (E : Set ℝ) (x₀ : ℝ)
  : Convergesto E (fun x ↦ x) x₀ x₀ := by
  sorry

-- Функция `x ↦ x²` сходится к `x₀²` в точке `x₀`
theorem Convergesto.sq (E : Set ℝ) (x₀ : ℝ)
  : Convergesto E (fun x ↦ x^2) (x₀^2) x₀ := by
  sorry

-- Линейная функция `x ↦ c*x` сходится к `c*x₀` в точке `x₀`
theorem Convergesto.linear (E : Set ℝ) (x₀ : ℝ) (c : ℝ)
  : Convergesto E (fun x ↦ c * x) (c * x₀) x₀ := by
  sorry

-- Квадратичная функция `x ↦ x² + c*x + d` сходится к `x₀² + c*x₀ + d` в точке `x₀`
theorem Convergesto.quadratic (E : Set ℝ) (x₀ : ℝ) (c d : ℝ)
  : Convergesto E (fun x ↦ x^2 + c * x + d) (x₀^2 + c * x₀ + d) x₀ := by
  sorry

-- Сходимость функции на множестве `X` влечёт сходимость к тому же пределу на любом подмножестве `Y ⊆ X`
theorem Convergesto.restrict {X Y : Set ℝ} {f : ℝ → ℝ} {L : ℝ} {x₀ : ℝ} (hf : Convergesto X f L x₀) (hY : Y ⊆ X) : Convergesto Y f L x₀ := by
  sorry

-- Явная формула для функции знака: `-1` при `x < 0`, `1` при `x > 0`, `0` при `x = 0`
theorem Real.sign_def (x : ℝ) : Real.sign x = if x < 0 then -1 else if x > 0 then 1 else 0 := rfl

/-- Пример 9.3.16 (a) -/
theorem Convergesto.sign_right : Convergesto (.Ioi 0) Real.sign 1 0 := by sorry

/-- Пример 9.3.16 (b) -/
theorem Convergesto.sign_left : Convergesto (.Iio 0) Real.sign (-1) 0 := by sorry

/-- Пример 9.3.16 (c) -/
theorem Convergesto.sign_all : ¬ ∃ L, Convergesto (.univ) Real.sign L 0 := by sorry

noncomputable abbrev f_9_3_17 : ℝ → ℝ := fun x ↦ if x = 0 then 1 else 0

-- Функция `f_9_3_17` (равная `1` в нуле и `0` иначе) сходится к `0` в точке `0`, если исключить саму точку `0` из области
theorem Convergesto.f_9_3_17_remove : Convergesto (.univ \ {0}) f_9_3_17 0 0 := by sorry

-- На всей прямой (включая точку `0`) у `f_9_3_17` нет предела в `0`
theorem Convergesto.f_9_3_17_all : ¬ ∃ L, Convergesto .univ f_9_3_17 L 0 := by sorry

/-- Утверждение 9.3.18 / Упражнение 9.3.3 -/
theorem Convergesto.local {E : Set ℝ} {f : ℝ → ℝ} {L : ℝ} {x₀ : ℝ} {δ : ℝ} (hδ : δ > 0) : 
  Convergesto E f L x₀ ↔ Convergesto (E ∩ .Ioo (x₀-δ) (x₀+δ)) f L x₀ := by
    sorry

/-- Пример 9.3.19.  Смысл этого примера несколько теряется из-за того, что мы можем убрать гипотезу о ненулевости {lit}`g` из соответствующей части Утверждения 9.3.14 -/
example : Convergesto .univ (fun x ↦ (x+2)/(x+1)) (4/3 : ℝ) 2 := by sorry

/-- Пример 9.3.20 -/
example : Convergesto (.univ \ {1}) (fun x ↦ (x^2-1)/(x-1)) 2 1 := by sorry

open Classical in
/-- Пример 9.3.21 -/
noncomputable abbrev f_9_3_21 : ℝ → ℝ := fun x ↦ if x ∈ (fun q : ℚ ↦ (q : ℝ)) '' .univ then 1 else 0

example : Filter.atTop.Tendsto (fun (n : ℕ) ↦ f_9_3_21 (1/(n : ℝ))) (nhds 1) := by sorry

example : Filter.atTop.Tendsto (fun (n : ℕ) ↦ f_9_3_21 ((Real.sqrt 2)/n : ℝ)) (nhds 0) := by sorry

example : ¬ ∃ L, Convergesto .univ f_9_3_21 L 0 := by sorry

/- Упражнение 9.3.4: Сформулируйте определение верхнего и нижнего предела для функций и докажите аналог Утверждения 9.3.9 для этих определений. -/

/-- Упражнение 9.3.5 (Непрерывная версия теоремы о двух милиционерах) -/
theorem Convergesto.squeeze {E : Set ℝ} {f g h : ℝ → ℝ} {L : ℝ} {x₀ : ℝ}
  (hfg : ∀ x ∈ E, f x ≤ g x) (hgh : ∀ x ∈ E, g x ≤ h x)
  (hf : Convergesto E f L x₀) (hh : Convergesto E h L x₀) : 
  Convergesto E g L x₀ := by
    sorry


end Chapter9
