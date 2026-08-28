import Mathlib.Tactic
import Mathlib.Data.Real.Sign
import Analysis.Section_9_3
import Analysis.Section_9_4

/-!
# Analysis I, раздел 9.5: Левые и правые пределы

Я старался сделать перевод максимально точным перефразированием оригинального текста. Когда
приходилось выбирать между более идиоматичным Lean-решением и более точным переводом, я, как
правило, выбирал второе. В частности, местами Lean-код можно было бы "заголфить", сделав его более
элегантным и идиоматичным, но я сознательно этого избегал.

Основные конструкции и результаты этого раздела:
- Левые и правые пределы.
-/

namespace Chapter9

/-- Definition 9.5.1.  Мы присваиваем левым и правым пределам "мусорное" значение 0, если предел не существует. -/
abbrev RightLimitExists (X : Set ℝ) (f : ℝ → ℝ) (x₀ : ℝ) : Prop := ∃ L, (nhdsWithin x₀ (X ∩ .Ioi x₀)).Tendsto f (nhds L)

open Classical in
noncomputable abbrev right_limit (X : Set ℝ) (f : ℝ → ℝ) (x₀ : ℝ) : ℝ := if h : RightLimitExists X f x₀ then h.choose else 0

abbrev LeftLimitExists (X : Set ℝ) (f : ℝ → ℝ) (x₀ : ℝ) : Prop := ∃ L, (nhdsWithin x₀ (X ∩ .Iio x₀)).Tendsto f (nhds L)

open Classical in
noncomputable abbrev left_limit (X : Set ℝ) (f : ℝ → ℝ) (x₀ : ℝ) : ℝ := if h : LeftLimitExists X f x₀ then h.choose else 0

-- Если правый предел `f` в `x₀` вдоль `X` равен `L`, то `right_limit` корректно вычисляет именно это значение `L`
theorem right_limit.eq {X : Set ℝ} {f : ℝ → ℝ} {x₀ : ℝ} {L : ℝ} (had : AdherentPt x₀ (X ∩ .Ioi x₀))
  (h : (nhdsWithin x₀ (X ∩ .Ioi x₀)).Tendsto f (nhds L)) : RightLimitExists X f x₀ ∧ right_limit X f x₀ = L := by
  have h' : RightLimitExists X f x₀ := by use L
  simp [right_limit, h']
  have hne : (nhdsWithin x₀ (X ∩ .Ioi x₀)).NeBot := by
    rwa [←mem_closure_iff_nhdsWithin_neBot, closure_def']
  exact tendsto_nhds_unique h'.choose_spec h

-- Если левый предел `f` в `x₀` вдоль `X` равен `L`, то `left_limit` корректно вычисляет именно это значение `L`
theorem left_limit.eq {X : Set ℝ} {f : ℝ → ℝ} {x₀ : ℝ} {L : ℝ} (had : AdherentPt x₀ (X ∩ .Iio x₀))
  (h : (nhdsWithin x₀ (X ∩ .Iio x₀)).Tendsto f (nhds L)) : LeftLimitExists X f x₀ ∧ left_limit X f x₀ = L := by
  have h' : LeftLimitExists X f x₀ := by use L
  simp [left_limit, h']
  have hne : (nhdsWithin x₀ (X ∩ .Iio x₀)).NeBot := by
    rwa [←mem_closure_iff_nhdsWithin_neBot, closure_def']
  exact tendsto_nhds_unique h'.choose_spec h

-- Если правый предел существует, то `f` действительно сходится к `right_limit X f x₀` в этом смысле
theorem right_limit.eq' {X : Set ℝ} {f : ℝ → ℝ} {x₀ : ℝ} (h : RightLimitExists X f x₀) : 
  (nhdsWithin x₀ (X ∩ .Ioi x₀)).Tendsto f (nhds (right_limit X f x₀)) := by
  simp [right_limit, h]; exact h.choose_spec

-- Если левый предел существует, то `f` действительно сходится к `left_limit X f x₀` в этом смысле
theorem left_limit.eq' {X : Set ℝ} {f : ℝ → ℝ} {x₀ : ℝ} (h : LeftLimitExists X f x₀) : 
  (nhdsWithin x₀ (X ∩ .Iio x₀)).Tendsto f (nhds (left_limit X f x₀)) := by
  simp [left_limit, h]; exact h.choose_spec

/-- Example 9.5.2.  Вторая часть этого примера больше не актуальна, так как мы присваиваем нашим функциям "мусорные" значения вместо того, чтобы оставлять их неопределёнными. -/
example : right_limit .univ Real.sign 0 = 1 := by sorry

example : left_limit .univ Real.sign 0 = -1 := by sorry

-- Последовательностная характеризация: если `aₙ → x₀` оставаясь в `X ∩ (x₀, ∞)`, то `f(aₙ)` сходится к правому пределу
theorem right_limit.conv {X : Set ℝ} {f : ℝ → ℝ} {x₀ : ℝ} (had : AdherentPt x₀ (X ∩ .Ioi x₀))
  (h : RightLimitExists X f x₀)
  (a : ℕ → ℝ) (ha : ∀ n, a n ∈ X ∩ .Ioi x₀)
  (hconv : Filter.atTop.Tendsto a (nhds x₀)) : 
  Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds (right_limit X f x₀)) := by
  choose L hL using h
  apply Convergesto.comp _ ha hconv
  rwa [Convergesto.iff, (eq had hL).2]

-- Последовательностная характеризация: если `aₙ → x₀` оставаясь в `X ∩ (-∞, x₀)`, то `f(aₙ)` сходится к левому пределу
theorem left_limit.conv {X : Set ℝ} {f : ℝ → ℝ} {x₀ : ℝ} (had : AdherentPt x₀ (X ∩ .Iio x₀))
  (h : LeftLimitExists X f x₀)
  (a : ℕ → ℝ) (ha : ∀ n, a n ∈ X ∩ .Iio x₀)
  (hconv : Filter.atTop.Tendsto a (nhds x₀)) : 
  Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds (left_limit X f x₀)) := by
  choose L hL using h
  apply Convergesto.comp _ ha hconv
  rwa [Convergesto.iff, (eq had hL).2]

/-- Proposition 9.5.3 -/
theorem ContinuousAt.iff_eq_left_right_limit {X : Set ℝ} {f : ℝ → ℝ} {x₀ : ℝ} (h : x₀ ∈ X)
  (had_left : AdherentPt x₀ (X ∩ .Iio x₀)) (had_right : AdherentPt x₀ (X ∩ .Ioi x₀)) : 
  ContinuousWithinAt f X x₀ ↔ (RightLimitExists X f x₀ ∧ right_limit X f x₀ = f x₀) ∧ (LeftLimitExists X f x₀ ∧ left_limit X f x₀ = f x₀) := by
  -- Это доказательство написано так, чтобы следовать структуре оригинального текста.
  constructor
  . sorry
  intro ⟨ ⟨ hre, hright⟩, ⟨ hle, lheft ⟩ ⟩
  set L := f x₀
  have := (ContinuousWithinAt.tfae X f x₀).out 0 2
  rw [this]
  intro ε hε
  apply right_limit.eq' at hre
  apply left_limit.eq' at hle
  rw [hright, ←Convergesto.iff] at hre
  rw [lheft, ←Convergesto.iff] at hle
  simp [Convergesto, Real.CloseNear, Real.CloseFn] at hre hle
  choose δ_plus hδ_plus hre using hre ε hε
  choose δ_minus hδ_minus hle using hle ε hε
  use min δ_plus δ_minus, (by positivity)
  intro x hx hxx₀
  obtain hlt | rfl | hgt := lt_trichotomy x x₀
  . sorry
  . sorry
  sorry

abbrev HasJumpDiscontinuity (X : Set ℝ) (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  RightLimitExists X f x₀ ∧ LeftLimitExists X f x₀ ∧ right_limit X f x₀ ≠ left_limit X f x₀

example : HasJumpDiscontinuity .univ Real.sign 0 := by sorry

abbrev HasRemovableDiscontinuity (X : Set ℝ) (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  RightLimitExists X f x₀ ∧ LeftLimitExists X f x₀ ∧ right_limit X f x₀ = left_limit X f x₀
  ∧ right_limit X f x₀ ≠ f x₀

example : HasRemovableDiscontinuity .univ f_9_3_17 0 := by sorry

example : ¬ HasRemovableDiscontinuity .univ (fun x ↦ 1/x) 0 := by sorry

example : ¬ HasJumpDiscontinuity .univ (fun x ↦ 1/x) 0 := by sorry

/- Exercise 9.5.1: Сформулируйте определение того, что значит для предела функции быть `+∞` или `-∞`, примените его к `fun x ↦ 1/x`, а также сформулируйте и докажите версию Proposition 9.3.9. -/


end Chapter9
