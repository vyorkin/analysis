import Mathlib.Tactic
import Mathlib.Topology.Instances.Irrational
import Analysis.Section_11_6

set_option doc.verso.suggestions false

/-!
# Analysis I, раздел 11.8: Интеграл Римана-Стилтьеса

Я старался сделать перевод максимально точным перефразированием оригинального текста. Когда
приходилось выбирать между более идиоматичным Lean-решением и более точным переводом, я, как
правило, выбирал второе. В частности, местами Lean-код можно было бы "заголфить", сделав его более
элегантным и идиоматичным, но я сознательно этого избегал.

Основные конструкции и результаты этого раздела:
- Определение `α_length`.
- Кусочно-постоянный интеграл Римана-Стилтьеса.
- Полный интеграл Римана-Стилтьеса.

{open Set}

Технические замечания:
- В Lean удобнее делать такие определения, как `α_length` и интеграл Римана-Стилтьеса,
  всюду определёнными, присваивая "бросовые" значения в тех случаях, для которых определение
  не предназначено. Для определения `α_length` предполагается, что оно применяется в контекстах,
  где существуют левый и правый пределы, а функция продолжена константами влево и вправо от
  предполагаемой области определения; например, если функция `f` задана на {lean}`Icc 0 1`, то
  предполагается, что `f x = f 1` для всех `x ≥ 1` и `f x = f 0` для всех `x ≤ 0`; в частности,
  на правом конце значение функции предполагается совпадающим с её правым пределом, и аналогично
  для левого конца, хотя мы и не требуем этого явно в нашем определении `α_length`. (Для функций,
  заданных на открытых интервалах, это продолжение несущественно.)
- Понятие `α_length` и кусочно-постоянного интеграла Римана-Стилтьеса предназначено для ситуаций,
  где существуют левый и правый пределы, например для монотонных или непрерывных функций, хотя
  технически они имеют смысл и без этих предположений. Полный интеграл Римана-Стилтьеса
  предназначен для функций ограниченной вариации, хотя по большей части мы ограничимся частным
  случаем монотонно возрастающих функций.
-/

namespace Chapter11

open BoundedInterval Chapter9

/-- Левый и правый пределы. Если предел не существует, присваивается бросовое значение. -/
noncomputable abbrev right_lim (f : ℝ → ℝ) (x₀ : ℝ) : ℝ := Filter.lim ((nhdsWithin x₀ (.Ioi x₀)).map f)

noncomputable abbrev left_lim (f : ℝ → ℝ) (x₀ : ℝ) : ℝ := Filter.lim ((nhdsWithin x₀ (.Iio x₀)).map f)

-- Если `f` сходится к `L` справа от `x₀`, то `right_lim f x₀ = L`
theorem right_lim_def {f : ℝ → ℝ} {x₀ L : ℝ} (h : Convergesto (.Ioi x₀) f L x₀) : 
  right_lim f x₀ = L := by
  show Filter.lim _ = L
  apply lim_eq; rwa [Convergesto.iff, Filter.Tendsto.eq_1] at h

-- Если `f` сходится к `L` слева от `x₀`, то `left_lim f x₀ = L`
theorem left_lim_def {f : ℝ → ℝ} {x₀ L : ℝ} (h : Convergesto (.Iio x₀) f L x₀) : 
  left_lim f x₀ = L := by
  show Filter.lim _ = L
  apply lim_eq; rwa [Convergesto.iff, Filter.Tendsto.eq_1] at h

noncomputable abbrev jump (f : ℝ → ℝ) (x₀ : ℝ) : ℝ :=
  right_lim f x₀ - left_lim f x₀

/-- Правые пределы существуют для непрерывных функций -/
theorem right_lim_of_continuous {X : Set ℝ} {f : ℝ → ℝ} {x₀ : ℝ}
  (h : ∃ ε>0, .Ico x₀ (x₀+ε) ⊆ X) (hf : ContinuousWithinAt f X x₀) : 
  right_lim f x₀ = f x₀ := by
  choose ε hε hX using h
  apply right_lim_def
  rw [ContinuousWithinAt.eq_1] at hf
  replace hf : (nhdsWithin x₀ (.Ioo x₀ (x₀ + ε))).Tendsto f  (nhds (f x₀)) :=
    tendsto_nhdsWithin_mono_left (Set.Ioo_subset_Ico_self.trans hX) hf
  rw [Convergesto.iff]
  convert hf using 1
  have h1 : .Ioo x₀ (x₀ + ε) ∈ nhdsWithin x₀ (.Ioi x₀) := by
    convert inter_mem_nhdsWithin (t := .Ioo (x₀-ε) (x₀+ε)) _ _
    . grind
    apply Ioo_mem_nhds <;> linarith
  rw [←nhdsWithin_inter_of_mem h1]; congr 1; simp [Set.Ioo_subset_Ioi_self]

/-- Левые пределы существуют для непрерывных функций -/
theorem left_lim_of_continuous {X : Set ℝ} {f : ℝ → ℝ} {x₀ : ℝ}
  (h : ∃ ε>0, .Ioc (x₀-ε) x₀ ⊆ X) (hf : ContinuousWithinAt f X x₀) : 
  left_lim f x₀ = f x₀ := by
  choose ε hε hX using h
  apply left_lim_def
  rw [ContinuousWithinAt.eq_1] at hf
  replace hf : (nhdsWithin x₀ (.Ioo (x₀ - ε) x₀)).Tendsto f (nhds (f x₀)) :=
    tendsto_nhdsWithin_mono_left (Set.Ioo_subset_Ioc_self.trans hX) hf
  rw [Convergesto.iff]
  convert hf using 1
  have h1 : .Ioo (x₀-ε) x₀ ∈ nhdsWithin x₀ (.Iio x₀) := by
    convert inter_mem_nhdsWithin (t := .Ioo (x₀-ε) (x₀+ε)) _ _
    . grind
    apply Ioo_mem_nhds <;> linarith
  rw [←nhdsWithin_inter_of_mem h1]
  congr 1; simp [Set.Ioo_subset_Iio_self]

/-- У непрерывных функций нет скачка -/
theorem jump_of_continuous {X : Set ℝ} {f : ℝ → ℝ} {x₀ : ℝ}
  (h : X ∈ nhds x₀) (hf : ContinuousWithinAt f X x₀) : 
  jump f x₀ = 0 := by
  rw [mem_nhds_iff_exists_Ioo_subset] at h
  choose l u hx₀ hX using h; simp at hx₀
  have hl : ∃ ε>0, .Ioc (x₀-ε) x₀ ⊆ X :=
    ⟨ x₀-l, by linarith, Set.Subset.trans (by intro x ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩) hX ⟩
  have hu : ∃ ε>0, .Ico x₀ (x₀+ε) ⊆ X :=
    ⟨ u-x₀, by linarith, Set.Subset.trans (by intro x ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩) hX ⟩
  simp [jump, left_lim_of_continuous hl hf, right_lim_of_continuous hu hf]

/-- Правые пределы существуют для монотонных функций -/
theorem right_lim_of_monotone {f : ℝ → ℝ} (x₀ : ℝ) (hf : Monotone f) : 
  Convergesto (.Ioi x₀) f (sInf (f '' .Ioi x₀)) x₀ := by
  rw [Convergesto.iff]
  apply (hf.monotoneOn _).tendsto_nhdsGT
  rw [bddBelow_def]; use f x₀; intro y hy; simp at hy; obtain ⟨ x, hx, rfl ⟩ := hy; apply hf; grind

-- Явная формула правого предела монотонной `f`: `right_lim f x₀ = sInf (f '' Ioi x₀)`
theorem right_lim_of_monotone' {f : ℝ → ℝ} (x₀ : ℝ) (hf : Monotone f) : 
  right_lim f x₀ = sInf (f '' .Ioi x₀) := right_lim_def (right_lim_of_monotone x₀ hf)

/-- Левые пределы существуют для монотонных функций -/
theorem left_lim_of_monotone {f : ℝ → ℝ} (x₀ : ℝ) (hf : Monotone f) : 
  Convergesto (.Iio x₀) f (sSup (f '' .Iio x₀)) x₀ := by
  rw [Convergesto.iff]
  apply (hf.monotoneOn _).tendsto_nhdsLT
  rw [bddAbove_def]; use f x₀; intro y hy; simp at hy; obtain ⟨ x, hx, rfl ⟩ := hy; apply hf; grind

-- Явная формула левого предела монотонной `f`: `left_lim f x₀ = sSup (f '' Iio x₀)`
theorem left_lim_of_monotone' {f : ℝ → ℝ} (x₀ : ℝ) (hf : Monotone f) : 
  left_lim f x₀ = sSup (f '' .Iio x₀) := left_lim_def (left_lim_of_monotone x₀ hf)

-- Скачок `jump f x₀` монотонной функции всегда неотрицателен
theorem jump_of_monotone {f : ℝ → ℝ} (x₀ : ℝ) (hf : Monotone f) : 
  0 ≤ jump f x₀  := by
  simp [jump, left_lim_of_monotone' x₀ hf, right_lim_of_monotone' x₀ hf]
  apply csSup_le (by simp); intro a ha
  apply le_csInf (by simp); intro b hb; simp at ha hb
  obtain ⟨ x, hx, rfl ⟩ := ha; obtain ⟨ y, hy, rfl ⟩ := hb
  apply hf; grind

-- Для монотонной `f` и `a < b` правый предел в `a` не превосходит левого предела в `b`
theorem right_lim_le_left_lim_of_monotone {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
  (hf : Monotone f) : 
  right_lim f a ≤ left_lim f b := by
  rw [left_lim_of_monotone' b hf, right_lim_of_monotone' a hf]
  calc
    _ ≤ f ((a+b)/2) := by
      apply csInf_le
      . rw [bddBelow_def]; use f a; intro y hy; simp at hy; obtain ⟨ x, hx, rfl ⟩ := hy; apply hf; grind
      simp; use (a+b)/2; simp; linarith
    _ ≤ _ := by
      apply le_csSup
      . rw [bddAbove_def]; use f b; intro y hy; simp at hy; obtain ⟨ x, hx, rfl ⟩ := hy; apply hf; grind
      simp; use (a+b)/2; simp; linarith

/-- Определение 11.8.1 -/
noncomputable abbrev α_length (α : ℝ → ℝ) (I : BoundedInterval) : ℝ := match I with
| Icc a b => if a ≤ b then (right_lim α b) - (left_lim α a) else 0
| Ico a b => if a ≤ b then (left_lim α b) - (left_lim α a) else 0
| Ioc a b => if a ≤ b then (right_lim α b) - (right_lim α a) else 0
| Ioo a b => if a < b then (left_lim α b) - (right_lim α a) else 0

syntax:max term "[" term "]ₗ" : term
macro_rules | `($α[$I]ₗ) => `(α_length $α $I)

-- Длина по `α` пустого интервала равна нулю
theorem α_length_of_empty (α : ℝ → ℝ) {I : BoundedInterval} (hI : (I : Set ℝ) = ∅) : α[I]ₗ = 0 :=
  match I with
  | Icc _ _ => by simp [Set.Icc_eq_empty_iff] at *; simp [*]
  | Ico a b => by simp [Set.Ico_eq_empty_iff] at *; intro h; have := le_antisymm hI h; subst this; simp
  | Ioc a b => by simp [Set.Ioc_eq_empty_iff] at *; intro h; have := le_antisymm hI h; subst this; simp
  | Ioo _ _ => by simp [Set.Ioo_eq_empty_iff] at *; simp [*]

-- Длина по `α` вырожденного отрезка `{a}` равна скачку `jump α a`
@[simp]
theorem α_length_of_pt {α : ℝ → ℝ} (a : ℝ) : α[Icc a a]ₗ = jump α a := by simp [α_length, jump]

-- Если `α` непрерывна на охватывающем `(a,b)`, длина `α[I]ₗ` сводится к разности значений `α I.b - α I.a`
theorem α_length_of_cts {α : ℝ → ℝ} {I : BoundedInterval} {a b : ℝ}
  (haa : a < I.a) (hab : I.a ≤ I.b) (hbb : I.b < b)
  (hI : I ⊆ Ioo a b) (hα : ContinuousOn α (Ioo a b)) : 
  α[I]ₗ = α I.b - α I.a := by
  have ha_left : left_lim α I.a = α I.a := by
    apply left_lim_of_continuous _ (hα.continuousWithinAt (by simp; grind))
    exact ⟨ I.a - a, by grind, by intro _; simp; grind ⟩
  have ha_right : right_lim α I.a = α I.a := by
    apply right_lim_of_continuous _ (hα.continuousWithinAt (by simp; grind))
    exact ⟨ b - I.a, by grind, by intro _; simp; grind ⟩
  have hb_left : left_lim α I.b = α I.b := by
    apply left_lim_of_continuous _ (hα.continuousWithinAt (by simp; grind))
    exact ⟨ I.b - a, by grind, by intro _; simp; grind ⟩
  have hb_right : right_lim α I.b = α I.b := by
    apply right_lim_of_continuous _ (hα.continuousWithinAt (by simp; grind))
    exact ⟨ b - I.b, by grind, by intro _; simp; grind ⟩
  cases I with
  | Icc _ _ => grind
  | Ico _ _ => grind
  | Ioc _ _ => grind
  | Ioo _ _ => simp [α_length, ha_right, hb_left]; intro h; have := le_antisymm h (by linarith); subst this; simp

/-- Пример 11.8.2 -/
example : (fun x ↦ x^2)[Icc 2 3]ₗ = 5 := by
  sorry

example : (fun x ↦ x^2)[Icc 2 2]ₗ = 0 := by
  sorry

example : (fun x ↦ x^2)[Ioo 2 2]ₗ = 0 := by
  sorry

/-- Пример 11.8.3 -/
@[simp]
theorem α_len_of_id (I : BoundedInterval) : (fun x ↦ x)[I]ₗ = |I|ₗ := by
  sorry

/-- Улучшенная версия {name}`BoundedInterval.joins`, которая также контролирует {name}`α_length`. -/
abbrev BoundedInterval.joins' (K I J : BoundedInterval) : Prop :=  K.joins I J ∧ ∀ α : ℝ → ℝ, α[K]ₗ = α[I]ₗ + α[J]ₗ

-- Усиленная версия `join_Icc_Ioc`: разбиение `Icc a c = Icc a b ∪ Ioc b c` аддитивно и по `α_length`
theorem BoundedInterval.join_Icc_Ioc' {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) : (Icc a c).joins' (Icc a b) (Ioc b c) := ⟨ join_Icc_Ioc hab hbc,
  by simp [α_length, show a ≤ b by grind, show b ≤ c by grind, show a ≤ c by grind] ⟩


-- Усиленная версия `join_Icc_Ioo`: разбиение `Ico a c = Icc a b ∪ Ioo b c` аддитивно и по `α_length`
theorem BoundedInterval.join_Icc_Ioo' {a b c : ℝ} (hab : a ≤ b) (hbc : b < c) : (Ico a c).joins' (Icc a b) (Ioo b c) := ⟨ join_Icc_Ioo hab hbc,
  by simp [α_length, show a ≤ b by grind, show b < c by grind, show a ≤ c by grind] ⟩

-- Усиленная версия `join_Ioc_Ioc`: разбиение `Ioc a c = Ioc a b ∪ Ioc b c` аддитивно и по `α_length`
theorem BoundedInterval.join_Ioc_Ioc' {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) : (Ioc a c).joins' (Ioc a b) (Ioc b c) := ⟨ join_Ioc_Ioc hab hbc,
  by simp [α_length, show a ≤ b by grind, show b ≤ c by grind, show a ≤ c by grind] ⟩

-- Усиленная версия `join_Ioc_Ioo`: разбиение `Ioo a c = Ioc a b ∪ Ioo b c` аддитивно и по `α_length`
theorem BoundedInterval.join_Ioc_Ioo' {a b c : ℝ} (hab : a ≤ b) (hbc : b < c) : (Ioo a c).joins' (Ioc a b) (Ioo b c) := ⟨ join_Ioc_Ioo hab hbc,
  by simp [α_length, show a ≤ b by grind, show b < c by grind, show a < c by grind] ⟩

-- Усиленная версия `join_Ico_Icc`: разбиение `Icc a c = Ico a b ∪ Icc b c` аддитивно и по `α_length`
theorem BoundedInterval.join_Ico_Icc' {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) : (Icc a c).joins' (Ico a b) (Icc b c) := ⟨ join_Ico_Icc hab hbc,
  by simp [α_length, show a ≤ b by grind, show b ≤ c by grind, show a ≤ c by grind] ⟩

-- Усиленная версия `join_Ico_Ico`: разбиение `Ico a c = Ico a b ∪ Ico b c` аддитивно и по `α_length`
theorem BoundedInterval.join_Ico_Ico' {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) : (Ico a c).joins' (Ico a b) (Ico b c) := ⟨ join_Ico_Ico hab hbc,
  by simp [α_length, show a ≤ b by grind, show b ≤ c by grind, show a ≤ c by grind] ⟩

-- Усиленная версия `join_Ioo_Icc`: разбиение `Ioc a c = Ioo a b ∪ Icc b c` аддитивно и по `α_length`
theorem BoundedInterval.join_Ioo_Icc' {a b c : ℝ} (hab : a < b) (hbc : b ≤ c) : (Ioc a c).joins' (Ioo a b) (Icc b c) := ⟨ join_Ioo_Icc hab hbc,
  by simp [α_length, show a < b by grind, show b ≤ c by grind, show a ≤ c by grind] ⟩

-- Усиленная версия `join_Ioo_Ico`: разбиение `Ioo a c = Ioo a b ∪ Ico b c` аддитивно и по `α_length`
theorem BoundedInterval.join_Ioo_Ico' {a b c : ℝ} (hab : a < b) (hbc : b ≤ c) : (Ioo a c).joins' (Ioo a b) (Ico b c) := ⟨ join_Ioo_Ico hab hbc,
  by simp [α_length, show a < b by grind, show b ≤ c by grind, show a < c by grind] ⟩

/-- Теорема 11.8.4 / Упражнение 11.8.1 -/
theorem Partition.sum_of_α_length  {I : BoundedInterval} (P : Partition I) (α : ℝ → ℝ) : 
  ∑ J ∈ P.intervals, α[J]ₗ = α[I]ₗ := by
  sorry

/-- Определение 11.8.5 (кусочно-постоянный RS-интеграл). -/
noncomputable abbrev PiecewiseConstantWith.RS_integ (f : ℝ → ℝ) {I : BoundedInterval} (P : Partition I) (α : ℝ → ℝ)   : 
  ℝ := ∑ J ∈ P.intervals, constant_value_on f (J : Set ℝ) * α[J]ₗ

/-- Пример 11.8.6 -/
noncomputable abbrev f_11_8_6 (x : ℝ) : ℝ := if x < 2 then 4 else 2

noncomputable abbrev P_11_8_6 : Partition (Icc 1 3) :=
  (⊥ : Partition (Ico 1 2)).join (⊥ : Partition (Icc 2 3))
  (join_Ico_Icc (by norm_num) (by norm_num) )

-- Проверка формулы RS-интеграла на конкретном примере 11.8.6
theorem f_11_8_6_RS_integ : PiecewiseConstantWith.RS_integ f_11_8_6 P_11_8_6 (fun x ↦ x^2) = 22 := by
  sorry

/-- Пример 11.8.7 -/
theorem PiecewiseConstantWith.RS_integ_eq_integ {f : ℝ → ℝ} {I : BoundedInterval} (P : Partition I) : RS_integ f P (fun x ↦ x) = integ f P := by
  sorry

/-- Аналог Утверждения 11.2.13 -/
theorem PiecewiseConstantWith.RS_integ_eq {f : ℝ → ℝ} {I : BoundedInterval} {P P' : Partition I}
  (hP : PiecewiseConstantWith f P) (hP' : PiecewiseConstantWith f P') (α : ℝ → ℝ) : RS_integ f P α = RS_integ f P' α := by
  sorry

open Classical in
noncomputable abbrev PiecewiseConstantOn.RS_integ (f : ℝ → ℝ) (I : BoundedInterval) (α : ℝ → ℝ) : 
  ℝ := if h : PiecewiseConstantOn f I then PiecewiseConstantWith.RS_integ f h.choose α else 0

-- RS-интеграл, определённый через инфимум/супремум, совпадает с явной формулой по разбиению `P`
theorem PiecewiseConstantOn.RS_integ_def {f : ℝ → ℝ} {I : BoundedInterval} {P : Partition I}
  (h : PiecewiseConstantWith f P) (α : ℝ → ℝ) : RS_integ f I α = PiecewiseConstantWith.RS_integ f P α := by
  have h' : PiecewiseConstantOn f I := by use P
  simp [RS_integ, h']; exact PiecewiseConstantWith.RS_integ_eq h'.choose_spec h α

/-- {name}`α_length` неотрицательна, когда α монотонна -/
theorem α_length_nonneg_of_monotone {α : ℝ → ℝ}  (hα : Monotone α) (I : BoundedInterval) : 
  0 ≤ α[I]ₗ := by
  sorry

/-- Аналог Теоремы 11.2.16 (a) (законы интегрирования) / Упражнение 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_add {f g : ℝ → ℝ} {I : BoundedInterval}
  (hf : PiecewiseConstantOn f I) (hg : PiecewiseConstantOn g I) {α : ℝ → ℝ} (hα : Monotone α) : 
  RS_integ (f + g) I α = RS_integ f I α + RS_integ g I α := by
  sorry

/-- Аналог Теоремы 11.2.16 (b) (законы интегрирования) / Упражнение 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_smul {f : ℝ → ℝ} {I : BoundedInterval} (c : ℝ)
  (hf : PiecewiseConstantOn f I) {α : ℝ → ℝ} (hα : Monotone α) : 
  RS_integ (c • f) I α = c * RS_integ f I α
   := by
  sorry

/-- Теорема 11.8.8 (c) (законы RS-интегрирования) / Упражнение 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_sub {f g : ℝ → ℝ} {I : BoundedInterval}
  {α : ℝ → ℝ} (hα : Monotone α)
  (hf : PiecewiseConstantOn f I) (hg : PiecewiseConstantOn g I) : 
  RS_integ (f - g) I α = RS_integ f I α - RS_integ g I α := by
  sorry

/-- Теорема 11.8.8 (d) (законы RS-интегрирования) / Упражнение 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_of_nonneg {f : ℝ → ℝ} {I : BoundedInterval}
  {α : ℝ → ℝ} (hα : Monotone α)
  (h : ∀ x ∈ I, 0 ≤ f x) (hf : PiecewiseConstantOn f I) : 
  0 ≤ RS_integ f I α := by
  sorry

/-- Теорема 11.8.8 (e) (законы RS-интегрирования) / Упражнение 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_mono {f g : ℝ → ℝ} {I : BoundedInterval}
  {α : ℝ → ℝ} (hα : Monotone α)
  (h : ∀ x ∈ I, f x ≤ g x) (hf : PiecewiseConstantOn f I) (hg : PiecewiseConstantOn g I) : 
  RS_integ f I α ≤ RS_integ g I α := by
  sorry

/-- Теорема 11.8.8 (f) (законы RS-интегрирования) / Упражнение 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_const (c : ℝ) (I : BoundedInterval) {α : ℝ → ℝ} (hα : Monotone α) : 
  RS_integ (fun _ ↦ c) I α = c * α[I]ₗ := by
  sorry

/-- Теорема 11.8.8 (f') (законы RS-интегрирования) / Упражнение 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_const' {f : ℝ → ℝ} {I : BoundedInterval}
  {α : ℝ → ℝ} (hα : Monotone α) (h : ConstantOn f I) : 
  RS_integ f I α = (constant_value_on f I) * α[I]ₗ := by
  sorry

open Classical in
/-- Теорема 11.8.8 (g) (законы RS-интегрирования) / Упражнение 11.8.3 -/
theorem PiecewiseConstantOn.RS_of_extend {I J : BoundedInterval} (hIJ : I ⊆ J)
  {f : ℝ → ℝ} (h : PiecewiseConstantOn f I) {α : ℝ → ℝ} (hα : Monotone α) : 
  PiecewiseConstantOn (fun x ↦ if x ∈ I then f x else 0) J := by
  sorry

open Classical in
/-- Теорема 11.8.8 (g') (законы RS-интегрирования) / Упражнение 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_of_extend {I J : BoundedInterval} (hIJ : I ⊆ J)
  {f : ℝ → ℝ} (h : PiecewiseConstantOn f I) {α : ℝ → ℝ} (hα : Monotone α) : 
  RS_integ (fun x ↦ if x ∈ I then f x else 0) J α = RS_integ f I α := by
  sorry

/-- Теорема 11.8.8 (h) (законы RS-интегрирования) / Упражнение 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_of_join {I J K : BoundedInterval} (hIJK : K.joins' I J)
  {f : ℝ → ℝ} (h : PiecewiseConstantOn f K) {α : ℝ → ℝ} (hα : Monotone α) : 
  RS_integ f K α = RS_integ f I α + RS_integ f J α := by
  sorry

/-- Аналог Определения 11.3.2 (верхний и нижний интегралы Римана). -/
noncomputable abbrev upper_RS_integral (f : ℝ → ℝ) (I : BoundedInterval) (α : ℝ → ℝ) : ℝ :=
  sInf ((PiecewiseConstantOn.RS_integ · I α) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I})

noncomputable abbrev lower_RS_integral (f : ℝ → ℝ) (I : BoundedInterval) (α : ℝ → ℝ) : ℝ :=
  sSup ((PiecewiseConstantOn.RS_integ · I α) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I})

-- Постоянная мажоранта `M` даёт значение `M * α[I]ₗ` среди RS-интегралов кусочно-постоянных мажорант `f`
lemma RS_integral_bound_upper_of_bounded {f : ℝ → ℝ} {M : ℝ} {I : BoundedInterval}
  (h : ∀ x ∈ (I : Set ℝ), |f x| ≤ M) {α : ℝ → ℝ} (hα : Monotone α)
  : M * α[I]ₗ ∈ (PiecewiseConstantOn.RS_integ · I α) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I} := by
  simp; refine ⟨ fun _ ↦ M, ⟨ ⟨ ?_, ?_ ⟩, PiecewiseConstantOn.RS_integ_const M I hα ⟩ ⟩
  . grind [abs_le']
  exact (ConstantOn.of_const (c := M) (by simp)).piecewiseConstantOn


-- Постоянная миноранта `-M` даёт значение `-M * α[I]ₗ` среди RS-интегралов кусочно-постоянных минорант `f`
lemma RS_integral_bound_lower_of_bounded {f : ℝ → ℝ} {M : ℝ} {I : BoundedInterval} (h : ∀ x ∈ (I : Set ℝ), |f x| ≤ M) {α : ℝ → ℝ} (hα : Monotone α)
  : -M * α[I]ₗ ∈ (PiecewiseConstantOn.RS_integ · I α) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I} := by
  simp; refine ⟨ fun _ ↦ -M, ⟨ ⟨ ?_, ?_ ⟩, by convert PiecewiseConstantOn.RS_integ_const _ _ hα using 1; simp ⟩ ⟩
  . grind [abs_le']
  exact (ConstantOn.of_const (c := -M) (by simp)).piecewiseConstantOn


-- Множество RS-интегралов кусочно-постоянных мажорант ограниченной `f` непусто
lemma RS_integral_bound_upper_nonempty {f : ℝ → ℝ} {I : BoundedInterval} (h : BddOn f I)
  {α : ℝ → ℝ} (hα : Monotone α) : 
  ((PiecewiseConstantOn.RS_integ · I α) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I}).Nonempty := by
  choose M h using h; exact Set.nonempty_of_mem (RS_integral_bound_upper_of_bounded h hα)

-- Множество RS-интегралов кусочно-постоянных минорант ограниченной `f` непусто
lemma RS_integral_bound_lower_nonempty {f : ℝ → ℝ} {I : BoundedInterval} (h : BddOn f I)
  {α : ℝ → ℝ} (hα : Monotone α) : 
  ((PiecewiseConstantOn.RS_integ · I α) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I}).Nonempty := by
  choose M h using h; exact Set.nonempty_of_mem (RS_integral_bound_lower_of_bounded h hα)

-- RS-интеграл любой кусочно-постоянной миноранты `f` не превосходит RS-интеграла любой мажоранты
lemma RS_integral_bound_lower_le_upper {f : ℝ → ℝ} {I : BoundedInterval} {a b : ℝ}
  {α : ℝ → ℝ} (hα : Monotone α)
  (ha : a ∈ (PiecewiseConstantOn.RS_integ · I α) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I})
  (hb : b ∈ (PiecewiseConstantOn.RS_integ · I α) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I})
  : b ≤ a:= by
    have ⟨ g, ⟨ ⟨ hmaj, hgp⟩, hgi ⟩ ⟩ := ha
    have ⟨ h, ⟨ ⟨ hmin, hhp⟩, hhi ⟩ ⟩ := hb
    rw [←hgi, ←hhi]; apply hhp.RS_integ_mono hα _ hgp; intro _ hx; linarith [hmin _ hx, hmaj _ hx]

-- Множество RS-интегралов кусочно-постоянных мажорант `f` ограничено снизу
lemma RS_integral_bound_below {f : ℝ → ℝ} {I : BoundedInterval} (h : BddOn f I)
  {α : ℝ → ℝ} (hα : Monotone α) : 
  BddBelow ((PiecewiseConstantOn.RS_integ · I α) ''
    {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I}) := by
    rw [bddBelow_def]; use (RS_integral_bound_lower_nonempty h hα).some
    intro a ha; exact RS_integral_bound_lower_le_upper hα ha (RS_integral_bound_lower_nonempty h hα).some_mem

-- Множество RS-интегралов кусочно-постоянных минорант `f` ограничено сверху
lemma RS_integral_bound_above {f : ℝ → ℝ} {I : BoundedInterval} (h : BddOn f I)
  {α : ℝ → ℝ} (hα : Monotone α) : 
  BddAbove ((PiecewiseConstantOn.RS_integ · I α) ''
    {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I}) := by
    rw [bddAbove_def]; use (RS_integral_bound_upper_nonempty h hα).some
    intro b hb; exact RS_integral_bound_lower_le_upper hα (RS_integral_bound_upper_nonempty h hα).some_mem hb

-- Равномерная оценка `|f| ≤ M` даёт нижнюю границу `-M * α[I]ₗ` для нижнего RS-интеграла
lemma le_lower_RS_integral {f : ℝ → ℝ} {I : BoundedInterval} {M : ℝ} (h : ∀ x ∈ (I : Set ℝ), |f x| ≤ M)
  {α : ℝ → ℝ} (hα : Monotone α) : 
  -M * α[I]ₗ ≤ lower_RS_integral f I α :=
  le_csSup (RS_integral_bound_above (BddOn.of_bounded h) hα) (RS_integral_bound_lower_of_bounded h hα)

-- Нижний RS-интеграл не превосходит верхнего
lemma lower_RS_integral_le_upper {f : ℝ → ℝ} {I : BoundedInterval} (h : BddOn f I)
  {α : ℝ → ℝ} (hα : Monotone α) : 
  lower_RS_integral f I α ≤ upper_RS_integral f I α := by
  apply csSup_le (RS_integral_bound_lower_nonempty h hα)
  intros
  apply le_csInf (RS_integral_bound_upper_nonempty h hα)
  intros; solve_by_elim [RS_integral_bound_lower_le_upper]

-- Равномерная оценка `|f| ≤ M` даёт верхнюю границу `M * α[I]ₗ` для верхнего RS-интеграла
lemma RS_upper_integral_le {f : ℝ → ℝ} {I : BoundedInterval} {M : ℝ} (h : ∀ x ∈ (I : Set ℝ), |f x| ≤ M)
  {α : ℝ → ℝ} (hα : Monotone α) : 
  upper_RS_integral f I α ≤ M * α[I]ₗ :=
  csInf_le (RS_integral_bound_below (.of_bounded h) hα) (RS_integral_bound_upper_of_bounded h hα)

-- Верхний RS-интеграл `f` не превосходит RS-интеграла любой её кусочно-постоянной мажоранты `g`
lemma upper_RS_integral_le_integ {f g : ℝ → ℝ} {I : BoundedInterval} (hf : BddOn f I)
  (hfg : MajorizesOn g f I) (hg : PiecewiseConstantOn g I)
  {α : ℝ → ℝ} (hα : Monotone α) : 
  upper_RS_integral f I α ≤ PiecewiseConstantOn.RS_integ g I α :=
  csInf_le (RS_integral_bound_below hf hα) ⟨ g, by simpa [hg] ⟩

-- RS-интеграл любой кусочно-постоянной миноранты `h` функции `f` не превосходит нижнего RS-интеграла `f`
lemma integ_le_lower_RS_integral {f h : ℝ → ℝ} {I : BoundedInterval} (hf : BddOn f I)
  (hfh : MinorizesOn h f I) (hg : PiecewiseConstantOn h I)
  {α : ℝ → ℝ} (hα : Monotone α) : 
  PiecewiseConstantOn.RS_integ h I α ≤ lower_RS_integral f I α :=
  le_csSup (RS_integral_bound_above hf hα) ⟨ h, by simpa [hg] ⟩

-- Если `X` больше верхнего RS-интеграла `f`, найдётся мажорирующая кусочно-постоянная `g` с RS-интегралом меньше `X`
lemma lt_of_gt_upper_RS_integral {f : ℝ → ℝ} {I : BoundedInterval} (hf : BddOn f I)
  {α : ℝ → ℝ} (hα : Monotone α) {X : ℝ} (hX : upper_RS_integral f I α < X ) : 
  ∃ g, MajorizesOn g f I ∧ PiecewiseConstantOn g I ∧ PiecewiseConstantOn.RS_integ g I α < X := by
  have ⟨ Y, hY, hYX ⟩ := exists_lt_of_csInf_lt (RS_integral_bound_upper_nonempty hf hα) hX
  simp at hY; have ⟨ g, ⟨ hmaj, hgp ⟩, hgi ⟩ := hY; exact ⟨ g, hmaj, hgp, by rwa [hgi] ⟩

-- Если `X` меньше нижнего RS-интеграла `f`, найдётся минорирующая кусочно-постоянная `h` с RS-интегралом больше `X`
lemma gt_of_lt_lower_RS_integral {f : ℝ → ℝ} {I : BoundedInterval} (hf : BddOn f I)
  {α : ℝ → ℝ} (hα : Monotone α) {X : ℝ} (hX : X < lower_RS_integral f I α) : 
  ∃ h, MinorizesOn h f I ∧ PiecewiseConstantOn h I ∧ X < PiecewiseConstantOn.RS_integ h I α := by
  have ⟨ Y, hY, hYX ⟩ := exists_lt_of_lt_csSup (RS_integral_bound_lower_nonempty hf hα) hX
  simp at hY; have ⟨ h, ⟨ hmin, hhp ⟩, hhi ⟩ := hY; exact ⟨ h, hmin, hhp, by rwa [hhi] ⟩

/-- Analogue of Определение 11.3.4 -/
noncomputable abbrev RS_integ (f : ℝ → ℝ) (I : BoundedInterval) (α : ℝ → ℝ) : ℝ := upper_RS_integral f I α

noncomputable abbrev RS_IntegrableOn (f : ℝ → ℝ) (I : BoundedInterval) (α : ℝ → ℝ) : Prop :=
  BddOn f I ∧ lower_RS_integral f I α = upper_RS_integral f I α

/-- Аналог различных частей Леммы 11.3.3 -/
theorem upper_RS_integral_eq_upper_integral (f : ℝ → ℝ) (I : BoundedInterval) : 
  upper_RS_integral f I (fun x ↦ x) = upper_integral f I := by
  sorry

-- Нижний RS-интеграл с весом `α(x) = x` совпадает с обычным нижним интегралом Римана
theorem lower_RS_integral_eq_lower_integral (f : ℝ → ℝ) (I : BoundedInterval) : 
  lower_RS_integral f I (fun x ↦ x) = lower_integral f I := by
  sorry

-- RS-интеграл с весом `α(x) = x` совпадает с обычным интегралом Римана
theorem RS_integ_eq_integ (f : ℝ → ℝ) (I : BoundedInterval) : 
  RS_integ f I (fun x ↦ x) = integ f I := by
  sorry

-- Интегрируемость по Риману–Стилтьесу с весом `α(x) = x` равносильна обычной интегрируемости по Риману
theorem RS_IntegrableOn_iff_IntegrableOn (f : ℝ → ℝ) (I : BoundedInterval) : 
  RS_IntegrableOn f I (fun x ↦ x) ↔ IntegrableOn f I := by
  sorry

/-- Упражнение 11.8.4 -/
theorem RS_integ_of_uniform_cts {I : BoundedInterval} {f : ℝ → ℝ} (hf : UniformContinuousOn f I)
 {α : ℝ → ℝ} (hα : Monotone α) : 
  RS_IntegrableOn f I α := by
  sorry

/-- Упражнение 11.8.5 -/
theorem RS_integ_with_sign (f : ℝ → ℝ) (hf : ContinuousOn f (.Icc (-1) 1)) : RS_IntegrableOn f (Icc (-1) 1) Real.sign ∧ RS_integ f (Icc (-1) 1) Real.sign = 2 * f 0 := by
  sorry

/-- Аналог Леммы 11.3.7 -/
theorem RS_integ_of_piecewise_const {f : ℝ → ℝ} {I : BoundedInterval} (hf : PiecewiseConstantOn f I)
  {α : ℝ → ℝ} (hα : Monotone α) : 
  RS_IntegrableOn f I α ∧ RS_integ f I α = PiecewiseConstantOn.RS_integ f I α := by
  sorry

end Chapter11
