import Mathlib.Tactic
import Analysis.Section_11_1

/-!
# Analysis I, раздел 11.2: Кусочно-постоянные функции

Я старался сделать перевод максимально точным перефразированием оригинального текста. Когда
приходилось выбирать между более идиоматичным Lean-решением и более точным переводом, я, как
правило, выбирал второе. В частности, местами Lean-код можно было бы "заголфить", сделав его более
элегантным и идиоматичным, но я сознательно этого избегал.

Основные конструкции и результаты этого раздела:
- Кусочно-постоянные функции.
- Кусочно-постоянный интеграл.

-/

namespace Chapter11
open BoundedInterval

/-- Определение 11.2.1 -/
abbrev Constant {X Y : Type} (f : X → Y) : Prop := ∃ c, ∀ x, f x = c

open Classical in
noncomputable abbrev constant_value {X Y : Type} [hY : Nonempty Y] (f : X → Y) : Y :=
  if h : Constant f
  then h.choose
  else hY.some

-- Значение постоянной функции `f` в любой точке `x` совпадает с её значением `constant_value f`
theorem Constant.eq {X Y : Type} {f : X → Y} [Nonempty Y] (h : Constant f) (x : X) :
  f x = constant_value f := by simp [constant_value, h]; apply h.choose_spec

-- Функция, принимающая одно и то же значение `c` во всех точках, постоянна (`Constant f`)
theorem Constant.of_const {X Y : Type} {f : X → Y} {c : Y} (h : ∀ x, f x = c) :
  Constant f := by use c

-- Если `f x = c` для всех `x`, то `constant_value f = c`
theorem Constant.const_eq {X Y : Type} {f : X → Y} [hX : Nonempty X] [Nonempty Y] {c : Y}
  (h : ∀ x, f x = c) :
    constant_value f = c := by
      rw [←eq (of_const h) hX.some, h hX.some]

-- Любая функция на не более чем одноэлементной области определения (`Subsingleton X`) постоянна
theorem Constant.of_subsingleton {X Y : Type} [hs : Subsingleton X] [hY : Nonempty Y] {f : X → Y} :
  Constant f := by
  by_cases h : Nonempty X
  . use f h.some
    intros
    congr
    exact hs.elim _ h.some
  · simp at h
    exact ⟨ hY.some, h.elim ⟩

abbrev ConstantOn (f : ℝ → ℝ) (X : Set ℝ) : Prop :=
  Constant (fun x : X ↦ f ↑x)

noncomputable abbrev constant_value_on (f : ℝ → ℝ) (X : Set ℝ) : ℝ :=
  constant_value (fun x : X ↦ f ↑x)

-- Значение функции `f`, постоянной на `X` (`ConstantOn f X`), в любой точке `x ∈ X` совпадает с `constant_value_on f X`
theorem ConstantOn.eq
  {f : ℝ → ℝ} {X : Set ℝ} (h : ConstantOn f X) {x : ℝ} (hx : x ∈ X) :
    f x = constant_value_on f X := by
    convert Constant.eq h ⟨ _, hx ⟩

-- Если `f x = c` для всех `x ∈ X`, то `f` постоянна на `X`
theorem ConstantOn.of_const
  {f : ℝ → ℝ} {X : Set ℝ} {c : ℝ} (h : ∀ x ∈ X, f x = c) :
    ConstantOn f X := ⟨ c, by grind ⟩

-- Постоянная функция `fun _ ↦ c` постоянна на любом множестве `X`
theorem ConstantOn.of_const' (c : ℝ) (X : Set ℝ) : ConstantOn (fun _ ↦ c) X :=
  of_const (c := c) (by simp)

-- Если `X` непусто и `f x = c` для всех `x ∈ X`, то `constant_value_on f X = c`
theorem ConstantOn.const_eq
  {f : ℝ → ℝ} {X : Set ℝ} (hX : X.Nonempty) {c : ℝ} (h : ∀ x ∈ X, f x = c) :
    constant_value_on f X = c := by
      rw [←eq (of_const h) hX.some_mem, h _ hX.some_mem]

-- Если `f` и `g` совпадают на `X`, то `ConstantOn f X` равносильно `ConstantOn g X`
theorem ConstantOn.congr {f g : ℝ → ℝ} {X : Set ℝ}
  (h : ∀ x ∈ X, f x = g x) : ConstantOn f X ↔ ConstantOn g X := by
    simp_rw [ConstantOn, iff_iff_eq]
    congr
    grind

-- Если `f` постоянна на `X` и совпадает с `g` на `X`, то `g` тоже постоянна на `X`
theorem ConstantOn.congr' {f g : ℝ → ℝ} {X : Set ℝ}
  (hf : ConstantOn f X) (h : ∀ x ∈ X, f x = g x) : ConstantOn g X :=
    (congr h).mp hf

-- Любая функция постоянна на не более чем одноэлементном множестве `X`
theorem ConstantOn.of_subsingleton {f : ℝ → ℝ} {X : Set ℝ} [Subsingleton X] :
  ConstantOn f X := Constant.of_subsingleton

-- Если `f` и `g` совпадают на `X`, их постоянные значения на `X` (`constant_value_on`) равны
theorem constant_value_on_congr {f g : ℝ → ℝ} {X : Set ℝ} (h : ∀ x ∈ X, f x = g x) :
  constant_value_on f X = constant_value_on g X := by
  simp [constant_value_on]; congr; grind

/-- Определение 11.2.3 (кусочно-постоянные функции I) -/
abbrev PiecewiseConstantWith (f : ℝ → ℝ) {I : BoundedInterval} (P : Partition I) : Prop := ∀ J ∈ P, ConstantOn f (J : Set ℝ)

-- Разворачивает определение `PiecewiseConstantWith f P`: на каждом интервале `J` разбиения `P` функция `f` принимает единственное значение `c`
theorem PiecewiseConstantWith.def (f : ℝ → ℝ) {I : BoundedInterval} {P : Partition I} :
  PiecewiseConstantWith f P ↔ ∀ J ∈ P, ∃ c, ∀ x ∈ J, f x = c := by
    simp [PiecewiseConstantWith, ConstantOn, Constant, mem_iff]

-- Если `f` и `g` совпадают на `I`, то `PiecewiseConstantWith f P` равносильно `PiecewiseConstantWith g P`
theorem PiecewiseConstantWith.congr {f g : ℝ → ℝ} {I : BoundedInterval} {P : Partition I}
  (h : ∀ x ∈ (I : Set ℝ), f x = g x) :
  PiecewiseConstantWith f P ↔ PiecewiseConstantWith g P := by
  simp [PiecewiseConstantWith]; peel with J hJ
  apply ConstantOn.congr; have := P.contains _ hJ; grind [subset_iff]

/-- Определение 11.2.5 (кусочно-постоянные функции I) -/
abbrev PiecewiseConstantOn (f : ℝ → ℝ) (I : BoundedInterval) : Prop := ∃ P : Partition I, PiecewiseConstantWith f P

-- Разворачивает определение `PiecewiseConstantOn f I`: существует разбиение `I`, на каждом элементе которого `f` постоянна
theorem PiecewiseConstantOn.def (f : ℝ → ℝ) (I : BoundedInterval) :
  PiecewiseConstantOn f I ↔ ∃ P : Partition I, ∀ J ∈ P, ConstantOn f (J : Set ℝ) := by rfl

-- Если `f` и `g` совпадают на `I`, то `PiecewiseConstantOn f I` равносильно `PiecewiseConstantOn g I`
theorem PiecewiseConstantOn.congr {f g : ℝ → ℝ} {I : BoundedInterval} (h : ∀ x ∈ (I : Set ℝ), f x = g x) :
  PiecewiseConstantOn f I ↔ PiecewiseConstantOn g I := by
  simp_rw [PiecewiseConstantOn, PiecewiseConstantWith.congr h]

-- Если `f` кусочно-постоянна на `I` и совпадает с `g` на `I`, то `g` тоже кусочно-постоянна на `I`
theorem PiecewiseConstantOn.congr' {f g : ℝ → ℝ} {I : BoundedInterval} (hf : PiecewiseConstantOn f I) (h : ∀ x ∈ (I : Set ℝ), f x = g x) : PiecewiseConstantOn g I := (congr h).mp hf

/-- Пример 11.2.4 / Пример 11.2.6 -/
noncomputable abbrev f_11_2_4 : ℝ → ℝ := fun x ↦
  if x < 1 then 0 else  -- бросовое значение
    if x < 3 then 7 else
      if x = 3 then 4 else
        if x < 6 then 5 else
          if x = 6 then 2 else
            0 -- бросовое значение

example : PiecewiseConstantOn f_11_2_4 (Icc 1 6) := by
  use Partition.mk { Ico 1 3, Icc 3 3, Ioo 3 6, Icc 6 6} ?_ ?_
  . sorry
  . sorry
  sorry

example : PiecewiseConstantOn f_11_2_4 (Icc 1 6) := by
  use Partition.mk { Ico 1 2, Icc 2 2, Ioo 2 3, Icc 3 3, Ioo 3 5, Ico 5 6, Icc 6 6} ?_ ?_
  . sorry
  . sorry
  sorry

/-- Пример 11.2.6 -/
theorem ConstantOn.piecewiseConstantOn {f : ℝ → ℝ} {I : BoundedInterval} (h : ConstantOn f (I : Set ℝ)) :
  PiecewiseConstantOn f I := by sorry

/-- Лемма 11.2.7 / Упражнение 11.2.1 -/
theorem PiecewiseConstantWith.mono {f : ℝ → ℝ} {I : BoundedInterval} {P P' : Partition I} (hPP' : P ≤ P')
  (hP : PiecewiseConstantWith f P) : PiecewiseConstantWith f P' := by
  sorry

/-- Лемма 11.2.8 / Упражнение 11.2.2 (add). -/
theorem PiecewiseConstantOn.add {f g : ℝ → ℝ} {I : BoundedInterval}
  (hf : PiecewiseConstantOn f I) (hg : PiecewiseConstantOn g I) : PiecewiseConstantOn (f + g) I := by
  sorry

/-- Лемма 11.2.8 / Упражнение 11.2.2 (sub). -/
theorem PiecewiseConstantOn.sub {f g : ℝ → ℝ} {I : BoundedInterval}
  (hf : PiecewiseConstantOn f I) (hg : PiecewiseConstantOn g I) : PiecewiseConstantOn (f - g) I := by
  sorry

/-- Лемма 11.2.8 / Упражнение 11.2.2 (max). -/
theorem PiecewiseConstantOn.max {f g : ℝ → ℝ} {I : BoundedInterval}
  (hf : PiecewiseConstantOn f I) (hg : PiecewiseConstantOn g I) : PiecewiseConstantOn (max f g) I := by
  sorry

/-- Лемма 11.2.8 / Упражнение 11.2.2 (min). -/
theorem PiecewiseConstantOn.min {f g : ℝ → ℝ} {I : BoundedInterval}
  (hf : PiecewiseConstantOn f I) (hg : PiecewiseConstantOn g I) : PiecewiseConstantOn (min f g) I := by
  sorry

/-- Лемма 11.2.8 / Упражнение 11.2.2 (mul). -/
theorem PiecewiseConstantOn.mul {f g : ℝ → ℝ} {I : BoundedInterval}
  (hf : PiecewiseConstantOn f I) (hg : PiecewiseConstantOn g I) : PiecewiseConstantOn (f * g) I := by
  sorry

/-- Лемма 11.2.8 / Упражнение 11.2.2 (smul). -/
theorem PiecewiseConstantOn.smul {f : ℝ → ℝ} {I : BoundedInterval}
  (c : ℝ) (hf : PiecewiseConstantOn f I) : PiecewiseConstantOn (c • f) I := by
  sorry

/-- Лемма 11.2.8 / Упражнение 11.2.2 (div). -/
theorem PiecewiseConstantOn.div {f g : ℝ → ℝ} {I : BoundedInterval}
  (hf : PiecewiseConstantOn f I) (hg : PiecewiseConstantOn g I) (hg_ne : ∀ x ∈ I.toSet, g x ≠ 0) :
  PiecewiseConstantOn (f / g) I := by
  sorry

/-- Определение 11.2.9 (кусочно-постоянный интеграл I). -/
noncomputable abbrev PiecewiseConstantWith.integ (f : ℝ → ℝ) {I : BoundedInterval} (P : Partition I)  :
  ℝ := ∑ J ∈ P.intervals, constant_value_on f (J : Set ℝ) * |J|ₗ

-- Если `f` и `g` совпадают на `I`, их кусочно-постоянные интегралы по разбиению `P` равны
theorem PiecewiseConstantWith.integ_congr {f g : ℝ → ℝ} {I : BoundedInterval} {P : Partition I}
  (h : ∀ x ∈ (I : Set ℝ), f x = g x) : integ f P = integ g P := by
  apply Finset.sum_congr rfl; intro J hJ; congr 1; apply constant_value_on_congr
  have := P.contains _ hJ; grind [subset_iff]

/-- Пример 11.2.12 -/
noncomputable abbrev f_11_2_12 : ℝ → ℝ := fun x ↦
    if x < 3 then 2 else
      if x = 3 then 4 else
        6

noncomputable abbrev P_11_2_12 : Partition (Icc 1 4) :=
  ((⊥ : Partition (Ico 1 3)).join (⊥ : Partition (Icc 3 3))
  (join_Ico_Icc (by norm_num) (by norm_num) )).join
  (⊥ : Partition (Ioc 3 4))
  (join_Icc_Ioc (by norm_num) (by norm_num))

example : PiecewiseConstantWith f_11_2_12 P_11_2_12 := by
  sorry

example : PiecewiseConstantWith.integ f_11_2_12 P_11_2_12 = 10 := by
  sorry

noncomputable abbrev P_11_2_12' : Partition (Icc 1 4) :=
  ((((⊥ : Partition (Ico 1 2)).join (⊥ : Partition (Ico 2 3))
  (join_Ico_Ico (by norm_num) (by norm_num) )).join
  (⊥ : Partition (Icc 3 3))
  (join_Ico_Icc (by norm_num) (by norm_num))).join
  (⊥ : Partition (Ioc 3 4))
  (join_Icc_Ioc (by norm_num) (by norm_num))).add_empty

example : PiecewiseConstantWith f_11_2_12 P_11_2_12' := by
  sorry

example : PiecewiseConstantWith.integ f_11_2_12 P_11_2_12' = 10 := by
  sorry

/-- Утверждение 11.2.13 (кусочно-постоянный интеграл не зависит от разбиения) / Упражнение 11.2.3 -/
theorem PiecewiseConstantWith.integ_eq {f : ℝ → ℝ} {I : BoundedInterval} {P P' : Partition I}
  (hP : PiecewiseConstantWith f P) (hP' : PiecewiseConstantWith f P') : integ f P = integ f P' := by
  sorry

open Classical in
/-- Определение 11.2.14 (кусочно-постоянный интеграл II)  -/
noncomputable abbrev PiecewiseConstantOn.integ (f : ℝ → ℝ) (I : BoundedInterval) :
  ℝ := if h : PiecewiseConstantOn f I then PiecewiseConstantWith.integ f h.choose else 0

noncomputable abbrev PiecewiseConstantOn.integ' {f : ℝ → ℝ} {I : BoundedInterval} (_ : PiecewiseConstantOn f I) := integ f I

-- Если `f` кусочно-постоянна относительно разбиения `P`, то интеграл `integ f I` (Определение 11.2.14) совпадает с `PiecewiseConstantWith.integ f P`
theorem PiecewiseConstantOn.integ_def {f : ℝ → ℝ} {I : BoundedInterval} {P : Partition I}
  (h : PiecewiseConstantWith f P) : integ f I = PiecewiseConstantWith.integ f P := by
  have h' : PiecewiseConstantOn f I := by use P
  simp [integ, h']; exact PiecewiseConstantWith.integ_eq h'.choose_spec h

-- Если `f` и `g` совпадают на `I`, их интегралы `integ f I` и `integ g I` равны
theorem PiecewiseConstantOn.integ_congr {f g : ℝ → ℝ} {I : BoundedInterval}
  (h : ∀ x ∈ (I : Set ℝ), f x = g x) : integ f I = integ g I := by
  by_cases hf : PiecewiseConstantOn f I
  <;> (have hg := hf; rw [congr h] at hg; simp [integ, hf, hg])
  rw [PiecewiseConstantWith.integ_congr h, ←integ_def hg.choose_spec, ←integ_def]
  rw [←PiecewiseConstantWith.congr h]; exact hf.choose_spec

/-- Пример 11.2.15 -/
example : PiecewiseConstantOn.integ f_11_2_12 (Icc 1 4) = 10 := by
  sorry

/-- Теорема 11.2.16 (a) (законы интегрирования) / Упражнение 11.2.4 -/
theorem PiecewiseConstantOn.integ_add {f g : ℝ → ℝ} {I : BoundedInterval}
  (hf : PiecewiseConstantOn f I) (hg : PiecewiseConstantOn g I) :
  integ (f + g) I = integ f I + integ g I := by
  sorry

/-- Теорема 11.2.16 (b) (законы интегрирования) / Упражнение 11.2.4 -/
theorem PiecewiseConstantOn.integ_smul {f : ℝ → ℝ} {I : BoundedInterval} (c : ℝ) (hf : PiecewiseConstantOn f I) :
  integ (c • f) I = c * integ f I
   := by
  sorry

/-- Теорема 11.2.16 (c) (законы интегрирования) / Упражнение 11.2.4 -/
theorem PiecewiseConstantOn.integ_sub {f g : ℝ → ℝ} {I : BoundedInterval}
  (hf : PiecewiseConstantOn f I) (hg : PiecewiseConstantOn g I) :
  integ (f - g) I = integ f I - integ g I := by
  sorry

/-- Теорема 11.2.16 (d) (законы интегрирования) / Упражнение 11.2.4 -/
theorem PiecewiseConstantOn.integ_of_nonneg {f : ℝ → ℝ} {I : BoundedInterval} (h : ∀ x ∈ I, 0 ≤ f x)
  (hf : PiecewiseConstantOn f I) :
  0 ≤ integ f I := by
  sorry

/-- Теорема 11.2.16 (e) (законы интегрирования) / Упражнение 11.2.4 -/
theorem PiecewiseConstantOn.integ_mono {f g : ℝ → ℝ} {I : BoundedInterval} (h : ∀ x ∈ I, f x ≤ g x)
  (hf : PiecewiseConstantOn f I) (hg : PiecewiseConstantOn g I) :
  integ f I ≤ integ g I := by
  sorry


/-- Теорема 11.2.16 (f) (законы интегрирования) / Упражнение 11.2.4 -/
theorem PiecewiseConstantOn.integ_const (c : ℝ) (I : BoundedInterval) :
  integ (fun _ ↦ c) I = c * |I|ₗ := by
  sorry

/-- Теорема 11.2.16 (f') (законы интегрирования) / Упражнение 11.2.4 -/
theorem PiecewiseConstantOn.integ_const' {f : ℝ → ℝ} {I : BoundedInterval} (h : ConstantOn f I) :
  integ f I = (constant_value_on f I) * |I|ₗ := by
  sorry

open Classical in
/-- Теорема 11.2.16 (g) (законы интегрирования) / Упражнение 11.2.4 -/
theorem PiecewiseConstantOn.of_extend {I J : BoundedInterval} (hIJ : I ⊆ J)
  {f : ℝ → ℝ} (h : PiecewiseConstantOn f I) :
  PiecewiseConstantOn (fun x ↦ if x ∈ I then f x else 0) J := by
  sorry

open Classical in
/-- Теорема 11.2.16 (g') (законы интегрирования) / Упражнение 11.2.4 -/
theorem PiecewiseConstantOn.integ_of_extend {I J : BoundedInterval} (hIJ : I ⊆ J)
  {f : ℝ → ℝ} (h : PiecewiseConstantOn f I) :
  integ (fun x ↦ if x ∈ I then f x else 0) J = integ f I := by
  sorry

/-- Теорема 11.2.16 (h) (законы интегрирования) / Упражнение 11.2.4 -/
theorem PiecewiseConstantOn.of_join {I J K : BoundedInterval} (hIJK : K.joins I J)
  (f : ℝ → ℝ) : PiecewiseConstantOn f K ↔ PiecewiseConstantOn f I ∧ PiecewiseConstantOn f J := by
  sorry

/-- Теорема 11.2.16 (h') (законы интегрирования) / Упражнение 11.2.4 -/
theorem PiecewiseConstantOn.integ_of_join {I J K : BoundedInterval} (hIJK : K.joins I J)
  {f : ℝ → ℝ} (h : PiecewiseConstantOn f K) :
  integ f K = integ f I + integ f J := by
  sorry

end Chapter11
