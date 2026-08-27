import Analysis.MeasureTheory.Notation
import Analysis.Section_9_1

/-!
# Introduction to Measure Theory, Section 1.1.1: Элементарная мера

Дополнение к разделу 1.1.1 книги "An introduction to Measure Theory".

-/

/- Definition 1.1.1.  (Интервалы) Мы используем ту же формализацию интервалов, что и в
Chapter 11 "Analysis I". Следуя обычному в Lean предпочтению допускать "мусорные" значения,
мы допускаем возможность `b < a`. -/
inductive BoundedInterval where
  | Ioo (a b : ℝ) : BoundedInterval
  | Icc (a b : ℝ) : BoundedInterval
  | Ioc (a b : ℝ) : BoundedInterval
  | Ico (a b : ℝ) : BoundedInterval

open BoundedInterval

/-- Приводит {name}`BoundedInterval` к его базовому множеству действительных чисел. -/
@[coe]
def BoundedInterval.toSet (I : BoundedInterval) : Set ℝ := match I with
  | Ioo a b => .Ioo a b
  | Icc a b => .Icc a b
  | Ioc a b => .Ioc a b
  | Ico a b => .Ico a b

/-- Включает приведение типа из {name}`BoundedInterval` в {lean}`Set ℝ`. -/
instance BoundedInterval.inst_coeSet : Coe BoundedInterval (Set ℝ) where
  coe := toSet

/-- Пустой {name}`BoundedInterval` представлен как вырожденный открытый интервал (0,0). -/
instance BoundedInterval.instEmpty : EmptyCollection BoundedInterval where
  emptyCollection := Ioo 0 0

/-- Пустой {name}`BoundedInterval` приводится к пустому множеству. -/
@[simp]
theorem BoundedInterval.coe_empty : ((∅ : BoundedInterval) : Set ℝ) = ∅ := by
  simp [toSet]

open Classical in
/-- Это нужно, чтобы {name}`Finset`-ы из {name}`BoundedInterval` работали корректно -/
noncomputable instance BoundedInterval.decidableEq : DecidableEq BoundedInterval := instDecidableEqOfLawfulBEq

/-- Simp-леммы для приведения каждого конструктора {name}`BoundedInterval` к {lean}`Set ℝ`. -/
@[simp]
theorem BoundedInterval.set_Ioo (a b : ℝ) : (Ioo a b : Set ℝ) = .Ioo a b := by rfl

@[simp]
theorem BoundedInterval.set_Icc (a b : ℝ) : (Icc a b : Set ℝ) = .Icc a b := by rfl

@[simp]
theorem BoundedInterval.set_Ioc (a b : ℝ) : (Ioc a b : Set ℝ) = .Ioc a b := by rfl

@[simp]
theorem BoundedInterval.set_Ico (a b : ℝ) : (Ico a b : Set ℝ) = .Ico a b := by rfl

/-- Несколько полезных общих лемм про {name}`BoundedInterval` -/
theorem Bornology.IsBounded.of_boundedInterval (I : BoundedInterval) : Bornology.IsBounded (I : Set ℝ) := by
  cases I with
  | Ioo a b =>
    simp [set_Ioo]
    exact Metric.isBounded_Ioo a b
  | Icc a b =>
    simp [set_Icc]
    exact Metric.isBounded_Icc a b
  | Ioc a b =>
    simp [set_Ioc]
    exact Metric.isBounded_Ioc a b
  | Ico a b =>
    simp [set_Ico]
    exact Metric.isBounded_Ico a b

namespace BoundedInterval

/-- Извлекает концы интервала из равенства {name}`BoundedInterval.Icc` -/
lemma Icc_eq_endpoints {a₁ b₁ a₂ b₂ : ℝ}
    (h : Set.Icc a₁ b₁ = Set.Icc a₂ b₂) (ha₁b₁ : a₁ ≤ b₁) (ha₂b₂ : a₂ ≤ b₂) : 
    a₁ = a₂ ∧ b₁ = b₂ := by
  constructor
  · have h₁ : a₁ ∈ Set.Icc a₁ b₁ := by simp [Set.mem_Icc, ha₁b₁]
    rw [h] at h₁; simp [Set.mem_Icc] at h₁
    have h₂ : a₂ ∈ Set.Icc a₂ b₂ := by simp [Set.mem_Icc, ha₂b₂]
    rw [← h] at h₂; simp [Set.mem_Icc] at h₂
    linarith
  · have h₁ : b₁ ∈ Set.Icc a₁ b₁ := by simp [Set.mem_Icc, ha₁b₁]
    rw [h] at h₁; simp [Set.mem_Icc] at h₁
    have h₂ : b₂ ∈ Set.Icc a₂ b₂ := by simp [Set.mem_Icc, ha₂b₂]
    rw [← h] at h₂; simp [Set.mem_Icc] at h₂
    linarith

/-- {name}`BoundedInterval.Ioo` не может быть равен {name}`BoundedInterval.Icc` -/
lemma Ioo_ne_Icc {a₁ b₁ a₂ b₂ : ℝ} (ha₁b₁ : a₁ < b₁) (ha₂b₂ : a₂ ≤ b₂) : 
    Set.Ioo a₁ b₁ ≠ Set.Icc a₂ b₂ := by
  intro h
  have h_cl := congr_arg closure h
  rw [closure_Ioo ha₁b₁.ne, isClosed_Icc.closure_eq] at h_cl
  obtain ⟨ha, hb⟩ := Icc_eq_endpoints h_cl (le_of_lt ha₁b₁) ha₂b₂
  have : a₂ ∉ Set.Ioo a₁ b₁ := by simp [Set.mem_Ioo]; intro; linarith
  have : a₂ ∈ Set.Icc a₂ b₂ := by simp [Set.mem_Icc, ha₂b₂]
  rw [← h] at this
  contradiction

/-- {name}`BoundedInterval.Ioo` не может быть равен {name}`BoundedInterval.Ioc` -/
lemma Ioo_ne_Ioc {a₁ b₁ a₂ b₂ : ℝ} (ha₁b₁ : a₁ < b₁) (ha₂b₂ : a₂ < b₂) : 
    Set.Ioo a₁ b₁ ≠ Set.Ioc a₂ b₂ := by
  intro h
  have h_cl := congr_arg closure h
  rw [closure_Ioo ha₁b₁.ne, closure_Ioc ha₂b₂.ne] at h_cl
  obtain ⟨_, hb⟩ := Icc_eq_endpoints h_cl (le_of_lt ha₁b₁) (le_of_lt ha₂b₂)
  have : b₂ ∈ Set.Ioc a₂ b₂ := ⟨ha₂b₂, le_refl b₂⟩
  rw [← h] at this
  simp [Set.mem_Ioo] at this
  linarith

/-- {name}`BoundedInterval.Ioo` не может быть равен {name}`BoundedInterval.Ico` -/
lemma Ioo_ne_Ico {a₁ b₁ a₂ b₂ : ℝ} (ha₁b₁ : a₁ < b₁) (ha₂b₂ : a₂ < b₂) : 
    Set.Ioo a₁ b₁ ≠ Set.Ico a₂ b₂ := by
  intro h
  have h_cl := congr_arg closure h
  rw [closure_Ioo ha₁b₁.ne, closure_Ico ha₂b₂.ne] at h_cl
  obtain ⟨ha, _⟩ := Icc_eq_endpoints h_cl (le_of_lt ha₁b₁) (le_of_lt ha₂b₂)
  have : a₂ ∈ Set.Ico a₂ b₂ := ⟨le_refl a₂, ha₂b₂⟩
  rw [← h] at this
  simp [Set.mem_Ioo] at this
  linarith

/-- {name}`BoundedInterval.Ioc` не может быть равен {name}`BoundedInterval.Ico` -/
lemma Ioc_ne_Ico {a₁ b₁ a₂ b₂ : ℝ} (ha₁b₁ : a₁ < b₁) (ha₂b₂ : a₂ < b₂) : 
    Set.Ioc a₁ b₁ ≠ Set.Ico a₂ b₂ := by
  intro h
  have h_cl := congr_arg closure h
  rw [closure_Ioc ha₁b₁.ne, closure_Ico ha₂b₂.ne] at h_cl
  obtain ⟨_, hb⟩ := Icc_eq_endpoints h_cl (le_of_lt ha₁b₁) (le_of_lt ha₂b₂)
  have : b₁ ∈ Set.Ioc a₁ b₁ := ⟨ha₁b₁, le_refl b₁⟩
  rw [h] at this
  simp [Set.mem_Ico] at this
  linarith

/-- {name}`BoundedInterval.Icc` не может быть равен {name}`BoundedInterval.Ioc` -/
lemma Icc_ne_Ioc {a₁ b₁ a₂ b₂ : ℝ} (ha₁b₁ : a₁ ≤ b₁) (ha₂b₂ : a₂ < b₂) : 
    Set.Icc a₁ b₁ ≠ Set.Ioc a₂ b₂ := by
  intro h
  have h_cl := congr_arg closure h
  rw [isClosed_Icc.closure_eq, closure_Ioc ha₂b₂.ne] at h_cl
  obtain ⟨ha, _⟩ := Icc_eq_endpoints h_cl ha₁b₁ (le_of_lt ha₂b₂)
  have : a₁ ∈ Set.Icc a₁ b₁ := by simp [Set.mem_Icc, ha₁b₁]
  rw [h] at this
  simp [Set.mem_Ioc] at this
  linarith

/-- {name}`BoundedInterval.Icc` не может быть равен {name}`BoundedInterval.Ico` -/
lemma Icc_ne_Ico {a₁ b₁ a₂ b₂ : ℝ} (ha₁b₁ : a₁ ≤ b₁) (ha₂b₂ : a₂ < b₂) : 
    Set.Icc a₁ b₁ ≠ Set.Ico a₂ b₂ := by
  intro h
  have h_cl := congr_arg closure h
  rw [isClosed_Icc.closure_eq, closure_Ico ha₂b₂.ne] at h_cl
  obtain ⟨_, hb⟩ := Icc_eq_endpoints h_cl ha₁b₁ (le_of_lt ha₂b₂)
  have : b₁ ∈ Set.Icc a₁ b₁ := by simp [Set.mem_Icc, ha₁b₁]
  rw [h] at this
  simp [Set.mem_Ico] at this
  linarith

/-- Извлекает a < b из непустоты {name}`BoundedInterval.Ioo` -/
private lemma nonempty_Ioo_strictness {a b : ℝ} (h : (Ioo a b).toSet.Nonempty) : a < b := by
  obtain ⟨x, hx⟩ := h
  simp [toSet] at hx
  exact hx.1.trans hx.2

/-- Извлекает a < b из непустоты {name}`BoundedInterval.Ioc` -/
private lemma nonempty_Ioc_strictness {a b : ℝ} (h : (Ioc a b).toSet.Nonempty) : a < b := by
  obtain ⟨x, hx⟩ := h
  simp [toSet] at hx
  exact hx.1.trans_le hx.2

/-- Извлекает a < b из непустоты {name}`BoundedInterval.Ico` -/
private lemma nonempty_Ico_strictness {a b : ℝ} (h : (Ico a b).toSet.Nonempty) : a < b := by
  obtain ⟨x, hx⟩ := h
  simp [toSet] at hx
  exact hx.1.trans_lt hx.2

/-- Извлекает a ≤ b из непустоты {name}`BoundedInterval.Icc` -/
private lemma nonempty_Icc_order {a b : ℝ} (h : (Icc a b).toSet.Nonempty) : a ≤ b := by
  obtain ⟨x, hx⟩ := h
  simp [toSet] at hx
  exact hx.1.trans hx.2

/-- Извлекает равные концы из равных множеств {name}`BoundedInterval.Icc` -/
private lemma endpoints_of_Icc_eq {a₁ b₁ a₂ b₂ : ℝ}
    (h_closure : Set.Icc a₁ b₁ = Set.Icc a₂ b₂) (ha₁b₁ : a₁ ≤ b₁) (ha₂b₂ : a₂ ≤ b₂) : 
    a₁ = a₂ ∧ b₁ = b₂ := by
  constructor
  · have h₁ : a₁ ∈ Set.Icc a₁ b₁ := by simp [Set.mem_Icc, ha₁b₁]
    rw [h_closure] at h₁; simp [Set.mem_Icc] at h₁
    have h₂ : a₂ ∈ Set.Icc a₂ b₂ := by simp [Set.mem_Icc, ha₂b₂]
    rw [← h_closure] at h₂; simp [Set.mem_Icc] at h₂
    linarith
  · have h₁ : b₁ ∈ Set.Icc a₁ b₁ := by simp [Set.mem_Icc, ha₁b₁]
    rw [h_closure] at h₁; simp [Set.mem_Icc] at h₁
    have h₂ : b₂ ∈ Set.Icc a₂ b₂ := by simp [Set.mem_Icc, ha₂b₂]
    rw [← h_closure] at h₂; simp [Set.mem_Icc] at h₂
    linarith

/-- {name}`BoundedInterval.toSet` инъективно на непустых интервалах -/
lemma toSet_injective_of_nonempty {I J : BoundedInterval}
    (hI : I.toSet.Nonempty) (hJ : J.toSet.Nonempty) (h_eq : I.toSet = J.toSet) :
    I = J := by
  -- Разбор случаев по обоим интервалам (всего 16 случаев)
  cases I with
  | Ioo a₁ b₁ =>
    cases J with
    | Ioo a₂ b₂ =>
      -- Ioo a₁ b₁ = Ioo a₂ b₂: используем замыкание, чтобы извлечь концы
      have ha₁b₁ := nonempty_Ioo_strictness hI
      have ha₂b₂ := nonempty_Ioo_strictness hJ
      have h_set_eq : Set.Ioo a₁ b₁ = Set.Ioo a₂ b₂ := h_eq
      have h_closure : closure (Set.Ioo a₁ b₁) = closure (Set.Ioo a₂ b₂) := by rw [h_set_eq]
      rw [closure_Ioo ha₁b₁.ne, closure_Ioo ha₂b₂.ne] at h_closure
      obtain ⟨ha, hb⟩ := endpoints_of_Icc_eq h_closure ha₁b₁.le ha₂b₂.le
      rw [ha, hb]
    | Icc a₂ b₂ =>
      exact absurd h_eq (Ioo_ne_Icc (nonempty_Ioo_strictness hI) (nonempty_Icc_order hJ))
    | Ioc a₂ b₂ =>
      exact absurd h_eq (Ioo_ne_Ioc (nonempty_Ioo_strictness hI) (nonempty_Ioc_strictness hJ))
    | Ico a₂ b₂ =>
      exact absurd h_eq (Ioo_ne_Ico (nonempty_Ioo_strictness hI) (nonempty_Ico_strictness hJ))
  | Icc a₁ b₁ =>
    cases J with
    | Ioo a₂ b₂ =>
      exact absurd h_eq.symm (Ioo_ne_Icc (nonempty_Ioo_strictness hJ) (nonempty_Icc_order hI))
    | Icc a₂ b₂ =>
      -- Icc a₁ b₁ = Icc a₂ b₂: извлекаем концы напрямую
      have ha₁b₁ := nonempty_Icc_order hI
      have ha₂b₂ := nonempty_Icc_order hJ
      obtain ⟨ha, hb⟩ := endpoints_of_Icc_eq h_eq ha₁b₁ ha₂b₂
      rw [ha, hb]
    | Ioc a₂ b₂ =>
      exact absurd h_eq (Icc_ne_Ioc (nonempty_Icc_order hI) (nonempty_Ioc_strictness hJ))
    | Ico a₂ b₂ =>
      exact absurd h_eq (Icc_ne_Ico (nonempty_Icc_order hI) (nonempty_Ico_strictness hJ))
  | Ioc a₁ b₁ =>
    cases J with
    | Ioo a₂ b₂ =>
      exact absurd h_eq.symm (Ioo_ne_Ioc (nonempty_Ioo_strictness hJ) (nonempty_Ioc_strictness hI))
    | Icc a₂ b₂ =>
      exact absurd h_eq.symm (Icc_ne_Ioc (nonempty_Icc_order hJ) (nonempty_Ioc_strictness hI))
    | Ioc a₂ b₂ =>
      -- Ioc a₁ b₁ = Ioc a₂ b₂: используем замыкание, как для Ioo
      have ha₁b₁ := nonempty_Ioc_strictness hI
      have ha₂b₂ := nonempty_Ioc_strictness hJ
      have h_set_eq : Set.Ioc a₁ b₁ = Set.Ioc a₂ b₂ := h_eq
      have h_closure : closure (Set.Ioc a₁ b₁) = closure (Set.Ioc a₂ b₂) := by rw [h_set_eq]
      rw [closure_Ioc ha₁b₁.ne, closure_Ioc ha₂b₂.ne] at h_closure
      obtain ⟨ha, hb⟩ := endpoints_of_Icc_eq h_closure ha₁b₁.le ha₂b₂.le
      rw [ha, hb]
    | Ico a₂ b₂ =>
      exact absurd h_eq (Ioc_ne_Ico (nonempty_Ioc_strictness hI) (nonempty_Ico_strictness hJ))
  | Ico a₁ b₁ =>
    cases J with
    | Ioo a₂ b₂ =>
      exact absurd h_eq.symm (Ioo_ne_Ico (nonempty_Ioo_strictness hJ) (nonempty_Ico_strictness hI))
    | Icc a₂ b₂ =>
      exact absurd h_eq.symm (Icc_ne_Ico (nonempty_Icc_order hJ) (nonempty_Ico_strictness hI))
    | Ioc a₂ b₂ =>
      exact absurd h_eq.symm (Ioc_ne_Ico (nonempty_Ioc_strictness hJ) (nonempty_Ico_strictness hI))
    | Ico a₂ b₂ =>
      -- Ico a₁ b₁ = Ico a₂ b₂: используем замыкание, как для Ioo
      have ha₁b₁ := nonempty_Ico_strictness hI
      have ha₂b₂ := nonempty_Ico_strictness hJ
      have h_set_eq : Set.Ico a₁ b₁ = Set.Ico a₂ b₂ := h_eq
      have h_closure : closure (Set.Ico a₁ b₁) = closure (Set.Ico a₂ b₂) := by rw [h_set_eq]
      rw [closure_Ico ha₁b₁.ne, closure_Ico ha₂b₂.ne] at h_closure
      obtain ⟨ha, hb⟩ := endpoints_of_Icc_eq h_closure ha₁b₁.le ha₂b₂.le
      rw [ha, hb]

end BoundedInterval

/-- Свидетель для lowerBound от upperBounds -/
def witness_lowerBound_upperBounds {X : Set ℝ} (y : ℝ) (hy : y ∈ X)
    : y ∈ lowerBounds (upperBounds X) := by
  intro u hu; simp [upperBounds] at hu; exact hu hy

/-- Свидетель для upperBound от lowerBounds -/
def witness_upperBound_lowerBounds {X : Set ℝ} (y : ℝ) (hy : y ∈ X)
    : y ∈ upperBounds (lowerBounds X) := by
  intro u hu; simp [lowerBounds] at hu; exact hu hy

/- Если x < sSup X и X непусто, то существует z ∈ X с x < z -/
/- Нам не нужно предполагать, что X является BddAbove
-(если X не BddAbove, то мы получаем, что sSup X = 0 (мусорное значение), и результат всё равно верен -/
#check exists_lt_of_lt_csSup

/- Если sInf X < x и X непусто, то существует w ∈ X с w ≤ x -/
/- Нам не нужно предполагать, что X является BddBelow.
-(если X не BddBelow, то мы получаем, что sInf X = 0 (мусорное значение), и результат всё равно верен -/
#check exists_lt_of_csInf_lt

/-- Показывает x < b, когда b = sSup X и b ∉ X -/
theorem lt_sSup_of_ne_sSup {X : Set ℝ} {x b : ℝ} (_hBddAbove : BddAbove X) (_hb : b = sSup X)
    (hb_notin : b ∉ X) (hx : x ∈ X) (hx_le_b : x ≤ b) : x < b := by
  by_contra! h;  exact hb_notin (hx_le_b.antisymm h ▸ hx)

/-- Показывает a < x, когда a = sInf X и a ∉ X -/
theorem sInf_lt_of_ne_sInf {X : Set ℝ} {a x : ℝ} (_hBddBelow : BddBelow X) (_ha : a = sInf X)
    (ha_notin : a ∉ X) (hx : x ∈ X) (ha_le_x : a ≤ x) : a < x := by
  by_contra! h; exact ha_notin (h.antisymm ha_le_x ▸ hx)

/-- Использует упорядоченную связность, чтобы показать x ∈ X, когда x ∈ \[w, z\] и w, z ∈ X -/
theorem mem_of_mem_Icc_ordConnected {X : Set ℝ}
    (hOrdConn : ∀ ⦃x : ℝ⦄, x ∈ X → ∀ ⦃y : ℝ⦄, y ∈ X → Set.Icc x y ⊆ X)
    {x w z : ℝ} (hw : w ∈ X) (hz : z ∈ X) (hx : x ∈ Set.Icc w z) : x ∈ X :=
  hOrdConn hw hz hx

/-- Множество действительных чисел ограничено и упорядоченно связно тогда и только тогда,
    когда оно равно некоторому ограниченному интервалу. -/
theorem BoundedInterval.ordConnected_iff (X : Set ℝ) :
    Bornology.IsBounded X ∧ X.OrdConnected ↔ ∃ I : BoundedInterval, X = I := by
  constructor
  · -- Нетривиальное направление: если X ограничено и упорядоченно связно,
    -- то X = I для некоторого BoundedInterval I
    -- Стратегия:
    -- 1. Разобраться со случаем пустого множества: если X = ∅, используем Ioo 0 0
    --    (представление пустого интервала)
    -- 2. Для непустого X:
    --    a. Используем ограниченность, чтобы показать, что у X есть инфимум и супремум
    --       (ограниченные множества в ℝ ограничены сверху и снизу)
    --    b. Извлекаем концы: a = sInf X, b = sSup X
    --    c. Определяем тип интервала на основе принадлежности концов:
    --       - Если a ∈ X ∧ b ∈ X → используем Icc a b
    --       - Если a ∈ X ∧ b ∉ X → используем Ico a b
    --       - Если a ∉ X ∧ b ∈ X → используем Ioc a b
    --       - Если a ∉ X ∧ b ∉ X → используем Ioo a b
    --    d. Показываем, что X равно построенному интервалу:
    --       - X ⊆ interval: используем, что a = sInf X и b = sSup X
    --       - interval ⊆ X: используем упорядоченную связность
    --         (если x, y ∈ X, то [x, y] ⊆ X)
    intro ⟨hBounded, hOrdConn⟩
    by_cases hEmpty : X = ∅
    · -- Шаг 1: случай пустого множества
      use Ioo 0 0
      simp [set_Ioo]
      exact hEmpty
    · -- Шаг 2: случай непустого множества
      have hNonempty : X.Nonempty := Set.nonempty_iff_ne_empty.mpr hEmpty
      rw [Set.ordConnected_def] at hOrdConn
      -- Шаг 2a: получаем ограниченность сверху и снизу
      -- используем, что ограниченные множества в ℝ содержатся в некотором Icc,
      -- что сразу даёт границы
      rw [Chapter9.isBounded_def] at hBounded
      obtain ⟨M, hM_pos, hX_subset⟩ := hBounded
      have hBddBelow : BddBelow X := ⟨-M, fun x hx => (hX_subset hx).1⟩
      have hBddAbove : BddAbove X := ⟨M, fun x hx => (hX_subset hx).2⟩
      -- Шаг 2b: извлекаем концы
      set a := sInf X
      set b := sSup X
      -- Шаг 2c: определяем тип интервала на основе принадлежности концов
      by_cases ha : a ∈ X
      · by_cases hb : b ∈ X
        · -- Случай: a ∈ X ∧ b ∈ X → используем Icc a b
          use Icc a b; simp [set_Icc]; ext x; constructor
          · intro hx; simp [Set.mem_Icc]
            exact ⟨csInf_le hBddBelow hx, le_csSup hBddAbove hx⟩
          · intro hx; simp [Set.mem_Icc] at hx; exact (hOrdConn ha hb) hx
        · -- Случай: a ∈ X ∧ b ∉ X → используем Ico a b
          use Ico a b; simp [set_Ico]; ext x; constructor
          · intro hx; simp [Set.mem_Ico]
            exact ⟨csInf_le hBddBelow hx, lt_sSup_of_ne_sSup hBddAbove rfl hb hx (le_csSup hBddAbove hx)⟩
          · intro hx; simp [Set.mem_Ico] at hx
            have hb_eq : b = sSup X := rfl
            obtain ⟨z, hz, hxz⟩ := exists_lt_of_lt_csSup hNonempty
              (by rw [←hb_eq]; exact hx.2)
            exact mem_of_mem_Icc_ordConnected hOrdConn ha hz ⟨hx.1, le_of_lt hxz⟩
      · by_cases hb : b ∈ X
        · -- Случай: a ∉ X ∧ b ∈ X → используем Ioc a b
          use Ioc a b; simp [set_Ioc]; ext x; constructor
          · intro hx; simp [Set.mem_Ioc]
            exact ⟨sInf_lt_of_ne_sInf hBddBelow rfl ha hx (csInf_le hBddBelow hx), le_csSup hBddAbove hx⟩
          · intro hx; simp [Set.mem_Ioc] at hx
            by_cases hx_eq_b : x = b
            · rw [hx_eq_b]; exact hb
            · have ha_eq : a = sInf X := rfl
              obtain ⟨w, hw, hwx⟩ := exists_lt_of_csInf_lt  hNonempty
                (by rw [←ha_eq]; exact hx.1)
              exact mem_of_mem_Icc_ordConnected hOrdConn hw hb ⟨le_of_lt hwx, hx.2⟩
        · -- Случай: a ∉ X ∧ b ∉ X → используем Ioo a b
          use Ioo a b; simp [set_Ioo]; ext x; constructor
          · intro hx; simp [Set.mem_Ioo]
            exact ⟨sInf_lt_of_ne_sInf hBddBelow rfl ha hx (csInf_le hBddBelow hx),
              lt_sSup_of_ne_sSup hBddAbove rfl hb hx (le_csSup hBddAbove hx)⟩
          · intro hx; simp [Set.mem_Ioo] at hx
            have ha_eq : a = sInf X := rfl; have hb_eq : b = sSup X := rfl
            obtain ⟨z, hz, hxz⟩ := exists_lt_of_lt_csSup hNonempty
              (by rw [←hb_eq]; exact hx.2)
            obtain ⟨w, hw, hwx⟩ := exists_lt_of_csInf_lt hNonempty
              (by rw [←ha_eq]; exact hx.1)
            exact mem_of_mem_Icc_ordConnected hOrdConn hw hz ⟨le_of_lt hwx, le_of_lt hxz⟩
  · -- Тривиальное направление: если X = I для некоторого BoundedInterval I,
    -- то X ограничено и упорядоченно связно
    intro ⟨I, hX⟩
    have hX' : X = (I : Set ℝ) := hX
    constructor
    · -- Показываем, что X ограничено
      rw [hX']
      exact Bornology.IsBounded.of_boundedInterval I
    · -- Показываем, что X упорядоченно связно: разбором случаев по четырём типам интервалов,
      -- используя `Set.ordConnected_def` и доказывая, что для любых `x, y` в интервале
      -- и `z` в `[x, y]` имеем `z` в интервале
      rw [hX']
      rw [Set.ordConnected_def]
      intro x hx y hy z hz
      cases I with
      | Ioo a b =>
        simp [set_Ioo, Set.mem_Ioo] at hx hy hz; simp [Set.mem_Ioo]
        exact ⟨lt_of_lt_of_le hx.1 hz.1, lt_of_le_of_lt hz.2 hy.2⟩
      | Icc a b =>
        simp [set_Icc, Set.mem_Icc] at hx hy hz; simp [Set.mem_Icc]
        exact ⟨le_trans hx.1 hz.1, le_trans hz.2 hy.2⟩
      | Ioc a b =>
        simp [set_Ioc, Set.mem_Ioc] at hx hy hz; simp [Set.mem_Ioc]
        exact ⟨lt_of_lt_of_le hx.1 hz.1, le_trans hz.2 hy.2⟩
      | Ico a b =>
        simp [set_Ico, Set.mem_Ico] at hx hy hz; simp [Set.mem_Ico]
        exact ⟨le_trans hx.1 hz.1, lt_of_le_of_lt hz.2 hy.2⟩

/-- Пересечение двух ограниченных интервалов снова является ограниченным интервалом. -/
theorem BoundedInterval.inter (I J : BoundedInterval) : ∃ K : BoundedInterval, (I : Set ℝ) ∩ (J : Set ℝ) = (K : Set ℝ) := by
  -- Стратегия: используем теорему-характеризацию `BoundedInterval.ordConnected_iff`
  -- Шаг 1: показываем, что (I:Set ℝ) ∩ (J:Set ℝ) ограничено
  -- Шаг 2: показываем, что (I:Set ℝ) ∩ (J:Set ℝ) упорядоченно связно
  -- Шаг 3: применяем теорему-характеризацию
  have hBounded : Bornology.IsBounded ((I : Set ℝ) ∩ (J : Set ℝ)) := by
    -- Пересечение является подмножеством I, которое ограничено
    exact (Bornology.IsBounded.of_boundedInterval I).subset Set.inter_subset_left
  have hOrdConn : ((I : Set ℝ) ∩ (J : Set ℝ)).OrdConnected := by
    -- И I, и J упорядоченно связны (из ordConnected_iff)
    have hI_ordConn : (I : Set ℝ).OrdConnected := by
      exact (BoundedInterval.ordConnected_iff (I : Set ℝ)).mpr ⟨I, rfl⟩ |>.2
    have hJ_ordConn : (J : Set ℝ).OrdConnected := by
      exact (BoundedInterval.ordConnected_iff (J : Set ℝ)).mpr ⟨J, rfl⟩ |>.2
    -- Пересечение упорядоченно связных множеств упорядоченно связно
    exact Set.OrdConnected.inter hI_ordConn hJ_ordConn
  exact (BoundedInterval.ordConnected_iff ((I : Set ℝ) ∩ (J : Set ℝ))).mp ⟨hBounded, hOrdConn⟩

/-- Инстанс, включающий нотацию ∩ для {name}`BoundedInterval`. -/
noncomputable instance BoundedInterval.instInter : Inter BoundedInterval where
  inter I J := (inter I J).choose

/-- Пересечение {name}`BoundedInterval` равно теоретико-множественному пересечению. -/
@[simp]
theorem BoundedInterval.inter_eq (I J : BoundedInterval) : (I ∩ J : BoundedInterval) = (I : Set ℝ) ∩ (J : Set ℝ)  :=
  (inter I J).choose_spec.symm

/-- Инстанс, включающий нотацию ∈ для принадлежности {name}`BoundedInterval`. -/
instance BoundedInterval.instMembership : Membership ℝ BoundedInterval where
  mem I x := x ∈ (I : Set ℝ)

/-- Принадлежность {name}`BoundedInterval` эквивалентна принадлежности его базовому множеству. -/
@[simp]
theorem BoundedInterval.mem_iff (I : BoundedInterval) (x : ℝ) : 
  x ∈ I ↔ x ∈ (I : Set ℝ) := by rfl

/-- Инстанс, включающий нотацию ⊆ для {name}`BoundedInterval`. -/
instance BoundedInterval.instSubset : HasSubset BoundedInterval where
  Subset I J := ∀ x, x ∈ I → x ∈ J

/-- Отношение подмножества для {name}`BoundedInterval` эквивалентно отношению подмножества
    для их базовых множеств. -/
@[simp]
theorem BoundedInterval.subset_iff (I J : BoundedInterval) : 
  I ⊆ J ↔ (I : Set ℝ) ⊆ (J : Set ℝ) := by rfl

/-- Извлекает левый конец ограниченного интервала. -/
abbrev BoundedInterval.a (I : BoundedInterval) : ℝ := match I with
  | Ioo a _ => a
  | Icc a _ => a
  | Ioc a _ => a
  | Ico a _ => a

/-- Извлекает правый конец ограниченного интервала. -/
abbrev BoundedInterval.b (I : BoundedInterval) : ℝ := match I with
  | Ioo _ b => b
  | Icc _ b => b
  | Ioc _ b => b
  | Ico _ b => b

/-- Любой непустой {name}`BoundedInterval` удовлетворяет a ≤ b -/
lemma BoundedInterval.nonempty_implies_le (I : BoundedInterval) (h : I.toSet.Nonempty) : I.a ≤ I.b := by
  cases I with
  | Ioo a b => exact le_of_lt (nonempty_Ioo_strictness h)
  | Icc a b => exact nonempty_Icc_order h
  | Ioc a b => exact le_of_lt (nonempty_Ioc_strictness h)
  | Ico a b => exact le_of_lt (nonempty_Ico_strictness h)

/-- Любой ограниченный интервал содержится в замкнутом интервале с теми же концами. -/
theorem BoundedInterval.subset_Icc (I : BoundedInterval) : I ⊆ Icc I.a I.b := match I with
  | Ioo _ _ => by simp [subset_iff, Set.Ioo_subset_Icc_self]
  | Icc _ _ => by simp [subset_iff]
  | Ioc _ _ => by simp [subset_iff, Set.Ioc_subset_Icc_self]
  | Ico _ _ => by simp [subset_iff, Set.Ico_subset_Icc_self]

/-- Открытый интервал с теми же концами содержится в любом ограниченном интервале. -/
theorem BoundedInterval.Ioo_subset (I : BoundedInterval) : Ioo I.a I.b ⊆ I := match I with
  | Ioo _ _ => by simp [subset_iff]
  | Icc _ _ => by simp [subset_iff, Set.Ioo_subset_Icc_self]
  | Ioc _ _ => by simp [subset_iff, Set.Ioo_subset_Ioc_self]
  | Ico _ _ => by simp [subset_iff, Set.Ioo_subset_Ico_self]

/-- Definition 1.1.1 (боксы): длина интервала равна max(b - a, 0). -/
abbrev BoundedInterval.length (I : BoundedInterval) : ℝ := max (I.b - I.a) 0

/-- Длина всегда неотрицательна -/
lemma BoundedInterval.length_nonneg (I : BoundedInterval) : 0 ≤ I.length := le_max_right _ _

/-- Используем здесь нижний индекс ||ₗ, чтобы не переопределять || -/
macro:max atomic("|" noWs) a:term noWs "|ₗ" : term => `(BoundedInterval.length $a)

/-- d-мерный бокс — это декартово произведение d ограниченных интервалов. -/
@[ext]
structure Box (d : ℕ) where
  side : Fin d → BoundedInterval

/-- Приводит {name}`Box` к его базовому множеству в d-мерном евклидовом пространстве. -/
@[coe]
def Box.toSet {d : ℕ} (B : Box d) : Set (EuclideanSpace' d) :=
  {x | ∀ i, x i ∈ (B.side i : Set ℝ)}

@[simp]
theorem Box.mem_toSet {d : ℕ} {B : Box d} {x : EuclideanSpace' d} : 
    x ∈ B.toSet ↔ ∀ i, x i ∈ (B.side i : Set ℝ) := Iff.rfl

/-- Включает приведение типа из {lean}`Box d` в {lean}`Set (EuclideanSpace' d)`. -/
instance Box.inst_coeSet {d : ℕ} : Coe (Box d) (Set (EuclideanSpace' d)) where
  coe := toSet

/-- Поднимает одномерный интервал до одномерного бокса. -/
@[coe]
abbrev BoundedInterval.toBox (I : BoundedInterval) : Box 1 where
  side := fun _ ↦ I

/-- Включает приведение типа из {name}`BoundedInterval` в {lean}`Box 1`. -/
instance BoundedInterval.inst_coeBox : Coe (BoundedInterval) (Box 1) where
  coe := toBox

/-- Приведение к {lean}`Box 1` инъективно: равные боксы влекут равные интервалы. -/
@[simp]
theorem BoundedInterval.toBox_inj {I J : BoundedInterval} : (I : Box 1) = (J : Box 1) ↔ I = J := by
  refine' ⟨fun h => _, fun h => h ▸ rfl⟩
  have : (I : Box 1).side 0 = (J : Box 1).side 0 := by rw [h]
  exact this

/-- Множество одномерного бокса равно образу интервала при эквивалентности
    {lean}`Real ≃ EuclideanSpace' 1`. -/
@[simp]
theorem BoundedInterval.coe_of_box (I : BoundedInterval) : (I : Box 1).toSet = Real.equiv_EuclideanSpace' '' I.toSet := by
  ext x; simp only [Box.mem_toSet, Set.mem_image]; constructor
  . intro h; use x 0; refine ⟨h 0, ?_⟩
    apply PiLp.ext; intro ⟨ i, hi ⟩; have : i=0 := by omega
    subst this; rfl
  rintro ⟨ y, hy, rfl ⟩ i
  have : i = 0 := Fin.ext_iff.mpr (by omega)
  subst this; exact hy

/-- Definition 1.1.1 (боксы): объём бокса — это произведение длин его сторон. -/
abbrev Box.volume {d : ℕ} (B : Box d) : ℝ := ∏ i, |B.side i|ₗ

/-- Используем здесь нижний индекс ||ᵥ, чтобы не переопределять || -/
macro:max atomic("|" noWs) a:term noWs "|ᵥ" : term => `(Box.volume $a)

/-- Вспомогательная лемма: если бокс пуст, его объём равен нулю -/
lemma Box.volume_eq_zero_of_empty {d : ℕ} (B : Box d) (h : B.toSet = ∅) : |B|ᵥ = 0 := by
  -- Если B.toSet = ∅, то у бокса есть хотя бы один пустой сторонний интервал
  have : ∃ i, (B.side i).toSet = ∅ := by
    by_contra! h_all_nonempty
    have h_all_nonempty : ∀ i, (B.side i).toSet.Nonempty := h_all_nonempty
    choose x hx using h_all_nonempty
    have h_nonempty : B.toSet.Nonempty := ⟨.toLp 2 (fun i ↦ x i), by simp; exact fun i => hx i⟩
    rw [h] at h_nonempty
    exact Set.not_nonempty_empty h_nonempty
  obtain ⟨i, hi⟩ := this
  -- Показываем |B.side i|ₗ = 0, что влечёт |B|ᵥ = 0
  rw [Box.volume]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  -- Если (B.side i).toSet = ∅, то интервал вырожден (b ≤ a), а значит длина = 0
  have h_le : (B.side i).b ≤ (B.side i).a := by
    match B.side i, hi with
    | Ioo a b, hi => simp [BoundedInterval.set_Ioo] at hi; simp; exact le_of_not_gt (Set.Ioo_eq_empty_iff.1 hi)
    | Icc a b, hi => simp [BoundedInterval.set_Icc] at hi; simp; exact le_of_not_ge (Set.Icc_eq_empty_iff.1 hi)
    | Ioc a b, hi => simp [BoundedInterval.set_Ioc] at hi; simp; exact le_of_not_gt (Set.Ioc_eq_empty_iff.1 hi)
    | Ico a b, hi => simp [BoundedInterval.set_Ico] at hi; simp; exact le_of_not_gt (Set.Ico_eq_empty_iff.1 hi)
  simp [BoundedInterval.length, max_eq_right (sub_nonpos.2 h_le)]

/-- Бокс, все стороны которого вырождены \[x, x\], имеет объём 0 при d > 0 -/
lemma Box.volume_singleton {d : ℕ} (hd : 0 < d) (x : EuclideanSpace' d) :
    |⟨fun i => BoundedInterval.Icc (x i) (x i)⟩|ᵥ = 0 := by
  unfold Box.volume BoundedInterval.length
  -- Все стороны имеют длину 0
  have h_sides : ∀ i : Fin d, max ((x i) - (x i)) 0 = 0 := by
    intro i
    simp [sub_self]
  -- Произведение содержит хотя бы один 0 (по индексу 0), значит произведение равно 0
  let i₀ : Fin d := ⟨0, hd⟩
  calc ∏ i : Fin d, max ((x i) - (x i)) 0
      = ∏ i : Fin d, (0 : ℝ) := by simp only [h_sides]
    _ = 0 := Finset.prod_eq_zero (Finset.mem_univ i₀) rfl

/-- У непустого бокса непустые стороны по каждому измерению -/
lemma Box.side_nonempty_of_nonempty {d : ℕ} (B : Box d) (hB : B.toSet.Nonempty) (i : Fin d) : 
    (B.side i).toSet.Nonempty := by
  obtain ⟨f, hf⟩ := hB
  simp at hf
  exact ⟨f i, hf i⟩

/-- Объём одномерного бокса равен длине его базового интервала. -/
@[simp]
theorem Box.volume_of_interval (I : BoundedInterval) : |(I : Box 1)|ᵥ = |I|ₗ := by
  simp [Box.volume]

/-- {name}`Box.toSet` инъективно на непустых боксах -/
lemma Box.toSet_injective_of_nonempty {d : ℕ} {B₁ B₂ : Box d}
    (h₁ : B₁.toSet.Nonempty) (h₂ : B₂.toSet.Nonempty) (h_eq : B₁.toSet = B₂.toSet) :
    B₁ = B₂ := by
  -- Используем экстенсиональность Box: боксы равны, если равны их стороны
  ext i
  -- Из B₁.toSet = B₂.toSet извлекаем, что B₁.side i = B₂.side i
  -- B.toSet = Set.univ.pi (fun i => (B.side i).toSet)
  -- Так что если pi-множества равны, каждое координатное множество тоже должно быть равно
  have h_side : (B₁.side i).toSet = (B₂.side i).toSet := by
    -- Используем экстенсиональность множеств: показываем x ∈ B₁.side i ↔ x ∈ B₂.side i для всех x
    ext x
    -- Получаем функцию-свидетель из гипотезы непустоты
    obtain ⟨f, hf⟩ := h₁
    simp at hf
    -- Строим тестовую функцию, которая равна x в координате i, и равна f в остальных
    let g : EuclideanSpace' d := .toLp 2 (fun j => if j = i then x else f j)
    -- Показываем: x ∈ B₁.side i ↔ x ∈ B₂.side i
    constructor
    · intro hx
      have hg₁ : g ∈ B₁.toSet := by
        simp [g]
        intro j
        by_cases h : j = i
        · simp [h, hx]
        · simp [h, hf j]
      rw [h_eq] at hg₁
      simp at hg₁
      have := hg₁ i
      simp [g] at this
      exact this
    · intro hx
      obtain ⟨f₂, hf₂⟩ := h₂
      simp at hf₂
      let g₂ : EuclideanSpace' d := .toLp 2 (fun j => if j = i then x else f₂ j)
      have hg₂ : g₂ ∈ B₂.toSet := by
        simp [g₂]
        intro j
        by_cases h : j = i
        · simp [h, hx]
        · simp [h, hf₂ j]
      rw [← h_eq] at hg₂
      simp at hg₂
      have := hg₂ i
      simp [g₂] at this
      exact this
  -- Теперь используем инъективность BoundedInterval
  have h_sides_nonempty : (B₁.side i).toSet.Nonempty ∧ (B₂.side i).toSet.Nonempty := by
    constructor
    · obtain ⟨f, hf⟩ := h₁
      simp at hf
      exact ⟨f i, hf i⟩
    · obtain ⟨f, hf⟩ := h₂
      simp at hf
      exact ⟨f i, hf i⟩
  exact BoundedInterval.toSet_injective_of_nonempty h_sides_nonempty.1 h_sides_nonempty.2 h_side

/-- Множество называется элементарным, если его можно представить в виде конечного
    объединения боксов. -/
abbrev IsElementary {d : ℕ} (E : Set (EuclideanSpace' d)) : Prop := ∃ S : Finset (Box d), E = ⋃ B ∈ S, ↑B

/-- Каждый бокс является элементарным множеством (свидетель — одноэлементный finset). -/
theorem IsElementary.box {d : ℕ} (B : Box d) : IsElementary B.toSet := by
  use {B}
  simp

/-- Exercise 1.1.1 (Boolean closure): The union of two elementary sets is elementary. -/
theorem IsElementary.union {d:ℕ} {E F: Set (EuclideanSpace' d)}
  (hE: IsElementary E) (hF: IsElementary F) : IsElementary (E ∪ F) := by
  classical
  obtain ⟨S, rfl⟩ := hE
  obtain ⟨T, rfl⟩ := hF
  exact ⟨S ∪ T, (Finset.set_biUnion_union S T _).symm⟩

/-- The empty set is elementary. -/
theorem IsElementary.empty (d:ℕ) : IsElementary (∅: Set (EuclideanSpace' d)) := by
  exact ⟨∅, by simp⟩

/-- The union of a finset of elementary sets is elementary. -/
lemma IsElementary.union' {d:ℕ} {S: Finset (Set (EuclideanSpace' d))}
(hE: ∀ E ∈ S, IsElementary E) : IsElementary (⋃ E ∈ S, E) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using IsElementary.empty d
  | insert a S' ha ih =>
    have hrest : IsElementary (⋃ E ∈ S', E) :=
      ih (fun E hE' ↦ hE E (Finset.mem_insert_of_mem hE'))
    have ha' : IsElementary a := hE a (Finset.mem_insert_self a S')
    simpa using ha'.union hrest

/-- The intersection of two boxes is a box: intersect the sides coordinatewise. -/
lemma Box.inter {d:ℕ} (B₁ B₂ : Box d) :
    ∃ B : Box d, B.toSet = B₁.toSet ∩ B₂.toSet := by
  refine ⟨⟨fun i ↦ B₁.side i ∩ B₂.side i⟩, ?_⟩
  ext x
  simp only [Box.mem_toSet, Set.mem_inter_iff]
  constructor
  · intro hx
    exact ⟨fun i ↦ ((BoundedInterval.inter_eq _ _ ▸ hx i : x i ∈ (B₁.side i:Set ℝ) ∩ _)).1,
           fun i ↦ ((BoundedInterval.inter_eq _ _ ▸ hx i : x i ∈ (B₁.side i:Set ℝ) ∩ _)).2⟩
  · intro ⟨h₁, h₂⟩ i
    have : x i ∈ (B₁.side i:Set ℝ) ∩ (B₂.side i:Set ℝ) := ⟨h₁ i, h₂ i⟩
    rwa [← BoundedInterval.inter_eq] at this

/-- Exercise 1.1.1 (Boolean closure): The intersection of two elementary sets is elementary. -/
theorem IsElementary.inter {d:ℕ} {E F: Set (EuclideanSpace' d)}
  (hE: IsElementary E) (hF: IsElementary F) : IsElementary (E ∩ F) := by
  classical
  obtain ⟨S, rfl⟩ := hE
  obtain ⟨T, rfl⟩ := hF
  choose f hf using fun p : Box d × Box d ↦ Box.inter p.1 p.2
  refine ⟨(S ×ˢ T).image f, ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iUnion, Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨⟨B, hB, hxB⟩, ⟨C, hC, hxC⟩⟩
    refine ⟨f (B, C), ⟨⟨(B, C), ⟨hB, hC⟩, rfl⟩, ?_⟩⟩
    rw [hf (B, C)]
    exact ⟨hxB, hxC⟩
  · rintro ⟨D, ⟨⟨⟨B, C⟩, ⟨hB, hC⟩, rfl⟩, hxD⟩⟩
    rw [hf (B, C)] at hxD
    exact ⟨⟨B, hB, hxD.1⟩, ⟨C, hC, hxD.2⟩⟩

/-- The bounded interval with the given endpoints, open or closed at each end as specified. -/
def BoundedInterval.mk' (a b : ℝ) (lclosed uclosed : Bool) : BoundedInterval :=
  match lclosed, uclosed with
  | true, true => Icc a b
  | true, false => Ico a b
  | false, true => Ioc a b
  | false, false => Ioo a b

/-- Whether a bounded interval contains its left endpoint. -/
def BoundedInterval.lclosed : BoundedInterval → Bool
  | Icc _ _ => true
  | Ico _ _ => true
  | Ioo _ _ => false
  | Ioc _ _ => false

/-- Whether a bounded interval contains its right endpoint. -/
def BoundedInterval.uclosed : BoundedInterval → Bool
  | Icc _ _ => true
  | Ioc _ _ => true
  | Ioo _ _ => false
  | Ico _ _ => false

@[simp]
theorem BoundedInterval.mk'_a (a b : ℝ) (lclosed uclosed : Bool) :
    (mk' a b lclosed uclosed).a = a := by cases lclosed <;> cases uclosed <;> rfl

@[simp]
theorem BoundedInterval.mk'_b (a b : ℝ) (lclosed uclosed : Bool) :
    (mk' a b lclosed uclosed).b = b := by cases lclosed <;> cases uclosed <;> rfl

@[simp]
theorem BoundedInterval.mk'_lclosed (a b : ℝ) (lclosed uclosed : Bool) :
    (mk' a b lclosed uclosed).lclosed = lclosed := by cases lclosed <;> cases uclosed <;> rfl

@[simp]
theorem BoundedInterval.mk'_uclosed (a b : ℝ) (lclosed uclosed : Bool) :
    (mk' a b lclosed uclosed).uclosed = uclosed := by cases lclosed <;> cases uclosed <;> rfl

theorem BoundedInterval.mem_iff' (I: BoundedInterval) (x:ℝ) :
    x ∈ (I:Set ℝ) ↔
      ((if I.lclosed then I.a ≤ x else I.a < x) ∧ (if I.uclosed then x ≤ I.b else x < I.b)) := by
  cases I <;> simp [toSet, lclosed, uclosed]

/-- The set difference of two bounded intervals is the union of two bounded intervals: the
part of the first below the second, and the part above it. -/
theorem BoundedInterval.sdiff (I J: BoundedInterval) :
    ∃ K₁ K₂ : BoundedInterval, (I:Set ℝ) \ (J:Set ℝ) = (K₁:Set ℝ) ∪ (K₂:Set ℝ) := by
  obtain ⟨K₁, hK₁⟩ := BoundedInterval.inter I (mk' I.a J.a I.lclosed (!J.lclosed))
  obtain ⟨K₂, hK₂⟩ := BoundedInterval.inter I (mk' J.b I.b (!J.uclosed) I.uclosed)
  refine ⟨K₁, K₂, ?_⟩
  rw [← hK₁, ← hK₂]
  ext x
  simp only [Set.mem_diff, Set.mem_union, Set.mem_inter_iff, mem_iff', mk'_a, mk'_b,
    mk'_lclosed, mk'_uclosed]
  cases hIl : I.lclosed <;> cases hIu : I.uclosed <;> cases hJl : J.lclosed <;> cases hJu : J.uclosed <;>
    simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, reduceIte] <;>
    push_neg <;>
    constructor <;>
    intro h <;>
    grind

/-- The difference of two boxes is elementary: a point of the difference leaves the second box
in some coordinate, and in that coordinate the difference of the two sides is a union of two
intervals. -/
theorem Box.sdiff {d:ℕ} (B C: Box d) : IsElementary (B.toSet \ C.toSet) := by
  classical
  choose K₁ K₂ hK using fun i ↦ BoundedInterval.sdiff (B.side i) (C.side i)
  -- the box obtained from `B` by shrinking side `i` to one of the two pieces
  let piece : Fin d → Bool → Box d := fun i k ↦
    ⟨fun j ↦ if j = i then (if k then K₁ i else K₂ i) else B.side j⟩
  have hpiece_side (i : Fin d) (k : Bool) :
      (piece i k).side i = (if k then K₁ i else K₂ i) := by simp [piece]
  have hsub (i : Fin d) (k : Bool) :
      ((if k then K₁ i else K₂ i : BoundedInterval) : Set ℝ) ⊆
        (B.side i : Set ℝ) \ (C.side i : Set ℝ) := by
    rw [hK i]
    cases k <;> simp
  refine ⟨Finset.univ.image (fun p : Fin d × Bool ↦ piece p.1 p.2), ?_⟩
  ext x
  simp only [Set.mem_diff, Box.mem_toSet, Set.mem_iUnion, Finset.mem_image, Finset.mem_univ,
    true_and, exists_prop]
  constructor
  · rintro ⟨hxB, hxC⟩
    obtain ⟨i, hi⟩ : ∃ i, x i ∉ (C.side i : Set ℝ) := by
      by_contra hc
      push_neg at hc
      exact hxC (fun i ↦ hc i)
    have : x i ∈ ((K₁ i : Set ℝ)) ∪ ((K₂ i : Set ℝ)) := by
      rw [← hK i]; exact ⟨hxB i, hi⟩
    rcases this with h | h
    · refine ⟨piece i true, ⟨⟨(i, true), rfl⟩, ?_⟩⟩
      intro j
      by_cases hj : j = i
      · subst hj; simpa [piece] using h
      · simpa [piece, hj] using hxB j
    · refine ⟨piece i false, ⟨⟨(i, false), rfl⟩, ?_⟩⟩
      intro j
      by_cases hj : j = i
      · subst hj; simpa [piece] using h
      · simpa [piece, hj] using hxB j
  · rintro ⟨P, ⟨⟨⟨i, k⟩, rfl⟩, hxP⟩⟩
    have hxi : x i ∈ (B.side i : Set ℝ) \ (C.side i : Set ℝ) := by
      have := hxP i
      rw [hpiece_side] at this
      exact hsub i k this
    refine ⟨fun j ↦ ?_, ?_⟩
    · by_cases hj : j = i
      · subst hj; exact hxi.1
      · simpa [piece, hj] using hxP j
    · intro hxC
      exact hxi.2 (hxC i)

/-- Exercise 1.1.1 (Boolean closure): The set difference of two elementary sets is elementary. -/
theorem IsElementary.sdiff {d:ℕ} {E F: Set (EuclideanSpace' d)}
  (hE: IsElementary E) (hF: IsElementary F) : IsElementary (E \ F) := by
  classical
  obtain ⟨T, rfl⟩ := hF
  induction T using Finset.induction_on with
  | empty => simpa using hE
  | insert C T' hC ih =>
    have hrw : E \ (⋃ B ∈ insert C T', (B:Set (EuclideanSpace' d)))
        = (E \ ⋃ B ∈ T', (B:Set (EuclideanSpace' d))) \ C.toSet := by
      rw [Finset.set_biUnion_insert, Set.diff_diff, Set.union_comm]
    rw [hrw]
    obtain ⟨S, hS⟩ := ih
    rw [hS]
    have hdiff : (⋃ B ∈ S, (B:Set (EuclideanSpace' d))) \ C.toSet
        = ⋃ B ∈ S, ((B:Set (EuclideanSpace' d)) \ C.toSet) := by
      ext y; simp only [Set.mem_diff, Set.mem_iUnion, exists_prop]; tauto
    rw [hdiff]
    have : (⋃ B ∈ S, ((B:Set (EuclideanSpace' d)) \ C.toSet))
        = ⋃ X ∈ S.image (fun B : Box d ↦ (B:Set (EuclideanSpace' d)) \ C.toSet), X := by
      ext y
      simp only [Set.mem_iUnion, Finset.mem_image, exists_prop]
      constructor
      · rintro ⟨B, hB, hy⟩; exact ⟨_, ⟨B, hB, rfl⟩, hy⟩
      · rintro ⟨X, ⟨B, hB, rfl⟩, hy⟩; exact ⟨B, hB, hy⟩
    rw [this]
    refine IsElementary.union' ?_
    intro X hX
    simp only [Finset.mem_image] at hX
    obtain ⟨B, -, rfl⟩ := hX
    exact Box.sdiff B C

/-- Exercise 1.1.1 (Boolean closure): The symmetric difference of two elementary sets is elementary. -/
theorem IsElementary.symmDiff {d:ℕ} {E F: Set (EuclideanSpace' d)}
  (hE: IsElementary E) (hF: IsElementary F) : IsElementary (symmDiff E F) := by
  have := (hE.sdiff hF).union (hF.sdiff hE)
  simpa [Set.symmDiff_def] using this

open Pointwise

/-- Translating a bounded interval gives a bounded interval with the same open/closed ends. -/
theorem BoundedInterval.translate (I: BoundedInterval) (c:ℝ) :
    ((mk' (I.a + c) (I.b + c) I.lclosed I.uclosed : BoundedInterval) : Set ℝ)
      = (I:Set ℝ) + {c} := by
  ext y
  simp only [mem_iff', mk'_a, mk'_b, mk'_lclosed, mk'_uclosed, Set.add_singleton,
    Set.mem_image]
  constructor
  · intro hy
    refine ⟨y - c, ?_, by ring⟩
    revert hy
    cases I.lclosed <;> cases I.uclosed <;> simp only [if_true, if_false,
      Bool.false_eq_true] <;> grind
  · rintro ⟨z, hz, rfl⟩
    revert hz
    cases I.lclosed <;> cases I.uclosed <;> simp only [if_true, if_false,
      Bool.false_eq_true] <;> grind

/-- Translating a box gives a box. -/
theorem Box.translate {d:ℕ} (B: Box d) (x: EuclideanSpace' d) :
    ∃ B' : Box d, (B':Set (EuclideanSpace' d)) = (B:Set (EuclideanSpace' d)) + {x} := by
  let I' : Fin d → BoundedInterval := fun i ↦
    BoundedInterval.mk' ((B.side i).a + x i) ((B.side i).b + x i)
      (B.side i).lclosed (B.side i).uclosed
  have hI' (i : Fin d) : (I' i : Set ℝ) = ((B.side i : Set ℝ)) + {x i} :=
    BoundedInterval.translate (B.side i) (x i)
  refine ⟨⟨I'⟩, ?_⟩
  ext y
  simp only [Box.mem_toSet]
  constructor
  · intro hy
    apply Set.mem_add.mpr
    refine ⟨.toLp 2 (fun i ↦ y i - x i), ?_, x, rfl, by apply PiLp.ext; intro i; simp⟩
    simp only [Box.mem_toSet]; intro i
    have : y i ∈ (I' i : Set ℝ) := hy i
    rw [hI' i] at this
    obtain ⟨a, ha, b, rfl, hab⟩ := this
    convert ha using 1; linarith
  · intro hy
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp hy
    rw [Set.mem_singleton_iff.mp hb] at hab
    simp only [Box.mem_toSet] at ha
    intro i
    rw [hI' i]
    exact Set.mem_add.mpr ⟨a i, ha i, x i, rfl,
      by have := congr_fun (congrArg WithLp.ofLp hab) i; simpa using this⟩

/-- Exercise 1.1.1 (Boolean closure): Translation of an elementary set is elementary. -/
theorem IsElementary.translate {d:ℕ} {E: Set (EuclideanSpace' d)}
  (hE: IsElementary E) (x: EuclideanSpace' d) : IsElementary (E + {x}) := by
  classical
  obtain ⟨S, rfl⟩ := hE
  choose f hf using fun B : Box d ↦ Box.translate B x
  refine ⟨S.image f, ?_⟩
  ext y
  simp only [Set.mem_iUnion, Finset.mem_image, exists_prop]
  constructor
  · intro hy
    obtain ⟨z, hz, w, hw, hzw⟩ := Set.mem_add.mp hy
    rw [Set.mem_singleton_iff.mp hw] at hzw
    obtain ⟨B, hB, hzB⟩ : ∃ B ∈ S, z ∈ (B:Set (EuclideanSpace' d)) := by simpa using hz
    refine ⟨f B, ⟨B, hB, rfl⟩, ?_⟩
    rw [hf B, ← hzw]
    exact Set.mem_add.mpr ⟨z, hzB, x, rfl, rfl⟩
  · rintro ⟨D, ⟨B, hB, rfl⟩, hyD⟩
    rw [hf B] at hyD
    obtain ⟨z, hzB, w, hw, hzw⟩ := Set.mem_add.mp hyD
    rw [Set.mem_singleton_iff.mp hw] at hzw
    exact Set.mem_add.mpr ⟨z, by simpa using Set.mem_biUnion hB hzB, x, rfl, hzw⟩

/-- Вспомогательная лемма для доказательства Lemma 1.1.2(i): любой finset интервалов допускает
общее измельчение (refinement) в попарно непересекающиеся подынтервалы. -/
theorem BoundedInterval.partition (S : Finset BoundedInterval) : ∃ T : Finset BoundedInterval, (T : Set _).PairwiseDisjoint BoundedInterval.toSet ∧ ∀ I ∈ S, ∃ U : Set T, I = ⋃ J ∈ U, J.val.toSet := by
  let endpoints : Finset ℝ := S.image BoundedInterval.a ∪ S.image BoundedInterval.b
  have ha_mem {I : BoundedInterval} (hI : I ∈ S) : I.a ∈ endpoints := by grind
  have hb_mem {I : BoundedInterval} (hI : I ∈ S) : I.b ∈ endpoints := by grind
  let k := endpoints.card
  let sorted : Fin k ≃o endpoints := endpoints.orderIsoOfFin (by rfl)
  let a : ℕ → ℝ := fun n ↦ if h : n < k then sorted ⟨n,h⟩ else 0  -- 0 — мусорное значение
  let T := Finset.univ.image (fun x : endpoints ↦ Icc x x)
    ∪ (Finset.range (k-1)).image (fun n ↦ Ioo (a n) (a (n+1)))
  refine' ⟨T,_,_⟩
  . rw [Set.pairwiseDisjoint_iff]
    intro I hI J hJ hIJ
    have := hIJ.some_mem
    simp_all [T]
    obtain ⟨ x, hx, rfl ⟩ | ⟨ n, hn, rfl ⟩ := hI
      <;> obtain ⟨ y, hy, rfl ⟩ | ⟨ m, hm, rfl ⟩ := hJ
      <;> simp at this
    . rw [show x=y by grind]
    . rw [this.1] at this
      set n := sorted.symm ⟨ x, hx ⟩
      have hax : x = sorted n := by simp [n]
      obtain ⟨ n, hn ⟩ := n
      simp [a, show m < k by omega, show m+1 < k by omega, hax] at this
      omega
    . rw [this.2] at this
      set m := sorted.symm ⟨ y, hy ⟩
      have hay : y = sorted m := by simp [m]
      obtain ⟨ m, hm ⟩ := m
      simp [a, show n < k by omega, show n+1 < k by omega, hay] at this
      omega
    have h1 : a n < a (m+1) := this.1.1.trans this.2.2
    have h2 : a m < a (n+1) := this.2.1.trans this.1.2
    simp [a, show n < k by omega, show n+1 < k by omega,
          show m < k by omega, show m+1 < k by omega] at h1 h2
    rw [show n=m by omega]
  intro I hI
  use {J | J.val ⊆ I }
  ext x; simp; constructor
  . intro hx
    by_cases hend : x ∈ endpoints
    . use Icc x x; simp [T, hx, hend]
    let n := sorted.symm ⟨ I.a, ha_mem hI ⟩
    let m := sorted.symm ⟨ I.b, hb_mem hI ⟩
    have hnI : I.a = sorted n := by simp [n]
    have hmI : I.b = sorted m := by simp [m]
    obtain ⟨ m, hm ⟩ := m; obtain ⟨ n, hn ⟩ := n
    apply I.subset_Icc at hx
    simp [hnI, hmI] at hx
    obtain ⟨ hx1, hx2 ⟩ := hx
    have H : ∃ m, x ≤ a m := by use m; grind
    let r := Nat.find H
    have hrm : r ≤ m := by convert Nat.find_min' H _; grind
    have hr : r < k := by linarith
    have hxr : x ≤ sorted ⟨ r, hr ⟩ := by convert Nat.find_spec H; grind
    have hnr : n < r := by
      by_contra!
      replace : (sorted ⟨r, hr⟩).val ≤ (sorted ⟨n, hn⟩).val := by
        simp only [Subtype.coe_le_coe]
        apply sorted.monotone; simpa
      simp [show x = sorted ⟨ n, hn ⟩ by order] at hend
    refine' ⟨ Ioo (sorted ⟨ r-1, by omega ⟩) (sorted ⟨ r, hr ⟩), _ , _, _ ⟩
    . apply Set.Subset.trans _ I.Ioo_subset
      simp [hnI, hmI]
      apply Set.Ioo_subset_Ioo <;> simp [Subtype.coe_le_coe] <;> omega
    . simp [T]; refine' ⟨ r-1, by omega, _ ⟩
      simp [a, show r-1 < k by omega, show r < k by omega, show r-1+1=r by omega]
    simp
    have h1 : x ≠ sorted ⟨ r, hr ⟩ := by by_contra!; simp [this] at hend
    have h3 : sorted ⟨ r-1, by omega ⟩ < x := by
      by_contra!
      convert Nat.find_min H (show r-1 < r by omega) _
      simp [a, show r-1 < k by omega, this]
    exact ⟨h3, by order⟩
  rintro ⟨a, ha_sub, _, ha_mem⟩; exact ha_sub ha_mem

/-- Lemma 1.1.2(i): любой finset боксов допускает общее измельчение в попарно непересекающиеся
подбоксы. -/
theorem Box.partition {d : ℕ} (S : Finset (Box d)) : ∃ T : Finset (Box d), (T : Set (Box d)).PairwiseDisjoint Box.toSet ∧ ∀ I ∈ S, ∃ U : Set T, I = ⋃ J ∈ U, J.val.toSet := by
  choose T hTdisj hT using BoundedInterval.partition
  let J : Fin d → Finset BoundedInterval := fun i ↦ T (S.image (fun B ↦ B.side i))
  have hJdisj (i : Fin d) : (J i : Set _).PairwiseDisjoint BoundedInterval.toSet :=
    hTdisj (S.image (fun B ↦ B.side i))
  have hJ (i : Fin d) {B : Box d} (hB : B ∈ S) : ∃ U : Set (J i), B.side i = ⋃ K ∈ U, K.val.toSet := by
    apply hT (S.image (fun B ↦ B.side i)) (B.side i); simp; use B
  classical
  refine' ⟨ (Finset.univ.pi J).image (fun I ↦ ⟨ fun i ↦ I i (by simp) ⟩ ) , _, _ ⟩
  . rw [Set.pairwiseDisjoint_iff]
    intro B₁ hB₁ B₂ hB₂ hB₁B₂; simp at hB₁ hB₂
    obtain ⟨ J₁, hJ₁, rfl ⟩ := hB₁
    obtain ⟨ J₂, hJ₂, rfl ⟩ := hB₂
    ext i; simp
    have := hB₁B₂.some_mem
    simp at this
    obtain ⟨ h₁, h₂ ⟩ := this
    specialize hJdisj i; rw [Set.pairwiseDisjoint_iff] at hJdisj
    apply_rules [hJdisj, Set.nonempty_of_mem (x := (hB₁B₂.some i))]
    grind
  intro B hB
  choose U hU using hJ
  use {B' | ∀ i, ∃ hi : B'.val.side i ∈ J i, ⟨ _, hi ⟩ ∈ U i hB}
  ext x; simp only [Box.mem_toSet, Set.mem_iUnion, Set.mem_setOf_eq, Subtype.exists]
  constructor
  . intro h
    have h' : ∀ i, x i ∈ ⋃ K ∈ U i hB, (K : BoundedInterval).toSet := by
      intro i; rw [← hU i hB]; exact h i
    simp only [Set.mem_iUnion] at h'
    choose I hI₁ hI₂ using h'
    refine' ⟨ ⟨ fun i ↦ (I i).1 ⟩, ?_, fun i ↦ ⟨(I i).2, hI₁ i⟩, fun i ↦ hI₂ i ⟩
    · exact Finset.mem_image.mpr ⟨fun i _ ↦ I i, Finset.mem_pi.mpr (fun i _ ↦ by simp), by ext i; simp⟩
  rintro ⟨ B', h1, h2, h3 ⟩ i
  rw [hU i hB]; simp only [Set.mem_iUnion]
  obtain ⟨hi, hU'⟩ := h2 i
  exact ⟨⟨B'.side i, hi⟩, hU', h3 i⟩

/-- Каждое элементарное множество можно разбить на попарно непересекающиеся боксы. -/
theorem IsElementary.partition {d : ℕ} {E : Set (EuclideanSpace' d)}
(hE : IsElementary E) : ∃ T : Finset (Box d), (T : Set (Box d)).PairwiseDisjoint Box.toSet ∧ E = ⋃ J ∈ T, J.toSet := by
  obtain ⟨ S, rfl ⟩ := hE
  have ⟨ T', hT', hST' ⟩ := Box.partition S
  choose U hU using hST'
  conv => rhs; ext T; rhs; lhs; rhs; ext B; rhs; ext h; rw [hU B h]
  classical
  use T'.filter (fun J ↦ ∃ B, ∃ h : B ∈ S, J ∈ Subtype.val '' (U B h))
  simp; split_ands
  . apply hT'.subset; intro _; simp; tauto
  ext; simp; grind

/-- Вспомогательная лемма для Lemma 1.1.2(ii): множество узлов решётки (кратных 1/N)
    в интервале конечно. -/
theorem BoundedInterval.sample_finite (I : BoundedInterval) {N : ℕ} (hN : N ≠ 0) : 
  Finite ↥(I.toSet ∩ (Set.range (fun n : ℤ ↦ (N : ℝ)⁻¹*n))) := by
  rw [Set.finite_coe_iff]
  apply Set.Finite.subset _ (Set.inter_subset_inter_left _ (BoundedInterval.subset_Icc I))
  suffices Set.Finite (Set.Icc I.a I.b ∩ Set.range (fun n : ℤ ↦ (N : ℝ)⁻¹*n)) by exact this
  have : Set.Icc I.a I.b ∩ Set.range (fun n : ℤ ↦ (N : ℝ)⁻¹*n) ⊆
         (fun n : ℤ ↦ (N : ℝ)⁻¹*n) '' (Finset.Icc ⌈(N : ℝ) * I.a⌉ ⌊(N : ℝ) * I.b⌋ : Set ℤ) := by
    intro x ⟨hx_in_Icc, n, hn⟩
    simp at hn; subst hn
    refine ⟨n, ?_, rfl⟩
    simp only [Finset.mem_coe]
    rw [Finset.mem_Icc]
    constructor
    · have : I.a ≤ (N : ℝ)⁻¹ * n := hx_in_Icc.1
      have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
      have : (N : ℝ) * I.a ≤ n := by
        calc (N : ℝ) * I.a ≤ (N : ℝ) * ((N : ℝ)⁻¹ * n) := by nlinarith
             _ = n := by field_simp
      exact Int.ceil_le.mpr this
    · have : (N : ℝ)⁻¹ * n ≤ I.b := hx_in_Icc.2
      have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
      have : n ≤ (N : ℝ) * I.b := by
        calc n = (N : ℝ) * ((N : ℝ)⁻¹ * n) := by field_simp
             _ ≤ (N : ℝ) * I.b := by nlinarith
      exact Int.le_floor.mpr this
  exact Set.Finite.subset ((Finset.finite_toSet _).image _) this

/-- Exercise для Lemma 1.1.2(ii): длина интервала равна пределу числа узлов решётки,
    масштабированного на 1/N. -/
theorem BoundedInterval.length_eq (I : BoundedInterval) : 
  Filter.atTop.Tendsto (fun N : ℕ ↦ (N : ℝ)⁻¹ * Nat.card ↥(I.toSet ∩ (Set.range (fun n : ℤ ↦ (N : ℝ)⁻¹*n))))
  (nhds |I|ₗ) := by
  sorry

/-- Узлы решётки в боксе раскладываются в произведение узлов решётки по каждой стороне-интервалу. -/
def Box.sample_congr {d : ℕ} (B : Box d) (N : ℕ) : 
↥(B.toSet ∩ (Set.range (fun (n : Fin d → ℤ) ↦ .toLp 2 (fun i ↦ (N : ℝ)⁻¹*(n i))))) ≃ ((i : Fin d) → ↑(↑(B.side i) ∩ Set.range fun n : ℤ ↦ (N : ℝ)⁻¹ * ↑n)) := {
    toFun x i := by
      obtain ⟨ x, hx ⟩ := x; refine ⟨ x i, ?_ ⟩
      simp at hx; obtain ⟨hx1, n, hn⟩ := hx
      exact ⟨hx1 i, ⟨n i, by rw [← hn]⟩⟩
    invFun x := by
      refine ⟨ .toLp 2 (fun i ↦ (x i).1), ?_ ⟩
      simp; constructor
      . intro i; exact (x i).2.1
      have h (i : Fin d) : ∃ y : ℤ, (N : ℝ)⁻¹ * y = (x i).1 := by
        obtain ⟨ w, hx ⟩ := (x i).2.2; exact ⟨w, by simpa using hx⟩
      choose y hy using h; use y; ext i; simp [hy i]
    left_inv x := by ext; simp
    right_inv x := by ext; simp
  }

/-- Вспомогательная лемма для Lemma 1.1.2(ii): множество узлов решётки в боксе конечно. -/
theorem Box.sample_finite {d : ℕ} (B : Box d) {N : ℕ} (hN : N ≠ 0) : 
  Finite ↥(B.toSet ∩ (Set.range (fun (n : Fin d → ℤ) ↦ .toLp 2 (fun i ↦ (N : ℝ)⁻¹*(n i))))) := by
    rw [Equiv.finite_iff (B.sample_congr N)]
    apply @Pi.finite _ _ _ (fun i ↦ (B.side i).sample_finite hN)

/-- Вспомогательная лемма для Lemma 1.1.2(ii): объём бокса равен пределу числа узлов решётки,
    масштабированного на N^(-d). -/
theorem Box.vol_eq {d : ℕ} (B : Box d) : 
  Filter.atTop.Tendsto (fun N : ℕ ↦ (N : ℝ)^(-d : ℝ) * Nat.card ↥(B.toSet ∩ (Set.range (fun (n : Fin d → ℤ) ↦ .toLp 2 (fun i ↦ (N : ℝ)⁻¹*(n i))))))
  (nhds |B|ᵥ) := by
  simp [Box.volume]
  have : ∀ i ∈ Finset.univ, Filter.atTop.Tendsto (fun N : ℕ ↦ (N : ℝ)⁻¹ * Nat.card ↥((B.side i).toSet ∩ Set.range ((fun n : ℤ ↦ (N : ℝ)⁻¹*n)))) (nhds |B.side i|ₗ) := fun i _ ↦ (B.side i).length_eq
  convert tendsto_finset_prod Finset.univ this with N
  simp [Finset.prod_mul_distrib]; left
  norm_cast; simp_rw [←Nat.card_coe_set_eq, ←Nat.card_pi]
  apply Nat.card_congr (B.sample_congr N)


/-- Lemma 1.1.2(ii), вспомогательная лемма: сумма объёмов равна пределу числа узлов решётки
    по непересекающемуся объединению. -/
theorem Box.sum_vol_eq {d : ℕ} {T : Finset (Box d)}
 (hT : (T : Set (Box d)).PairwiseDisjoint Box.toSet) : 
  Filter.atTop.Tendsto (fun N : ℕ ↦ (N : ℝ)^(-d : ℝ) * Nat.card ↥((⋃ B ∈ T, B.toSet) ∩ (Set.range (fun (n : Fin d → ℤ) ↦ .toLp 2 (fun i ↦ (N : ℝ)⁻¹*(n i))))))
  (nhds (∑ B ∈ T, |B|ᵥ)) := by
  apply (tendsto_finset_sum T (fun B _ ↦ B.vol_eq)).congr'
  rw [Filter.EventuallyEq, Filter.eventually_atTop]; use 1; intro N hN
  symm; convert Finset.mul_sum _ _ _
  convert Nat.cast_sum _ _
  rw [←Finset.sum_coe_sort, ←@Nat.card_sigma _ _ _ ?_]
  . exact Nat.card_congr {
      toFun x := by
        obtain ⟨ x, hx ⟩ := x
        simp at hx
        have hB := hx.1.choose_spec
        refine ⟨ ⟨ hx.1.choose, hB.1 ⟩, ⟨ x, ?_⟩ ⟩
        simp_all
      invFun x := by
        obtain ⟨ ⟨ B, hB ⟩, ⟨ x, hx ⟩ ⟩ := x
        refine ⟨ x, ?_ ⟩
        simp_all; aesop
      left_inv x := by grind
      right_inv x := by
        obtain ⟨ ⟨ B, hB ⟩, ⟨ x, hxB⟩ ⟩ := x
        simp at hxB
        have : ∃ B ∈ T, x ∈ B.toSet := by use B; tauto
        have h : this.choose = B := by
          have h := this.choose_spec
          apply hT.elim h.1 hB
          rw [Set.not_disjoint_iff]; grind
        subst h; rfl
    }
  intro ⟨ B, _ ⟩; convert B.sample_finite ?_
  omega

/-- Lemma 1.1.2(ii): два непересекающихся разбиения одного и того же множества имеют равные
    суммы объёмов. -/
theorem Box.measure_uniq {d : ℕ} {T₁ T₂ : Finset (Box d)}
 (hT₁ : (T₁ : Set (Box d)).PairwiseDisjoint Box.toSet)
 (hT₂ : (T₂ : Set (Box d)).PairwiseDisjoint Box.toSet)
 (heq : ⋃ B ∈ T₁, B.toSet = ⋃ B ∈ T₂, B.toSet) : 
 ∑ B ∈ T₁, |B|ᵥ = ∑ B ∈ T₂, |B|ᵥ := by
  apply tendsto_nhds_unique _ (Box.sum_vol_eq hT₂)
  rw [←heq]
  exact Box.sum_vol_eq hT₁

/-- Элементарная мера множества, определённая как сумма объёмов по непересекающемуся
    разбиению. -/
noncomputable abbrev IsElementary.measure {d : ℕ} {E : Set (EuclideanSpace' d)} (hE : IsElementary E) : ℝ
  := ∑ B ∈ hE.partition.choose, |B|ᵥ

/-- Мера равна сумме объёмов для любого непересекающегося разбиения множества на боксы. -/
theorem IsElementary.measure_eq {d : ℕ} {E : Set (EuclideanSpace' d)} (hE : IsElementary E)
  {T : Finset (Box d)} (hT : (T : Set (Box d)).PairwiseDisjoint Box.toSet)
  (heq : E = ⋃ B ∈ T, B.toSet) : 
  hE.measure = ∑ B ∈ T, |B|ᵥ := by
  apply Box.measure_uniq hE.partition.choose_spec.1 hT _
  rw [←heq, ←hE.partition.choose_spec.2]

/-- Exercise 1.1.2: приведите альтернативное доказательство этого утверждения, показав, что
два разбиения {lean}`T₁`, {lean}`T₂` допускают общее измельчение на боксы, возникающие как
декартовы произведения элементов из конечных наборов непересекающихся интервалов. -/
theorem Box.measure_uniq' {d : ℕ} {T₁ T₂ : Finset (Box d)}
 (hT₁ : (T₁ : Set (Box d)).PairwiseDisjoint Box.toSet)
 (hT₂ : (T₂ : Set (Box d)).PairwiseDisjoint Box.toSet)
 (heq : ⋃ B ∈ T₁, B.toSet = ⋃ B ∈ T₂, B.toSet) : 
 ∑ B ∈ T₁, |B|ᵥ = ∑ B ∈ T₂, |B|ᵥ := by
 sorry

/-- Пример: мера множества (1,2) ∪ \[3,6\] равна 1 + 3 = 4. -/
example : 
  let E : Set (EuclideanSpace' 1) := Real.equiv_EuclideanSpace' '' ((Set.Ioo 1 2) ∪ (Set.Icc 3 6))
  ∃ hE : IsElementary E, hE.measure = 4 := by
  extract_lets E
  classical
  let T : Finset (Box 1) := {(BoundedInterval.Ioo 1 2 : Box 1), (BoundedInterval.Icc 3 6 : Box 1)}
  have hET : E = ⋃ B ∈ T, B.toSet := by
    simp [E, T, Set.image_union]
  let hE : IsElementary E := ⟨ T, hET⟩
  use hE
  rw [hE.measure_eq _ hET]
  . rw [Finset.sum_pair]
    . norm_num
    by_contra!; simp [-Box.mk.injEq] at this
  rw [Set.pairwiseDisjoint_iff]
  simp [T]; split_ands <;> intro ⟨ x, hx ⟩ <;> grind

/-- Элементарная мера всегда неотрицательна. -/
lemma IsElementary.measure_nonneg {d : ℕ} {E : Set (EuclideanSpace' d)} (hE : IsElementary E) :
  0 ≤ hE.measure := by
  -- Стратегия:
  -- 1. Раскрываем меру: hE.measure = ∑ B ∈ partition, |B|ᵥ
  -- 2. Показываем каждое |B|ᵥ ≥ 0: объём — произведение длин, каждая длина = max(...) ≥ 0
  -- 3. Применяем Finset.sum_nonneg: сумма неотрицательных слагаемых неотрицательна
  -- Шаг 1: раскрываем определение меры
  rw [IsElementary.measure]
  -- Шаг 2: показываем каждое |B|ᵥ ≥ 0 для B из разбиения
  have hvol_nonneg : ∀ B ∈ hE.partition.choose, 0 ≤ |B|ᵥ := by
    intro B hB
    -- Объём — произведение длин
    rw [Box.volume]
    apply Finset.prod_nonneg
    intro i _
    -- Каждая длина = max(...) ≥ 0
    rw [BoundedInterval.length]
    exact le_max_right _ _
  -- Шаг 3: применяем Finset.sum_nonneg с фактом из шага 2
  exact Finset.sum_nonneg hvol_nonneg

/-- Мера аддитивна на непересекающихся элементарных множествах: μ(E ∪ F) = μ(E) + μ(F). -/
lemma IsElementary.measure_of_disjUnion {d : ℕ} {E F : Set (EuclideanSpace' d)}
(hE : IsElementary E) (hF : IsElementary F) (hdisj : Disjoint E F) :
  (hE.union hF).measure = hE.measure + hF.measure := by
  -- Стратегия:
  -- 1. Получаем разбиения: T_E = hE.partition.choose, T_F = hF.partition.choose
  -- 2. Показываем, что T_E ∪ T_F попарно не пересекается
  -- 3. Показываем E ∪ F = ⋃ B ∈ T_E ∪ T_F, B.toSet, используя свойства разбиения
  -- 4. Используем IsElementary.measure_eq, чтобы показать
  --    (hE.union hF).measure = ∑ B ∈ T_E ∪ T_F, |B|ᵥ
  -- 5. Используем Finset.sum_union, чтобы разделить сумму:
  --    ∑ B ∈ T_E ∪ T_F, |B|ᵥ = ∑ B ∈ T_E, |B|ᵥ + ∑ B ∈ T_F, |B|ᵥ
  -- 6. Применяем IsElementary.measure_eq, чтобы показать hE.measure = ∑ B ∈ T_E, |B|ᵥ
  --    и hF.measure = ∑ B ∈ T_F, |B|ᵥ
  classical -- для аксиомы выбора
  -- Шаг 1: получаем разбиения
  set T_E := hE.partition.choose
  set T_F := hF.partition.choose
  have hT_E_disj : (T_E : Set (Box d)).PairwiseDisjoint Box.toSet := hE.partition.choose_spec.1
  have hT_F_disj : (T_F : Set (Box d)).PairwiseDisjoint Box.toSet := hF.partition.choose_spec.1
  have hE_eq : E = ⋃ B ∈ T_E, B.toSet := hE.partition.choose_spec.2
  have hF_eq : F = ⋃ B ∈ T_F, B.toSet := hF.partition.choose_spec.2
  -- Шаг 2: показываем, что T_E ∪ T_F попарно не пересекается
  have hT_union_disj : ((T_E ∪ T_F : Finset (Box d)) : Set (Box d)).PairwiseDisjoint Box.toSet := by
    rw [Set.pairwiseDisjoint_iff]
    intro B₁ hB₁ B₂ hB₂ hB₁B₂
    simp at hB₁ hB₂
    -- Вспомогательный факт: боксы из разных разбиений не могут пересекаться (E и F не пересекаются)
    have h_cross_disj : ∀ B_E ∈ T_E, ∀ B_F ∈ T_F, (B_E.toSet ∩ B_F.toSet).Nonempty → False := by
      intro B_E hB_E B_F hB_F h_intersect
      obtain ⟨x, hx₁, hx₂⟩ := h_intersect
      have : x ∈ E ∩ F := by
        constructor
        · rw [hE_eq]
          exact Set.mem_biUnion hB_E hx₁
        · rw [hF_eq]
          exact Set.mem_biUnion hB_F hx₂
      rw [Set.disjoint_iff] at hdisj
      exact Set.notMem_empty x (hdisj this)
    -- Разбор случаев, каким разбиениям принадлежат боксы
    obtain (hB₁_E | hB₁_F) := hB₁ <;> obtain (hB₂_E | hB₂_F) := hB₂
    · -- Оба в T_E: используем hT_E_disj
      rw [Set.pairwiseDisjoint_iff] at hT_E_disj
      exact hT_E_disj hB₁_E hB₂_E hB₁B₂
    · -- B₁ в T_E, B₂ в T_F: противоречие через h_cross_disj
      exact False.elim (h_cross_disj B₁ hB₁_E B₂ hB₂_F hB₁B₂)
    · -- B₁ в T_F, B₂ в T_E: противоречие через h_cross_disj (симметричный случай)
      exact False.elim (h_cross_disj B₂ hB₂_E B₁ hB₁_F (Set.inter_comm B₁.toSet B₂.toSet ▸ hB₁B₂))
    · -- Оба в T_F: используем hT_F_disj
      rw [Set.pairwiseDisjoint_iff] at hT_F_disj
      exact hT_F_disj hB₁_F hB₂_F hB₁B₂
  -- Шаг 3: показываем E ∪ F = ⋃ B ∈ T_E ∪ T_F, B.toSet
  have h_union_eq : E ∪ F = ⋃ B ∈ T_E ∪ T_F, B.toSet := by
    rw [hE_eq, hF_eq]
    ext x
    simp [Set.mem_union, Finset.mem_union]
    constructor
    · rintro (⟨B, hB, hx⟩ | ⟨B, hB, hx⟩)
      · exact ⟨B, Or.inl hB, hx⟩
      · exact ⟨B, Or.inr hB, hx⟩
    · rintro ⟨B, hB | hB, hx⟩
      · left; exact ⟨B, hB, hx⟩
      · right; exact ⟨B, hB, hx⟩
  -- Шаг 4: используем IsElementary.measure_eq
  have h_union_measure : (hE.union hF).measure = ∑ B ∈ T_E ∪ T_F, |B|ᵥ :=
    (hE.union hF).measure_eq hT_union_disj h_union_eq
  -- Шаг 5: используем Finset.sum_union_inter, чтобы разделить сумму
  have h_sum_split : ∑ B ∈ T_E ∪ T_F, |B|ᵥ = ∑ B ∈ T_E, |B|ᵥ + ∑ B ∈ T_F, |B|ᵥ := by
    rw [←Finset.sum_union_inter]
    suffices ∑ B ∈ T_E ∩ T_F, |B|ᵥ = 0 by
      simp [this]
    apply Finset.sum_eq_zero
    intro B hB
    simp [Finset.mem_inter] at hB
    obtain ⟨hB_E, hB_F⟩ := hB
    -- B входит в оба разбиения, значит B.toSet ⊆ E ∩ F = ∅
    have hB_subset_empty : B.toSet ⊆ ∅ := by
      have hB_E_subset : B.toSet ⊆ E := by
        rw [hE_eq]
        intro x hx
        exact Set.mem_biUnion hB_E hx
      have hB_F_subset : B.toSet ⊆ F := by
        rw [hF_eq]
        intro x hx
        exact Set.mem_biUnion hB_F hx
      have : B.toSet ⊆ E ∩ F := Set.subset_inter hB_E_subset hB_F_subset
      exact this.trans (Set.disjoint_iff_inter_eq_empty.1 hdisj).subset
    -- Поскольку B.toSet ⊆ ∅, имеем B.toSet = ∅, значит объём равен 0
    have hB_empty : B.toSet = ∅ := Set.subset_empty_iff.1 hB_subset_empty
    exact Box.volume_eq_zero_of_empty B hB_empty
  -- Шаг 6: применяем IsElementary.measure_eq к отдельным мерам
  have hE_measure : hE.measure = ∑ B ∈ T_E, |B|ᵥ := hE.measure_eq hT_E_disj hE_eq
  have hF_measure : hF.measure = ∑ B ∈ T_F, |B|ᵥ := hF.measure_eq hT_F_disj hF_eq
  -- Собираем всё вместе
  rw [h_union_measure, h_sum_split, hE_measure, hF_measure]

-- Вспомогательные леммы для measure_of_disjUnion'

/-- Два разных доказательства элементарности множества дают одну и ту же меру. -/
lemma IsElementary.measure_irrelevant {d : ℕ} {E : Set (EuclideanSpace' d)}
    (h₁ h₂ : IsElementary E) : h₁.measure = h₂.measure := by
  classical
  -- Используем данные разбиения, упакованные внутри h₂
  obtain ⟨h_pair, h_union⟩ := h₂.partition.choose_spec
  -- Вычисляем обе меры через одно и то же разбиение
  have h₁_exp := h₁.measure_eq h_pair h_union
  have h₂_exp := h₂.measure_eq h_pair h_union
  simp [h₂_exp] at h₁_exp
  assumption

/-- Если два элементарных множества равны, то их меры равны. -/
lemma IsElementary.measure_eq_of_set_eq {d : ℕ} {E F : Set (EuclideanSpace' d)}
    (hE : IsElementary E) (hF : IsElementary F) (h : E = F) :
    hE.measure = hF.measure := by
  subst h  -- Теперь оба доказательства описывают одно и то же множество
  exact IsElementary.measure_irrelevant hE hF

/-- Объединение по пустому finset-у элементарных множеств есть пустое множество. -/
lemma IsElementary.union'_empty_eq {d : ℕ} : 
    (⋃ E ∈ (∅ : Finset (Set (EuclideanSpace' d))), E) = ∅ := by
  simp

open Classical in
/-- Мера суммы по {lean}`insert a S'` равна мере {lean}`a` плюс мера суммы по {lean}`S'`. -/
lemma IsElementary.sum_insert_split {d : ℕ} {a : Set (EuclideanSpace' d)} {S' : Finset (Set (EuclideanSpace' d))}
    (ha : a ∉ S')
    (hE : ∀ E ∈ insert a S', IsElementary E) : 
    ∑ E : (insert a S' : Finset (Set (EuclideanSpace' d))), (hE E.val E.property).measure =
    (hE a (Finset.mem_insert_self _ _)).measure +
    ∑ E : S', (hE E.val (Finset.mem_insert_of_mem E.property)).measure := by
  induction S' using Finset.induction_on with
  | empty =>
    -- Базовый случай: S' = ∅
    -- Левая часть: ∑ E:(insert a ∅), ... = сумма по {a}
    -- Правая часть: мера a + ∑ E:∅, ... = мера a + 0
    simp [Finset.sum_empty]
  | @insert b S'' hb_notin ih =>
    -- Индуктивный случай: S' = insert b S''
    -- Цель: ∑ E:(insert a (insert b S'')), ... = мера(a) + ∑ E:(insert b S''), ...
    -- Используем simp, чтобы раскрыть обе стороны
    simp [hb_notin]
    -- Теперь разделяем сумму в левой части через Finset.sum_insert
    -- Сначала выделяем a
    have ha_ne_b : a ≠ b := by simp_all
    have ha_notin_S'' : a ∉ S'' := by simp_all
    rw [Finset.sum_insert (by simp [ha_ne_b, ha_notin_S''])]
    -- Теперь выделяем b из оставшейся суммы
    rw [Finset.sum_insert (by simp [hb_notin])]
    -- Теперь обе стороны должны совпасть
    simp

/-- Мера аддитивна на попарно непересекающихся finset-ах элементарных множеств. -/
lemma IsElementary.measure_of_disjUnion' {d : ℕ} {S : Finset (Set (EuclideanSpace' d))}
(hE : ∀ E ∈ S, IsElementary E) (hdisj : (S : Set (Set (EuclideanSpace' d))).PairwiseDisjoint id) :
  (IsElementary.union' hE).measure = ∑ E : S, (hE E.val E.property).measure := by
  -- Стратегия: индукция по S. База: пустое множество даёт 0 = 0. Шаг: разделяем S = insert a S',
  -- показываем union = a ∪ (union S'), доказываем непересечение a с union S' через попарную
  -- непересекаемость, применяем аддитивность для двух множеств, используем предположение
  -- индукции для S', объединяем.
  classical
  -- Индукция по S через Finset.induction_on, чтобы свести к случаю двух множеств
  induction S using Finset.induction_on with
  | empty =>
    -- Базовый случай: S = ∅, обе стороны равны 0
    have h_set_eq := IsElementary.union'_empty_eq (d := d)
    have h_measure_eq : (IsElementary.union' hE).measure = (IsElementary.empty d).measure :=
      IsElementary.measure_eq_of_set_eq (IsElementary.union' hE) (IsElementary.empty d) h_set_eq
    rw [h_measure_eq]
    -- Показываем (IsElementary.empty d).measure = 0
    have h_empty_measure : (IsElementary.empty d).measure = 0 := by
      have h_empty_eq : (∅ : Set (EuclideanSpace' d)) = ⋃ B ∈ (∅ : Finset (Box d)), B.toSet := by simp
      have h_empty_disj : ((∅ : Finset (Box d)) : Set (Box d)).PairwiseDisjoint Box.toSet := by simp
      rw [(IsElementary.empty d).measure_eq h_empty_disj h_empty_eq]
      simp [Finset.sum_empty]
    rw [h_empty_measure]
    simp [Finset.sum_empty]
  | @insert a S' ha_notin ih =>
    -- Извлекаем гипотезы для S' и элемента a
    have hE_S' : ∀ E ∈ S', IsElementary E := by
      intro E hE_mem
      exact hE E (Finset.mem_insert_of_mem hE_mem)
    have hdisj_S' : Set.PairwiseDisjoint (S' : Set (Set (EuclideanSpace' d))) id := by
      intro E₁ hE₁ E₂ hE₂ hne
      apply hdisj
      · simp [hE₁]
      · simp [hE₂]
      · exact hne
    have hE_a : IsElementary a := hE a (Finset.mem_insert_self _ _)

    -- Показываем, что объединение по insert a S' равно a ∪ (объединение по S')
    have h_union_split : ⋃ E ∈ insert a S', E = a ∪ (⋃ E ∈ S', E) := by
      ext x
      simp [Set.mem_iUnion, Set.mem_union, Finset.mem_insert]

    -- Доказываем, что a не пересекается с объединением по S'
    have h_disj : Disjoint a (⋃ E ∈ S', E) := by
      rw [Set.disjoint_iff]
      intro x ⟨hx_a, hx_rest⟩
      simp [Set.mem_iUnion] at hx_rest
      obtain ⟨E, hE_mem, hx_E⟩ := hx_rest
      -- Используем hdisj, чтобы показать, что a и E не пересекаются
      have h_disj_a_E : Disjoint a E := by
        have ha_mem : a ∈ ((insert a S' : Finset _) : Set _) := by simp
        have hE_mem' : E ∈ ((insert a S' : Finset _) : Set _) := by simp [hE_mem]
        have hne : a ≠ E := by
          intro h; subst h
          exact ha_notin hE_mem
        -- hdisj: (insert a S').toSet.PairwiseDisjoint id означает, что различные множества
        -- не пересекаются
        -- Переписываем, чтобы извлечь свойство непересечения
        rw [Set.pairwiseDisjoint_iff] at hdisj
        -- После переписывания hdisj говорит: для различных i, j в множестве
        -- (id i ∩ id j).Nonempty → i = j
        -- У нас x ∈ a и x ∈ E, значит (id a ∩ id E).Nonempty, что дало бы a = E
        -- Но у нас также hne : a ≠ E, значит это противоречие
        have h_inter_nonempty : (id a ∩ id E).Nonempty := by
          simp [id]
          exact ⟨x, hx_a, hx_E⟩
        have h_eq := hdisj ha_mem hE_mem' h_inter_nonempty
        -- h_eq говорит a = E, но у нас hne : a ≠ E — противоречие
        exact (hne h_eq).elim
      rw [Set.disjoint_iff] at h_disj_a_E
      exact h_disj_a_E ⟨hx_a, hx_E⟩

    -- Применяем лемму об аддитивности для двух множеств
    let hE_rest : IsElementary (⋃ E ∈ S', E) := IsElementary.union' hE_S'
    have h_two_set : (hE_a.union hE_rest).measure = hE_a.measure + hE_rest.measure :=
      IsElementary.measure_of_disjUnion hE_a hE_rest h_disj

    -- Приравниваем меру свидетеля объединения к мере объединения двух множеств
    have h_measure_eq : (IsElementary.union' hE).measure = (hE_a.union hE_rest).measure :=
      IsElementary.measure_eq_of_set_eq (IsElementary.union' hE) (hE_a.union hE_rest) h_union_split

    -- Разделяем сумму на меру a плюс сумму по S'
    have h_sum_split := IsElementary.sum_insert_split ha_notin hE
    -- Применяем предположение индукции к объединению по S', согласовывая различия доказательств
    have h_ih_applied : hE_rest.measure = ∑ E : S', (hE_S' E.val E.property).measure := ih hE_S' hdisj_S'
    -- hE_S' определена как hE_S' E hE_mem = hE E (Finset.mem_insert_of_mem hE_mem),
    -- поэтому суммы определительно равны, и мы можем напрямую использовать h_ih_applied
    have h_ih_adjusted : hE_rest.measure = ∑ E : S', (hE E.val (Finset.mem_insert_of_mem E.property)).measure :=
      h_ih_applied

    -- Собираем все равенства вместе, чтобы завершить
    rw [h_measure_eq, h_two_set, h_sum_split]
    congr 1

/-- Пустое множество имеет нулевую меру. -/
@[simp]
lemma IsElementary.measure_of_empty (d : ℕ) : (IsElementary.empty d).measure = 0 := by
  -- Стратегия: используем пустое разбиение T = ∅, применяем measure_eq,
  -- упрощаем через Finset.sum_empty
  classical
  have h_empty_eq : (∅ : Set (EuclideanSpace' d)) = ⋃ B ∈ (∅ : Finset (Box d)), B.toSet := by
    simp
  have h_empty_disj : ((∅ : Finset (Box d)) : Set (Box d)).PairwiseDisjoint Box.toSet := by
    simp
  rw [(IsElementary.empty d).measure_eq h_empty_disj h_empty_eq]
  simp [Finset.sum_empty]

/-- Мера одного бокса равна его объёму. -/
@[simp]
lemma IsElementary.measure_of_box {d : ℕ} (B : Box d) : (IsElementary.box B).measure = |B|ᵥ := by
  -- Стратегия: используем одноэлементное разбиение T = {B}, применяем measure_eq,
  -- упрощаем через Finset.sum_singleton
  classical
  have h_box_eq : B.toSet = ⋃ B' ∈ ({B} : Finset (Box d)), B'.toSet := by
    simp
  have h_box_disj : (({B} : Finset (Box d)) : Set (Box d)).PairwiseDisjoint Box.toSet := by
    rw [Set.pairwiseDisjoint_iff]
    intro B₁ hB₁ B₂ hB₂ hB₁B₂
    simp at hB₁ hB₂
    -- Для одноэлементного разбиения B₁ = B₂ = B, поэтому условие выполняется тривиально
    rw [hB₁, hB₂]
  rw [(IsElementary.box B).measure_eq h_box_disj h_box_eq]
  simp [Finset.sum_singleton]

/-- Элементарная мера монотонна: если E ⊆ F, то μ(E) ≤ μ(F). -/
lemma IsElementary.measure_mono  {d : ℕ} {E F : Set (EuclideanSpace' d)}
(hE : IsElementary E) (hF : IsElementary F) (hcont : E ⊆ F) :
  hE.measure ≤ hF.measure := by
  -- Стратегия через разность множеств:
  -- 1. Раскладываем F = E ∪ (F \ E) (не пересекаются, т.к. E ⊆ F)
  -- 2. Показываем, что F \ E элементарно через IsElementary.sdiff
  -- 3. Применяем measure_of_disjUnion: hF.measure = hE.measure + (F \ E).measure
  -- 4. Используем measure_nonneg: (F \ E).measure ≥ 0, значит hE.measure ≤ hF.measure
  -- Шаг 1: раскладываем F = E ∪ (F \ E)
  have hF_decomp : F = E ∪ (F \ E) := by
    ext x
    constructor
    · intro hx; by_cases hx_E : x ∈ E
      · left; exact hx_E
      · right; exact ⟨hx, hx_E⟩
    · intro h; obtain (hx_E | ⟨hx, _⟩) := h
      · exact hcont hx_E
      · exact hx
  -- Шаг 2: показываем, что F \ E элементарно и не пересекается с E
  have hF_sdiff_E : IsElementary (F \ E) := IsElementary.sdiff hF hE
  have h_disj : Disjoint E (F \ E) := by
    rw [Set.disjoint_iff]; intro x ⟨hx_E, _, hx_not_E⟩; exact hx_not_E hx_E
  -- Шаг 3: применяем measure_of_disjUnion
  have h_union_measure : (hE.union hF_sdiff_E).measure = hE.measure + hF_sdiff_E.measure :=
    IsElementary.measure_of_disjUnion hE hF_sdiff_E h_disj
  -- Шаг 4: показываем, что (hE.union hF_sdiff_E) и hF представляют одно и то же множество F
  classical
  set T_F := hF.partition.choose
  have hT_F_disj : (T_F : Set (Box d)).PairwiseDisjoint Box.toSet := hF.partition.choose_spec.1
  have hF_eq : F = ⋃ B ∈ T_F, B.toSet := hF.partition.choose_spec.2
  have h_union_eq_partition : E ∪ (F \ E) = ⋃ B ∈ T_F, B.toSet := by rw [← hF_decomp, hF_eq]
  -- Шаг 5: используем measure_eq, чтобы показать (hE.union hF_sdiff_E).measure = hF.measure
  have h_union_measure_eq : (hE.union hF_sdiff_E).measure = hF.measure := by
    rw [(hE.union hF_sdiff_E).measure_eq hT_F_disj h_union_eq_partition, hF.measure_eq hT_F_disj hF_eq]
  -- Шаг 6: объединяем с measure_nonneg
  rw [← h_union_measure_eq, h_union_measure]
  linarith [IsElementary.measure_nonneg hF_sdiff_E]

/-- Субаддитивность меры на объединениях: μ(E ∪ F) ≤ μ(E) + μ(F). -/
lemma IsElementary.measure_of_union {d : ℕ} {E F : Set (EuclideanSpace' d)}
(hE : IsElementary E) (hF : IsElementary F) :
  (hE.union hF).measure ≤ hE.measure + hF.measure := by
  -- Стратегия (используя Exercise 1.1.1):
  -- 1. Раскладываем E ∪ F = E ∪ (F \ E) (непересекающееся объединение)
  -- 2. Используем IsElementary.sdiff (Exercise 1.1.1), чтобы показать, что F \ E элементарно
  -- 3. Применяем measure_of_disjUnion:
  --    (hE.union hF_sdiff_E).measure = hE.measure + (F \ E).measure
  -- 4. Показываем, что (hE.union hF) и (hE.union hF_sdiff_E) представляют одно и то же
  --    множество E ∪ F
  -- 5. Применяем measure_mono: (F \ E).measure ≤ hF.measure, так как F \ E ⊆ F
  -- 6. Объединяем: (hE.union hF).measure = hE.measure + (F \ E).measure ≤ hE.measure + hF.measure
  -- Шаг 1: раскладываем E ∪ F = E ∪ (F \ E)
  have h_union_decomp : E ∪ F = E ∪ (F \ E) := by
    ext x
    constructor
    · rintro (hx_E | hx_F); exact Or.inl hx_E
      by_cases hx_E : x ∈ E; exact Or.inl hx_E; exact Or.inr ⟨hx_F, hx_E⟩
    · rintro (hx_E | ⟨hx_F, _⟩); exact Or.inl hx_E; exact Or.inr hx_F
  -- Шаг 2-3: используем IsElementary.sdiff и применяем measure_of_disjUnion
  have hF_sdiff_E : IsElementary (F \ E) := IsElementary.sdiff hF hE
  have h_disj : Disjoint E (F \ E) := by
    rw [Set.disjoint_iff]; intro x ⟨hx_E, _, hx_not_E⟩; exact hx_not_E hx_E
  have h_union_measure : (hE.union hF_sdiff_E).measure = hE.measure + hF_sdiff_E.measure :=
    IsElementary.measure_of_disjUnion hE hF_sdiff_E h_disj
  -- Шаг 4: показываем, что оба объединения представляют одно и то же множество E ∪ F
  classical
  set T := (hE.union hF).partition.choose
  have hT_disj : (T : Set (Box d)).PairwiseDisjoint Box.toSet := (hE.union hF).partition.choose_spec.1
  have h_eq : E ∪ F = ⋃ B ∈ T, B.toSet := (hE.union hF).partition.choose_spec.2
  have h_union_measure_eq : (hE.union hF_sdiff_E).measure = (hE.union hF).measure := by
    rw [(hE.union hF_sdiff_E).measure_eq hT_disj (by rw [← h_union_decomp, h_eq]),
        (hE.union hF).measure_eq hT_disj h_eq]
  -- Шаг 5-6: применяем measure_mono и объединяем
  have h_mono : hF_sdiff_E.measure ≤ hF.measure :=
    IsElementary.measure_mono hF_sdiff_E hF (fun _ hx => hx.1)
  rw [← h_union_measure_eq, h_union_measure]
  linarith


/-- Субаддитивность меры на объединениях finset-ов: μ(⋃ S) ≤ ∑ μ(E) для E ∈ S. -/
lemma IsElementary.measure_of_union' {d : ℕ} {S : Finset (Set (EuclideanSpace' d))}
(hE : ∀ E ∈ S, IsElementary E) :
  (IsElementary.union' hE).measure ≤ ∑ E : S, (hE E.val E.property).measure := by
  -- Стратегия: индукция по S, зеркально к measure_of_disjUnion', но с неравенством
  classical
  induction S using Finset.induction_on with
  | empty =>
    -- Базовый случай: S = ∅, обе стороны равны 0
    have h_set_eq := IsElementary.union'_empty_eq (d := d)
    have h_measure_eq : (IsElementary.union' hE).measure = (IsElementary.empty d).measure :=
      IsElementary.measure_eq_of_set_eq (IsElementary.union' hE) (IsElementary.empty d) h_set_eq
    simp [IsElementary.measure_of_empty]
  | @insert a S' ha_notin ih =>
    -- Извлекаем гипотезы для S' и элемента a
    have hE_S' : ∀ E ∈ S', IsElementary E := fun E hE_mem => hE E (Finset.mem_insert_of_mem hE_mem)
    have hE_a : IsElementary a := hE a (Finset.mem_insert_self _ _)
    -- Показываем, что объединение по insert a S' равно a ∪ (объединение по S')
    have h_union_split : ⋃ E ∈ insert a S', E = a ∪ (⋃ E ∈ S', E) := by
      ext x; simp [Set.mem_iUnion, Set.mem_union, Finset.mem_insert]
    -- Применяем лемму о субаддитивности для двух множеств
    let hE_rest : IsElementary (⋃ E ∈ S', E) := IsElementary.union' hE_S'
    have h_two_set : (hE_a.union hE_rest).measure ≤ hE_a.measure + hE_rest.measure :=
      IsElementary.measure_of_union hE_a hE_rest
    -- Приравниваем меру свидетеля объединения к мере объединения двух множеств
    have h_measure_eq : (IsElementary.union' hE).measure = (hE_a.union hE_rest).measure :=
      IsElementary.measure_eq_of_set_eq (IsElementary.union' hE) (hE_a.union hE_rest) h_union_split
    -- Разделяем сумму на меру a плюс сумму по S'
    have h_sum_split := IsElementary.sum_insert_split ha_notin hE
    -- Применяем предположение индукции
    have h_ih : hE_rest.measure ≤ ∑ E : S', (hE_S' E.val E.property).measure := ih hE_S'
    have h_ih_adjusted : hE_rest.measure ≤ ∑ E : S', (hE E.val (Finset.mem_insert_of_mem E.property)).measure :=
      h_ih
    -- Объединяем: (union' hE).measure = (hE_a.union hE_rest).measure ≤ hE_a.measure + hE_rest.measure
    --             ≤ hE_a.measure + ∑ E:S', ... = ∑ E:(insert a S'), ...
    rw [h_measure_eq, h_sum_split]
    linarith [h_two_set, h_ih_adjusted]

/-- Вспомогательный факт: сдвиг сохраняет длину интервала -/
lemma BoundedInterval.length_of_translate (I : BoundedInterval) (c : ℝ) : 
  ∃ I' : BoundedInterval, I'.toSet = I.toSet + {c} ∧ |I'|ₗ = |I|ₗ := by
  cases I with
  | Ioo a b => use Ioo (a + c) (b + c); constructor <;> simp [toSet, BoundedInterval.length]
  | Icc a b => use Icc (a + c) (b + c); constructor <;> simp [toSet, BoundedInterval.length]
  | Ioc a b => use Ioc (a + c) (b + c); constructor <;> simp [toSet, BoundedInterval.length]
  | Ico a b => use Ico (a + c) (b + c); constructor <;> simp [toSet, BoundedInterval.length]

/-- Вспомогательный факт: сдвиг сохраняет объём бокса -/
lemma Box.volume_of_translate {d : ℕ} (B : Box d) (x : EuclideanSpace' d) :
  ∃ B' : Box d, B'.toSet = B.toSet + {x} ∧ |B'|ᵥ = |B|ᵥ := by
  -- Стратегия:
  -- 1. Для каждой координаты i сдвигаем B.side i на x i, используя length_of_translate
  -- 2. Строим B' со сдвинутыми интервалами: B'.side i = сдвинутый интервал
  -- 3. Показываем B'.toSet = B.toSet + {x}: y ∈ B'.toSet ↔ y - x ∈ B.toSet (покоординатно)
  -- 4. Показываем |B'|ᵥ = |B|ᵥ: произведение длин, каждая длина сохраняется при сдвиге
  -- Шаг 1: для каждой координаты i получаем сдвинутый интервал
  choose I' hI' using fun i ↦ BoundedInterval.length_of_translate (B.side i) (x i)
  -- Шаг 2: строим B' со сдвинутыми интервалами
  use ⟨fun i ↦ I' i⟩
  constructor
  -- Шаг 3: показываем B'.toSet = B.toSet + {x}
  · ext y
    simp only [Box.mem_toSet]
    constructor
    · intro hy
      apply Set.mem_add.mpr
      refine ⟨.toLp 2 (fun i ↦ y i - x i), ?_, x, rfl, by apply PiLp.ext; intro i; simp⟩
      simp only [Box.mem_toSet]; intro i
      have : y i ∈ (I' i).toSet := hy i
      rw [(hI' i).1] at this
      obtain ⟨a, ha, b, rfl, hab⟩ := this
      convert ha using 1; linarith
    · intro hy
      obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp hy
      rw [Set.mem_singleton_iff.mp hb] at hab
      simp only [Box.mem_toSet] at ha
      intro i
      rw [(hI' i).1]
      exact Set.mem_add.mpr ⟨a i, ha i, x i, rfl, by have := congr_fun (congrArg WithLp.ofLp hab) i; simpa using this⟩
  -- Шаг 4: показываем |B'|ᵥ = |B|ᵥ
  · simp [Box.volume]
    congr 1
    ext i
    exact (hI' i).2

/-- Сдвиг инъективен на множествах: если S₁ + \{x\} = S₂ + \{x\}, то S₁ = S₂ -/
lemma Set.translate_inj {d : ℕ} (x : EuclideanSpace' d) (S₁ S₂ : Set (EuclideanSpace' d))
  (h_eq : S₁ + {x} = S₂ + {x}) : S₁ = S₂ := by
  ext y
  constructor
  · intro hy
    have : y + x ∈ S₁ + {x} := Set.mem_add.mpr ⟨y, hy, x, Set.mem_singleton x, rfl⟩
    rw [h_eq] at this
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp this
    rw [Set.mem_singleton_iff.mp hb] at hab
    exact (add_right_cancel hab) ▸ ha
  · intro hy
    have : y + x ∈ S₂ + {x} := Set.mem_add.mpr ⟨y, hy, x, Set.mem_singleton x, rfl⟩
    rw [← h_eq] at this
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp this
    rw [Set.mem_singleton_iff.mp hb] at hab
    exact (add_right_cancel hab) ▸ ha

/-- Элементарная мера инвариантна относительно сдвига: μ(E + \{x\}) = μ(E). -/
lemma IsElementary.measure_of_translate {d : ℕ} {E : Set (EuclideanSpace' d)}
(hE : IsElementary E) (x : EuclideanSpace' d) :
  (hE.translate x).measure = hE.measure := by
  -- Стратегия:
  -- 0. Разбор случаев: E = ∅ или E ≠ ∅
  --    a. Пустой случай: E = ∅ → E + {x} = ∅, обе меры равны 0
  --    b. Непустой случай: E ≠ ∅, продолжаем со сдвигом разбиения
  -- 1. Получаем разбиение T множества E: E = ⋃ B ∈ T, B.toSet (из hE.partition)
  -- 2. Для каждого B ∈ T используем Box.volume_of_translate, чтобы получить B' с
  --    B'.toSet = B.toSet + {x} и |B'|ᵥ = |B|ᵥ
  -- 3. Строим T' = {B' | B ∈ T} (используя choose, чтобы получить сдвинутые боксы)
  -- 4. Показываем, что T' попарно не пересекается (сдвиг сохраняет непересечение)
  -- 5. Показываем E + {x} = ⋃ B' ∈ T', B'.toSet (сдвиг распределяется по объединению)
  -- 6. Применяем measure_eq:
  --    (hE.translate x).measure = ∑ B' ∈ T', |B'|ᵥ = ∑ B ∈ T, |B|ᵥ = hE.measure
  classical
  by_cases h_empty : E = ∅
  · -- Пустой случай: E = ∅ → E + {x} = ∅, обе меры равны 0
    subst h_empty
    simp [IsElementary.measure_of_empty]
  · -- Непустой случай: E ≠ ∅
    -- Шаг 1: получаем разбиение T множества E, затем фильтруем непустые боксы
    set T := hE.partition.choose
    have hT_disj : (T : Set (Box d)).PairwiseDisjoint Box.toSet := hE.partition.choose_spec.1
    have hE_eq : E = ⋃ B ∈ T, B.toSet := hE.partition.choose_spec.2
    -- Оставляем только непустые боксы (пустые боксы всё равно вносят 0 в меру)
    set T := T.filter (fun B => B.toSet.Nonempty) with hT_def
    have hT_disj : (T : Set (Box d)).PairwiseDisjoint Box.toSet := by
      intro B₁ hB₁ B₂ hB₂ hB₁B₂
      simp only [Finset.mem_coe] at hB₁ hB₂
      exact hE.partition.choose_spec.1 (Finset.mem_of_mem_filter B₁ hB₁) (Finset.mem_of_mem_filter B₂ hB₂) hB₁B₂
    have hE_eq : E = ⋃ B ∈ T, B.toSet := by
      rw [hE_eq]
      ext y; simp
      constructor
      · intro ⟨B, hB, hy⟩
        exact ⟨B, Finset.mem_filter.mpr ⟨hB, ⟨y, hy⟩⟩, hy⟩
      · intro ⟨B, hB, hy⟩
        exact ⟨B, Finset.mem_of_mem_filter B hB, hy⟩
    have hT_nonempty : ∀ B ∈ T, B.toSet.Nonempty := by
      intro B hB
      exact (Finset.mem_filter.mp hB).2
    -- Шаг 2-3: строим сдвинутое разбиение T'
    choose f hf using fun B : Box d => Box.volume_of_translate B x
    set T' := T.image f
    have hf_spec : ∀ B ∈ T, (f B).toSet = B.toSet + {x} ∧ |f B|ᵥ = |B|ᵥ := fun B hB => hf B
    -- Вспомогательный факт: f инъективна на T (все боксы в T непусты по построению)
    have hf_inj : ∀ B₁ B₂, B₁ ∈ T → B₂ ∈ T → f B₁ = f B₂ → B₁ = B₂ := by
      intro B₁ B₂ hB₁ hB₂ h_eq
      have h_set_eq' : B₁.toSet = B₂.toSet :=
        Set.translate_inj x _ _ ((hf_spec B₁ hB₁).1.symm.trans ((congr_arg Box.toSet h_eq).trans (hf_spec B₂ hB₂).1))
      -- Поскольку B₁ входит в отфильтрованное T, оно непусто, и B₁.toSet = B₂.toSet
      have h_inter_nonempty : (B₁.toSet ∩ B₂.toSet).Nonempty := by
        rw [h_set_eq', Set.inter_self]
        rw [← h_set_eq']
        exact hT_nonempty B₁ hB₁
      rw [Set.pairwiseDisjoint_iff] at hT_disj
      exact hT_disj hB₁ hB₂ h_inter_nonempty
    -- Шаг 4: показываем, что T' попарно не пересекается
    have hT'_disj : (T' : Set (Box d)).PairwiseDisjoint Box.toSet := by
      rw [Set.pairwiseDisjoint_iff]
      intro B₁' hB₁' B₂' hB₂' hB₁'B₂'
      simp [T'] at hB₁' hB₂'
      obtain ⟨B₁, hB₁, rfl⟩ := hB₁'
      obtain ⟨B₂, hB₂, rfl⟩ := hB₂'
      by_cases h_eq : f B₁ = f B₂
      · exact h_eq
      · -- Если f B₁ ≠ f B₂, но они пересекаются, то B₁ = B₂ (противоречие)
        have h_translate_inter : (f B₁).toSet ∩ (f B₂).toSet = (B₁.toSet ∩ B₂.toSet) + {x} := by
          rw [(hf_spec B₁ hB₁).1, (hf_spec B₂ hB₂).1]
          ext y; simp only [Set.mem_inter_iff, Set.mem_add]
          constructor
          · rintro ⟨⟨a₁, ha₁, b₁, hb₁, hab₁⟩, ⟨a₂, ha₂, b₂, hb₂, hab₂⟩⟩
            have hb₁_eq : b₁ = x := Set.mem_singleton_iff.mp hb₁
            have hb₂_eq : b₂ = x := Set.mem_singleton_iff.mp hb₂
            rw [hb₁_eq] at hab₁
            rw [hb₂_eq] at hab₂
            exact ⟨a₁, ⟨ha₁, add_right_cancel (hab₁.trans hab₂.symm) ▸ ha₂⟩, x, Set.mem_singleton x, hab₁⟩
          · rintro ⟨a, ⟨ha₁, ha₂⟩, b, hb, hab⟩
            rw [Set.mem_singleton_iff.mp hb] at hab
            exact ⟨⟨a, ha₁, x, Set.mem_singleton x, hab⟩, ⟨a, ha₂, x, Set.mem_singleton x, hab⟩⟩
        have h_B_nonempty : (B₁.toSet ∩ B₂.toSet).Nonempty := by
          rw [h_translate_inter] at hB₁'B₂'
          obtain ⟨y, hy⟩ := hB₁'B₂'
          obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp hy
          exact ⟨a, ha.1, ha.2⟩
        rw [Set.pairwiseDisjoint_iff] at hT_disj
        exact (h_eq (congr_arg f (hT_disj hB₁ hB₂ h_B_nonempty))).elim
    -- Шаг 5: показываем E + {x} = ⋃ B' ∈ T', B'.toSet
    have h_union_eq : E + {x} = ⋃ B' ∈ T', B'.toSet := by
      rw [hE_eq]
      ext y; constructor
      · intro hy
        rw [Set.mem_iUnion₂]
        obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp hy
        rw [Set.mem_iUnion₂] at ha
        obtain ⟨B, hB, haB⟩ := ha
        rw [Set.mem_singleton_iff.mp hb] at hab
        exact ⟨f B, Finset.mem_image.mpr ⟨B, hB, rfl⟩,
          by rw [(hf_spec B hB).1]; exact Set.mem_add.mpr ⟨a, haB, x, rfl, hab⟩⟩
      · intro hy
        rw [Set.mem_iUnion₂] at hy
        obtain ⟨B', hB', hyB'⟩ := hy
        obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hB'
        rw [(hf_spec B hB).1] at hyB'
        obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp hyB'
        rw [Set.mem_singleton_iff.mp hb] at hab
        exact Set.mem_add.mpr ⟨a, Set.mem_iUnion₂.mpr ⟨B, hB, ha⟩, x, rfl, hab⟩
    -- Шаг 6: применяем measure_eq и показываем равенство сумм
    have h_translate_measure : (hE.translate x).measure = ∑ B' ∈ T', |B'|ᵥ :=
      (hE.translate x).measure_eq hT'_disj h_union_eq
    have h_sum_eq : ∑ B' ∈ T', |B'|ᵥ = ∑ B ∈ T, |B|ᵥ := by
      rw [Finset.sum_image (fun B₁ hB₁ B₂ hB₂ h_eq => hf_inj B₁ B₂ hB₁ hB₂ h_eq)]
      exact Finset.sum_congr rfl fun B hB => (hf_spec B hB).2
    rw [h_translate_measure, h_sum_eq, hE.measure_eq hT_disj hE_eq]

/-- Exercise 1.1.3 (единственность элементарной меры): любая неотрицательная, аддитивная,
инвариантная относительно сдвига функция на элементарных множествах является скалярным кратным
стандартной элементарной меры. -/
theorem IsElementary.measure_uniq {d : ℕ} {m' : (E : Set (EuclideanSpace' d)) → (IsElementary E) → ℝ}
  (hnonneg : ∀ E : Set (EuclideanSpace' d), ∀ hE : IsElementary E, m' E hE ≥ 0)
  (hadd : ∀ E F : Set (EuclideanSpace' d), ∀ (hE : IsElementary E) (hF : IsElementary F),
   Disjoint E F → m' (E ∪ F) (hE.union hF) = m' E hE + m' F hF)
  (htrans : ∀ E : Set (EuclideanSpace' d), ∀ (hE : IsElementary E) (x : EuclideanSpace' d), m' (E + {x}) (hE.translate x) = m' E hE) : ∃ c, c ≥ 0 ∧ ∀ E : Set (EuclideanSpace' d), ∀ hE : IsElementary E, m' E hE = c * hE.measure := by
    sorry

/-- d-мерный единичный куб (0,1\]^d. -/
abbrev Box.unit_cube (d : ℕ) : Box d := { side := fun _ ↦ BoundedInterval.Ioc 0 1}

/-- Любая мера, удовлетворяющая нормировке m'(единичный куб) = 1, должна совпадать со стандартной
элементарной мерой. -/
theorem IsElementary.measure_uniq' {d : ℕ} {m' : (E : Set (EuclideanSpace' d)) → (IsElementary E) → ℝ}
  (hnonneg : ∀ E : Set (EuclideanSpace' d), ∀ hE : IsElementary E, m' E hE ≥ 0)
  (hadd : ∀ E F : Set (EuclideanSpace' d), ∀ (hE : IsElementary E) (hF : IsElementary F),
   Disjoint E F → m' (E ∪ F) (hE.union hF) = m' E hE + m' F hF)
  (htrans : ∀ E : Set (EuclideanSpace' d), ∀ (hE : IsElementary E) (x : EuclideanSpace' d), m' (E + {x}) (hE.translate x) = m' E hE)
  (hcube : m' (Box.unit_cube d) (IsElementary.box _) = 1) : 
  ∀ E : Set (EuclideanSpace' d), ∀ hE : IsElementary E, m' E hE = hE.measure := by
    sorry

/-- Декартово произведение двух боксов — это бокс в суммарной размерности. -/
abbrev Box.prod {d₁ d₂ : ℕ} (B₁ : Box d₁) (B₂ : Box d₂) : Box (d₁ + d₂) where
  side i := by
    obtain ⟨ i, hi ⟩ := i
    exact if h : i < d₁ then B₁.side ⟨i, h⟩ else (B₂.side ⟨i - d₁, by omega⟩)

/-- Exercise 1.1.4: декартово произведение двух элементарных множеств элементарно. -/
theorem IsElementary.prod {d₁ d₂ : ℕ} {E₁ : Set (EuclideanSpace' d₁)} {E₂ : Set (EuclideanSpace' d₂)}
  (hE₁ : IsElementary E₁) (hE₂ : IsElementary E₂) : IsElementary (EuclideanSpace'.prod E₁ E₂) := by sorry

/-- Мера мультипликативна на произведениях: μ(E₁ × E₂) = μ(E₁) \* μ(E₂). -/
theorem IsElementary.measure_of_prod {d₁ d₂ : ℕ} {E₁ : Set (EuclideanSpace' d₁)} {E₂ : Set (EuclideanSpace' d₂)}
  (hE₁ : IsElementary E₁) (hE₂ : IsElementary E₂)
  : (hE₁.prod hE₂).measure = hE₁.measure * hE₂.measure := by sorry
