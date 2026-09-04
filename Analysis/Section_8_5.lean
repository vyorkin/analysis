import Mathlib.Tactic
import Analysis.Section_8_4

set_option doc.verso.suggestions false

/-!
# Analysis I, раздел 8.5: Упорядоченные множества

Я старался сделать перевод максимально точным перефразированием оригинального текста. Когда
приходилось выбирать между более идиоматичным Lean-решением и более точным переводом, я, как
правило, выбирал второе. В частности, местами Lean-код можно было бы "заголфить", сделав его более
элегантным и идиоматичным, но я сознательно этого избегал.

Основные конструкции и результаты этого раздела:

- Обзор {name}`PartialOrder`, {name}`LinearOrder` и {name}`WellFoundedLT`, с некоторым API.
- Сильная индукция.
- Лемма Цорна.

-/

namespace Chapter8

/-- Определение 8.5.1 — здесь мы просто повторяем класс {name}`PartialOrder` из Mathlib. -/

example {X : Type} [PartialOrder X] (x : X) : x ≤ x := le_refl x
example {X : Type} [PartialOrder X] {x y : X} (h₁ : x ≤ y) (h₂ : y ≤ x) : x = y := antisymm h₁ h₂
example {X : Type} [PartialOrder X] {x y z : X} (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ z := le_trans h₁ h₂
example {X : Type} [PartialOrder X] (x y : X) : x < y ↔ x ≤ y ∧ x ≠ y := lt_iff_le_and_ne

@[implicit_reducible] def PartialOrder.mk {X : Type} [LE X]
  (hrefl : ∀ x : X, x ≤ x)
  (hantisymm : ∀ x y : X, x ≤ y → y ≤ x → x = y)
  (htrans : ∀ x y z : X, x ≤ y → y ≤ z → x ≤ z) : PartialOrder X :=
{
  le := (· ≤ ·)
  le_refl := hrefl
  le_antisymm := hantisymm
  le_trans := htrans
}

example {X : Type} : PartialOrder (Set X) := by infer_instance
example {X : Type} (A B : Set X) : A ≤ B ↔ A ⊆ B := by rfl

/-- Определение 8.5.3. Здесь мы просто повторяем класс {name}`LinearOrder` из Mathlib. -/
example {X : Type} [LinearOrder X] : PartialOrder X := by infer_instance
def IsTotal (X : Type) [PartialOrder X] : Prop := ∀ x y : X, x ≤ y ∨ y ≤ x
example {X : Type} [LinearOrder X] : IsTotal X := le_total

open Classical in
@[implicit_reducible] noncomputable def LinearOrder.mk {X : Type} [PartialOrder X]
  (htotal : IsTotal X) : LinearOrder X :=
{
   le_total := htotal
   toDecidableLE := decRel LE.le
}

/- Примеры 8.5.4 -/
#check (inferInstance : LinearOrder ℕ)
#check (inferInstance : LinearOrder ℚ)
#check (inferInstance : LinearOrder ℝ)
#check (inferInstance : LinearOrder EReal)


@[implicit_reducible] noncomputable def LinearOrder.subtype {X : Type} [LinearOrder X] (A : Set X) : LinearOrder A :=
LinearOrder.mk (by
  sorry
  )

/-- Тотальность порядка на `X` наследуется любым подмножеством `A`. -/
theorem IsTotal.subtype {X : Type} [PartialOrder X] {A : Set X} (hA : IsTotal X) : IsTotal A := by
  intro ⟨ x, hx ⟩ ⟨ y, hy ⟩
  specialize hA x y; simp_all

/-- Тотальность порядка на `A` передаётся любому подмножеству `B ⊆ A`. -/
theorem IsTotal.subset {X : Type} [PartialOrder X] {A B : Set X} (hA : IsTotal A) (hAB : B ⊆ A) : IsTotal B := by
  intro ⟨ x, hx ⟩ ⟨ y, hy ⟩
  specialize hA ⟨ x, hAB hx ⟩ ⟨ y, hAB hy ⟩; simp_all

abbrev X_8_5_4 : Set (Set ℕ) := { {1,2}, {2}, {2,3}, {2,3,4}, {5} }
example : ¬ IsTotal X_8_5_4 := by sorry

/-- Определение 8.5.5 (максимальные и минимальные элементы). Здесь мы используем {name}`IsMax` и {name}`IsMin` из Mathlib. -/
theorem IsMax.iff {X : Type} [PartialOrder X] (x : X) : 
  IsMax x ↔ ¬ ∃ y, x < y := by rw [isMax_iff_forall_not_lt]; grind

/-- `x` минимален тогда и только тогда, когда не существует элемента, строго меньшего `x`. -/
theorem IsMin.iff {X : Type} [PartialOrder X] (x : X) : 
  IsMin x ↔ ¬ ∃ y, x > y := by rw [isMin_iff_forall_not_lt]; grind

/-- Примеры 8.5.6 -/
example : IsMin (⟨ {2}, by aesop ⟩ : X_8_5_4) := by sorry
example : IsMax (⟨ {1,2}, by aesop ⟩ : X_8_5_4) := by sorry
example : IsMax (⟨ {2,3,4}, by aesop ⟩ : X_8_5_4) := by sorry
example : IsMin (⟨ {5}, by aesop ⟩ : X_8_5_4) ∧ IsMax (⟨ {5}, by aesop ⟩ : X_8_5_4) := by sorry
example : ¬ IsMin (⟨ {2,3}, by aesop ⟩ : X_8_5_4) ∧ ¬ IsMax (⟨ {2,3}, by aesop ⟩ : X_8_5_4) := by sorry

/-- Пример 8.5.7 -/
example : IsMin (0 : ℕ) := by sorry
example (n : ℕ) : ¬ IsMax n := by sorry
example (n : ℤ) : ¬ IsMin n ∧ ¬ IsMax n := by sorry

/-- Определение 8.5.8. Мы используем `[LinearOrder X] [WellFoundedLT X]` для описания вполне упорядоченных множеств. -/
theorem WellFoundedLT.iff (X : Type) [LinearOrder X] : 
  WellFoundedLT X ↔ ∀ A : Set X, A.Nonempty → ∃ x : A, IsMin x := by
  unfold WellFoundedLT IsMin
  rw [isWellFounded_iff, WellFounded.wellFounded_iff_has_min]
  peel with A hA; constructor
  . intro ⟨ x, hxA, h ⟩; use ⟨ x, hxA ⟩; intro ⟨ y, hy ⟩ this; specialize h y hy
    simp at *; order
  intro ⟨ ⟨ x, hx ⟩, h ⟩; refine ⟨ _, hx, ?_ ⟩; intro y hy; specialize h (b := ⟨ _, hy ⟩)
  simp at h; contrapose! h; simp [h]; order

-- тот же результат, что и `WellFoundedLT.iff`, но для `PartialOrder X` со свидетельством тотальности `h` вместо инстанса `LinearOrder X`
theorem WellFoundedLT.iff' {X : Type} [PartialOrder X] (h : IsTotal X) : 
  WellFoundedLT X ↔ ∀ A : Set X, A.Nonempty → ∃ x : A, IsMin x := @iff X (LinearOrder.mk h)

/-- Пример 8.5.9 -/
example : WellFoundedLT ℕ := by
  rw [WellFoundedLT.iff]
  intro A hA; use ⟨ _, (Nat.min_spec hA).1 ⟩
  simp [IsMin]; grind [Nat.min_spec]

/-- Упражнение 8.1.2 -/
example : ¬ WellFoundedLT ℤ := by sorry
example : ¬ WellFoundedLT ℚ := by sorry
example : ¬ WellFoundedLT ℝ := by sorry

/-- Упражнение 8.5.8 (i) -/
theorem IsMax.ofFinite {X : Type} [LinearOrder X] [Finite X] [Nonempty X] : ∃ x : X, IsMax x := by sorry

/-- Упражнение 8.5.8 (ii) -/
theorem IsMin.ofFinite {X : Type} [LinearOrder X] [Finite X] [Nonempty X] : ∃ x : X, IsMin x := by sorry

/-- Упражнение 8.5.8 (iii) -/
theorem WellFoundedLT.ofFinite {X : Type} [LinearOrder X] [Finite X] : WellFoundedLT X := by sorry

example {X : Type} [LinearOrder X] [WellFoundedLT X] (A : Set X) : WellFoundedLT A := by sorry

/-- Фундированность порядка на `A` наследуется любым подмножеством `B ⊆ A`. -/
theorem WellFoundedLT.subset {X : Type} [PartialOrder X] {A B : Set X} (hA : IsTotal A) [hwell : WellFoundedLT A] (hAB : B ⊆ A) : WellFoundedLT B := by
  set hAlin : LinearOrder A := LinearOrder.mk hA
  set hBlin : LinearOrder B := LinearOrder.mk (hA.subset hAB)
  rw [iff' hA] at hwell; rw [iff' (hA.subset hAB)]; intro C hC
  have ⟨ ⟨ ⟨ x, hx ⟩, hx' ⟩, hmin ⟩ := hwell ((B.embeddingOfSubset _ hAB) '' C) (by aesop)
  simp at hx'; choose y hy hyC this using hx'; use ⟨ _, hyC ⟩
  simp_all [IsMin, Set.embeddingOfSubset]
  intro a ha_B ha_C
  apply hmin _ (hAB ha_B) <;> trivial

/-- Утверждение 8.5.10 / Упражнение 8.5.10 -/
theorem WellFoundedLT.strong_induction {X : Type} [LinearOrder X] [WellFoundedLT X] {P : X → Prop}
  (h : ∀ n, (∀ m < n, P m) → P n) : ∀ n, P n := by
  sorry

/-- Определение 8.5.12 (верхние и строгие верхние границы) -/
abbrev IsUpperBound {X : Type} [PartialOrder X] (A : Set X) (x : X) : Prop :=
  ∀ y ∈ A, y ≤ x

/-- Связь с {name}`upperBounds` из Mathlib -/
theorem IsUpperBound.iff {X : Type} [PartialOrder X] (A : Set X) (x : X) : 
  IsUpperBound A x ↔ x ∈ upperBounds A := by simp [IsUpperBound, upperBounds]

abbrev IsStrictUpperBound {X : Type} [PartialOrder X] (A : Set X) (x : X) : Prop :=
  IsUpperBound A x ∧ x ∉ A

-- `x` — строгая верхняя граница `A` тогда и только тогда, когда `x` строго больше каждого элемента `A`
theorem IsStrictUpperBound.iff {X : Type} [PartialOrder X] (A : Set X) (x : X) : 
  IsStrictUpperBound A x ↔ ∀ y ∈ A, y < x := by sorry

-- тот же результат, что и `IsStrictUpperBound.iff`, но выражен через `upperBounds A \ A` из Mathlib
theorem IsStrictUpperBound.iff' {X : Type} [PartialOrder X] (A : Set X) (x : X) : 
  IsStrictUpperBound A x ↔ x ∈ upperBounds A \ A := by
  simp [IsStrictUpperBound, IsUpperBound.iff]

example : IsUpperBound (.Icc 1 2 : Set ℝ) 2 := by sorry

example : ¬ IsStrictUpperBound (.Icc 1 2 : Set ℝ) 2 := by sorry

example : IsStrictUpperBound (.Icc 1 2 : Set ℝ) 3 := by sorry

/-- Удобный способ упростить понятие того, что {name}`x₀` является минимальным элементом. -/
theorem IsMin.iff_lowerbound {X : Type} [PartialOrder X] {Y : Set X} (hY : IsTotal Y) (x₀ : X) : (∃ hx₀ : x₀ ∈ Y, IsMin (⟨ x₀, hx₀ ⟩ : Y)) ↔ x₀ ∈ Y ∧ ∀ x ∈ Y, x₀ ≤ x := by
  constructor
  . rintro ⟨ hx₀, hmin ⟩; simp [IsMin, hx₀] at *
    peel hmin with x hx _; specialize hY ⟨ _, hx ⟩ ⟨ _, hx₀ ⟩; aesop
  intro h; use h.1; simp [IsMin]; aesop

-- тот же результат, что и `IsMin.iff_lowerbound`, но `x₀` квантифицируется экзистенциально по обе стороны эквивалентности
theorem IsMin.iff_lowerbound' {X : Type} [PartialOrder X] {Y : Set X} (hY : IsTotal Y) : (∃ x₀ : Y, IsMin x₀) ↔ ∃ x₀, x₀ ∈ Y ∧ ∀ x ∈ Y, x₀ ≤ x := by
  constructor
  . intro ⟨ ⟨ x₀, hx₀ ⟩, hmin ⟩
    have : ∃ (hx₀ : x₀ ∈ Y), IsMin (⟨ _, hx₀ ⟩ : Y) := by use hx₀
    rw [iff_lowerbound hY x₀] at this; use x₀
  intro ⟨ x₀, hx₀, hmin ⟩; choose hx₀ _ using (iff_lowerbound hY x₀).mpr ⟨ hx₀, hmin ⟩; use ⟨ _, hx₀ ⟩

/-- Упражнение 8.5.11 -/
example {X : Type} [PartialOrder X] {Y Y' : Set X} (hY : IsTotal Y) (hY' : IsTotal Y') (hY_well : WellFoundedLT Y) (hY'_well : WellFoundedLT Y') (hYY' : IsTotal (Y ∪ Y' : Set X)) : WellFoundedLT (Y ∪ Y' : Set X) := by sorry

/-- Лемма 8.5.14 -/
theorem WellFoundedLT.partialOrder {X : Type} [PartialOrder X] (x₀ : X) : ∃ Y : Set X, IsTotal Y ∧ WellFoundedLT Y ∧ (∃ hx₀ : x₀ ∈ Y, IsMin (⟨ x₀, hx₀ ⟩ : Y)) ∧ ¬ ∃ x, IsStrictUpperBound Y x := by
  -- Это доказательство основано на оригинальном тексте с некоторыми техническими упрощениями.

  -- Класс вполне упорядоченных подмножеств `Y` множества `X`, содержащих `x₀` как минимальный элемент,
  -- не имеет имени в тексте, но для формализации удобно дать ему имя (`Ω₀`). Здесь мы используем
  -- `IsMin.iff_lowerbound`, чтобы упростить понятие минимальности.
  let Ω₀ := { Y : Set X | IsTotal Y ∧ WellFoundedLT Y ∧ x₀ ∈ Y ∧ ∀ x ∈ Y, x₀ ≤ x}
  suffices : ∃ Y ∈ Ω₀, ¬ ∃ x, IsStrictUpperBound Y x
  . have ⟨ Y, ⟨ hY, hY'⟩, hstrict ⟩ := this; use Y, hY
    rw [IsMin.iff_lowerbound hY x₀]; tauto
  by_contra! hs
  let s : Ω₀ → X := fun Y ↦ (hs Y Y.property).choose
  replace hs (Y : Ω₀) : IsStrictUpperBound Y (s Y) := (hs Y Y.property).choose_spec

  have hpt : {x₀} ∈ Ω₀ := by
    have htotal : IsTotal ({x₀} : Set X) := by simp [IsTotal]
    let _lin : LinearOrder ({x₀} : Set X) := LinearOrder.mk htotal
    simp [Ω₀, htotal]; apply WellFoundedLT.ofFinite
  let pt : Ω₀ := ⟨ _, hpt ⟩

  -- Операция, переводящая множество `Y` из `Ω₀` в меньшее множество `{y ∈ Y.val | y < x}`, которое
  -- также лежит в `Ω₀`, если `x ∈ Y.val \ {x₀}`, явно не названа в тексте, но мы дадим ей имя `F`
  -- для формализации.
  have hF {Y : Set X} (hY : Y ∈ Ω₀) {x : X} (hxy : x ∈ Y \ {x₀}) : {y ∈ Y | y < x} ∈ Ω₀ := by
    simp [Ω₀, IsTotal] at hY ⊢; choose _ hmin using hY.2.2; simp_all
    split_ands
    . convert WellFoundedLT.subset (hwell := hY.2) (B := {y ∈ Y | y < x}) _ _
      . intro ⟨ _, _ ⟩ ⟨ _, _ ⟩; simp; solve_by_elim [hY.1]
      intro _; simp; tauto
    have := hmin _ hxy.1; contrapose! hxy; order
  classical
  let F : Ω₀ → X → Ω₀ := fun Y x ↦ if hxy : x ∈ Y.val \ {x₀} then ⟨ {y ∈ (Y : Set X) | y < x}, hF Y.property hxy ⟩ else pt
  replace hF {Y : Ω₀} {x : X} (hxy : x ∈ (Y : Set X) \ {x₀}) : F Y x = { y ∈ (Y : Set X) | y < x } := by
    simp_all [F]

  -- Множество `Ω` отражает понятие «хорошего множества».
  set Ω := { Y : Ω₀ | ∀ x ∈ (Y : Set X) \ {x₀}, x = s (F Y x) }
  have hΩ : pt ∈ Ω := by
    sorry

  -- Упражнение 8.5.13
  have ex_8_5_13 {Y Y' : Ω} (x : X) (h : x ∈ (Y' : Set X) \ Y) : IsStrictUpperBound Y x := by
    sorry

  have : IsTotal Ω := by
    unfold IsTotal; by_contra!; obtain ⟨ ⟨ ⟨ Y, hY1 ⟩, hY2 ⟩, ⟨ ⟨ Y', hY'1⟩, hY'2 ⟩, h1, h2 ⟩ := this
    simp_all [Set.not_subset]
    choose x₁ hx₁ hx₁' using h1; choose x₂ hx₂ hx₂' using h2
    observe h1 : IsStrictUpperBound Y x₂
    observe h2 : IsStrictUpperBound Y' x₁
    simp [IsStrictUpperBound.iff] at h1 h2
    specialize h1 _ hx₁; specialize h2 _ hx₂; order
  set Y_infty : Set X := ⋃ Y : Ω, Y
  have hmem : x₀ ∈ Y_infty := by simp [Y_infty]; use pt; grind
  have hmin {x : X} (hx : x ∈ Y_infty) : x₀ ≤ x := by
    sorry
  have htotal : IsTotal Y_infty := by
    intro ⟨ x, hx ⟩ ⟨ x', hx'⟩; simp [Y_infty] at hx hx'
    obtain ⟨ Y, ⟨ hYΩ₀, hYΩ ⟩, hxY ⟩ := hx; obtain ⟨ Y', ⟨ hY'Ω₀, hY'Ω ⟩, hxY' ⟩ := hx'
    specialize this ⟨ _, hYΩ ⟩ ⟨ _, hY'Ω ⟩; simp [Ω₀] at this ⊢ hYΩ₀ hY'Ω₀
    obtain this | this := this
    . replace hY'Ω₀ := hY'Ω₀.1 ⟨ _, this hxY ⟩ ⟨ _, hxY' ⟩; simpa using hY'Ω₀
    replace hYΩ₀ := hYΩ₀.1 ⟨ _, hxY ⟩ ⟨ _, this hxY' ⟩; simpa using hYΩ₀
  have hwell : WellFoundedLT Y_infty := by
    rw [iff' htotal]; intro A ⟨ ⟨a, ha⟩, haA ⟩
    simp [Y_infty] at ha; obtain ⟨ Y, ⟨hYΩ₀, hYΩ⟩, haY ⟩ := ha
    simp [Ω₀, iff' hYΩ₀.1] at hYΩ₀
    choose b hb hbY hbmin using hYΩ₀.2.1 {x : Y | ∃ x' : A, (x : X) = x'} (by use ⟨ _, haY ⟩; simp [ha, haA])
    simp at hbY; choose hbY_infty hbA using hbY
    rw [IsMin.iff_lowerbound' (IsTotal.subtype htotal)]
    use ⟨ _, hbY_infty ⟩, hbA; intro ⟨ x, hx ⟩ hxA
    simp [Y_infty] at hx ⊢; obtain ⟨ Y', ⟨ hY'Ω₀, hY'Ω ⟩, hxY' ⟩ := hx
    sorry
  have hY_inftyΩ₀ : Y_infty ∈ Ω₀ := by
    sorry
  set sY_infty : X := s ⟨ _, hY_inftyΩ₀ ⟩
  have hYs_total : IsTotal (Y_infty ∪ {sY_infty} : Set X) := by
    sorry
  have hYs_well : WellFoundedLT (Y_infty ∪ {sY_infty} : Set X) := by
    sorry
  have hYs_mem : x₀ ∈ Y_infty ∪ {sY_infty} := by sorry
  have hYs_min : ∀ x ∈ Y_infty ∪ {sY_infty}, x₀ ≤ x := by sorry
  have hYs_Ω₀ : (Y_infty ∪ {sY_infty}) ∈ Ω₀ := by
    simpa [-Set.union_singleton, Ω₀, hYs_total, hYs_well, hYs_mem]
  specialize hs ⟨ _, hY_inftyΩ₀ ⟩
  simp [IsStrictUpperBound.iff] at hs
  have hYs_Ω : ⟨ _, hYs_Ω₀ ⟩ ∈ Ω := by
    simp [Ω, -Set.mem_insert_iff, -and_imp]
    intro x hx hxx₀
    rcases hx with rfl | hx
    . unfold sY_infty; congr 1
      symm; apply Subtype.val_injective; convert hF _
      . ext; simp; constructor
        . grind
        rintro ⟨ _ | _, _ ⟩
        . order
        assumption
      simp; specialize hs (y := x₀) (by simp [hmem]); order
    have hx' := hx; simp [Y_infty] at hx'; obtain ⟨ Y, ⟨hYΩ₀, hYΩ⟩, hxY ⟩ := hx'
    have hYΩ' := hYΩ; simp [Ω] at hYΩ
    convert hYΩ _ hxY hxx₀ using 2
    apply Subtype.val_injective
    rw [hF, hF]
    . ext y; simp [Y_infty]; intro hyx; constructor
      . rintro (rfl | ⟨ Y', ⟨hY'Ω₀, hY'Ω⟩, hyY' ⟩)
        . specialize hs _ hx; order
        by_contra!
        specialize ex_8_5_13 (Y := ⟨_, hYΩ'⟩) (Y' := ⟨_, hY'Ω⟩) y (by grind)
        rw [IsStrictUpperBound.iff] at ex_8_5_13
        specialize ex_8_5_13 x (by simp [hxY]); order
      grind
    all_goals simp [hxY, hx, hxx₀]
  have hs_mem : sY_infty ∈ Y_infty := Set.mem_iUnion_of_mem ⟨ _, hYs_Ω ⟩ (by simp)
  specialize hs _ hs_mem; order


/-- Лемма 8.5.15 (лемма Цорна) / Упражнение 8.5.14 -/
theorem Zorns_lemma {X : Type} [PartialOrder X] [Nonempty X]
  (hchain : ∀ Y : Set X, IsTotal Y ∧ Y.Nonempty → ∃ x, IsUpperBound Y x) : ∃ x : X, IsMax x := by
  sorry

/-- Упражнение 8.5.1 -/
def empty_set_partial_order [h₀ : LE Empty] : Decidable (∃ h : PartialOrder Empty, h.le = h₀.le) := by
  sorry

def empty_set_linear_order [h₀ : LE Empty] : Decidable (∃ h : LinearOrder Empty, h.le = h₀.le) := by
  sorry

def empty_set_well_order [h₀ : LT Empty] : Decidable (Nonempty (WellFoundedLT Empty)) := by
  sorry

/-- Упражнение 8.5.2 -/
example : ∃ (X : Type) (h₀ : LE X), (∀ x : X, x ≤ x) ∧ (∀ x y : X, x ≤ y → y ≤ x → x = y) ∧ ¬ (∀ x y z : X, x ≤ y → y ≤ z → x ≤ z) := by sorry

example : ∃ (X : Type) (h₀ : LE X), (∀ x : X, x ≤ x) ∧ (∀ x y z : X, x ≤ y → y ≤ z → x ≤ z) ∧ ¬ (∀ x y : X, x ≤ y → y ≤ x → x = y) := by sorry

example : ∃ (X : Type) (h₀ : LE X), (∀ x y : X, x ≤ y → y ≤ x → x = y) ∧ (∀ x y z : X, x ≤ y → y ≤ z → x ≤ z) ∧ ¬ (∀ x : X, x ≤ x) := by sorry

/-- Упражнение 8.5.3: отношение делимости на PNat. -/
@[reducible] def PNat.divOrder : PartialOrder PNat where
  le x y := ∃ n : PNat, y = n * x
  lt x y := (∃ n : PNat, y = n * x) ∧ ¬∃ n : PNat, x = n * y
  le_refl := by sorry
  le_antisymm := by sorry
  le_trans := by sorry
  lt_iff_le_not_ge := fun _ _ ↦ Iff.rfl

/-- `PNat.divOrder` действительно задаёт частичный порядок с отношением делимости `x ≤ y ↔ ∃ n, y = n * x`. -/
theorem PNat.divOrder_exists : 
    ∃ (h₀ : PartialOrder PNat), h₀.le = (fun x y ↦ ∃ n, y = n * x) :=
  ⟨PNat.divOrder, rfl⟩

/-- Отношение делимости на `PNat` не продолжается до линейного порядка: например, 2 и 3 несравнимы. -/
theorem PNat.divOrder_not_linear : 
    ¬∃ (h₀ : LinearOrder PNat), h₀.le = (fun x y ↦ ∃ n, y = n * x) := by
  sorry

/-- Упражнение 8.5.4 -/
example : ¬ ∃ x : {x : ℝ| x > 0}, IsMin x := by sorry

/-- Упражнение 8.5.5 -/
example {X Y : Type} [PartialOrder Y] (f : X → Y) : ∃ h₀ : PartialOrder X, h₀.le = (fun x y ↦ f x < f y ∨ x = y) := by sorry

def Ex_8_5_5_b : Decidable (∀ (X Y : Type) (h : LinearOrder Y) (f : X → Y), ∃ h₀ : LinearOrder X, h₀.le = (fun x y ↦ f x < f y ∨ x = y)) := by
  sorry

-- Заключительная часть Упражнения 8.5.5; если ответ на предыдущую часть "нет", измените гипотезы так, чтобы утверждение стало верным.

/-- Упражнение 8.5.6 -/
abbrev OrderIdeals (X : Type) [PartialOrder X] : Set (Set X) := .Iic '' (.univ : Set X)

def OrderIdeals.iso {X : Type} [PartialOrder X] : X ≃o OrderIdeals X := {
  toFun x := ⟨ .Iic x, by simp ⟩
  invFun := by sorry
  left_inv := by sorry
  right_inv := by sorry
  map_rel_iff' := by sorry
  }

/-- Упражнение 8.5.7 -/
example {Y : Type} [LinearOrder Y] {x y : Y} (hx : IsMin x) (hy : IsMin y) : x = y := by
  sorry

example {Y : Type} [LinearOrder Y] {x y : Y} (hx : IsMax x) (hy : IsMax y) : x = y := by
 sorry

/-- Упражнение 8.5.9 -/
example {X : Type} [LinearOrder X] (hmin : ∀ Y : Set X, Y.Nonempty → ∃ x : Y, IsMin x) (hmax : ∀ Y : Set X, Y.Nonempty → ∃ x : Y, IsMax x) : Finite X := by sorry


/-- Упражнение 8.5.12. Здесь мы делаем копию обёртки {name}`Lex` из Mathlib для лексикографических
порядков. Эта обёртка нужна, поскольку произведениям `X × Y` упорядоченных множеств по умолчанию
присваивается инстанс произведения частичных порядков, а не лексикографический порядок. -/
def Lex' (α : Type) := α

instance Lex'.partialOrder {X Y : Type} [PartialOrder X] [PartialOrder Y] : PartialOrder (Lex' (X × Y)) := {
  le := fun ⟨ x, y ⟩ ⟨ x', y' ⟩ ↦ (x < x') ∨ (x = x' ∧ y ≤ y')
  le_refl := by sorry
  le_antisymm := by sorry
  le_trans := by sorry
}

instance Lex'.linearOrder {X Y : Type} [LinearOrder X] [LinearOrder Y] : LinearOrder (Lex' (X × Y)) := by sorry

instance Lex'.WellFoundedLT {X Y : Type} [LinearOrder X] [WellFoundedLT X] [LinearOrder Y] [WellFoundedLT Y] : 
  WellFoundedLT (Lex' (X × Y)) := by sorry


/-- Упражнение 8.5.15 -/
theorem inj_trichotomy {X Y : Type}
    (h : ¬∃ f : X → Y, Function.Injective f) : 
    ∃ g : Y → X, Function.Injective g := by sorry

/-- Упражнение 8.5.16: множество частичных порядков на X, упорядоченное отношением "грубее чем",
само является частичным порядком. -/
instance PartialOrder.coarserOrder (X : Type) : PartialOrder (PartialOrder X) where
  le p1 p2 := ∀ x y : X, p1.le x y → p2.le x y
  le_refl := by simp
  le_trans p1 p2 p3 h12 h23 := fun x y h => h23 x y (h12 x y h)
  le_antisymm p1 p2 h12 h21 := by ext x y; exact ⟨h12 x y, h21 x y⟩

/-- Отношение делимости на PNat грубее, чем обычный порядок. -/
example : PNat.divOrder ≤ (inferInstance : PartialOrder PNat) := by
  intro x y h
  obtain ⟨n, rfl⟩ := h
  show x ≤ n * x
  exact Nat.le_mul_of_pos_left x n.pos

/-- Дискретный порядок (x ≤ y ↔ x = y) — единственный минимальный элемент. -/
@[reducible] def PartialOrder.discrete (X : Type) : PartialOrder X where
  le x y := x = y
  le_refl := fun _ ↦ rfl
  le_antisymm := fun _ _ h _ ↦ h
  le_trans := fun _ _ _ h1 h2 ↦ h1.trans h2

/-- Дискретный порядок — наименьший элемент в порядке "грубее чем" на всех частичных порядках `X`. -/
theorem PartialOrder.discrete_isBot (X : Type) (p : PartialOrder X) : 
    PartialOrder.discrete X ≤ p := by sorry

/-- Дискретный порядок минимален в порядке "грубее чем" на частичных порядках `X`. -/
theorem PartialOrder.discrete_isMin (X : Type) : 
    @IsMin (PartialOrder X) (coarserOrder X).toPreorder.toLE
      (PartialOrder.discrete X) := by sorry

/-- Дискретный порядок — единственный минимальный элемент в порядке "грубее чем". -/
theorem PartialOrder.discrete_unique_min (X : Type) (p : PartialOrder X)
    (h : @IsMin (PartialOrder X) (coarserOrder X).toPreorder.toLE p) : 
    p = discrete X := by sorry

/-- Частичный порядок максимален в порядке "грубее чем" тогда и только тогда, когда он тотален. -/
theorem PartialOrder.isMax_iff_isTotal (X : Type) (p : PartialOrder X) : 
    @IsMax (PartialOrder X) (coarserOrder X).toPreorder.toLE p ↔
    @IsTotal X p := by sorry

/-- Любой частичный порядок продолжается до тотального (по лемме Цорна). -/
theorem PartialOrder.extends_to_total (X : Type) (p : PartialOrder X) : 
    ∃ q : PartialOrder X, p ≤ q ∧ @IsTotal X q := by sorry

/-- Упражнение 8.5.17: докажите Упражнение 8.4.2 заново с помощью леммы Цорна -/
theorem exists_set_singleton_intersect' {I U : Type} {X : I → Set U}
    (h : Set.PairwiseDisjoint .univ X) (hne : ∀ α, Nonempty (X α)) : 
    ∃ Y : Set U, ∀ α, Nat.card (Y ∩ X α : Set U) = 1 := by sorry

/-- Упражнение 8.5.18 -/
theorem hausdorff_of_zorns_lemma {X : Type} [PartialOrder X] : 
    ∃ M : Set X, Maximal (fun (S : Set X) => IsTotal S) M := by sorry

/-- Принцип Хаусдорфа о максимальной цепи вместе с условием на верхние границы цепей влечёт лемму Цорна. -/
theorem zorns_lemma_of_hausdorff {X : Type} [PartialOrder X] [Nonempty X]
    (hhausdorff : ∃ M : Set X, Maximal (fun (S : Set X) => IsTotal S) M)
    (hchain : ∀ Y : Set X, IsTotal Y ∧ Y.Nonempty → ∃ x, IsUpperBound Y x) : 
    ∃ x : X, IsMax x := by sorry

/-- Упражнение 8.5.19: вполне упорядоченное подмножество X — подмножество с линейным порядком и
условием фундированности. -/
structure WellOrderedSubset (X : Type) where
  carrier : Set X
  ord : LinearOrder carrier
  wf : @WellFoundedLT carrier ord.toLT

/-- (W, ≤) — начальный отрезок (W', ≤'), если W ⊆ W', порядки согласуются на W,
и W = \{y ∈ W' : y <' x\} для некоторого x ∈ W'. -/
def WellOrderedSubset.IsInitialSegment {X : Type}
    (W W' : WellOrderedSubset X) : Prop :=
  ∃ x : W'.carrier,
    W.carrier = Subtype.val '' {z : W'.carrier | W'.ord.lt z x} ∧
    ∀ (a b : W.carrier) (ha : a.1 ∈ W'.carrier) (hb : b.1 ∈ W'.carrier),
      W.ord.le a b ↔ W'.ord.le ⟨a, ha⟩ ⟨b, hb⟩

/-- Начальный отрезок является собственным подмножеством большего вполне упорядоченного множества. -/
theorem WellOrderedSubset.IsInitialSegment.subset {X : Type}
    {W W' : WellOrderedSubset X} (h : W.IsInitialSegment W') : 
    W.carrier ⊂ W'.carrier := by sorry

/-- Порядок на вполне упорядоченных подмножествах: равенство или начальный отрезок. -/
instance WellOrderedSubset.instPartialOrder (X : Type) : 
    PartialOrder (WellOrderedSubset X) where
  le W W' := W = W' ∨ W.IsInitialSegment W'
  le_refl := fun W ↦ Or.inl rfl
  le_antisymm := by
    intro W W' h1 h2
    rcases h1 with rfl | h1
    · rfl
    rcases h2 with rfl | h2
    · rfl
    exact (h1.subset.asymm h2.subset).elim
  le_trans := by sorry

/-- Пустое вполне упорядоченное подмножество. -/
def WellOrderedSubset.empty (X : Type) : WellOrderedSubset X where
  carrier := ∅
  ord := { PartialOrder.discrete (∅ : Set X) with
    le_total := fun ⟨_, h⟩ ↦ h.elim
    toDecidableLE := fun ⟨_, h⟩ ↦ h.elim }
  wf := ⟨⟨fun ⟨_, h⟩ ↦ h.elim⟩⟩

/-- Пустое вполне упорядоченное подмножество минимально в порядке "начальный отрезок или равенство". -/
theorem WellOrderedSubset.empty_isMin (X : Type) : 
    @IsMin (WellOrderedSubset X) (instPartialOrder X).toPreorder.toLE
      (empty X) := by sorry

/-- Максимальные элементы — это в точности полные упорядочения всего X. -/
theorem WellOrderedSubset.isMax_iff_full (X : Type) (W : WellOrderedSubset X) : 
    @IsMax (WellOrderedSubset X) (instPartialOrder X).toPreorder.toLE W ↔
    W.carrier = Set.univ := by sorry

/-- Принцип полного упорядочения: на любом множестве существует полное упорядочение. -/
theorem well_ordering_principle (X : Type) : 
    ∃ (l : LinearOrder X), @WellFoundedLT X l.toLT := by sorry

/-- Принцип полного упорядочения влечёт аксиому выбора. Полностью упорядочиваем несвязное
объединение `Σ i, X i`, затем берём минимум в каждом слое. -/
theorem axiom_of_choice_of_well_ordering
    (hwo : ∀ T : Type, ∃ (l : LinearOrder T), @WellFoundedLT T l.toLT)
    {I : Type} {X : I → Type} (hne : ∀ i, Nonempty (X i)) : 
    Nonempty (∀ i, X i) := by sorry

/-- Упражнение 8.5.20 -/
theorem maximal_disjoint_subcollection {X : Type} (Ω : Set (Set X)) (hne : ∅ ∉ Ω) : 
    ∃ Ω' ⊆ Ω, Ω'.Pairwise Disjoint ∧
      (∀ C ∈ Ω, ∃ A ∈ Ω', (C ∩ A).Nonempty) := by sorry

/-- Свойство максимального непересекающегося подсемейства влечёт Упражнение 8.4.2, а значит,
эквивалентно аксиоме выбора. -/
theorem exists_set_singleton_intersect_of_maximal_disjoint
    (hmds : ∀ (X : Type) (Ω : Set (Set X)), ∅ ∉ Ω →
      ∃ Ω' ⊆ Ω, Ω'.Pairwise Disjoint ∧
        (∀ C ∈ Ω, ∃ A ∈ Ω', (C ∩ A).Nonempty))
    {I U : Type} {X : I → Set U}
    (h : Set.PairwiseDisjoint .univ X) (hne : ∀ α, Nonempty (X α)) : 
    ∃ Y : Set U, ∀ α, Nat.card (Y ∩ X α : Set U) = 1 := by sorry

end Chapter8
