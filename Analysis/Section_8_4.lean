import Mathlib.Tactic
import Analysis.Section_8_1
import Analysis.Section_8_2

set_option doc.verso.suggestions false

/-!
# Analysis I, раздел 8.4: Аксиома выбора

Я старался сделать перевод максимально точным перефразированием оригинального текста. Когда
приходилось выбирать между более идиоматичным Lean-решением и более точным переводом, я, как
правило, выбирал второе. В частности, местами Lean-код можно было бы "заголфить", сделав его более
элегантным и идиоматичным, но я сознательно этого избегал.

Основные конструкции и результаты этого раздела:

- Обзор зависимого произведения Mathlib `∀ α, X α`.
- Аксиома выбора в различных эквивалентных формах, а также счётная аксиома выбора.

Поскольку теория множеств Главы 3 к этому моменту уже устарела на протяжении многих глав, мы не
будем встраивать аксиому выбора непосредственно в эту теорию в данном тексте; но при желании это
можно было бы сделать (например, расширив класс `Chapter3.SetTheory` до класса
`Chapter3.SetTheoryWithChoice`), и студенты вольны попробовать это отдельно. Вместо этого мы будем
использовать встроенную аксиому Mathlib {name}`Classical.choice`. Строго говоря, эта аксиома уже
довольно часто использовалась в тексте и раньше, во многом потому, что Mathlib использует
{name}`Classical.choice` для вывода многих более слабых утверждений, таких как закон исключённого
третьего. Поэтому различия, которые проводятся в оригинальном тексте относительно того, использует
ли данное утверждение аксиому выбора или нет, в этой формализации несколько размыты. Теоретически
можно восстановить это различие, отказавшись от Mathlib и работая всюду с собственными структурами
вроде `Chapter3.SetTheory` и `Chapter3.SetTheoryWithChoice`, но это было бы крайне утомительно, и мы
не будем этого делать.
-/

namespace Chapter8

/-- Definition 8.4.1 (бесконечное декартово произведение). Мы будем избегать использования этого
определения в пользу формы Mathlib {lean}`∀ α, X α`, которая, как мы вскоре покажем, эквивалентна
(точнее, обобщает) это определение.

{given -show}`α : I`
Поскольку Lean не допускает неограниченных объединений типов, здесь мы немного жульничаем,
предполагая, что все {lean}`X α` — это множества в общей вселенной {name}`U`. Заметьте, что
определение Mathlib такого ограничения не имеет. -/
abbrev CartesianProduct {I U : Type} (X : I → Set U) := { x : I → ⋃ α, X α // ∀ α, ↑(x α) ∈ X α }

/-- Эквивалентность с произведением из Mathlib -/
def CartesianProduct.equiv {I U : Type} (X : I → Set U) : 
  CartesianProduct X ≃ ∀ α, X α := {
  toFun x α := ⟨ x.val α, by aesop ⟩
  invFun x := ⟨ fun α ↦ ⟨ x α, by simp; use α; aesop ⟩, by aesop ⟩
  left_inv x := by aesop
  right_inv x := by aesop
  }

/-- Example 8.4.2. -/
def Function.equiv {I X : Type} : (∀ _ : I, X) ≃ (I → X) := {
  toFun f := f
  invFun f := f
  left_inv _f := rfl
  right_inv _f := rfl
}

def product_zero_equiv {X : Fin 0 → Type} : (∀ i : Fin 0, X i) ≃ PUnit := {
  toFun f := PUnit.unit
  invFun x i := nomatch i
  left_inv f := by aesop
  right_inv f := rfl
}

def product_one_equiv {X : Fin 1 → Type} : (∀ i : Fin 1, X i) ≃ X 0 := {
  toFun f := f 0
  invFun x i := by rwa [←Fin.fin_one_eq_zero i] at x
  left_inv f := by ext i; rw [Fin.fin_one_eq_zero i]; simp
  right_inv f := rfl
}

def product_two_equiv {X : Fin 2 → Type} : (∀ i : Fin 2, X i) ≃ (X 0 × X 1) := {
  toFun f := (f 0, f 1)
  invFun f i := match i with
    | 0 => f.1
    | 1 => f.2
  left_inv f := by aesop
  right_inv f := rfl
}

def product_three_equiv {X : Fin 3 → Type} : (∀ i : Fin 3, X i) ≃ (X 0 × X 1 × X 2) := {
  toFun f := (f 0, f 1, f 2)
  invFun f i := match i with
    | 0 => f.1
    | 1 => f.2.1
    | 2 => f.2.2
  left_inv f := by aesop
  right_inv f := rfl
}

/-- Axiom 8.1 (выбор) -/
theorem axiom_of_choice {I : Type} {X : I → Type} (h : ∀ i, Nonempty (X i)) : 
  Nonempty (∀ i, X i) := by use fun i ↦ (h i).some

theorem axiom_of_countable_choice {I : Type} {X : I → Type} [Countable I] (h : ∀ i, Nonempty (X i)) : 
  Nonempty (∀ i, X i) := axiom_of_choice h

/-- Lemma 8.4.5 -/
theorem exist_tendsTo_sup {E : Set ℝ} (hnon : E.Nonempty) (hbound : BddAbove E) : 
  ∃ a : ℕ → ℝ, (∀ n, a n ∈ E) ∧ Filter.atTop.Tendsto a (nhds (sSup E)) := by
  -- Это доказательство написано так, чтобы следовать структуре оригинального текста.
  set X : ℕ → Set ℝ := fun n ↦ { x ∈ E | sSup E - 1 / (n+1 : ℝ) ≤ x ∧ x ≤ sSup E }
  have hX : ∀ n, Nonempty (X n) := by
    intro n
    have : 1 / (n+1 : ℝ) > 0 := by positivity
    choose s hs using (lt_csSup_iff hbound hnon).mp (show sSup E - 1 / (n+1 : ℝ) < sSup E by linarith)
    use s; simp_all [X]
    refine ⟨ by linarith, le_csSup hbound hs.1 ⟩
  have ⟨ a ⟩ := axiom_of_countable_choice hX
  use fun n ↦ ↑(a n); constructor; swap
  apply Filter.Tendsto.squeeze (g := fun n : ℕ ↦ sSup E - 1/(n+1 : ℝ)) (h := fun _ : ℕ ↦ sSup E)
  . convert tendsto_const_nhds.sub (a := sSup E) (b := 0) _; simp
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  . exact tendsto_const_nhds
  all_goals intro n; have := (a n).property; simp_all [X]

/-- Remark 8.4.6. Этот частный случай Lemma 8.4.5 обходится без (счётной) аксиомы выбора. -/
theorem exist_tendsTo_sup_of_closed {E : Set ℝ} (hnon : E.Nonempty) (hbound : BddAbove E) (hclosed : IsClosed E) : 
  ∃ a : ℕ → ℝ, (∀ n, a n ∈ E) ∧ Filter.atTop.Tendsto a (nhds (sSup E)) := by
  set X : ℕ → Set ℝ := fun n ↦ { x ∈ E | sSup E - 1 / (n+1 : ℝ) ≤ x ∧ x ≤ sSup E }
  have hX : ∀ n, Nonempty (X n) := by
    intro n
    have : 1 / (n+1 : ℝ) > 0 := by positivity
    choose s hs using (lt_csSup_iff hbound hnon).mp (show sSup E - 1 / (n+1 : ℝ) < sSup E by linarith)
    use s; simp_all [X]
    refine ⟨ by linarith, le_csSup hbound hs.1 ⟩
  set a : ℕ → ℝ := fun n ↦ sInf (X n)
  have ha (n : ℕ) : a n ∈ X n := by
    apply IsClosed.csInf_mem _ Set.Nonempty.of_subtype
    . rw [bddBelow_def]; use sSup E - 1 / (n+1 : ℝ); aesop
    . rw [show X n = E ∩ .Icc (sSup E - 1 / (n+1 : ℝ)) (sSup E) by ext; aesop]
      exact hclosed.inter isClosed_Icc
  use a; constructor; swap
  apply Filter.Tendsto.squeeze (g := fun n : ℕ ↦ sSup E - 1/(n+1 : ℝ)) (h := fun _ : ℕ ↦ sSup E)
  . convert tendsto_const_nhds.sub (a := sSup E) (b := 0) _; simp
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  . exact tendsto_const_nhds
  all_goals intro _; simp_all [X]

/-- Proposition 8.4.7 / Exercise 8.4.1 -/
theorem exists_function {X Y : Type} {P : X → Y → Prop} (h : ∀ x, ∃ y, P x y) : 
  ∃ f : X → Y, ∀ x, P x (f x) := by
  sorry

/-- Exercise 8.4.1. Дух этого вопроса — установить данный результат непосредственно
из {name}`exists_function`, избегая предыдущих результатов, которые более явно опирались
на аксиому выбора. -/
theorem axiom_of_choice_from_exists_function {I : Type} {X : I → Type} (h : ∀ i, Nonempty (X i)) : 
  Nonempty (∀ i, X i) := by
  sorry

/-- Exercise 8.4.2 -/
theorem exists_set_singleton_intersect {I U : Type} {X : I → Set U} (h : Set.PairwiseDisjoint .univ X)
  (hnon : ∀ α, Nonempty (X α)) : 
  ∃ Y : Set U, ∀ α, Nat.card (Y ∩ X α : Set U) = 1 := by
  sorry

/-- Exercise 8.4.2. Дух этого вопроса — установить данный результат непосредственно
из {name}`exists_set_singleton_intersect`, избегая предыдущих результатов, которые более явно
опирались на аксиому выбора. -/
theorem axiom_of_choice_from_exists_set_singleton_intersect {I : Type} {X : I → Type} (h : ∀ i, Nonempty (X i)) : 
  Nonempty (∀ i, X i) := by
  sorry

/-- Exercise 8.4.3 -/
theorem Function.Injective.inv_surjective {A B : Type} {g : B → A} (hg : Function.Surjective g) : 
  ∃ f : A → B, Function.Injective f ∧ Function.RightInverse f g := by
  sorry

/-- Exercise 8.4.3. Дух этого вопроса — установить данный результат непосредственно
из {name}`Function.Injective.inv_surjective`, избегая предыдущих результатов, которые более явно
опирались на аксиому выбора. -/
theorem axiom_of_choice_from_function_injective_inv_surjective {I : Type} {X : I → Type} (h : ∀ i, Nonempty (X i)) : 
  Nonempty (∀ i, X i) := by
  sorry

end Chapter8
