import Mathlib.Tactic
import Analysis.Section_4_3

set_option doc.verso.suggestions false

/-!
# Analysis I, раздел 5.1: Последовательности Коши

Я старался сделать перевод максимально точным перефразированием оригинального текста. Когда
приходилось выбирать между более идиоматичным Lean-решением и более точным переводом, я, как
правило, выбирал второе. В частности, местами Lean-код можно было бы "заголфить", сделав его более
элегантным и идиоматичным, но я сознательно этого избегал.

Основные конструкции и результаты этого раздела:

- Понятие последовательности рациональных чисел
- Понятия `ε`-устойчивости, эвентуальной `ε`-устойчивости и последовательностей Коши

## Советы от прошлых пользователей

Пользователи, прошедшие упражнения этого раздела, могут присылать свои советы для будущих
пользователей в виде PR.

- (Добавьте совет сюда)

-/

namespace Chapter5

/--
  Definition 5.1.1 (Последовательность).
  Чтобы избежать некоторых технических сложностей, связанных с зависимыми типами,
  мы продолжаем последовательности нулём слева от начальной точки {name (full := Sequence.n₀)}`n₀`.
-/
@[ext]
structure Sequence where
  n₀ : ℤ
  seq : ℤ → ℚ
  vanish : ∀ n < n₀, seq n = 0

/-- Последовательности можно рассматривать как функции из {lean}`ℤ` в {lean}`ℚ`. -/
instance Sequence.instCoeFun : CoeFun Sequence (fun _ ↦ ℤ → ℚ) where
  coe := fun a ↦ a.seq

/--
Функции из {lean}`ℕ` в {lean}`ℚ` можно рассматривать
как последовательности, начинающиеся с 0.
{name}`Sequence.ofNatFun` выполняет это преобразование.

Атрибут {attr}`coe` позволяет делаборатору печатать
{lean}`Sequence.ofNatFun f` как {lit}`↑f`, что более лаконично.
Вы можете спокойно убрать его, если предпочитаете более явную нотацию.
-/
@[coe]
def Sequence.ofNatFun (f : ℕ → ℚ) : Sequence where
  n₀ := 0
  seq n := if n ≥ 0 then f n.toNat else 0
  vanish := by grind

-- Обратите внимание, как делаборатор печатает это как `↑fun x ↦ ↑x ^ 2 : Sequence`.
#check Sequence.ofNatFun (· ^ 2)

/--
Если {given}`a : ℕ → ℚ` используется в контексте, где ожидается {name}`Sequence`,
автоматически приводит {name}`a` к {lean}`Sequence.ofNatFun a`
(которое будет напечатано как {lean (type :="Sequence")}`↑a`).
-/
instance : Coe (ℕ → ℚ) Sequence where
  coe := Sequence.ofNatFun

abbrev Sequence.mk' (n₀ : ℤ) (a : { n // n ≥ n₀ } → ℚ) : Sequence where
  n₀ := n₀
  seq n := if h : n ≥ n₀ then a ⟨n, h⟩ else 0
  vanish := by grind

lemma Sequence.eval_mk {n n₀ : ℤ} (a : { n // n ≥ n₀ } → ℚ) (h : n ≥ n₀) :
  (Sequence.mk' n₀ a) n = a ⟨ n, h ⟩ := by grind

@[simp]
lemma Sequence.eval_coe (n : ℕ) (a : ℕ → ℚ) : (a : Sequence) n = a n :=
  by norm_cast

@[simp]
lemma Sequence.eval_coe_at_int (n : ℤ) (a : ℕ → ℚ) : (a : Sequence) n = if n ≥ 0 then a n.toNat else 0 := by norm_cast

@[simp]
lemma Sequence.n0_coe (a : ℕ → ℚ) : (a : Sequence).n₀ = 0 := by norm_cast

/-- Example 5.1.2 (a) -/
abbrev Sequence.squares : Sequence := ((fun n : ℕ ↦ (n^2 : ℚ)) : Sequence)

/-- Example 5.1.2 (b) -/
example (n : ℕ) : Sequence.squares n = n^2 := Sequence.eval_coe _ _

/-- Example 5.1.2 (c) -/
abbrev Sequence.three : Sequence := ((fun (_ : ℕ) ↦ (3 : ℚ)) : Sequence)

/-- Example 5.1.2 (d) -/
example (n : ℕ) : Sequence.three n = 3 := Sequence.eval_coe _ (fun (_ : ℕ) ↦ (3 : ℚ))

/-- Example 5.1.2 (e) -/
abbrev Sequence.squares_from_three : Sequence := mk' 3 (·^2)

/-- Example 5.1.2 (f) -/
example (n : ℤ) (hn : n ≥ 3) : Sequence.squares_from_three n = n^2 := Sequence.eval_mk _ hn

-- нужно временно выйти из пространства имён `Chapter5`, чтобы ввести следующую нотацию

end Chapter5

/--
Небольшое обобщение Definition 5.1.3 — определение {name}`ε`-устойчивости для последовательности
с произвольной начальной точкой {lean}`a.n₀`
-/
abbrev Rat.Steady (ε : ℚ) (a : Chapter5.Sequence) : Prop :=
  ∀ n ≥ a.n₀, ∀ m ≥ a.n₀, ε.Close (a n) (a m)

lemma Rat.steady_def (ε : ℚ) (a : Chapter5.Sequence) :
  ε.Steady a ↔ ∀ n ≥ a.n₀, ∀ m ≥ a.n₀, ε.Close (a n) (a m) := by rfl

namespace Chapter5

/--
Definition 5.1.3 — определение {name}`ε`-устойчивости для последовательности, начинающейся с 0
-/
lemma Rat.Steady.coe (ε : ℚ) (a : ℕ → ℚ) :
    ε.Steady a ↔ ∀ n m : ℕ, ε.Close (a n) (a m) := by
  constructor
  · intro h n m; specialize h n ?_ m ?_ <;> simp_all
  intro h n hn m hm
  lift n to ℕ using hn
  lift m to ℕ using hm
  simp [h n m]

/--
Не из учебника: последовательность 3, 3 ... является 1-устойчивой.
Служит демонстрацией {name}`Rat.Steady.coe`.
-/
example : (1 : ℚ).Steady ((fun _ : ℕ ↦ (3 : ℚ)) : Sequence) := by
  simp [Rat.Steady.coe, Rat.Close]

/--
{given -show}`hn : n ≥ 0, hm : m ≥ 0`
Для сравнения: если вам нужно работать напрямую с {name}`Rat.Steady` на приведении типа, появятся
побочные условия {lean}`hn : n ≥ 0` и {lean}`hm : m ≥ 0`, которые придётся обрабатывать.
-/
example : (1 : ℚ).Steady ((fun _ : ℕ ↦ (3 : ℚ)) : Sequence) := by
  intro n _ m _; simp_all [Sequence.n0_coe, Sequence.eval_coe_at_int, Rat.Close]

/--
Example 5.1.5: последовательность `1, 0, 1, 0, ...` является 1-устойчивой.
-/
example : (1 : ℚ).Steady ((fun n : ℕ ↦ if Even n then (1 : ℚ) else (0 : ℚ)) : Sequence) := by
  rw [Rat.Steady.coe]
  intro n m
  -- Разбираем четыре случая в зависимости от того, чётны или нечётны n и m
  -- В каждом случае мы знаем точное значение a n и a m
  split_ifs <;> simp [Rat.Close]

/--
Example 5.1.5: последовательность `1, 0, 1, 0, ...` не является ½-устойчивой.
-/
example : ¬ (0.5 : ℚ).Steady ((fun n : ℕ ↦ if Even n then (1 : ℚ) else (0 : ℚ)) : Sequence) := by
  rw [Rat.Steady.coe]
  by_contra h; specialize h 0 1; simp [Rat.Close] at h
  norm_num at h

/--
Example 5.1.5: последовательность 0.1, 0.01, 0.001, ... является 0.1-устойчивой.
-/
example : (0.1 : ℚ).Steady ((fun n : ℕ ↦ (10 : ℚ) ^ (-(n : ℤ)-1) ) : Sequence) := by
  rw [Rat.Steady.coe]
  intro n m; unfold Rat.Close
  wlog h : m ≤ n
  · specialize this m n (by linarith); rwa [abs_sub_comm]
  rw [abs_sub_comm, abs_of_nonneg]
  . rw [show (0.1 : ℚ) = (10 : ℚ)^(-1 : ℤ) - 0 by norm_num]
    gcongr <;> try grind
    positivity
  linarith [show (10 : ℚ) ^ (-(n : ℤ)-1) ≤ (10 : ℚ) ^ (-(m : ℤ)-1) by gcongr; norm_num]

/--
Example 5.1.5: последовательность 0.1, 0.01, 0.001, ... не является 0.01-устойчивой. Оставлено как упражнение.
-/
example : ¬(0.01 : ℚ).Steady ((fun n : ℕ ↦ (10 : ℚ) ^ (-(n : ℤ)-1) ) : Sequence) := by sorry

/-- Example 5.1.5: последовательность 1, 2, 4, 8, ... не является ε-устойчивой ни для какого ε. Оставлено как упражнение.
-/
example (ε : ℚ) : ¬ ε.Steady ((fun n : ℕ ↦ (2 ^ (n+1) : ℚ) ) : Sequence) := by sorry

/-- Example 5.1.5: последовательность 2, 2, 2, ... является ε-устойчивой для любого ε > 0.
-/
example (ε : ℚ) (hε : ε>0) : ε.Steady ((fun _ : ℕ ↦ (2 : ℚ) ) : Sequence) := by
  rw [Rat.Steady.coe]; simp [Rat.Close]; positivity

/--
Последовательность 10, 0, 0, ... является 10-устойчивой.
-/
example : (10 : ℚ).Steady ((fun n : ℕ ↦ if n = 0 then (10 : ℚ) else (0 : ℚ)) : Sequence) := by
  rw [Rat.Steady.coe]; intro n m
  -- Разбираем 4 случая в зависимости от того, равны ли n и m нулю
  split_ifs <;> simp [Rat.Close]

/--
Последовательность 10, 0, 0, ... не является ε-устойчивой ни для какого меньшего значения ε.
-/
example (ε : ℚ) (hε : ε<10) :  ¬ ε.Steady ((fun n : ℕ ↦ if n = 0 then (10 : ℚ) else (0 : ℚ)) : Sequence) := by
  contrapose! hε; rw [Rat.Steady.coe] at hε; specialize hε 0 1; simpa [Rat.Close] using hε

/--
  {name}`Sequence.from` начинает {lean}`a : Sequence` с {name}`n₁`. Предполагается использовать
  при {lean}`n₁ ≥ n₀`, но в противном случае возвращает "мусорное" значение исходной
  последовательности {name}`a`.
-/
abbrev Sequence.from (a : Sequence) (n₁ : ℤ) : Sequence :=
  mk' (max a.n₀ n₁) (fun n ↦ a (n : ℤ))

lemma Sequence.from_eval (a : Sequence) {n₁ n : ℤ} (hn : n ≥ n₁) :
  (a.from n₁) n = a n := by simp [hn]; intro h; exact (a.vanish _ h).symm

end Chapter5

/-- Definition 5.1.6 (Эвентуально ε-устойчива) -/
abbrev Rat.EventuallySteady (ε : ℚ) (a : Chapter5.Sequence) : Prop := ∃ N ≥ a.n₀, ε.Steady (a.from N)

lemma Rat.eventuallySteady_def (ε : ℚ) (a : Chapter5.Sequence) :
  ε.EventuallySteady a ↔ ∃ N ≥ a.n₀, ε.Steady (a.from N) := by rfl

namespace Chapter5

/--
Example 5.1.7: последовательность 1, 1/2, 1/3, ... не является 0.1-устойчивой
-/
lemma Sequence.ex_5_1_7_a : ¬ (0.1 : ℚ).Steady ((fun n : ℕ ↦ (n+1 : ℚ)⁻¹ ) : Sequence) := by
  intro h; rw [Rat.Steady.coe] at h; specialize h 0 2; simp [Rat.Close] at h; norm_num at h

/--
Example 5.1.7: последовательность `a_10, a_11, a_12, ...` является 0.1-устойчивой
-/
lemma Sequence.ex_5_1_7_b : (0.1 : ℚ).Steady (((fun n : ℕ ↦ (n+1 : ℚ)⁻¹ ) : Sequence).from 10) := by
  rw [Rat.Steady]
  intro n hn m hm; simp at hn hm
  lift n to ℕ using (by omega)
  lift m to ℕ using (by omega)
  simp_all [Rat.Close]
  wlog h : m ≤ n
  · specialize this m n _ _ _ <;> try omega
    rwa [abs_sub_comm] at this
  rw [abs_sub_comm]
  have : ((n : ℚ) + 1)⁻¹ ≤ ((m : ℚ) + 1)⁻¹ := by gcongr
  rw [abs_of_nonneg (by linarith), show (0.1 : ℚ) = (10 : ℚ)⁻¹ - 0 by norm_num]
  gcongr
  · norm_cast; omega
  positivity

/--
Example 5.1.7: последовательность 1, 1/2, 1/3, ... эвентуально 0.1-устойчива
-/
lemma Sequence.ex_5_1_7_c : (0.1 : ℚ).EventuallySteady ((fun n : ℕ ↦ (n+1 : ℚ)⁻¹ ) : Sequence) :=
  ⟨10, by simp, ex_5_1_7_b⟩

/--
Example 5.1.7

Последовательность 10, 0, 0, ... эвентуально ε-устойчива для любого ε > 0. Оставлено как упражнение.
-/
lemma Sequence.ex_5_1_7_d {ε : ℚ} (hε : ε>0) :
    ε.EventuallySteady ((fun n : ℕ ↦ if n=0 then (10 : ℚ) else (0 : ℚ) ) : Sequence) := by sorry

abbrev Sequence.IsCauchy (a : Sequence) : Prop := ∀ ε > (0 : ℚ), ε.EventuallySteady a

lemma Sequence.isCauchy_def (a : Sequence) :
  a.IsCauchy ↔ ∀ ε > (0 : ℚ), ε.EventuallySteady a := by rfl

/-- Определение последовательностей Коши для последовательности, начинающейся с {lean}`0` -/
lemma Sequence.IsCauchy.coe (a : ℕ → ℚ) :
    (a : Sequence).IsCauchy ↔ ∀ ε > (0 : ℚ), ∃ N, ∀ j ≥ N, ∀ k ≥ N,
    Section_4_3.dist (a j) (a k) ≤ ε := by
  constructor <;> intro h ε hε
  · choose N hN h' using h ε hε
    lift N to ℕ using hN; use N
    intro j _ k _; simp [Rat.steady_def] at h'; specialize h' j _ k _ <;> try omega
    simp_all; exact h'
  choose N h' using h ε hε
  refine ⟨ max N 0, by simp, ?_ ⟩
  intro n hn m hm; simp at hn hm
  have npos : 0 ≤ n := ?_
  have mpos : 0 ≤ m := ?_
  lift n to ℕ using npos
  lift m to ℕ using mpos
  simp [hn, hm]; specialize h' n _ m _
  all_goals try omega
  norm_cast

lemma Sequence.IsCauchy.mk {n₀ : ℤ} (a : {n // n ≥ n₀} → ℚ) :
    (mk' n₀ a).IsCauchy ↔ ∀ ε > (0 : ℚ), ∃ N ≥ n₀, ∀ j ≥ N, ∀ k ≥ N,
    Section_4_3.dist (mk' n₀ a j) (mk' n₀ a k) ≤ ε := by
  constructor <;> intro h ε hε <;> choose N hN h' using h ε hε
  · refine ⟨ N, hN, ?_ ⟩; dsimp at hN; intro j _ k _
    simp only [Rat.Steady, show max n₀ N = N by omega] at h'
    specialize h' j _ k _ <;> try omega
    simp_all [show n₀ ≤ j by omega, show n₀ ≤ k by omega]
    exact h'
  refine ⟨ max n₀ N, by simp, ?_ ⟩
  intro n _ m _; simp_all
  apply h' n _ m <;> omega

noncomputable def Sequence.sqrt_two : Sequence := (fun n : ℕ ↦ ((⌊ (Real.sqrt 2)*10^n ⌋ / 10^n) : ℚ))

/--
  Example 5.1.10. (Для этого требуется хорошее знакомство с Mathlib API для вещественных чисел.)
-/
theorem Sequence.ex_5_1_10_a : (1 : ℚ).Steady sqrt_two := by sorry

/--
  Example 5.1.10. (Для этого требуется хорошее знакомство с Mathlib API для вещественных чисел.)
-/
theorem Sequence.ex_5_1_10_b : (0.1 : ℚ).Steady (sqrt_two.from 1) := by sorry

theorem Sequence.ex_5_1_10_c : (0.1 : ℚ).EventuallySteady sqrt_two := by sorry

/-- Proposition 5.1.11. Гармоническая последовательность, определённая как a₁ = 1, a₂ = 1/2, ...,
является последовательностью Коши. -/
theorem Sequence.IsCauchy.harmonic : (mk' 1 (fun n ↦ (1 : ℚ)/n)).IsCauchy := by
  rw [IsCauchy.mk]
  intro ε hε
  -- Мы действуем в обратном порядке по сравнению с книгой — сначала выбираем N такое, что N > 1/ε
  obtain ⟨ N, hN : N > 1/ε ⟩ := exists_nat_gt (1 / ε)
  have hN' : N > 0 := by
    observe : (1/ε) > 0
    observe : (N : ℚ) > 0
    norm_cast at this
  refine ⟨ N, by norm_cast, ?_ ⟩
  intro j hj k hk
  lift j to ℕ using (by linarith)
  lift k to ℕ using (by linarith)
  norm_cast at hj hk
  simp [show j ≥ 1 by linarith, show k ≥ 1 by linarith]

  have hdist : Section_4_3.dist ((1 : ℚ)/j) ((1 : ℚ)/k) ≤ (1 : ℚ)/N := by
    rw [Section_4_3.dist_eq, abs_le']
    /-
    Мы устанавливаем следующие оценки:
    - 1/j ∈ [0, 1/N]
    - 1/k ∈ [0, 1/N]
    Из этого следует, что расстояние между 1/j и 1/k не превосходит 1/N — когда они находятся
    настолько "далеко друг от друга", насколько это возможно.
    -/
    have : 1/j ≤ (1 : ℚ)/N := by gcongr
    observe : (0 : ℚ) ≤ 1/j
    have : 1/k ≤ (1 : ℚ)/N := by gcongr
    observe : (0 : ℚ) ≤ 1/k
    grind
  simp at *; apply hdist.trans
  rw [inv_le_comm₀] <;> try positivity
  order

abbrev BoundedBy {n : ℕ} (a : Fin n → ℚ) (M : ℚ) : Prop := ∀ i, |a i| ≤ M

/--
  Definition 5.1.12 (ограниченные последовательности). Здесь мы начинаем последовательности с
  {lean}`0`, а не с {lean}`1`, чтобы лучше согласовываться с соглашениями Mathlib.
-/
lemma boundedBy_def {n : ℕ} (a : Fin n → ℚ) (M : ℚ) : BoundedBy a M ↔ ∀ i, |a i| ≤ M := by rfl

abbrev Sequence.BoundedBy (a : Sequence) (M : ℚ) : Prop := ∀ n, |a n| ≤ M

/-- Definition 5.1.12 (ограниченные последовательности) -/
lemma Sequence.boundedBy_def (a : Sequence) (M : ℚ) : a.BoundedBy M ↔ ∀ n, |a n| ≤ M := by rfl

abbrev Sequence.IsBounded (a : Sequence) : Prop := ∃ M ≥ 0, a.BoundedBy M

/-- Definition 5.1.12 (ограниченные последовательности) -/
lemma Sequence.isBounded_def (a : Sequence) : a.IsBounded ↔ ∃ M ≥ 0, a.BoundedBy M := by rfl

/-- Example 5.1.13 (a) -/
example : BoundedBy ![1,-2,3,-4] 4 := by intro i; fin_cases i <;> norm_num

/-- Example 5.1.13 (b) -/
example : ¬((fun n : ℕ ↦ (-1)^n * (n+1 : ℚ)) : Sequence).IsBounded := by sorry

/-- Example 5.1.13 (c) -/
example : ((fun n : ℕ ↦ (-1 : ℚ)^n) : Sequence).IsBounded := by
  refine ⟨ 1, by norm_num, ?_ ⟩; intro i; by_cases h : 0 ≤ i <;> simp [h]

/-- Example 5.1.13 (d) -/
example : ¬((fun n : ℕ ↦ (-1 : ℚ)^n) : Sequence).IsCauchy := by
  rw [Sequence.IsCauchy.coe]
  by_contra h; specialize h (1/2 : ℚ) (by norm_num)
  choose N h using h; specialize h N _ (N+1) _ <;> try omega
  by_cases h' : Even N
  · simp [h'.neg_one_pow, (h'.add_one).neg_one_pow, Section_4_3.dist] at h
    norm_num at h
  observe h₁ : Odd N
  observe h₂ : Even (N+1)
  simp [h₁.neg_one_pow, h₂.neg_one_pow, Section_4_3.dist] at h
  norm_num at h

/-- Lemma 5.1.14 -/
lemma IsBounded.finite {n : ℕ} (a : Fin n → ℚ) : ∃ M ≥ 0,  BoundedBy a M := by
  -- это доказательство написано так, чтобы следовать структуре оригинального текста.
  induction' n with n hn
  . use 0; simp
  set a' : Fin n → ℚ := fun m ↦ a m.castSucc
  choose M hpos hM using hn a'
  have h1 : BoundedBy a' (M + |a (Fin.ofNat _ n)|) := fun m ↦ (hM m).trans (by simp)
  have h2 : |a (Fin.ofNat _ n)| ≤ M + |a (Fin.ofNat _ n)| := by simp [hpos]
  refine ⟨ M + |a (Fin.ofNat _ n)|, by positivity, ?_ ⟩
  intro m; obtain ⟨ j, rfl ⟩ | rfl := Fin.eq_castSucc_or_eq_last m
  . grind
  convert h2; simp

/-- Lemma 5.1.15 (Последовательности Коши ограничены) / Exercise 5.1.1 -/
lemma Sequence.isBounded_of_isCauchy {a : Sequence} (h : a.IsCauchy) : a.IsBounded := by
  sorry

/-- Exercise 5.1.2 -/
theorem Sequence.isBounded_add {a b : ℕ → ℚ} (ha : (a : Sequence).IsBounded) (hb : (b : Sequence).IsBounded) :
    (a + b : Sequence).IsBounded := by sorry

theorem Sequence.isBounded_sub {a b : ℕ → ℚ} (ha : (a : Sequence).IsBounded) (hb : (b : Sequence).IsBounded) :
    (a - b : Sequence).IsBounded := by sorry

theorem Sequence.isBounded_mul {a b : ℕ → ℚ} (ha : (a : Sequence).IsBounded) (hb : (b : Sequence).IsBounded) :
    (a * b : Sequence).IsBounded := by sorry

end Chapter5
