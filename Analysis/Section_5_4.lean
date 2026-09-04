import Mathlib.Tactic
import Analysis.Section_5_3


/-!
# Analysis I, раздел 5.4: Упорядочивание вещественных чисел

Я старался сделать перевод максимально точным перефразированием оригинального текста. Когда
приходилось выбирать между более идиоматичным Lean-решением и более точным переводом, я, как
правило, выбирал второе. В частности, местами Lean-код можно было бы "заголфить", сделав его более
элегантным и идиоматичным, но я сознательно этого избегал.

Основные конструкции и результаты этого раздела:

- Упорядочивание на вещественной прямой

## Советы от прошлых пользователей

Пользователи, прошедшие упражнения этого раздела, могут присылать свои советы для будущих
пользователей в виде PR.

- (Добавьте совет сюда)

-/

namespace Chapter5

/--
  Определение 5.4.1 (последовательности, отделённые от нуля с учётом знака). Последовательности
  индексируются начиная с нуля, так как это удобнее для целей Mathlib.
-/
abbrev BoundedAwayPos (a : ℕ → ℚ) : Prop :=
  ∃ (c : ℚ), c > 0 ∧ ∀ n, a n ≥ c

/-- Определение 5.4.1 (последовательности, отделённые от нуля с учётом знака). -/
abbrev BoundedAwayNeg (a : ℕ → ℚ) : Prop :=
  ∃ (c : ℚ), c > 0 ∧ ∀ n, a n ≤ -c

/-- Определение 5.4.1 (последовательности, отделённые от нуля с учётом знака). -/
theorem boundedAwayPos_def (a : ℕ → ℚ) : BoundedAwayPos a ↔ ∃ (c : ℚ), c > 0 ∧ ∀ n, a n ≥ c := by
  rfl

/-- Определение 5.4.1 (последовательности, отделённые от нуля с учётом знака). -/
theorem boundedAwayNeg_def (a : ℕ → ℚ) : BoundedAwayNeg a ↔ ∃ (c : ℚ), c > 0 ∧ ∀ n, a n ≤ -c := by
  rfl

/-- Примеры 5.4.2 -/
example : BoundedAwayPos (fun n ↦ 1 + 10^(-(n : ℤ)-1)) := ⟨ 1, by norm_num, by intros; simp; positivity ⟩

/-- Примеры 5.4.2 -/
example : BoundedAwayNeg (fun n ↦ -1 - 10^(-(n : ℤ)-1)) := ⟨ 1, by norm_num, by intros; simp; positivity ⟩

/-- Примеры 5.4.2 -/
example : ¬ BoundedAwayPos (fun n ↦ (-1)^n) := by
  intro ⟨ c, h1, h2 ⟩; specialize h2 1; grind

/-- Примеры 5.4.2 -/
example : ¬ BoundedAwayNeg (fun n ↦ (-1)^n) := by
  intro ⟨ c, h1, h2 ⟩; specialize h2 0; grind

/-- Примеры 5.4.2 -/
example : BoundedAwayZero (fun n ↦ (-1)^n) := ⟨ 1, by norm_num, by intros; simp ⟩

-- последовательность, отделённая от нуля положительной константой, отделена от нуля и в обычном смысле
theorem BoundedAwayZero.boundedAwayPos {a : ℕ → ℚ} (ha : BoundedAwayPos a) : BoundedAwayZero a := by
  peel 3 ha with c h1 n h2; rwa [abs_of_nonneg (by linarith)]

-- последовательность, отделённая от нуля отрицательной константой, отделена от нуля и в обычном смысле
theorem BoundedAwayZero.boundedAwayNeg {a : ℕ → ℚ} (ha : BoundedAwayNeg a) : BoundedAwayZero a := by
  peel 3 ha with c h1 n h2; rw [abs_of_neg (by linarith)]; linarith

-- последовательность не может быть одновременно отделена от нуля и сверху, и снизу
theorem not_boundedAwayPos_boundedAwayNeg {a : ℕ → ℚ} : ¬ (BoundedAwayPos a ∧ BoundedAwayNeg a) := by
  intro ⟨ ⟨ _, _, h2⟩ , ⟨ _, _, h4 ⟩ ⟩; linarith [h2 0, h4 0]

abbrev Real.IsPos (x : Real) : Prop :=
  ∃ a : ℕ → ℚ, BoundedAwayPos a ∧ (a : Sequence).IsCauchy ∧ x = LIM a

abbrev Real.IsNeg (x : Real) : Prop :=
  ∃ a : ℕ → ℚ, BoundedAwayNeg a ∧ (a : Sequence).IsCauchy ∧ x = LIM a

-- разворачивает `Real.IsPos` в определение: `x` положительно, если `x = LIM a` для некоторой последовательности Коши `a`, отделённой от нуля положительной константой
theorem Real.isPos_def (x : Real) :
    IsPos x ↔ ∃ a : ℕ → ℚ, BoundedAwayPos a ∧ (a : Sequence).IsCauchy ∧ x = LIM a := by rfl

-- разворачивает `Real.IsNeg` в определение: `x` отрицательно, если `x = LIM a` для некоторой последовательности Коши `a`, отделённой от нуля отрицательной константой
theorem Real.isNeg_def (x : Real) :
    IsNeg x ↔ ∃ a : ℕ → ℚ, BoundedAwayNeg a ∧ (a : Sequence).IsCauchy ∧ x = LIM a := by rfl

/-- Утверждение 5.4.4 (базовые свойства положительных вещественных чисел) / Упражнение 5.4.1 -/
theorem Real.trichotomous (x : Real) : x = 0 ∨ x.IsPos ∨ x.IsNeg := by sorry

/-- Утверждение 5.4.4 (базовые свойства положительных вещественных чисел) / Упражнение 5.4.1 -/
theorem Real.not_zero_pos (x : Real) : ¬(x = 0 ∧ x.IsPos) := by sorry

-- положительное вещественное число не равно нулю
theorem Real.nonzero_of_pos {x : Real} (hx : x.IsPos) : x ≠ 0 := by
  have := not_zero_pos x
  simpa [hx] using this

/-- Утверждение 5.4.4 (базовые свойства положительных вещественных чисел) / Упражнение 5.4.1 -/
theorem Real.not_zero_neg (x : Real) : ¬(x = 0 ∧ x.IsNeg) := by sorry

-- отрицательное вещественное число не равно нулю
theorem Real.nonzero_of_neg {x : Real} (hx : x.IsNeg) : x ≠ 0 := by
  have := not_zero_neg x
  simpa [hx] using this

/-- Утверждение 5.4.4 (базовые свойства положительных вещественных чисел) / Упражнение 5.4.1 -/
theorem Real.not_pos_neg (x : Real) : ¬(x.IsPos ∧ x.IsNeg) := by sorry

/-- Утверждение 5.4.4 (базовые свойства положительных вещественных чисел) / Упражнение 5.4.1 -/
@[simp]
theorem Real.neg_iff_pos_of_neg (x : Real) : x.IsNeg ↔ (-x).IsPos := by sorry

/-- Утверждение 5.4.4 (базовые свойства положительных вещественных чисел) / Упражнение 5.4.1 -/
theorem Real.pos_add {x y : Real} (hx : x.IsPos) (hy : y.IsPos) : (x+y).IsPos := by sorry

/-- Утверждение 5.4.4 (базовые свойства положительных вещественных чисел) / Упражнение 5.4.1 -/
theorem Real.pos_mul {x y : Real} (hx : x.IsPos) (hy : y.IsPos) : (x*y).IsPos := by sorry

-- приведённое к `Real` рациональное число `q` положительно тогда и только тогда, когда `q > 0`
theorem Real.pos_of_coe (q : ℚ) : (q : Real).IsPos ↔ q > 0 := by sorry

-- приведённое к `Real` рациональное число `q` отрицательно тогда и только тогда, когда `q < 0`
theorem Real.neg_of_coe (q : ℚ) : (q : Real).IsNeg ↔ q < 0 := by sorry

open Classical in
/-- Здесь нужна классическая логика, так как {name}`IsPos` и {name}`IsNeg` неразрешимы. -/
noncomputable abbrev Real.abs (x : Real) : Real := if x.IsPos then x else (if x.IsNeg then -x else 0)

/-- Определение 5.4.5 (абсолютная величина) -/
@[simp]
theorem Real.abs_of_pos (x : Real) (hx : x.IsPos) : abs x = x := by
  simp [abs, hx]

/-- Определение 5.4.5 (абсолютная величина) -/
@[simp]
theorem Real.abs_of_neg (x : Real) (hx : x.IsNeg) : abs x = -x := by
  have : ¬x.IsPos := by have := not_pos_neg x; simpa [hx] using this
  simp [abs, hx, this]

/-- Определение 5.4.5 (абсолютная величина) -/
@[simp]
theorem Real.abs_of_zero : abs 0 = 0 := by
  have hpos : ¬(0 : Real).IsPos := by have := not_zero_pos 0; simpa using this
  have hneg : ¬(0 : Real).IsNeg := by have := not_zero_neg 0; simpa using this
  simp [abs, hpos, hneg]

/-- Определение 5.4.6 (упорядочивание вещественных чисел) -/
instance Real.instLT : LT Real where
  lt x y := (x-y).IsNeg

/-- Определение 5.4.6 (упорядочивание вещественных чисел) -/
instance Real.instLE : LE Real where
  le x y := (x < y) ∨ (x = y)

-- разворачивает `<` в определение: `x < y` означает, что разность `x - y` отрицательна
theorem Real.lt_iff (x y : Real) : x < y ↔ (x-y).IsNeg := by rfl
-- разворачивает `≤` в определение: `x ≤ y` означает `x < y` или `x = y`
theorem Real.le_iff (x y : Real) : x ≤ y ↔ (x < y) ∨ (x = y) := by rfl

-- разворачивает `>` в определение: `x > y` означает, что разность `x - y` положительна
theorem Real.gt_iff (x y : Real) : x > y ↔ (x-y).IsPos := by sorry
-- разворачивает `≥` в определение: `x ≥ y` означает `x > y` или `x = y`
theorem Real.ge_iff (x y : Real) : x ≥ y ↔ (x > y) ∨ (x = y) := by sorry

-- порядок на `ℚ` согласован с порядком на `Real`: `q < q'` тогда и только тогда, когда `(q : Real) < (q' : Real)`
theorem Real.lt_of_coe (q q' : ℚ) : q < q' ↔ (q : Real) < (q' : Real) := by sorry

-- то же для `>`: `q > q'` тогда и только тогда, когда `(q : Real) > (q' : Real)`
theorem Real.gt_of_coe (q q' : ℚ) : q > q' ↔ (q : Real) > (q' : Real) := Real.lt_of_coe _ _

-- `x` положительно (`IsPos`) тогда и только тогда, когда `x > 0` в смысле порядка
theorem Real.isPos_iff (x : Real) : x.IsPos ↔ x > 0 := by sorry
-- `x` отрицательно (`IsNeg`) тогда и только тогда, когда `x < 0` в смысле порядка
theorem Real.isNeg_iff (x : Real) : x.IsNeg ↔ x < 0 := by sorry

/-- Утверждение 5.4.7(a) (трихотомия порядка) / Упражнение 5.4.2 -/
theorem Real.trichotomous' (x y : Real) : x > y ∨ x < y ∨ x = y := by sorry

/-- Утверждение 5.4.7(a) (трихотомия порядка) / Упражнение 5.4.2 -/
theorem Real.not_gt_and_lt (x y : Real) : ¬ (x > y ∧ x < y):= by sorry

/-- Утверждение 5.4.7(a) (трихотомия порядка) / Упражнение 5.4.2 -/
theorem Real.not_gt_and_eq (x y : Real) : ¬ (x > y ∧ x = y):= by sorry

/-- Утверждение 5.4.7(a) (трихотомия порядка) / Упражнение 5.4.2 -/
theorem Real.not_lt_and_eq (x y : Real) : ¬ (x < y ∧ x = y):= by sorry

/-- Утверждение 5.4.7(b) (антисимметричность порядка) / Упражнение 5.4.2 -/
theorem Real.antisymm (x y : Real) : x < y ↔ y > x := by sorry

/-- Утверждение 5.4.7(c) (транзитивность порядка) / Упражнение 5.4.2 -/
theorem Real.lt_trans {x y z : Real} (hxy : x < y) (hyz : y < z) : x < z := by sorry

/-- Утверждение 5.4.7(d) (сложение сохраняет порядок) / Упражнение 5.4.2 -/
theorem Real.add_lt_add_right {x y : Real} (z : Real) (hxy : x < y) : x + z < y + z := by sorry

/-- Утверждение 5.4.7(e) (умножение на положительное число сохраняет порядок) / Упражнение 5.4.2 -/
theorem Real.mul_lt_mul_right {x y z : Real} (hxy : x < y) (hz : z.IsPos) : x * z < y * z := by
  rw [antisymm, gt_iff] at hxy ⊢; convert pos_mul hxy hz using 1; ring

/-- Утверждение 5.4.7(e) (умножение на положительное число сохраняет порядок) / Упражнение 5.4.2 -/
theorem Real.mul_le_mul_left {x y z : Real} (hxy : x ≤ y) (hz : z.IsPos) : z * x ≤ z * y := by sorry

-- произведение положительного и отрицательного вещественных чисел отрицательно
theorem Real.mul_pos_neg {x y : Real} (hx : x.IsPos) (hy : y.IsNeg) : (x * y).IsNeg := by
  sorry

open Classical in
/--
  (Не из учебника) {name}`Real` обладает структурой линейного порядка. Этот порядок не является
  вычислимым, поэтому для обеспечения разрешимости требуется классическая логика.
-/
noncomputable instance Real.instLinearOrder : LinearOrder Real where
  le_refl := sorry
  le_trans := sorry
  lt_iff_le_not_ge := sorry
  le_antisymm := sorry
  le_total := sorry
  toDecidableLE := Classical.decRel _

/--
  (Не из учебника) {name}`LinearOrder` несёт с собой определение абсолютной величины
  {lean (type := "Real → Real")}`(|·|)`. Покажите, что оно согласуется с нашим более ранним
  определением.
-/
theorem Real.abs_eq_abs (x : Real) : |x| = abs x := by sorry

/-- Утверждение 5.4.8 -/
theorem Real.inv_of_pos {x : Real} (hx : x.IsPos) : x⁻¹.IsPos := by
  observe hnon : x ≠ 0
  observe hident : x⁻¹ * x = 1
  have hinv_non : x⁻¹ ≠ 0 := by contrapose! hident; simp [hident]
  have hnonneg : ¬x⁻¹.IsNeg := by
    intro h
    observe : (x * x⁻¹).IsNeg
    have id : -(1 : Real) = (-1 : ℚ) := by simp
    simp only [neg_iff_pos_of_neg, id, pos_of_coe, self_mul_inv hnon] at this
    linarith
  have trich := trichotomous x⁻¹
  simpa [hinv_non, hnonneg] using trich

-- частное двух положительных вещественных чисел положительно
theorem Real.div_of_pos {x y : Real} (hx : x.IsPos) (hy : y.IsPos) : (x/y).IsPos := by sorry

-- обращение положительных чисел меняет порядок на противоположный: из `x > y` следует `x⁻¹ < y⁻¹`
theorem Real.inv_of_gt {x y : Real} (hx : x.IsPos) (hy : y.IsPos) (hxy : x > y) : x⁻¹ < y⁻¹ := by
  observe hxnon : x ≠ 0
  observe hynon : y ≠ 0
  observe hxinv : x⁻¹.IsPos
  by_contra! this
  have : (1 : Real) > 1 := calc
    1 = x * x⁻¹ := (self_mul_inv hxnon).symm
    _ > y * x⁻¹ := mul_lt_mul_right hxy hxinv
    _ ≥ y * y⁻¹ := mul_le_mul_left this hy
    _ = _ := self_mul_inv hynon
  simp at this

/-- (Не из учебника) {name}`Real` обладает структурой строго упорядоченного кольца. -/
instance Real.instIsStrictOrderedRing : IsStrictOrderedRing Real where
  add_le_add_left := by sorry
  add_le_add_right := by sorry
  mul_lt_mul_of_pos_left := by sorry
  mul_lt_mul_of_pos_right := by sorry
  le_of_add_le_add_left := by sorry
  zero_le_one := by sorry

/-- Утверждение 5.4.9 (неотрицательные вещественные числа замкнуты) -/
theorem Real.LIM_of_nonneg {a : ℕ → ℚ} (ha : ∀ n, a n ≥ 0) (hcauchy : (a : Sequence).IsCauchy) : 
    LIM a ≥ 0 := by
  -- Это доказательство написано так, чтобы следовать структуре оригинального текста.
  by_contra! hlim
  set x := LIM a
  rw [←isNeg_iff, isNeg_def] at hlim; choose b hb hb_cauchy hlim using hlim
  rw [boundedAwayNeg_def] at hb; choose c cpos hb using hb
  have claim1 : ∀ n, ¬ (c/2).Close (a n) (b n) := by
    intro n; specialize ha n; specialize hb n
    simp [Section_4_3.close_iff]
    calc
      _ < c := by linarith
      _ ≤ a n - b n := by linarith
      _ ≤ _ := le_abs_self _
  have claim2 : ¬(c/2).EventuallyClose (a : Sequence) (b : Sequence) := by
    contrapose! claim1; rw [Rat.eventuallyClose_iff] at claim1; peel claim1 with N claim1; grind [Section_4_3.close_iff]
  have claim3 : ¬Sequence.Equiv a b := by contrapose! claim2; rw [Sequence.equiv_def] at claim2; solve_by_elim [half_pos]
  simp_rw [x, LIM_eq_LIM hcauchy hb_cauchy] at hlim
  contradiction

/-- Следствие 5.4.10 -/
theorem Real.LIM_mono {a b : ℕ → ℚ} (ha : (a : Sequence).IsCauchy) (hb : (b : Sequence).IsCauchy)
  (hmono : ∀ n, a n ≤ b n) : 
    LIM a ≤ LIM b := by
  -- Это доказательство написано так, чтобы следовать структуре оригинального текста.
  have := LIM_of_nonneg (a := b - a) (by intro n; simp [hmono n]) (Sequence.IsCauchy.sub hb ha)
  rw [←Real.LIM_sub hb ha] at this; linarith

/-- Замечание 5.4.11 -/
theorem Real.LIM_mono_fail : 
    ∃ (a b : ℕ → ℚ), (a : Sequence).IsCauchy
    ∧ (b : Sequence).IsCauchy
    ∧ (∀ n, a n > b n)
    ∧ ¬LIM a > LIM b := by
  use (fun n ↦ 1 + 1/((n : ℚ) + 1))
  use (fun n ↦ 1 - 1/((n : ℚ) + 1))
  sorry

/-- Утверждение 5.4.12 (ограничение вещественных чисел рациональными) -/
theorem Real.exists_rat_le_and_nat_gt {x : Real} (hx : x.IsPos) : 
    (∃ q : ℚ, q > 0 ∧ (q : Real) ≤ x) ∧ ∃ N : ℕ, x < (N : Real) := by
  -- Это доказательство написано так, чтобы следовать структуре оригинального текста.
  rw [isPos_def] at hx; choose a hbound hcauchy heq using hx
  rw [boundedAwayPos_def] at hbound; choose q hq hbound using hbound
  have := Sequence.isBounded_of_isCauchy hcauchy
  rw [Sequence.isBounded_def] at this; choose r hr this using this
  simp [Sequence.boundedBy_def] at this
  refine ⟨ ⟨ q, hq, ?_ ⟩, ?_ ⟩
  . convert LIM_mono (Sequence.IsCauchy.const _) hcauchy hbound
    exact Real.ratCast_def q
  choose N hN using exists_nat_gt r; use N
  calc
    x ≤ r := by
      rw [Real.ratCast_def r]
      convert LIM_mono hcauchy (Sequence.IsCauchy.const r) _
      intro n; specialize this n; simp at this
      exact (le_abs_self _).trans this
    _ < ((N : ℚ) : Real) := by simp [hN]
    _ = N := rfl

/-- Следствие 5.4.13 (архимедово свойство) -/
theorem Real.le_mul {ε : Real} (hε : ε.IsPos) (x : Real) : ∃ M : ℕ, M > 0 ∧ M * ε > x := by
  -- Это доказательство написано так, чтобы следовать структуре оригинального текста.
  obtain rfl | hx | hx := trichotomous x
  . use 1; simpa [isPos_iff] using hε
  . choose N hN using (exists_rat_le_and_nat_gt (div_of_pos hx hε)).2
    set M := N+1; refine ⟨ M, by positivity, ?_ ⟩
    replace hN : x/ε < M := hN.trans (by simp [M])
    simp
    convert mul_lt_mul_right hN hε
    rw [isPos_iff] at hε; field_simp
  use 1; simp_all [isPos_iff]; linarith

/-- Утверждение 5.4.14 / Упражнение 5.4.5 -/
theorem Real.rat_between {x y : Real} (hxy : x < y) : ∃ q : ℚ, x < (q : Real) ∧ (q : Real) < y := by sorry

/-- Упражнение 5.4.3 -/
theorem Real.floor_exist (x : Real) : ∃! n : ℤ, (n : Real) ≤ x ∧ x < (n : Real)+1 := by sorry

/-- Упражнение 5.4.4 -/
theorem Real.exist_inv_nat_le {x : Real} (hx : x.IsPos) : ∃ N : ℤ, N>0 ∧ (N : Real)⁻¹ < x := by sorry

/-- Упражнение 5.4.6 (a) -/
theorem Real.dist_lt_iff (ε x y : Real) : |x-y| < ε ↔ y-ε < x ∧ x < y+ε := by sorry

/-- Упражнение 5.4.6 (b) -/
theorem Real.dist_le_iff (ε x y : Real) : |x-y| ≤ ε ↔ y-ε ≤ x ∧ x ≤ y+ε := by sorry

/-- Упражнение 5.4.7 (a) -/
theorem Real.le_add_eps_iff (x y : Real) : (∀ ε > 0, x ≤ y+ε) ↔ x ≤ y := by sorry

/-- Упражнение 5.4.7 (b) -/
theorem Real.dist_le_eps_iff (x y : Real) : (∀ ε > 0, |x-y| ≤ ε) ↔ x = y := by sorry

/-- Упражнение 5.4.8 (a) -/
theorem Real.LIM_of_le {x : Real} {a : ℕ → ℚ} (hcauchy : (a : Sequence).IsCauchy) (h : ∀ n, a n ≤ x) : 
    LIM a ≤ x := by sorry

/-- Упражнение 5.4.8 (b) -/
theorem Real.LIM_of_ge {x : Real} {a : ℕ → ℚ} (hcauchy : (a : Sequence).IsCauchy) (h : ∀ n, a n ≥ x) : 
    LIM a ≥ x := by sorry

-- максимум двух вещественных чисел равен `x`, если `x ≥ y`, и `y` иначе
theorem Real.max_eq (x y : Real) : max x y = if x ≥ y then x else y := max_def' x y

-- минимум двух вещественных чисел равен `x`, если `x ≤ y`, и `y` иначе
theorem Real.min_eq (x y : Real) : min x y = if x ≤ y then x else y := rfl

/-- Упражнение 5.4.9 (a) -/
theorem Real.neg_max (x y : Real) : max x y = - min (-x) (-y) := by sorry

/-- Упражнение 5.4.9 (b) -/
theorem Real.neg_min (x y : Real) : min x y = - max (-x) (-y) := by sorry

/-- Упражнение 5.4.9 (c) -/
theorem Real.max_comm (x y : Real) : max x y = max y x := by sorry

/-- Упражнение 5.4.9 (d) -/
theorem Real.max_self (x : Real) : max x x = x := by sorry

/-- Упражнение 5.4.9 (e) -/
theorem Real.max_add (x y z : Real) : max (x + z) (y + z) = max x y + z := by sorry

/-- Упражнение 5.4.9 (f) -/
theorem Real.max_mul (x y : Real) {z : Real} (hz : z.IsPos) : max (x * z) (y * z) = max x y * z := by
  sorry
/- Дополнительное упражнение (после 5.4.9 (f)): что произойдёт, если z отрицательно? -/

/-- Упражнение 5.4.9 (g) -/
theorem Real.min_comm (x y : Real) : min x y = min y x := by sorry

/-- Упражнение 5.4.9 (h) -/
theorem Real.min_self (x : Real) : min x x = x := by sorry

/-- Упражнение 5.4.9 (i) -/
theorem Real.min_add (x y z : Real) : min (x + z) (y + z) = min x y + z := by sorry

/-- Упражнение 5.4.9 (j) -/
theorem Real.min_mul (x y : Real) {z : Real} (hz : z.IsPos) : min (x * z) (y * z) = min x y * z := by
  sorry

/-- Упражнение 5.4.9 (k) -/
theorem Real.inv_max {x y : Real} (hx : x.IsPos) (hy : y.IsPos) : (max x y)⁻¹ = min x⁻¹ y⁻¹ := by sorry

/-- Упражнение 5.4.9 (l) -/
theorem Real.inv_min {x y : Real} (hx : x.IsPos) (hy : y.IsPos) : (min x y)⁻¹ = max x⁻¹ y⁻¹ := by sorry

/-- Не из учебника: рациональные числа отображаются в вещественные как гомоморфизм упорядоченных колец. -/
abbrev Real.ratCast_ordered_hom : ℚ →+*o Real where
  toRingHom := ratCast_hom
  monotone' := by sorry

end Chapter5
