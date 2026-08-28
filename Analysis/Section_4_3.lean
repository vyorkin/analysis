import Mathlib.Tactic

/-!
# Analysis I, раздел 4.3: Абсолютная величина и возведение в степень

Я старался сделать перевод максимально точным перефразированием оригинального текста. Когда
приходилось выбирать между более идиоматичным Lean-решением и более точным переводом, я, как
правило, выбирал второе. В частности, местами Lean-код можно было бы "заголфить", сделав его более
элегантным и идиоматичным, но я сознательно этого избегал.

Основные конструкции и результаты этого раздела:

- Базовые свойства абсолютной величины и возведения в степень на рациональных числах (здесь мы
  используем рациональные числа Mathlib {lean}`ℚ`, а не рациональные числа раздела 4.2).

Примечание: чтобы избежать конфликта обозначений, мы используем стандартные определения Mathlib
для абсолютной величины и возведения в степень. Поэтому некоторые упражнения здесь можно решить
довольно легко, используя Mathlib API для этих операций. Однако суть упражнений в том, чтобы
решать их, используя API, предоставляемый этим разделом, а также более базовое Mathlib API для
рациональных чисел, не ссылающееся ни на абсолютную величину, ни на возведение в степень.

## Советы от прошлых пользователей

Пользователи, прошедшие упражнения этого раздела, могут присылать свои советы для будущих
пользователей в виде PR.

- (Добавьте совет сюда)

-/


/--
  Это определение должно быть дано вне пространства имён раздела 4.3 по техническим причинам.
-/
def Rat.Close (ε : ℚ) (x y : ℚ) := |x-y| ≤ ε


namespace Section_4_3

/-- Definition 4.3.1 (Абсолютная величина) -/
abbrev abs (x : ℚ) : ℚ :=
  if x > 0
  then x
  else (if x < 0 then -x else 0)

/-- Definition 4.3.1 (Абсолютная величина) (случай положительного числа) -/
theorem abs_of_pos {x : ℚ} (hx : 0 < x) : abs x = x := by grind

/-- Definition 4.3.1 (Абсолютная величина) (случай отрицательного числа) -/
theorem abs_of_neg {x : ℚ} (hx : x < 0) : abs x = -x := by grind

/-- Definition 4.3.1 (Абсолютная величина) (случай нуля) -/
theorem abs_of_zero : abs 0 = 0 := rfl

/--
  (Не из учебника) Это определение абсолютной величины согласуется с определением из Mathlib.
  Далее мы используем абсолютную величину из Mathlib.
-/
theorem abs_eq_abs (x : ℚ) : abs x = |x| := by
  sorry

abbrev dist (x y : ℚ) := |x - y|

/--
  Definition 4.3.2 (Расстояние).
  Здесь мы избегаем понятия расстояния из Mathlib, потому что оно вещественнозначное.
-/
theorem dist_eq (x y : ℚ) : dist x y = |x-y| := rfl

/-- Proposition 4.3.3(a) (неотрицательность) / Exercise 4.3.1 -/
theorem abs_nonneg (x : ℚ) : |x| ≥ 0 := by sorry

/-- Proposition 4.3.3(a) (обращается в ноль тогда и только тогда, когда само число ноль) / Exercise 4.3.1 -/
theorem abs_eq_zero_iff (x : ℚ) : |x| = 0 ↔ x = 0 := by sorry

/-- Proposition 4.3.3(b) / Exercise 4.3.1 -/
theorem abs_add (x y : ℚ) : |x + y| ≤ |x| + |y| := by sorry

/-- Proposition 4.3.3(c) (двусторонняя оценка) / Exercise 4.3.1 -/
theorem abs_le_iff (x y : ℚ) : -y ≤ x ∧ x ≤ y ↔ |x| ≤ y := by sorry

/-- Proposition 4.3.3(c) (ограничено собственной абсолютной величиной) / Exercise 4.3.1 -/
theorem le_abs (x : ℚ) : -|x| ≤ x ∧ x ≤ |x| := by sorry

/-- Proposition 4.3.3(d) (мультипликативность) / Exercise 4.3.1 -/
theorem abs_mul (x y : ℚ) : |x * y| = |x| * |y| := by sorry

/-- Proposition 4.3.3(d) (отрицание) / Exercise 4.3.1 -/
theorem abs_neg (x : ℚ) : |-x| = |x| := by sorry

/-- Proposition 4.3.3(e) (неотрицательность) / Exercise 4.3.1 -/
theorem dist_nonneg (x y : ℚ) : dist x y ≥ 0 := by sorry

/-- Proposition 4.3.3(e) (обращается в ноль тогда и только тогда, когда числа равны) / Exercise 4.3.1 -/
theorem dist_eq_zero_iff (x y : ℚ) : dist x y = 0 ↔ x = y := by
  sorry

/-- Proposition 4.3.3(f) / Exercise 4.3.1 -/
theorem dist_symm (x y : ℚ) : dist x y = dist y x := by sorry

/-- Proposition 4.3.3(g) / Exercise 4.3.1 -/
theorem dist_le (x y z : ℚ) : dist x z ≤ dist x y + dist y z := by sorry

/--
  Definition 4.3.4 (ε-близость).
  В тексте это понятие не определено для нулевого или отрицательного ε,
  но в Lean удобнее присвоить "мусорное" определение в этом случае.
  Это также позволяет несколько ослабить гипотезы в следующих далее леммах.
-/
theorem close_iff (ε x y : ℚ) : ε.Close x y ↔ |x - y| ≤ ε := by rfl

/-- Examples 4.3.6 (a) -/
example : (0.1 : ℚ).Close (0.99 : ℚ) (1.01 : ℚ) := by sorry

/-- Examples 4.3.6 (b) -/
example : ¬ (0.01 : ℚ).Close (0.99 : ℚ) (1.01 : ℚ) := by sorry

/-- Examples 4.3.6 (c) -/
example (ε : ℚ) (hε : ε > 0) : ε.Close 2 2 := by sorry

-- Каждое число `0`-близко к самому себе: `dist x x = 0 ≤ 0`
theorem close_refl (x : ℚ) : (0 : ℚ).Close x x := by sorry

/-- Proposition 4.3.7(a) / Exercise 4.3.2 -/
theorem eq_if_close (x y : ℚ) : x = y ↔ ∀ ε : ℚ, ε > 0 → ε.Close x y := by sorry

/-- Proposition 4.3.7(b) / Exercise 4.3.2 -/
theorem close_symm (ε x y : ℚ) : ε.Close x y ↔ ε.Close y x := by sorry

/-- Proposition 4.3.7(c) / Exercise 4.3.2 -/
theorem close_trans {ε δ x y z : ℚ} (hxy : ε.Close x y) (hyz : δ.Close y z) :
  (ε + δ).Close x z := by sorry

/-- Proposition 4.3.7(d) (addition) / Exercise 4.3.2 -/
theorem add_close {ε δ x y z w : ℚ} (hxy : ε.Close x y) (hzw : δ.Close z w) :
  (ε + δ).Close (x+z) (y+w) := by sorry

/-- Proposition 4.3.7(d) (subtraction) / Exercise 4.3.2 -/
theorem sub_close {ε δ x y z w : ℚ} (hxy : ε.Close x y) (hzw : δ.Close z w) :
  (ε + δ).Close (x-z) (y-w) := by sorry

/-- Proposition 4.3.7(e) / Exercise 4.3.2, слегка усиленное -/
theorem close_mono {ε ε' x y : ℚ} (hxy : ε.Close x y) (hε : ε' ≥  ε) :
  ε'.Close x y := by sorry

/-- Proposition 4.3.7(f) / Exercise 4.3.2 -/
theorem close_between {ε x y z w : ℚ} (hxy : ε.Close x y) (hxz : ε.Close x z)
  (hbetween : (y ≤ w ∧ w ≤ z) ∨ (z ≤ w ∧ w ≤ y)) : ε.Close x w := by sorry

/-- Proposition 4.3.7(g) / Exercise 4.3.2 -/
theorem close_mul_right {ε x y z : ℚ} (hxy : ε.Close x y) :
  (ε*|z|).Close (x * z) (y * z) := by sorry

/-- Proposition 4.3.7(h) / Exercise 4.3.2 -/
theorem close_mul_mul {ε δ x y z w : ℚ} (hxy : ε.Close x y) (hzw : δ.Close z w) :
  (ε*|z|+δ*|x|+ε*δ).Close (x * z) (y * w) := by
  -- Это доказательство написано так, чтобы следовать структуре оригинального текста,
  -- хотя неотрицательность ε и δ подразумевается и
  -- не нужно указывать её в качестве явных гипотез.
  have hε : ε ≥ 0 := le_trans (abs_nonneg _) hxy
  set a := y-x
  have ha : y = x + a := by grind
  have haε : |a| ≤ ε := by rwa [close_symm, close_iff] at hxy
  set b := w-z
  have hb : w = z + b := by grind
  have hbδ : |b| ≤ δ := by rwa [close_symm, close_iff] at hzw
  have : y*w = x * z + a * z + x * b + a * b := by grind
  rw [close_symm, close_iff]
  calc
    _ = |a * z + b * x + a * b| := by grind
    _ ≤ |a * z + b * x| + |a * b| := abs_add _ _
    _ ≤ |a * z| + |b * x| + |a * b| := by grind [abs_add]
    _ = |a| * |z| + |b| * |x| + |a| * |b| := by grind [abs_mul]
    _ ≤ _ := by gcongr

/-- Этого варианта Proposition 4.3.7(h) не было в учебнике,
    но он может пригодиться в некоторых последующих упражнениях. -/
theorem close_mul_mul' {ε δ x y z w : ℚ} (hxy : ε.Close x y) (hzw : δ.Close z w) :
  (ε*|z|+δ*|y|).Close (x * z) (y * w) := by
    sorry

/-- Definition 4.3.9 (возведение в степень) (базовый случай).
    Здесь мы используем определение из Mathlib. -/
lemma pow_zero (x : ℚ) : x^0 = 1 := _root_.pow_zero x

example : (0 : ℚ)^0 = 1 := pow_zero 0

/-- Definition 4.3.9 (возведение в степень) (индуктивный шаг).
    Здесь мы используем определение из Mathlib. -/
lemma pow_succ (x : ℚ) (n : ℕ) : x^(n+1) = x^n * x :=
  _root_.pow_succ x n

/-- Proposition 4.3.10(a) (Свойства возведения в степень, I) (сумма показателей) / Exercise 4.3.3 -/
theorem pow_add (x : ℚ) (m n : ℕ) : x^n * x^m = x^(n+m) := by sorry

/-- Proposition 4.3.10(a) (Свойства возведения в степень, I) (произведение показателей) / Exercise 4.3.3 -/
theorem pow_mul (x : ℚ) (m n : ℕ) : (x^n)^m = x^(n*m) := by sorry

/-- Proposition 4.3.10(a) (Свойства возведения в степень, I) (произведение оснований) / Exercise 4.3.3 -/
theorem mul_pow (x y : ℚ) (n : ℕ) : (x*y)^n = x^n * y^n := by sorry

/-- Proposition 4.3.10(b) (Свойства возведения в степень, I) / Exercise 4.3.3 -/
theorem pow_eq_zero (x : ℚ) (n : ℕ) (hn : 0 < n) : x^n = 0 ↔ x = 0 := by sorry

/-- Proposition 4.3.10(c) (Свойства возведения в степень, I) (неотрицательность) / Exercise 4.3.3 -/
theorem pow_nonneg {x : ℚ} (n : ℕ) (hx : x ≥ 0) : x^n ≥ 0 := by sorry

/-- Proposition 4.3.10(c) (Свойства возведения в степень, I) (положительность) / Exercise 4.3.3 -/
theorem pow_pos {x : ℚ} (n : ℕ) (hx : x > 0) : x^n > 0 := by sorry

/-- Proposition 4.3.10(c) (Свойства возведения в степень, I) (монотонность) / Exercise 4.3.3 -/
theorem pow_ge_pow (x y : ℚ) (n : ℕ) (hxy : x ≥ y) (hy : y ≥ 0) : x^n ≥ y^n := by sorry

/-- Proposition 4.3.10(c) (Свойства возведения в степень, I) (строгое неравенство) / Exercise 4.3.3 -/
theorem pow_gt_pow (x y : ℚ) (n : ℕ) (hxy : x > y) (hy : y ≥ 0) (hn : n > 0) : x^n > y^n := by sorry

/-- Proposition 4.3.10(d) (Свойства возведения в степень, I) / Exercise 4.3.3 -/
theorem pow_abs (x : ℚ) (n : ℕ) : |x|^n = |x^n| := by sorry

/--
  Definition 4.3.11 (Возведение в отрицательную степень).
  Здесь мы используем понятие возведения в целую степень из Mathlib
-/
theorem zpow_neg (x : ℚ) (n : ℕ) : x^(-(n : ℤ)) = 1/(x^n) := by simp

example (x : ℚ) : x^(-3 : ℤ) = 1/(x^3) := zpow_neg x 3

example (x : ℚ) : x^(-3 : ℤ) = 1/(x*x*x) := by convert zpow_neg x 3; ring

-- Возведение в степень `n : ℤ`, приведённую из `ℕ`, совпадает с обычным возведением в натуральную степень `x^n`
theorem pow_eq_zpow (x : ℚ) (n : ℕ) : x^(n : ℤ) = x^n := zpow_natCast x n

/-- Proposition 4.3.12(a) (Свойства возведения в степень, II) (сумма показателей) / Exercise 4.3.4 -/
theorem zpow_add (x : ℚ) (n m : ℤ) (hx : x ≠ 0) : x^n * x^m = x^(n+m) := by sorry

/-- Proposition 4.3.12(a) (Свойства возведения в степень, II) (произведение показателей) / Exercise 4.3.4 -/
theorem zpow_mul (x : ℚ) (n m : ℤ) : (x^n)^m = x^(n*m) := by sorry

/-- Proposition 4.3.12(a) (Свойства возведения в степень, II) (произведение оснований) / Exercise 4.3.4 -/
theorem mul_zpow (x y : ℚ) (n : ℤ) : (x*y)^n = x^n * y^n := by sorry

/-- Proposition 4.3.12(b) (Свойства возведения в степень, II) (положительность) / Exercise 4.3.4 -/
theorem zpow_pos {x : ℚ} (n : ℤ) (hx : x > 0) : x^n > 0 := by sorry

/-- Proposition 4.3.12(b) (Свойства возведения в степень, II) (монотонность) / Exercise 4.3.4 -/
theorem zpow_ge_zpow {x y : ℚ} {n : ℤ} (hxy : x ≥ y) (hy : y > 0) (hn : n > 0) : x^n ≥ y^n := by sorry

-- Для отрицательного показателя степени монотонность обращается: из `x ≥ y > 0` следует `x^n ≤ y^n`
theorem zpow_ge_zpow_ofneg {x y : ℚ} {n : ℤ} (hxy : x ≥ y) (hy : y > 0) (hn : n < 0) : x^n ≤ y^n := by
  sorry

/-- Proposition 4.3.12(c) (Свойства возведения в степень, II) / Exercise 4.3.4 -/
theorem zpow_inj {x y : ℚ} {n : ℤ} (hx : x > 0) (hy : y > 0) (hn : n ≠ 0) (hxy : x^n = y^n) : x = y := by
  sorry

/-- Proposition 4.3.12(d) (Свойства возведения в степень, II) / Exercise 4.3.4 -/
theorem zpow_abs (x : ℚ) (n : ℤ) : |x|^n = |x^n| := by sorry

/-- Exercise 4.3.5 -/
theorem two_pow_geq (N : ℕ) : 2^N ≥ N := by sorry
