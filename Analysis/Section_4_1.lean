import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

set_option doc.verso.suggestions false

/-!
# Analysis I, раздел 4.1: Целые числа

Я старался сделать перевод максимально точным перефразированием оригинального текста. Когда
приходилось выбирать между более идиоматичным Lean-решением и более точным переводом, я, как
правило, выбирал второе. В частности, местами Lean-код можно было бы "заголфить", сделав его более
элегантным и идиоматичным, но я сознательно этого избегал.

Основные конструкции и результаты этого раздела:

- Определение целых чисел "раздела 4.1", `Section_4_1.Int`, как формальных разностей `a —— b`
  натуральных чисел `a b:ℕ`, с точностью до эквивалентности. (Это фактор вспомогательного типа
  `Section_4_1.PreInt`, состоящего из формальных разностей без какой-либо наложенной
  эквивалентности.)

- Кольцевые операции и порядок на этих целых числах, а также вложение {lean}`ℕ`.

- Эквивалентность с целыми числами Mathlib {name}`_root_.Int` (или {lean}`ℤ`), которые мы будем
  использовать в дальнейшем.

## Советы от прошлых пользователей

Пользователи, прошедшие упражнения этого раздела, могут присылать свои советы для будущих
пользователей в виде PR.

- (Добавьте совет сюда)

-/

namespace Section_4_1

structure PreInt where
  minuend : ℕ
  subtrahend : ℕ

/-- Definition 4.1.1 -/
instance PreInt.instSetoid : Setoid PreInt where
  r a b := a.minuend + b.subtrahend = b.minuend + a.subtrahend
  iseqv := {
    refl := by sorry
    symm := by sorry
    trans := by
      -- Это доказательство написано так, чтобы следовать структуре оригинального текста.
      intro ⟨ a,b ⟩ ⟨ c,d ⟩ ⟨ e,f ⟩ h1 h2; simp_all
      have h3 := congrArg₂ (· + ·) h1 h2; simp at h3
      have : (a + f) + (c + d) = (e + b) + (c + d) := calc
        (a + f) + (c + d) = a + d + (c + f) := by abel
        _ = c + b + (e + d) := h3
        _ = (e + b) + (c + d) := by abel
      exact Nat.add_right_cancel this
    }

-- Эквивалентность формальных разностей `PreInt` в явном арифметическом виде: `(a,b) ≈ (c,d) ↔ a + d = c + b`
@[simp]
theorem PreInt.eq (a b c d : ℕ) : (⟨ a,b ⟩ : PreInt) ≈ ⟨ c,d ⟩ ↔ a + d = c + b := by rfl

abbrev Int := Quotient PreInt.instSetoid

abbrev Int.formalDiff (a b : ℕ)  : Int := Quotient.mk PreInt.instSetoid ⟨ a,b ⟩

infix:100 " —— " => Int.formalDiff

/-- Definition 4.1.1 (Целые числа, равенство) -/
theorem Int.eq (a b c d : ℕ) : a —— b = c —— d ↔ a + d = c + b :=
  ⟨ Quotient.exact, by intro h; exact Quotient.sound h ⟩

/-- Разрешимость равенства -/
instance Int.decidableEq : DecidableEq Int := by
  intro a b
  have : ∀ (n : PreInt) (m : PreInt),
      Decidable (Quotient.mk PreInt.instSetoid n = Quotient.mk PreInt.instSetoid m) := by
    intro ⟨ a,b ⟩ ⟨ c,d ⟩
    rw [eq]
    exact decEq _ _
  exact Quotient.recOnSubsingleton₂ a b this

/-- Definition 4.1.1 (Целые числа, существование представления) -/
theorem Int.eq_diff (n : Int) : ∃ a b, n = a —— b := by apply n.ind _; intro ⟨ a, b ⟩; use a, b

/-- Lemma 4.1.3 (Сложение определено корректно) -/
instance Int.instAdd : Add Int where
  add := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a+c) —— (b+d) ) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2
    simp [eq] at *
    omega)

/-- Definition 4.1.2 (Определение сложения) -/
theorem Int.add_eq (a b c d : ℕ) : a —— b + c —— d = (a+c)——(b+d) := Quotient.lift₂_mk _ _ _ _

/-- Lemma 4.1.3 (Умножение определено корректно, левый аргумент) -/
theorem Int.mul_congr_left (a b a' b' c d : ℕ) (h : a —— b = a' —— b') :
    (a*c+b*d) —— (a*d+b*c) = (a'*c+b'*d) —— (a'*d+b'*c) := by
  simp only [eq] at *
  calc
    _ = c*(a+b') + d*(a'+b) := by ring
    _ = c*(a'+b) + d*(a+b') := by rw [h]
    _ = _ := by ring

/-- Lemma 4.1.3 (Умножение определено корректно, правый аргумент) -/
theorem Int.mul_congr_right (a b c d c' d' : ℕ) (h : c —— d = c' —— d') :
    (a*c+b*d) —— (a*d+b*c) = (a*c'+b*d') —— (a*d'+b*c') := by
  simp only [eq] at *
  calc
    _ = a*(c+d') + b*(c'+d) := by ring
    _ = a*(c'+d) + b*(c+d') := by rw [h]
    _ = _ := by ring

/-- Lemma 4.1.3 (Умножение определено корректно, оба аргумента) -/
theorem Int.mul_congr {a b c d a' b' c' d' : ℕ} (h1 : a —— b = a' —— b') (h2 : c —— d = c' —— d') :
  (a*c+b*d) —— (a*d+b*c) = (a'*c'+b'*d') —— (a'*d'+b'*c') := by
  rw [mul_congr_left a b a' b' c d h1, mul_congr_right a' b' c d c' d' h2]

instance Int.instMul : Mul Int where
  mul := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a * c + b * d) —— (a * d + b * c)) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2
    exact mul_congr (Quotient.eq.mpr h1) (Quotient.eq.mpr h2)
    )

/-- Definition 4.1.2 (Умножение целых чисел) -/
theorem Int.mul_eq (a b c d : ℕ) : a —— b * c —— d = (a*c+b*d) —— (a*d+b*c) := Quotient.lift₂_mk _ _ _ _

instance Int.instOfNat {n : ℕ} : OfNat Int n where
  ofNat := n —— 0

instance Int.instNatCast : NatCast Int where
  natCast n := n —— 0

-- Числовой литерал `n : Int` — это формальная разность `n —— 0`
theorem Int.ofNat_eq (n : ℕ) : ofNat(n) = n —— 0 := rfl

-- Вложение натурального `n` в `Int` — это формальная разность `n —— 0`
theorem Int.natCast_eq (n : ℕ) : (n : Int) = n —— 0 := rfl

-- Вложение `ℕ → Int` согласовано с числовыми литералами: приведение литерала из `ℕ` в `Int` даёт тот же литерал
@[simp]
theorem Int.natCast_ofNat (n : ℕ) : ((ofNat(n) : ℕ) : Int) = ofNat(n) := by rfl

-- Числовые литералы `n` и `m` совпадают как `Int` тогда и только тогда, когда совпадают как `ℕ`
@[simp]
theorem Int.ofNat_inj (n m : ℕ) : (ofNat(n) : Int) = (ofNat(m) : Int) ↔ ofNat(n) = ofNat(m) := by
  simp only [ofNat_eq, eq, add_zero]; rfl

-- Вложение `ℕ → Int` инъективно
@[simp]
theorem Int.natCast_inj (n m : ℕ) : (n : Int) = (m : Int) ↔ n = m := by
  simp only [natCast_eq, eq, add_zero]

example : 3 = 3 —— 0 := rfl

example : 3 = 4 —— 1 := by rw [Int.ofNat_eq, Int.eq]

/-- (Не из учебника) 0 — единственное натуральное число, чей образ равен 0 -/
lemma Int.cast_eq_0_iff_eq_0 (n : ℕ) : (n : Int) = 0 ↔ n = 0 := by sorry

/-- Definition 4.1.4 (Отрицание целых чисел) / Exercise 4.1.2 -/
instance Int.instNeg : Neg Int where
  neg := Quotient.lift (fun ⟨ a, b ⟩ ↦ b —— a) (by sorry)

-- Отрицание формальной разности переставляет её компоненты: `-(a —— b) = b —— a`
theorem Int.neg_eq (a b : ℕ) : -(a —— b) = b —— a := rfl

example : -(3 —— 5) = 5 —— 3 := rfl

abbrev Int.IsPos (x : Int) : Prop := ∃ (n : ℕ), n > 0 ∧ x = n
abbrev Int.IsNeg (x : Int) : Prop := ∃ (n : ℕ), n > 0 ∧ x = -n

/-- Lemma 4.1.5 (трихотомия целых чисел). -/
theorem Int.trichotomous (x : Int) : x = 0 ∨ x.IsPos ∨ x.IsNeg := by
  -- Это доказательство слегка изменено по сравнению с оригинальным текстом.
  obtain ⟨ a, b, rfl ⟩ := eq_diff x
  obtain h_lt | rfl | h_gt := _root_.trichotomous (r := LT.lt) a b
  . obtain ⟨ c, rfl ⟩ := Nat.exists_eq_add_of_lt h_lt
    right; right; refine ⟨ c+1, by linarith, ?_ ⟩
    simp_rw [natCast_eq, neg_eq, eq]; abel
  . left; simp_rw [ofNat_eq, eq, add_zero, zero_add]
  obtain ⟨ c, rfl ⟩ := Nat.exists_eq_add_of_lt h_gt
  right; left; refine ⟨ c+1, by linarith, ?_ ⟩
  simp_rw [natCast_eq, eq]; abel

/-- Lemma 4.1.5 (ноль не положителен). -/
theorem Int.not_pos_zero (x : Int) : x = 0 ∧ x.IsPos → False := by
  rintro ⟨ rfl, ⟨ n, _, _ ⟩ ⟩; simp_all [←natCast_ofNat]

/-- Lemma 4.1.5 (ноль не отрицателен). -/
theorem Int.not_neg_zero (x : Int) : x = 0 ∧ x.IsNeg → False := by
  rintro ⟨ rfl, ⟨ n, _, hn ⟩ ⟩; simp_rw [←natCast_ofNat, natCast_eq, neg_eq, eq] at hn
  linarith

/-- Lemma 4.1.5 (положительное и отрицательное не пересекаются). -/
theorem Int.not_pos_neg (x : Int) : x.IsPos ∧ x.IsNeg → False := by
  rintro ⟨ ⟨ n, _, rfl ⟩, ⟨ m, _, hm ⟩ ⟩; simp_rw [natCast_eq, neg_eq, eq] at hm
  linarith

/-- Proposition 4.1.6 (законы алгебры, аддитивная группа) / Exercise 4.1.4 -/
instance Int.instAddGroup : AddGroup Int :=
  AddGroup.ofLeftAxioms (by sorry) (by sorry) (by sorry)

/-- Proposition 4.1.6 (законы алгебры, аддитивная коммутативная группа) / Exercise 4.1.4 -/
instance Int.instAddCommGroup : AddCommGroup Int where
  add_comm := by sorry

/-- Proposition 4.1.6 (законы алгебры, коммутативный моноид) / Exercise 4.1.4 -/
instance Int.instCommMonoid : CommMonoid Int where
  mul_comm := by sorry
  mul_assoc := by
    -- Это доказательство написано так, чтобы следовать структуре оригинального текста.
    intro x y z
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, rfl ⟩ := eq_diff y
    obtain ⟨ e, f, rfl ⟩ := eq_diff z
    simp_rw [mul_eq]; congr 1 <;> ring
  one_mul := by sorry
  mul_one := by sorry

/-- Proposition 4.1.6 (законы алгебры, коммутативное кольцо) / Exercise 4.1.4 -/
instance Int.instCommRing : CommRing Int where
  left_distrib := by sorry
  right_distrib := by sorry
  zero_mul := by sorry
  mul_zero := by sorry

/-- Определение вычитания (целых чисел). -/
theorem Int.sub_eq (a b : Int) : a - b = a + (-b) := by rfl

-- Разность образов двух натуральных чисел в `Int` совпадает с их формальной разностью `a —— b`
theorem Int.sub_eq_formal_sub (a b : ℕ) : (a : Int) - (b : Int) = a —— b := by sorry

/-- Proposition 4.1.8 (Отсутствие делителей нуля) / Exercise 4.1.5 -/
theorem Int.mul_eq_zero {a b : Int} (h : a * b = 0) : a = 0 ∨ b = 0 := by sorry

/-- Corollary 4.1.9 (Закон сокращения) / Exercise 4.1.6 -/
theorem Int.mul_right_cancel₀ (a b c : Int) (h : a*c = b*c) (hc : c ≠ 0) : a = b := by sorry

/-- Definition 4.1.10 (Порядок на целых числах, нестрогий) -/
instance Int.instLE : LE Int where
  le n m := ∃ a : ℕ, m = n + a

/-- Definition 4.1.10 (Порядок на целых числах, строгий) -/
instance Int.instLT : LT Int where
  lt n m := n ≤ m ∧ n ≠ m

-- Разворачивает `≤` в определение (Definition 4.1.10): `a ≤ b` означает, что `b` получается из `a` прибавлением некоторого натурального `t`
theorem Int.le_iff (a b : Int) : a ≤ b ↔ ∃ t : ℕ, b = a + t := by rfl

-- Разворачивает `<` в определение: `a < b` — это `a ≤ b` вместе с `a ≠ b`
theorem Int.lt_iff (a b : Int) : a < b ↔ (∃ t : ℕ, b = a + t) ∧ a ≠ b := by rfl

/-- Lemma 4.1.11(a) (Свойства порядка) / Exercise 4.1.7 -/
theorem Int.lt_iff_exists_positive_difference (a b : Int) : a < b ↔ ∃ n : ℕ, n ≠ 0 ∧ b = a + n := by sorry

/-- Lemma 4.1.11(b) (Сложение сохраняет порядок) / Exercise 4.1.7 -/
theorem Int.add_lt_add_right {a b : Int} (c : Int) (h : a < b) : a+c < b+c := by sorry

/-- Lemma 4.1.11(c) (Умножение на положительное сохраняет порядок) / Exercise 4.1.7 -/
theorem Int.mul_lt_mul_of_pos_right {a b c : Int} (hab : a < b) (hc : 0 < c) : a*c < b*c := by sorry

/-- Lemma 4.1.11(d) (Отрицание обращает порядок, строгий) / Exercise 4.1.7 -/
theorem Int.neg_gt_neg {a b : Int} (h : b < a) : -a < -b := by sorry

/-- Lemma 4.1.11(d) (Отрицание обращает порядок, нестрогий) / Exercise 4.1.7 -/
theorem Int.neg_ge_neg {a b : Int} (h : b ≤ a) : -a ≤ -b := by sorry

/-- Lemma 4.1.11(e) (Порядок транзитивен) / Exercise 4.1.7 -/
theorem Int.lt_trans {a b c : Int} (hab : a < b) (hbc : b < c) : a < c := by sorry

/-- Lemma 4.1.11(f) (Трихотомия порядка, утверждение) / Exercise 4.1.7 -/
theorem Int.trichotomous' (a b : Int) : a > b ∨ a < b ∨ a = b := by sorry

/-- Lemma 4.1.11(f) (Трихотомия порядка, не больше и меньше одновременно) / Exercise 4.1.7 -/
theorem Int.not_gt_and_lt (a b : Int) : ¬ (a > b ∧ a < b):= by sorry

/-- Lemma 4.1.11(f) (Трихотомия порядка, не больше и равно одновременно) / Exercise 4.1.7 -/
theorem Int.not_gt_and_eq (a b : Int) : ¬ (a > b ∧ a = b):= by sorry

/-- Lemma 4.1.11(f) (Трихотомия порядка, не меньше и равно одновременно) / Exercise 4.1.7 -/
theorem Int.not_lt_and_eq (a b : Int) : ¬ (a < b ∧ a = b):= by sorry

/-- (Не из учебника) Устанавливает разрешимость этого порядка. -/
instance Int.decidableRel : DecidableRel (· ≤ · : Int → Int → Prop) := by
  intro n m
  have : ∀ (n : PreInt) (m : PreInt),
      Decidable (Quotient.mk PreInt.instSetoid n ≤ Quotient.mk PreInt.instSetoid m) := by
    intro ⟨ a,b ⟩ ⟨ c,d ⟩
    change Decidable (a —— b ≤ c —— d)
    cases (a + d).decLe (b + c) with
      | isTrue h =>
        apply isTrue
        sorry
      | isFalse h =>
        apply isFalse
        sorry
  exact Quotient.recOnSubsingleton₂ n m this

/-- (Не из учебника) 0 — единственный нейтральный элемент по сложению -/
lemma Int.is_additive_identity_iff_eq_0 (b : Int) : (∀ a, a = a + b) ↔ b = 0 := by sorry

/-- (Не из учебника) Int обладает структурой линейного порядка. -/
instance Int.instLinearOrder : LinearOrder Int where
  le_refl := sorry
  le_trans := sorry
  lt_iff_le_not_ge := sorry
  le_antisymm := sorry
  le_total := sorry
  toDecidableLE := decidableRel

/-- Exercise 4.1.3 -/
theorem Int.neg_one_mul (a : Int) : -1 * a = -a := by sorry

/-- Exercise 4.1.8 -/
theorem Int.no_induction : ∃ P : Int → Prop, (P 0 ∧ ∀ n, P n → P (n+1)) ∧ ¬ ∀ n, P n := by sorry

/-- Квадрат неотрицательного числа неотрицателен. Это частный случай 4.1.9, полезный для доказательства общего случая. -/
lemma Int.sq_nonneg_of_pos (n : Int) (h : 0 ≤ n) : 0 ≤ n*n := by sorry

/-- Exercise 4.1.9. Квадрат любого целого числа неотрицателен. -/
theorem Int.sq_nonneg (n : Int) : 0 ≤ n*n := by sorry

/-- Exercise 4.1.9 -/
theorem Int.sq_nonneg' (n : Int) : ∃ (m : Nat), n*n = m := by sorry

/--
  Не из учебника: строит эквивалентность между {name}`Int` и {lean}`ℤ`.
  Для этого требуется некоторое знакомство с API версии целых чисел из Mathlib.
-/
abbrev Int.equivInt : Int ≃ ℤ where
  toFun := Quotient.lift (fun ⟨ a, b ⟩ ↦ a - b) (by
    sorry)
  invFun := sorry
  left_inv n := sorry
  right_inv n := sorry

/-- Не из учебника: эквивалентность сохраняет порядок и кольцевые операции -/
abbrev Int.equivInt_ordered_ring : Int ≃+*o ℤ where
  toEquiv := equivInt
  map_add' := by sorry
  map_mul' := by sorry
  map_le_map_iff' := by sorry

end Section_4_1
