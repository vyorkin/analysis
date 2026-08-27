import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

set_option doc.verso.suggestions false

/-!
# Analysis I, раздел 4.2

Этот файл — перевод раздела 4.2 книги Analysis I на Lean 4.
Вся нумерация ссылается на оригинальный текст.

Я старался сделать перевод максимально точным перефразированием оригинального текста. Когда
приходилось выбирать между более идиоматичным Lean-решением и более точным переводом, я, как
правило, выбирал второе. В частности, местами Lean-код можно было бы "заголфить", сделав его более
элегантным и идиоматичным, но я сознательно этого избегал.

Основные конструкции и результаты этого раздела:

- Определение рациональных чисел "раздела 4.2", `Section_4_2.Rat`, как формальных частных `a // b`
  целых чисел `a b:ℤ`, с точностью до эквивалентности. (Это фактор вспомогательного типа
  `Section_4_2.PreRat`, состоящего из формальных частных без какой-либо наложенной эквивалентности.)

- Операции поля и порядок на этих рациональных числах, а также вложение {lean}`ℕ` и {lean}`ℤ`.

- Эквивалентность с рациональными числами Mathlib {name}`_root_.Rat` (или {lean}`ℚ`), которые мы
  будем использовать в дальнейшем.

Примечание: здесь (и далее) мы используем натуральные числа {lean}`ℕ` и целые числа {lean}`ℤ` из
Mathlib, а не натуральные числа Главы 2 и целые числа раздела 4.1.

## Советы от прошлых пользователей

Пользователи, прошедшие упражнения этого раздела, могут присылать свои советы для будущих
пользователей в виде PR.

- (Добавьте совет сюда)

-/

namespace Section_4_2

structure PreRat where
  numerator : ℤ
  denominator : ℤ
  nonzero : denominator ≠ 0

/-- Exercise 4.2.1 -/
instance PreRat.instSetoid : Setoid PreRat where
  r a b := a.numerator * b.denominator = b.numerator * a.denominator
  iseqv := {
    refl := by sorry
    symm := by sorry
    trans := by sorry
    }

@[simp]
theorem PreRat.eq (a b c d : ℤ) (hb : b ≠ 0) (hd : d ≠ 0) :
    (⟨ a,b,hb ⟩ : PreRat) ≈ ⟨ c,d,hd ⟩ ↔ a * d = c * b := by rfl

abbrev Rat := Quotient PreRat.instSetoid

/-- Мы присваиваем делению "мусорное" значение 0//1, если знаменатель равен нулю -/
abbrev Rat.formalDiv (a b : ℤ) : Rat :=
  Quotient.mk PreRat.instSetoid (if h : b ≠ 0 then ⟨ a,b,h ⟩ else ⟨ 0, 1, by decide ⟩)

infix:100 " // " => Rat.formalDiv

/-- Definition 4.2.1 (Рациональные числа, равенство) -/
theorem Rat.eq (a c : ℤ) {b d : ℤ} (hb : b ≠ 0) (hd : d ≠ 0) : a // b = c // d ↔ a * d = c * b := by
  simp [formalDiv, hb, hd, Quotient.eq, PreRat.instSetoid]

/-- Definition 4.2.1 (Рациональные числа, существование представления) -/
theorem Rat.eq_diff (n : Rat) : ∃ a b, b ≠ 0 ∧ n = a // b := by
  apply Quotient.ind _ n; intro ⟨ a, b, h ⟩
  refine ⟨ a, b, h, ?_ ⟩
  simp [formalDiv, h]

/--
  Разрешимость равенства.
  Подсказка: измените доказательство {lean}`DecidableEq Int` из предыдущего раздела.
  Однако поскольку формальное деление отдельно обрабатывает случай нулевого знаменателя,
  может быть удобнее избегать этой операции и работать напрямую с API {name}`Quotient`.

-/
instance Rat.decidableEq : DecidableEq Rat := by
  sorry

/-- Lemma 4.2.3 (Сложение определено корректно) -/
instance Rat.add_inst : Add Rat where
  add := Quotient.lift₂ (fun ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ↦ (a*d+b*c) // (b*d)) (by
    intro ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ⟨ a', b', h1' ⟩ ⟨ c', d', h2' ⟩ h3 h4
    simp_all [Quotient.eq]
    linear_combination d * d' * h3 + b * b' * h4
  )

/-- Definition 4.2.2 (Сложение рациональных чисел) -/
theorem Rat.add_eq (a c : ℤ) {b d : ℤ} (hb : b ≠ 0) (hd : d ≠ 0) :
    (a // b) + (c // d) = (a*d + b*c) // (b*d) := by
  convert Quotient.lift₂_mk _ _ _ _ <;> simp [hb, hd]

/-- Lemma 4.2.3 (Умножение определено корректно) -/
instance Rat.mul_inst : Mul Rat where
  mul := Quotient.lift₂ (fun ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ↦ (a*c) // (b*d)) (by sorry)

/-- Definition 4.2.2 (Умножение рациональных чисел) -/
theorem Rat.mul_eq (a c : ℤ) {b d : ℤ} (hb : b ≠ 0) (hd : d ≠ 0) :
    (a // b) * (c // d) = (a*c) // (b*d) := by
  convert Quotient.lift₂_mk _ _ _ _ <;> simp [hb, hd]

/-- Lemma 4.2.3 (Отрицание определено корректно) -/
instance Rat.neg_inst : Neg Rat where
  neg := Quotient.lift (fun ⟨ a, b, h1 ⟩ ↦ (-a) // b) (by sorry)

/-- Definition 4.2.2 (Отрицание рациональных чисел) -/
theorem Rat.neg_eq (a : ℤ) {b : ℤ} (hb : b ≠ 0) : - (a // b) = (-a) // b := by
  convert Quotient.lift_mk _ _ _ <;> simp [hb]

/-- Вложение целых чисел в рациональные -/
instance Rat.instIntCast : IntCast Rat where
  intCast a := a // 1

instance Rat.instNatCast : NatCast Rat where
  natCast n := (n : ℤ) // 1

instance Rat.instOfNat {n : ℕ} : OfNat Rat n where
  ofNat := (n : ℤ) // 1

theorem Rat.coe_Int_eq (a : ℤ) : (a : Rat) = a // 1 := rfl

theorem Rat.coe_Nat_eq (n : ℕ) : (n : Rat) = n // 1 := rfl

theorem Rat.of_Nat_eq (n : ℕ) : (ofNat(n) : Rat) = (ofNat(n) : Nat) // 1 := rfl

/-- natCast дистрибутивен относительно следующего элемента -/
theorem Rat.natCast_succ (n : ℕ) : ((n + 1 : ℕ) : Rat) = (n : Rat) + 1 := by sorry

/-- intCast дистрибутивен относительно сложения -/
lemma Rat.intCast_add (a b : ℤ) : (a : Rat) + (b : Rat) = (a+b : ℤ) := by sorry

/-- intCast дистрибутивен относительно умножения -/
lemma Rat.intCast_mul (a b : ℤ) : (a : Rat) * (b : Rat) = (a*b : ℤ) := by sorry

/-- intCast коммутирует с отрицанием -/
lemma Rat.intCast_neg (a : ℤ) : - (a : Rat) = (-a : ℤ) := rfl

theorem Rat.coe_Int_inj : Function.Injective (fun n : ℤ ↦ (n : Rat)) := by sorry

/--
  В то время как в книге обратный элемент к 0 остаётся неопределённым, в Lean удобнее присвоить
  этой обратной величине "мусорное" значение; мы произвольно выбираем в качестве такого
  мусорного значения 0.
-/
instance Rat.instInv : Inv Rat where
  inv := Quotient.lift (fun ⟨ a, b, h1 ⟩ ↦ b // a) (by
    sorry -- подсказка: разберите случаи `a=0` и `a≠0`
)

lemma Rat.inv_eq (a : ℤ) {b : ℤ} (hb : b ≠ 0) : (a // b)⁻¹ = b // a := by
  convert Quotient.lift_mk _ _ _ <;> simp [hb]

@[simp]
theorem Rat.inv_zero : (0 : Rat)⁻¹ = 0 := rfl

/-- Proposition 4.2.4 (законы алгебры, аддитивная группа) / Exercise 4.2.3 -/
instance Rat.addGroup_inst : AddGroup Rat :=
AddGroup.ofLeftAxioms (by
  -- это доказательство написано так, чтобы следовать структуре оригинального текста.
  intro x y z
  obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
  obtain ⟨ c, d, hd, rfl ⟩ := eq_diff y
  obtain ⟨ e, f, hf, rfl ⟩ := eq_diff z
  have hbd : b*d ≠ 0 := Int.mul_ne_zero hb hd     -- можно также использовать `observe hbd : b*d ≠ 0`
  have hdf : d*f ≠ 0 := Int.mul_ne_zero hd hf     -- можно также использовать `observe hdf : d*f ≠ 0`
  have hbdf : b*d*f ≠ 0 := Int.mul_ne_zero hbd hf -- можно также использовать `observe hbdf : b*d*f ≠ 0`
  rw [add_eq _ _ hb hd, add_eq _ _ hbd hf, add_eq _ _ hd hf,
      add_eq _ _ hb hdf, ←mul_assoc b, eq _ _ hbdf hbdf]
  ring
)
 (by sorry) (by sorry)

/-- Proposition 4.2.4 (законы алгебры, аддитивная коммутативная группа) / Exercise 4.2.3 -/
instance Rat.instAddCommGroup : AddCommGroup Rat where
  add_comm := by sorry

/-- Proposition 4.2.4 (законы алгебры, коммутативный моноид) / Exercise 4.2.3 -/
instance Rat.instCommMonoid : CommMonoid Rat where
  mul_comm := by sorry
  mul_assoc := by sorry
  one_mul := by sorry
  mul_one := by sorry

/-- Proposition 4.2.4 (законы алгебры, коммутативное кольцо) / Exercise 4.2.3 -/
instance Rat.instCommRing : CommRing Rat where
  left_distrib := by sorry
  right_distrib := by sorry
  zero_mul := by sorry
  mul_zero := by sorry
  mul_assoc := by sorry
  -- Обычно CommRing сам генерирует инстанс natCast и доказательство для этого поля.
  -- Однако мы используем собственный natCast, для которого `natCast_succ` не может
  -- быть автоматически доказан через `rfl`. К счастью, мы уже доказали это ранее.
  natCast_succ := natCast_succ

instance Rat.instRatCast : RatCast Rat where
  ratCast q := q.num // q.den

theorem Rat.ratCast_inj : Function.Injective (fun n : ℚ ↦ (n : Rat)) := by sorry

theorem Rat.coe_Rat_eq (a : ℤ) {b : ℤ} (hb : b ≠ 0) : (a/b : ℚ) = a // b := by
  set q := (a/b : ℚ)
  set num : ℤ := q.num
  set den : ℤ := (q.den : ℤ)
  have hden : den ≠ 0 := by simp [den, q.den_nz]
  change num // den = a // b
  rw [eq _ _ hden hb]
  qify
  have hq : num / den = q := Rat.num_div_den q
  rwa [div_eq_div_iff] at hq <;> simp [hden, hb]

/-- Определение деления по умолчанию -/
instance Rat.instDivInvMonoid : DivInvMonoid Rat where

theorem Rat.div_eq (q r : Rat) : q/r = q * r⁻¹ := by rfl

/-- Proposition 4.2.4 (законы алгебры, поле) / Exercise 4.2.3 -/
instance Rat.instField : Field Rat where
  exists_pair_ne := by sorry
  mul_inv_cancel := by sorry
  inv_zero := rfl
  ratCast_def := by
    intro q
    set num := q.num
    set den := q.den
    have hden : (den : ℤ) ≠ 0 := by simp [den, q.den_nz]
    rw [← Rat.num_div_den q]
    convert coe_Rat_eq _ hden
    rw [coe_Int_eq, coe_Nat_eq, div_eq, inv_eq, mul_eq, eq] <;> simp [num, den, q.den_nz]
  qsmul := _
  nnqsmul := _

example : (3//4) / (5//6) = 9 // 10 := by sorry

/-- Определение вычитания (рациональных чисел). -/
theorem Rat.sub_eq (a b : Rat) : a - b = a + (-b) := by rfl

def Rat.coe_int_hom : ℤ →+* Rat where
  toFun n := (n : Rat)
  map_zero' := rfl
  map_one' := rfl
  map_add' := by sorry
  map_mul' := by sorry

/-- Definition 4.2.6 (положительность) -/
def Rat.isPos (q : Rat) : Prop := ∃ a b : ℤ, a > 0 ∧ b > 0 ∧ q = a/b

/-- Definition 4.2.6 (отрицательность) -/
def Rat.isNeg (q : Rat) : Prop := ∃ r : Rat, r.isPos ∧ q = -r

/-- Lemma 4.2.7 (трихотомия рациональных чисел, утверждение) / Exercise 4.2.4 -/
theorem Rat.trichotomous (x : Rat) : x = 0 ∨ x.isPos ∨ x.isNeg := by sorry

/-- Lemma 4.2.7 (трихотомия рациональных чисел, ноль и положительное) / Exercise 4.2.4 -/
theorem Rat.not_zero_and_pos (x : Rat) : ¬(x = 0 ∧ x.isPos) := by sorry

/-- Lemma 4.2.7 (трихотомия рациональных чисел, ноль и отрицательное) / Exercise 4.2.4 -/
theorem Rat.not_zero_and_neg (x : Rat) : ¬(x = 0 ∧ x.isNeg) := by sorry

/-- Lemma 4.2.7 (трихотомия рациональных чисел, положительное и отрицательное) / Exercise 4.2.4 -/
theorem Rat.not_pos_and_neg (x : Rat) : ¬(x.isPos ∧ x.isNeg) := by sorry

/-- Definition 4.2.8 (Порядок на рациональных числах, строгий) -/
instance Rat.instLT : LT Rat where
  lt x y := (x-y).isNeg

/-- Definition 4.2.8 (Порядок на рациональных числах, нестрогий) -/
instance Rat.instLE : LE Rat where
  le x y := (x < y) ∨ (x = y)

theorem Rat.lt_iff (x y : Rat) : x < y ↔ (x-y).isNeg := by rfl
theorem Rat.le_iff (x y : Rat) : x ≤ y ↔ (x < y) ∨ (x = y) := by rfl

theorem Rat.gt_iff (x y : Rat) : x > y ↔ (x-y).isPos := by sorry
theorem Rat.ge_iff (x y : Rat) : x ≥ y ↔ (x > y) ∨ (x = y) := by sorry

/-- Proposition 4.2.9(a) (трихотомия порядка, утверждение) / Exercise 4.2.5 -/
theorem Rat.trichotomous' (x y : Rat) : x > y ∨ x < y ∨ x = y := by sorry

/-- Proposition 4.2.9(a) (трихотомия порядка, не больше и меньше одновременно) / Exercise 4.2.5 -/
theorem Rat.not_gt_and_lt (x y : Rat) : ¬ (x > y ∧ x < y):= by sorry

/-- Proposition 4.2.9(a) (трихотомия порядка, не больше и равно одновременно) / Exercise 4.2.5 -/
theorem Rat.not_gt_and_eq (x y : Rat) : ¬ (x > y ∧ x = y):= by sorry

/-- Proposition 4.2.9(a) (трихотомия порядка, не меньше и равно одновременно) / Exercise 4.2.5 -/
theorem Rat.not_lt_and_eq (x y : Rat) : ¬ (x < y ∧ x = y):= by sorry

/-- Proposition 4.2.9(b) (порядок антисимметричен) / Exercise 4.2.5 -/
theorem Rat.antisymm (x y : Rat) : x < y ↔ y > x := by sorry

/-- Proposition 4.2.9(c) (порядок транзитивен) / Exercise 4.2.5 -/
theorem Rat.lt_trans {x y z : Rat} (hxy : x < y) (hyz : y < z) : x < z := by sorry

/-- Proposition 4.2.9(d) (сложение сохраняет порядок) / Exercise 4.2.5 -/
theorem Rat.add_lt_add_right {x y : Rat} (z : Rat) (hxy : x < y) : x + z < y + z := by sorry

/-- Proposition 4.2.9(e) (умножение на положительное сохраняет порядок) / Exercise 4.2.5 -/
theorem Rat.mul_lt_mul_right {x y z : Rat} (hxy : x < y) (hz : z.isPos) : x * z < y * z := by sorry

/-- (Не из учебника) Устанавливает разрешимость этого порядка. -/
instance Rat.decidableRel : DecidableRel (· ≤ · : Rat → Rat → Prop) := by
  intro n m
  have : ∀ (n : PreRat) (m : PreRat),
      Decidable (Quotient.mk PreRat.instSetoid n ≤ Quotient.mk PreRat.instSetoid m) := by
    intro ⟨ a,b,hb ⟩ ⟨ c,d,hd ⟩
    -- на этом этапе цель, по сути, `Decidable(a//b ≤ c//d)`, но здесь возникают технические
    -- сложности из-за мусорного значения формального деления, когда знаменатель обращается в ноль.
    -- Может быть удобнее избегать формального деления и работать напрямую с `Quotient.mk`.
    cases (0 : ℤ).decLe (b*d) with
      | isTrue hbd =>
        cases (a * d).decLe (b * c) with
          | isTrue h =>
            apply isTrue
            sorry
          | isFalse h =>
            apply isFalse
            sorry
      | isFalse hbd =>
        cases (b * c).decLe (a * d) with
          | isTrue h =>
            apply isTrue
            sorry
          | isFalse h =>
            apply isFalse
            sorry
  exact Quotient.recOnSubsingleton₂ n m this

/-- (Не из учебника) Rat обладает структурой линейного порядка. -/
instance Rat.instLinearOrder : LinearOrder Rat where
  le_refl := sorry
  le_trans := sorry
  lt_iff_le_not_ge := sorry
  le_antisymm := sorry
  le_total := sorry
  toDecidableLE := decidableRel

/-- (Не из учебника) Rat обладает структурой строго упорядоченного кольца. -/
instance Rat.instIsStrictOrderedRing : IsStrictOrderedRing Rat where
  add_le_add_left := by sorry
  add_le_add_right := by sorry
  mul_lt_mul_of_pos_left := by sorry
  mul_lt_mul_of_pos_right := by sorry
  le_of_add_le_add_left := by sorry
  zero_le_one := by sorry

/-- Exercise 4.2.6 -/
theorem Rat.mul_lt_mul_right_of_neg (x y z : Rat) (hxy : x < y) (hz : z.isNeg) : x * z > y * z := by
  sorry


/--
  Не из учебника: строит эквивалентность между Rat и ℚ. Для этого требуется некоторое знакомство
  с API версии рациональных чисел из Mathlib.
-/
abbrev Rat.equivRat : Rat ≃ ℚ where
  toFun := Quotient.lift (fun ⟨ a, b, h ⟩ ↦ a / b) (by
    sorry)
  invFun := fun n : ℚ ↦ (n : Rat)
  left_inv n := sorry
  right_inv n := sorry

/-- Не из учебника: эквивалентность сохраняет порядок -/
abbrev Rat.equivRat_order : Rat ≃o ℚ where
  toEquiv := equivRat
  map_rel_iff' := by sorry

/-- Не из учебника: эквивалентность сохраняет кольцевые операции -/
abbrev Rat.equivRat_ring : Rat ≃+* ℚ where
  toEquiv := equivRat
  map_add' := by sorry
  map_mul' := by sorry

/--
  (Не из учебника) Рациональные числа учебника изоморфны (как поле) рациональным числам Mathlib.
-/
def Rat.equivRat_ring_symm : ℚ ≃+* Rat := Rat.equivRat_ring.symm

end Section_4_2
