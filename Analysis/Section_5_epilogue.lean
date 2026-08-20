import Mathlib.Tactic
import Analysis.Section_5_6

/-!
# Analysis I, эпилог главы 5: изоморфизм с вещественными числами Mathlib

В этом (техническом) эпилоге мы показываем, что вещественные числа "Главы 5" {name}`Chapter5.Real`
изоморфны в различных стандартных смыслах стандартным вещественным числам {lean}`ℝ`. Мы делаем это,
сопоставляя обе структуры сечениям Дедекинда рациональных чисел (Mathlib) {lean}`ℚ`.

Начиная с этого момента {name}`Chapter5.Real` будет вытеснено, и далее мы будем использовать
стандартные вещественные числа {lean}`ℝ`. В частности, во всех последующих главах следует
использовать полное API Mathlib для {lean}`ℝ` вместо API {name}`Chapter5.Real`.

Заполнение {syntax term}`sorry` здесь требует как API {name}`Chapter5.Real`, так и API Mathlib для
стандартных вещественных чисел {lean}`ℝ`. Поэтому это отличные упражнения, готовящие вас к
упомянутому переходу.

## Советы от прошлых пользователей

Пользователи, прошедшие упражнения этого раздела, могут присылать свои советы для будущих
пользователей в виде PR.

- (Добавьте совет сюда)

-/

namespace Chapter5


@[ext]
structure DedekindCut where
  E : Set ℚ
  nonempty : E.Nonempty
  bounded : BddAbove E
  lower : IsLowerSet E
  nomax : ∀ q ∈ E, ∃ r ∈ E, r > q

theorem isLowerSet_iff (E : Set ℚ) : IsLowerSet E ↔ ∀ q r, r < q → q ∈ E → r ∈ E :=
  isLowerSet_iff_forall_lt

abbrev Real.toSet_Rat (x : Real) : Set ℚ := { q | (q : Real) < x }

lemma Real.toSet_Rat_nonempty (x : Real) : x.toSet_Rat.Nonempty := by sorry

lemma Real.toSet_Rat_bounded (x : Real) : BddAbove x.toSet_Rat := by sorry

lemma Real.toSet_Rat_lower (x : Real) : IsLowerSet x.toSet_Rat := by sorry

lemma Real.toSet_Rat_nomax {x : Real} : ∀ q ∈ x.toSet_Rat, ∃ r ∈ x.toSet_Rat, r > q := by sorry

abbrev Real.toCut (x : Real) : DedekindCut :=
 {
   E := x.toSet_Rat
   nonempty := x.toSet_Rat_nonempty
   bounded := x.toSet_Rat_bounded
   lower := x.toSet_Rat_lower
   nomax := x.toSet_Rat_nomax
 }

abbrev DedekindCut.toSet_Real (c : DedekindCut) : Set Real := (fun (q : ℚ) ↦ (q : Real)) '' c.E

lemma DedekindCut.toSet_Real_nonempty (c : DedekindCut) : c.toSet_Real.Nonempty := by sorry

lemma DedekindCut.toSet_Real_bounded (c : DedekindCut) : BddAbove c.toSet_Real := by sorry

noncomputable abbrev DedekindCut.toReal (c : DedekindCut) : Real := sSup c.toSet_Real

lemma DedekindCut.toReal_isLUB (c : DedekindCut) : IsLUB c.toSet_Real c.toReal :=
  ExtendedReal.sSup_of_bounded c.toSet_Real_nonempty c.toSet_Real_bounded

noncomputable abbrev Real.equivCut : Real ≃ DedekindCut where
  toFun := toCut
  invFun := DedekindCut.toReal
  left_inv x := by
    sorry
  right_inv c := by
    sorry

end Chapter5

/-- Теперь развернём аналогичные результаты для вещественных чисел Mathlib. -/

abbrev Real.toSet_Rat (x : ℝ) : Set ℚ := { q | (q : ℝ) < x }

lemma Real.toSet_Rat_nonempty (x : ℝ) : x.toSet_Rat.Nonempty := by sorry

lemma Real.toSet_Rat_bounded (x : ℝ) : BddAbove x.toSet_Rat := by sorry

lemma Real.toSet_Rat_lower (x : ℝ) : IsLowerSet x.toSet_Rat := by sorry

lemma Real.toSet_Rat_nomax (x : ℝ) : ∀ q ∈ x.toSet_Rat, ∃ r ∈ x.toSet_Rat, r > q := by sorry

abbrev Real.toCut (x : ℝ) : Chapter5.DedekindCut :=
 {
   E := x.toSet_Rat
   nonempty := x.toSet_Rat_nonempty
   bounded := x.toSet_Rat_bounded
   lower := x.toSet_Rat_lower
   nomax := x.toSet_Rat_nomax
 }

namespace Chapter5

abbrev DedekindCut.toSet_R (c : DedekindCut) : Set ℝ := (fun (q : ℚ) ↦ (q : ℝ)) '' c.E

lemma DedekindCut.toSet_R_nonempty (c : DedekindCut) : c.toSet_R.Nonempty := by sorry

lemma DedekindCut.toSet_R_bounded (c : DedekindCut) : BddAbove c.toSet_R := by sorry

noncomputable abbrev DedekindCut.toR (c : DedekindCut) : ℝ := sSup c.toSet_R

lemma DedekindCut.toR_isLUB (c : DedekindCut) : IsLUB c.toSet_R c.toR :=
  isLUB_csSup c.toSet_R_nonempty c.toSet_R_bounded

end Chapter5

noncomputable abbrev Real.equivCut : ℝ ≃ Chapter5.DedekindCut where
  toFun := _root_.Real.toCut
  invFun := Chapter5.DedekindCut.toR
  left_inv x := by
    sorry
  right_inv c := by
    sorry

namespace Chapter5

/-- Изоморфизм между числами {name}`Chapter5.Real` и вещественными числами Mathlib. -/
noncomputable abbrev Real.equivR : Real ≃ ℝ := Real.equivCut.trans _root_.Real.equivCut.symm

lemma Real.equivR_iff (x : Real) (y : ℝ) : y = Real.equivR x ↔ y.toCut = x.toCut := by
  simp only [equivR, Equiv.trans_apply, ←Equiv.apply_eq_iff_eq_symm_apply]
  rfl

-- Чтобы воспользоваться этим определением, нам понадобится некоторый инструментарий
-----

-- Начнём с того, что покажем, что это работает для ratCast-ов
theorem Real.equivR_ratCast {q : ℚ} : equivR q = (q : ℝ) := by
  sorry

lemma Real.equivR_nat {n : ℕ} : equivR n = (n : ℝ) := equivR_ratCast
lemma Real.equivR_int {n : ℤ} : equivR n = (n : ℝ) := equivR_ratCast

----

-- Далее мы хотим построить способ перехода от `LIM` для Real к `Real.mk` для ℝ.
-- Для этого нам понадобится несколько вещей:

-- Переход между понятиями последовательности Коши
theorem Sequence.IsCauchy.to_IsCauSeq {a : ℕ → ℚ} (ha : IsCauchy a) : IsCauSeq _root_.abs a := by
  sorry

-- Переход от `IsCauchy` к `CauSeq`
abbrev Sequence.IsCauchy.CauSeq {a : ℕ → ℚ} : (ha : IsCauchy a) → CauSeq ℚ _root_.abs :=
  (⟨a, ·.to_IsCauSeq⟩)

-- Далее мы строим переход от Sequence.Equiv к CauSeq.LimZero, так как
-- это и есть отношение эквивалентности
example {a b : CauSeq ℚ abs} : a ≈ b ↔ CauSeq.LimZero (a - b) := by rfl

theorem Sequence.Equiv.LimZero {a b : ℕ → ℚ} (ha : IsCauchy a) (hb : IsCauchy b) (h : Equiv a b)
  : CauSeq.LimZero (ha.CauSeq - hb.CauSeq) := by
    sorry

-- Теперь мы можем использовать это для перехода между разными функциями в Real.mk
theorem Real.mk_eq_mk {a b : ℕ → ℚ} (ha : Sequence.IsCauchy a) (hb : Sequence.IsCauchy b) (hab : Sequence.Equiv a b)
  : Real.mk ha.CauSeq = Real.mk hb.CauSeq := Real.mk_eq.mpr (hab.LimZero ha hb)

-- Оба направления эквивалентности
theorem Sequence.Equiv_iff_LimZero {a b : ℕ → ℚ} (ha : IsCauchy a) (hb : IsCauchy b)
  : Equiv a b ↔ CauSeq.LimZero (ha.CauSeq - hb.CauSeq) := by
    refine ⟨(·.LimZero ha hb), ?_⟩
    sorry

----
-- Построим несколько последовательностей Коши с полезными свойствами

-- Покажем, что для любой последовательности она в конце концов окажется сколь угодно близко к своему LIM
open Real in
theorem Sequence.difference_approaches_zero {a : ℕ → ℚ} (ha : Sequence.IsCauchy a) : 
  ∀ε > 0, ∃N, ∀n ≥ N, |LIM a - a n| ≤ (ε : ℚ) := by
    sorry

-- Существует последовательность Коши, целиком лежащая выше LIM
theorem Real.exists_equiv_above {a : ℕ → ℚ} (ha : Sequence.IsCauchy a)
  : ∃(b : ℕ → ℚ), Sequence.IsCauchy b ∧ Sequence.Equiv a b ∧ ∀n, LIM a ≤ b n := by
    sorry

-- Существует последовательность Коши, целиком лежащая ниже LIM
theorem Real.exists_equiv_below {a : ℕ → ℚ} (ha : Sequence.IsCauchy a)
  : ∃(b : ℕ → ℚ), Sequence.IsCauchy b ∧ Sequence.Equiv a b ∧ ∀n, b n ≤ LIM a := by
    sorry

----

-- полезные теоремы для следующего доказательства
#check Real.mk_le
#check Real.mk_le_of_forall_le
#check Real.mk_const

-- Переводим `Real` в `ℝ`, проходя через последовательности Коши;
-- переход Real.mk_eq позволяет использовать разные последовательности для доказательства разных частей
theorem Real.equivR_eq' {a : ℕ → ℚ} (ha : Sequence.IsCauchy a)
  : (LIM a).equivR = Real.mk ha.CauSeq := by
    by_cases hq : ∃(q : ℚ), q = LIM a
    · sorry
    show sSup (Rat.cast '' (LIM a).toSet_Rat) = _
    refine IsLUB.csSup_eq ⟨?_, ?_⟩ (Set.Nonempty.image _ <| Real.toSet_Rat_nonempty _)
    · -- покажем, что `Real.mk ha.CauSeq` — верхняя грань
      intro _ hy
      obtain ⟨y, hy, h⟩ := Set.mem_image _ _ _ |>.mp hy
      rw [← h, show (y : ℝ) = Real.mk (CauSeq.const _ y) from rfl]
      sorry
    -- покажем, что для любой другой верхней грани `Real.mk ha.CauSeq` меньше
    intro M hM
    sorry

lemma Real.equivR_eq (x : Real) : ∃(a : ℕ → ℚ) (ha : Sequence.IsCauchy a),
  x = LIM a ∧ x.equivR = Real.mk ha.CauSeq := by
    obtain ⟨a, ha, rfl⟩ := x.eq_lim
    exact ⟨a, ha, rfl, equivR_eq' ha⟩

/-- Изоморфизм сохраняет порядок и операции кольца. -/
noncomputable abbrev Real.equivR_ordered_ring : Real ≃+*o ℝ where
  toEquiv := equivR
  map_add' := by sorry
  map_mul' := by sorry
  map_le_map_iff' := by sorry

-- вспомогательные средства для переноса свойств между Real и ℝ
lemma Real.equivR_map_mul {x y : Real} : equivR (x * y) = equivR x * equivR y :=
  equivR_ordered_ring.map_mul _ _

lemma Real.equivR_map_inv {x : Real} : equivR (x⁻¹) = (equivR x)⁻¹ :=
  map_inv₀ equivR_ordered_ring _

theorem Real.equivR_map_pos {x : Real} : 0 < x ↔ 0 < equivR x := by sorry

theorem Real.equivR_map_nonneg {x : Real} : 0 ≤ x ↔ 0 ≤ equivR x := by sorry


-- Показываем эквивалентность разных видов возведения в степень
theorem Real.pow_of_equivR (x : Real) (n : ℕ) : equivR (x^n) = (equivR x)^n := by
  sorry

theorem Real.zpow_of_equivR (x : Real) (n : ℤ) : equivR (x^n) = (equivR x)^n := by
  sorry

theorem Real.ratPow_of_equivR (x : Real) (q : ℚ) (hx : x > 0) : equivR (x^q) = (equivR x)^(q : ℝ) := by
  sorry


end Chapter5
