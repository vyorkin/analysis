import Mathlib.Data.Nat.BitIndices
import Mathlib.Combinatorics.Colex

/-!
# Дополнительные леммы для битовых операций над натуральными числами

Этот файл содержит общие леммы про {name}`Nat.testBit`, {name}`Nat.bitIndices` и суммы степеней
двойки, используемые на протяжении всей формализации.

## Основные результаты

* {given -show}`n : ℕ, i : ℕ` `Nat.testBit_iff_mem_bitIndices`: {lean}`n.testBit i = true ↔ i ∈ n.bitIndices`
* {given -show}`j` `Nat.testBit_finset_sum_pow_two`: для finset {given}`s` натуральных чисел
  {lean}`(∑ i ∈ s, 2^i).testBit j ↔ j ∈ s`
* {given -show}`k` `Nat.testBit_sum_pow_two_fin`: то же самое для {lean}`Finset (Fin k)`

Эти леммы связывают битовое представление натуральных чисел с принадлежностью finset, что
является фундаментальным для аргументов, использующих двоичное кодирование.
-/

namespace Nat

/-- {lean}`n.testBit i = true` тогда и только тогда, когда {name}`i` встречается в
    {lean}`n.bitIndices`. Это связывает поразрядную проверку бита со списком позиций
    установленных битов. -/
lemma testBit_iff_mem_bitIndices (n i : ℕ) : 
    n.testBit i = true ↔ i ∈ n.bitIndices := by
  constructor
  · intro h
    induction n using Nat.binaryRec generalizing i with
    | zero => simp at h
    | bit b n ih =>
      cases b
      · simp only [Nat.bit_false, Nat.bitIndices_two_mul, List.mem_map]
        rcases Nat.eq_or_lt_of_le (Nat.zero_le i) with rfl | hpos
        · simp at h
        · have hi_succ : i = (i - 1) + 1 := (Nat.sub_add_cancel hpos).symm
          rw [hi_succ, Nat.testBit_bit_succ] at h
          exact ⟨i - 1, ih _ h, hi_succ.symm⟩
      · simp only [Nat.bit_true, Nat.bitIndices_two_mul_add_one, List.mem_cons, List.mem_map]
        rcases Nat.eq_or_lt_of_le (Nat.zero_le i) with rfl | hpos
        · left; rfl
        · right
          have hi_succ : i = (i - 1) + 1 := (Nat.sub_add_cancel hpos).symm
          rw [hi_succ, Nat.testBit_bit_succ] at h
          exact ⟨i - 1, ih _ h, hi_succ.symm⟩
  · intro h
    induction n using Nat.binaryRec generalizing i with
    | zero => simp at h
    | bit b n ih =>
      cases b
      · simp only [Nat.bit_false, Nat.bitIndices_two_mul, List.mem_map] at h
        obtain ⟨j, hj, rfl⟩ := h
        rw [Nat.testBit_bit_succ]
        exact ih _ hj
      · simp only [Nat.bit_true, Nat.bitIndices_two_mul_add_one, List.mem_cons, List.mem_map] at h
        rcases h with rfl | ⟨j, hj, rfl⟩
        · simp
        · rw [Nat.testBit_bit_succ]
          exact ih _ hj

/-- {name}`Nat.testBit` суммы различных степеней двойки равносильна принадлежности множеству
    индексов. Для finset {name}`s` натуральных чисел
    {given -show}`j` {lean}`(∑ i ∈ s, 2^i).testBit j = true ↔ j ∈ s`. -/
lemma testBit_finset_sum_pow_two {s : Finset ℕ} {i : ℕ} : 
    (s.sum (2^·)).testBit i = true ↔ i ∈ s := by
  rw [testBit_iff_mem_bitIndices]
  constructor
  · intro h
    have : i ∈ (s.sum (2^·)).bitIndices.toFinset := List.mem_toFinset.mpr h
    rw [Finset.toFinset_bitIndices_twoPowSum] at this
    exact this
  · intro h
    have : i ∈ (s.sum (2^·)).bitIndices.toFinset := by
      rw [Finset.toFinset_bitIndices_twoPowSum]
      exact h
    exact List.mem_toFinset.mp this

/-- {name}`Nat.testBit` суммы {lean (type := "ℕ")}`2^j.val` по {lean}`Finset (Fin k)` равносильна
    принадлежности множеству. Это версия {name}`Nat.testBit_finset_sum_pow_two`, индексированная
    типом {name}`Fin`. -/
lemma testBit_sum_pow_two_fin {k : ℕ} {s : Finset (Fin k)} (j : Fin k) : 
    (s.sum fun i => (2 : ℕ)^i.val).testBit j.val ↔ j ∈ s := by
  have h : s.sum (fun i => (2 : ℕ)^i.val) = (s.image (·.val)).sum (2^·) := by
    rw [Finset.sum_image]
    intro x _ y _ hxy
    exact Fin.val_injective hxy
  rw [h, testBit_finset_sum_pow_two]
  simp only [Finset.mem_image]
  constructor
  · intro ⟨x, hx, hxj⟩
    rw [← Fin.val_injective hxj]
    exact hx
  · intro hj
    exact ⟨j, hj, rfl⟩

end Nat
