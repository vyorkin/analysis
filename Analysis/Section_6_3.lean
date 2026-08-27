import Mathlib.Tactic
import Analysis.Section_6_1
import Analysis.Section_6_2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Analysis I, раздел 6.3: Супремумы и инфимумы последовательностей

Я старался сделать перевод максимально точным перефразированием оригинального текста. Когда
приходилось выбирать между более идиоматичным Lean-решением и более точным переводом, я, как
правило, выбирал второе. В частности, местами Lean-код можно было бы "заголфить", сделав его более
элегантным и идиоматичным, но я сознательно этого избегал.

Основные конструкции и результаты этого раздела:

- Супремумы и инфимумы последовательностей.

-/

namespace Chapter6

/-- Definition 6.3.1 (supremum of a sequence) -/
noncomputable abbrev Sequence.sup (a : Sequence) : EReal := sSup { x | ∃ n ≥ a.m, x = a n }

/-- Definition 6.3.1 (infimum of a sequence) -/
noncomputable abbrev Sequence.inf (a : Sequence) : EReal := sInf { x | ∃ n ≥ a.m, x = a n }

/-- Example 6.3.3 (a) -/
example : ((fun (n : ℕ) ↦ (-1 : ℝ)^(n+1)) : Sequence).sup = 1 := by sorry

/-- Example 6.3.3 (b) -/
example : ((fun (n : ℕ) ↦ (-1 : ℝ)^(n+1)) : Sequence).inf = -1 := by sorry

/-- Example 6.3.4 / Exercise 6.3.1 (a) -/
example : ((fun (n : ℕ) ↦ 1/((n : ℝ)+1)) : Sequence).sup = 1 := by sorry

/-- Example 6.3.4 / Exercise 6.3.1 (b) -/
example : ((fun (n : ℕ) ↦ 1/((n : ℝ)+1)) : Sequence).inf = 0 := by sorry

/-- Example 6.3.5 (a) -/
example : ((fun (n : ℕ) ↦ (n+1 : ℝ)) : Sequence).sup = ⊤ := by sorry

/-- Example 6.3.5 (b) -/
example : ((fun (n : ℕ) ↦ (n+1 : ℝ)) : Sequence).inf = 1 := by sorry

abbrev Sequence.BddAboveBy (a : Sequence) (M : ℝ) : Prop := ∀ n ≥ a.m, a n ≤ M

abbrev Sequence.BddAbove (a : Sequence) : Prop := ∃ M, a.BddAboveBy M

abbrev Sequence.BddBelowBy (a : Sequence) (M : ℝ) : Prop := ∀ n ≥ a.m, a n ≥ M

abbrev Sequence.BddBelow (a : Sequence) : Prop := ∃ M, a.BddBelowBy M

theorem Sequence.bounded_iff (a : Sequence) : a.IsBounded ↔ a.BddAbove ∧ a.BddBelow := by sorry

theorem Sequence.sup_of_bounded {a : Sequence} (h : a.IsBounded) : a.sup.IsFinite := by sorry

theorem Sequence.inf_of_bounded {a : Sequence} (h : a.IsBounded) : a.inf.IsFinite := by sorry

/-- Proposition 6.3.6 (a) (свойство точной верхней грани) / Exercise 6.3.2 -/
theorem Sequence.le_sup {a : Sequence} {n : ℤ} (hn : n ≥ a.m) : a n ≤ a.sup := by sorry

/-- Proposition 6.3.6 (b) (свойство точной верхней грани) / Exercise 6.3.2 -/
theorem Sequence.sup_le_upper {a : Sequence} {M : EReal} (h : ∀ n ≥ a.m, a n ≤ M) : a.sup ≤ M := by sorry

/-- Proposition 6.3.6 (c) (свойство точной верхней грани) / Exercise 6.3.2 -/
theorem Sequence.exists_between_lt_sup {a : Sequence} {y : EReal} (h : y < a.sup ) : 
    ∃ n ≥ a.m, y < a n ∧ a n ≤ a.sup := by sorry

/-- Remark 6.3.7 (a) -/
theorem Sequence.ge_inf {a : Sequence} {n : ℤ} (hn : n ≥ a.m) : a n ≥ a.inf := by sorry

/-- Remark 6.3.7 (b) -/
theorem Sequence.inf_ge_lower {a : Sequence} {M : EReal} (h : ∀ n ≥ a.m, a n ≥ M) : a.inf ≥ M := by sorry

/-- Remark 6.3.7 (c) -/
theorem Sequence.exists_between_gt_inf {a : Sequence} {y : EReal} (h : y > a.inf ) : 
    ∃ n ≥ a.m, y > a n ∧ a n ≥ a.inf := by sorry

abbrev Sequence.IsMonotone (a : Sequence) : Prop := ∀ n ≥ a.m, a (n+1) ≥ a n

abbrev Sequence.IsAntitone (a : Sequence) : Prop := ∀ n ≥ a.m, a (n+1) ≤ a n

/-- Proposition 6.3.8 (a) / Exercise 6.3.3 -/
theorem Sequence.convergent_of_monotone {a : Sequence} (hbound : a.BddAbove) (hmono : a.IsMonotone) : 
    a.Convergent := by sorry

/-- Proposition 6.3.8 (b) / Exercise 6.3.3 -/
theorem Sequence.lim_of_monotone {a : Sequence} (hbound : a.BddAbove) (hmono : a.IsMonotone) : 
    lim a = a.sup := by sorry

theorem Sequence.convergent_of_antitone {a : Sequence} (hbound : a.BddBelow) (hmono : a.IsAntitone) : 
    a.Convergent := by sorry

theorem Sequence.lim_of_antitone {a : Sequence} (hbound : a.BddBelow) (hmono : a.IsAntitone) : 
    lim a = a.inf := by sorry

theorem Sequence.convergent_iff_bounded_of_monotone {a : Sequence} (ha : a.IsMonotone) : 
    a.Convergent ↔ a.IsBounded := by sorry

theorem Sequence.bounded_iff_convergent_of_antitone {a : Sequence} (ha : a.IsAntitone) : 
    a.Convergent ↔ a.IsBounded := by sorry

/-- Example 6.3.9 (a) -/
noncomputable abbrev Example_6_3_9 (n : ℕ) := ⌊ Real.pi * 10^n ⌋ / (10 : ℝ)^n

/-- Example 6.3.9 (b) -/
example : (Example_6_3_9 : Sequence).IsMonotone := by sorry

/-- Example 6.3.9 (c) -/
example : (Example_6_3_9 : Sequence).BddAboveBy 4 := by sorry

/-- Example 6.3.9 (d) -/
example : (Example_6_3_9 : Sequence).Convergent := by sorry

/-- Example 6.3.9 (e) -/
example : lim (Example_6_3_9 : Sequence) ≤ 4 := by sorry

/-- Proposition 6.3.1 -/
theorem lim_of_exp {x : ℝ} (hpos : 0 < x) (hbound : x < 1) : 
    ((fun (n : ℕ) ↦ x^n) : Sequence).Convergent ∧ lim ((fun (n : ℕ) ↦ x^n) : Sequence) = 0 := by
  -- Это доказательство написано так, чтобы следовать структуре оригинального текста.
  set a := ((fun (n : ℕ) ↦ x^n) : Sequence)
  have why : a.IsAntitone := sorry
  have hbound : a.BddBelowBy 0 := by intro n _; positivity
  have hbound' : a.BddBelow := by use 0
  have hconv := a.convergent_of_antitone hbound' why
  set L := lim a
  have : lim ((fun (n : ℕ) ↦ x^(n+1)) : Sequence) = x * L := by
    rw [←(a.lim_smul x hconv).2]; congr; ext n; rfl
    simp [a, pow_succ', HSMul.hSMul, SMul.smul]
  have why2 : lim ((fun (n : ℕ) ↦ x^(n+1)) : Sequence) = lim ((fun (n : ℕ) ↦ x^n) : Sequence) := by sorry
  convert_to x * L = 1 * L at why2; simp [a,L]
  have hx : x ≠ 1 := by grind
  simp_all [-one_mul]

/-- Exercise 6.3.4 -/
theorem lim_of_exp' {x : ℝ} (hbound : x > 1) : ¬((fun (n : ℕ) ↦ x^n) : Sequence).Convergent := by sorry

end Chapter6
