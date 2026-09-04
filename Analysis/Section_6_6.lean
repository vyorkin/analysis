import Mathlib.Tactic
import Analysis.Section_6_5

/-!
# Analysis I, раздел 6.6: Подпоследовательности

Я старался сделать перевод максимально точным перефразированием оригинального текста. Когда
приходилось выбирать между более идиоматичным Lean-решением и более точным переводом, я, как
правило, выбирал второе. В частности, местами Lean-код можно было бы "заголфить", сделав его более
элегантным и идиоматичным, но я сознательно этого избегал.

Основные конструкции и результаты этого раздела:

- Определение подпоследовательности.
-/

namespace Chapter6

/-- Определение 6.6.1 -/
abbrev Sequence.subseq (a b : ℕ → ℝ) : Prop := ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ n, b n = a (f n)

/-- Пример 6.6.2 -/
example (a : ℕ → ℝ) : Sequence.subseq a (fun n ↦ a (2 * n)) := by sorry

example {f : ℕ → ℕ} (hf : StrictMono f) : Function.Injective f := by sorry

example : 
    Sequence.subseq (fun n ↦ if Even n then 1 + (10 : ℝ)^(-(n/2 : ℤ)-1) else (10 : ℝ)^(-(n/2 : ℤ)-1))
    (fun n ↦ 1 + (10 : ℝ)^(-(n : ℤ)-1)) := by
  sorry

example : 
    Sequence.subseq (fun n ↦ if Even n then 1 + (10 : ℝ)^(-(n/2 : ℤ)-1) else (10 : ℝ)^(-(n/2 : ℤ)-1))
    (fun n ↦ (10 : ℝ)^(-(n : ℤ)-1)) := by
  sorry

/-- Лемма 6.6.4 (рефлексивность) / Упражнение 6.6.1 -/
theorem Sequence.subseq_self (a : ℕ → ℝ) : Sequence.subseq a a := by sorry

/-- Лемма 6.6.4 (транзитивность) / Упражнение 6.6.1 -/
theorem Sequence.subseq_trans {a b c : ℕ → ℝ} (hab : Sequence.subseq a b) (hbc : Sequence.subseq b c) :
    Sequence.subseq a c := by sorry

/-- Утверждение 6.6.5 / Упражнение 6.6.4 -/
theorem Sequence.convergent_iff_subseq (a : ℕ → ℝ) (L : ℝ) : 
    (a : Sequence).TendsTo L ↔ ∀ b : ℕ → ℝ, Sequence.subseq a b → (b : Sequence).TendsTo L := by
  sorry

/-- Утверждение 6.6.6 / Упражнение 6.6.5 -/
theorem Sequence.limit_point_iff_subseq (a : ℕ → ℝ) (L : ℝ) : 
    (a : Sequence).LimitPoint L ↔ ∃ b : ℕ → ℝ, Sequence.subseq a b ∧ (b : Sequence).TendsTo L := by
  sorry

/-- Теорема 6.6.8 (теорема Больцано-Вейерштрасса) -/
theorem Sequence.convergent_of_subseq_of_bounded {a : ℕ→ ℝ} (ha : (a : Sequence).IsBounded) :
    ∃ b : ℕ → ℝ, Sequence.subseq a b ∧ (b : Sequence).Convergent := by
  -- Это доказательство написано так, чтобы следовать структуре оригинального текста.
  obtain ⟨ ⟨ L_plus, hL_plus ⟩, ⟨ _, _ ⟩ ⟩ := finite_limsup_liminf_of_bounded ha
  have := limit_point_of_limsup hL_plus
  rw [limit_point_iff_subseq] at this; peel 2 this; solve_by_elim

/-- Упражнение 6.6.2 -/
def Sequence.exist_subseq_of_subseq : 
  Decidable (∃ a b : ℕ → ℝ, a ≠ b ∧ Sequence.subseq a b ∧ Sequence.subseq b a) := by
    -- Первой строкой этой конструкции должна быть `apply isTrue` или `apply isFalse`.
    sorry

/--
  Упражнение 6.6.3. Вам может пригодиться API вокруг {name}`Nat.find` из Mathlib
  (а также {syntax command}`open Classical`, чтобы избежать проблем с разрешимостью)
-/
theorem Sequence.subseq_of_unbounded {a : ℕ → ℝ} (ha : ¬ (a : Sequence).IsBounded) : 
    ∃ b : ℕ → ℝ, Sequence.subseq a b ∧ (b : Sequence)⁻¹.TendsTo 0 := by
  sorry


end Chapter6
