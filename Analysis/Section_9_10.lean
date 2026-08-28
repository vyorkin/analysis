import Mathlib.Tactic
/-!
# Analysis I, раздел 9.10: Пределы на бесконечности

Я старался сделать перевод максимально точным перефразированием оригинального текста. Когда
приходилось выбирать между более идиоматичным Lean-решением и более точным переводом, я, как
правило, выбирал второе. В частности, местами Lean-код можно было бы "заголфить", сделав его более
элегантным и идиоматичным, но я сознательно этого избегал.

Основные конструкции и результаты этого раздела:
- Минимальное API для версий Mathlib понятий прикосновения на бесконечности и предела на бесконечности.
-/

namespace Chapter9

/-- Definition 9.10.1 (бесконечная точка прикосновения). Мы используем {lean}`¬ BddAbove X` как нашу нотацию для того, что `+∞` является точкой прикосновения -/
theorem BddAbove.unbounded_iff (X : Set ℝ) : ¬ BddAbove X ↔ ∀ M, ∃ x ∈ X, x > M := by
  simp [bddAbove_def]

-- Переформулировка неограниченности сверху через `EReal`: `sSup` образа `X` в `EReal` равен `⊤`
theorem BddAbove.unbounded_iff' (X : Set ℝ) : ¬ BddAbove X ↔ sSup ((fun x : ℝ ↦ (x : EReal)) '' X) = ⊤ := by
  erw [sSup_eq_top, unbounded_iff]
  constructor
  . intro h M hM; choose x hx hxM using h M.toReal
    use x, ⟨x, hx, rfl⟩; revert M; simp [EReal.forall]; tauto
  intro h M; specialize h (M : EReal) (EReal.coe_lt_top M)
  obtain ⟨_, ⟨x, hx, rfl⟩, hMx⟩ := h; exact ⟨x, hx, EReal.coe_lt_coe_iff.mp hMx⟩

-- `X` не ограничено снизу тогда и только тогда, когда для любого `M` найдётся элемент `X`, меньший `M`
theorem BddBelow.unbounded_iff (X : Set ℝ) : ¬ BddBelow X ↔ ∀ M, ∃ x ∈ X, x < M := by
  simp [bddBelow_def]

-- Переформулировка неограниченности снизу через `EReal`: `sInf` образа `X` в `EReal` равен `⊥`
theorem BddBelow.unbounded_iff' (X : Set ℝ) : ¬ BddBelow X ↔ sInf ((fun x : ℝ ↦ (x : EReal)) '' X) = ⊥ := by
  simp [sInf_eq_bot, unbounded_iff]
  constructor
  . intro h M hM; choose x hx hxM using h M.toReal
    use x, hx; revert M; simp [EReal.forall]
  intro h M; specialize h (M : EReal) ?_ <;>simp_all

/-- Definition 9.10.13 (предел на бесконечности) -/
theorem Filter.Tendsto.AtTop.iff {X : Set ℝ} (f : ℝ → ℝ) (L : ℝ) : Filter.Tendsto f (.atTop ⊓ .principal X) (nhds L) ↔ ∀ ε > (0 : ℝ), ∃ M, ∀ x ∈ X ∩ .Ici M, |f x - L| < ε := by
  rw [LinearOrderedAddCommGroup.tendsto_nhds]
  peel with ε hε
  simp [Filter.eventually_inf_principal]
  aesop

/-- Exercise 9.10.4 -/
example : Filter.Tendsto (fun x : ℝ ↦ 1/x) (.atTop ⊓ .principal (.Ioi 0)) (nhds 0) := by
  sorry

open Classical in
/-- Exercise 9.10.1 -/
example (a : ℕ → ℝ) (L : ℝ) : Filter.Tendsto (fun x : ℝ ↦ (if h : (∃ n : ℕ, x = n) then a h.choose else 0)) (.atTop ⊓ .principal ((fun n : ℕ ↦ (n : ℝ)) '' .univ)) (nhds L) ↔ Filter.atTop.Tendsto a (nhds L) := by
  sorry

end Chapter9
