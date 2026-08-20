import Mathlib.Tactic

/-!
# Analysis I, раздел 10.3: Монотонные функции и производные

Я старался сделать перевод максимально точным перефразированием оригинального текста. Когда
приходилось выбирать между более идиоматичным Lean-решением и более точным переводом, я, как
правило, выбирал второе. В частности, местами Lean-код можно было бы "заголфить", сделав его более
элегантным и идиоматичным, но я сознательно этого избегал.

Основные конструкции и результаты этого раздела:
- Связь между монотонностью и дифференцируемостью.

-/

namespace Chapter10

/-- Proposition 10.3.1 / Exercise 10.3.1 -/
theorem derivative_of_monotone (X : Set ℝ) {x₀ : ℝ} (hx₀ : ClusterPt x₀ (.principal (X \ {x₀})))
  {f : ℝ → ℝ} (hmono : Monotone f) (hderiv : DifferentiableWithinAt ℝ f X x₀) : 
    derivWithin f X x₀ ≥ 0 := by
  sorry

theorem derivative_of_antitone (X : Set ℝ) {x₀ : ℝ} (hx₀ : ClusterPt x₀ (.principal (X \ {x₀})))
  {f : ℝ → ℝ} (hmono : Antitone f) (hderiv : DifferentiableWithinAt ℝ f X x₀) : 
    derivWithin f X x₀ ≤ 0 := by
  sorry

/-- Proposition 10.3.3 / Exercise 10.3.4 -/
theorem strictMono_of_positive_derivative {a b : ℝ} {f : ℝ → ℝ}
  (hderiv : DifferentiableOn ℝ f (.Icc a b)) (hpos : ∀ x ∈ Set.Ioo a b, derivWithin f (.Icc a b) x > 0) : 
    StrictMonoOn f (.Icc a b) := by
  sorry

theorem strictAnti_of_negative_derivative {a b : ℝ} {f : ℝ → ℝ}
  (hderiv : DifferentiableOn ℝ f (.Icc a b)) (hneg : ∀ x ∈ Set.Ioo a b, derivWithin f (.Icc a b) x < 0) : 
    StrictAntiOn f (.Icc a b) := by
  sorry

/-- Example 10.3.2 -/
example : ∃ f : ℝ → ℝ, Continuous f ∧ StrictMono f ∧ ¬ DifferentiableAt ℝ f 0 := by sorry

/-- Exercise 10.3.3 -/
example : ∃ f : ℝ → ℝ, StrictMono f ∧ Differentiable ℝ f ∧ deriv f 0 = 0 := by sorry

/-- Exercise 10.3.5 -/
example : ∃ (X : Set ℝ) (f : ℝ → ℝ), DifferentiableOn ℝ f X ∧
  (∀ x ∈ X, derivWithin f X x > 0) ∧ ¬ StrictMonoOn f X  := by
  sorry

end Chapter10
