import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Analysis I, Appendix A.6: Некоторые примеры доказательств и кванторов

Несколько примеров доказательств и кванторов в Lean

-/

/-- Утверждение A.6.1 -/
example : ∀ ε > (0 : ℝ), ∃ δ > 0, 2 * δ < ε := by
  intro ε hε
  use ε / 3
  constructor
  . positivity
  . linarith

example : ¬ ∃ δ > 0, ∀ ε > (0 : ℝ), 2 * δ < ε := by
  sorry

open Real in
/-- Утверждение A.6.2. Доказательство ниже несколько неидиоматично для Lean, но
иллюстрирует, как реализовать доказательство вида «пусть ε — величина, которую выберем позже». -/
example : ∃ ε > 0, ∀ x, 0 < x ∧ x < ε → sin x > x / 2 := by
  use ?eps  -- выберем это позже
  constructor
  swap -- отложим проверку положительности на потом
  rintro x ⟨hpos, hx⟩
  have hderiv : deriv sin = cos := by
    ext x
    apply HasDerivAt.deriv
    apply hasDerivAt_sin
  have := exists_deriv_eq_slope sin hpos (by fun_prop) (by fun_prop)
  simp [hderiv] at this
  obtain ⟨ y, ⟨ hy1, hy2 ⟩, hy3 ⟩ := this
  suffices hcosy : cos y > 1/2
  . rw [hy3, gt_iff_lt, ←(mul_lt_mul_iff_right₀ hpos)] at hcosy
    rw [gt_iff_lt]
    convert hcosy using 1
    . ring
    field_simp
  suffices ybound : y < π/3
  . have := cos_lt_cos_of_nonneg_of_le_pi (le_of_lt hy1) (by linarith) ybound
    simp only [cos_pi_div_three, ←gt_iff_lt] at this
    exact this
  have : y < ?eps := by
    exact hy2.trans hx
  pick_goal 3  -- Теперь пора выбрать ε
  . exact π/3
  . exact this
  positivity

open Real in
/-- Утверждение A.6.2: более идиоматичное доказательство -/
example : ∃ ε > 0, ∀ x, 0 < x ∧ x < ε → sin x > x / 2 := by
  use π/3, by positivity
  intro x ⟨ hpos, hx ⟩
  have hderiv : deriv sin = cos := by
    ext x
    apply HasDerivAt.deriv
    apply hasDerivAt_sin
  have := exists_deriv_eq_slope sin hpos (by fun_prop) (by fun_prop)
  simp [hderiv] at this
  obtain ⟨ y, ⟨ hy1, hy2 ⟩, hy3 ⟩ := this
  have ybound : y < π/3 := by linarith
  have hcosy := cos_lt_cos_of_nonneg_of_le_pi (le_of_lt hy1) (by linarith) ybound
  simp only [cos_pi_div_three, ←gt_iff_lt] at hcosy
  rw [hy3, gt_iff_lt, ←(mul_lt_mul_iff_right₀ hpos)] at hcosy
  rw [gt_iff_lt]
  convert hcosy using 1
  . ring
  field_simp
