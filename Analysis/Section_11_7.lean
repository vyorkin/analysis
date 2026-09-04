import Mathlib.Tactic
import Mathlib.Topology.Instances.Irrational
import Analysis.Section_11_4

/-!
# Analysis I, раздел 11.7: Неинтегрируемая по Риману функция

Я старался сделать перевод максимально точным перефразированием оригинального текста. Когда
приходилось выбирать между более идиоматичным Lean-решением и более точным переводом, я, как
правило, выбирал второе. В частности, местами Lean-код можно было бы "заголфить", сделав его более
элегантным и идиоматичным, но я сознательно этого избегал.

Основные конструкции и результаты этого раздела:
- Пример ограниченной функции на компактном интервале, не интегрируемой по Риману.

-/

namespace Chapter11
open BoundedInterval Chapter9

/-- Утверждение 11.7.1 -/
theorem not_integrable : BddOn f_9_3_21 (Icc 0 1) ∧ ¬ IntegrableOn f_9_3_21 (Icc 0 1) := by
  -- Это доказательство адаптировано из структуры оригинального текста.
  have hbdd : BddOn f_9_3_21 (Icc 0 1):= by
    use 1; intro x _; by_cases h : ∃ y : ℚ, y = x <;> simp [f_9_3_21, h]
  refine ⟨ hbdd, ?_ ⟩
  have hsup (P : Partition (Icc 0 1)) : ∀ J ∈ P.intervals, (sSup (f_9_3_21 '' (J : Set ℝ))) * |J|ₗ = |J|ₗ := by
    intro J hJ; by_cases hJ0 : |J|ₗ = 0
    . simp [hJ0]
    have hJ0' := hJ0
    rw [←length_of_subsingleton] at hJ0
    convert (one_mul _)
    apply le_antisymm
    . apply csSup_le
      . contrapose! hJ0; simp_all
      grind
    apply le_csSup_of_le _ _ (show (1 : ℝ) ≤ 1 by norm_num)
    . rw [bddAbove_def]; use 1; grind
    simp at hJ0'; choose z hz hz' using Dense.exists_between (Rat.denseRange_cast (𝕜 := ℝ)) hJ0'
    simp at *; obtain ⟨ q, rfl ⟩ := hz
    have hq_mem : (q : ℝ) ∈ (J : Set ℝ) := (subset_iff _ _).mp (Ioo_subset J) (by simp [hz'])
    exact ⟨q, hq_mem⟩
  have hupper (P : Partition (Icc 0 1)) : upper_riemann_sum f_9_3_21 P = 1 := by
    simp [upper_riemann_sum]
    calc
      _ = ∑ J ∈ P.intervals, |J|ₗ := by apply Finset.sum_congr rfl; grind
      _ = _ := by simp [Partition.sum_of_length _ P]
  replace hupper : upper_integral f_9_3_21 (Icc 0 1) = 1 := by
    simp [upper_integ_eq_inf_upper_sum hbdd, hupper]
  have hinf (P : Partition (Icc 0 1)) : ∀ J ∈ P.intervals, (sInf (f_9_3_21 '' (J : Set ℝ))) * |J|ₗ = 0 := by
    intro J hJ; by_cases hJ0 : |J|ₗ = 0
    . simp [hJ0]
    have hJ0' := hJ0
    rw [←length_of_subsingleton] at hJ0
    convert (zero_mul _)
    apply le_antisymm
    . apply csInf_le_of_le _ _ (show (0 : ℝ) ≤ 0 by norm_num)
      . rw [bddBelow_def]; use 0; grind
      simp at hJ0'
      choose z hz hz' using Dense.exists_between dense_irrational hJ0'
      simp at *
      refine ⟨ z, (subset_iff _ _).mp (Ioo_subset J) (by simp [hz']), ?_ ⟩
      intro q; contrapose! hz; simp [←hz]
    apply le_csInf
    . contrapose! hJ0; simp_all
    grind
  have hlower (P : Partition (Icc 0 1)) : lower_riemann_sum f_9_3_21 P = 0 := by
    simp [lower_riemann_sum]; calc
      _ = ∑ J ∈ P.intervals, (0 : ℝ) := by apply Finset.sum_congr rfl; grind
      _ = _ := by simp
  replace hlower : lower_integral f_9_3_21 (Icc 0 1) = 0 := by
    simp [lower_integ_eq_sup_lower_sum hbdd, hlower]
  grind


end Chapter11
