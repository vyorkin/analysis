import Mathlib.Tactic
import Analysis.Section_9_3
import Analysis.Section_9_4


/-!
# Analysis I, раздел 9.7: Теорема о промежуточном значении

Я старался сделать перевод максимально точным перефразированием оригинального текста. Когда
приходилось выбирать между более идиоматичным Lean-решением и более точным переводом, я, как
правило, выбирал второе. В частности, местами Lean-код можно было бы "заголфить", сделав его более
элегантным и идиоматичным, но я сознательно этого избегал.

Основные конструкции и результаты этого раздела:
- Теорема о промежуточном значении.
-/

namespace Chapter9

/-- Theorem 9.7.1 (Теорема о промежуточном значении) -/
theorem intermediate_value {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hf : ContinuousOn f (.Icc a b)) {y : ℝ} (hy : y ∈ Set.Icc (f a) (f b) ∨ y ∈ Set.Icc (f b) (f a)) : 
  ∃ c ∈ Set.Icc a b, f c = y := by
  -- Это доказательство написано так, чтобы следовать структуре оригинального текста.
  obtain hy_left | hy_right := hy
  . by_cases hya : y = f a; use a; grind
    by_cases hyb : y = f b; use b; grind
    simp at hy_left
    replace hya : f a < y := by grind
    replace hyb : y < f b := by grind
    set E := {x | x ∈ Set.Icc a b ∧ f x < y}
    have hE : E ⊆ .Icc a b := fun x ⟨hx₁, hx₂⟩ ↦ hx₁
    have hE_bdd : BddAbove E := bddAbove_Icc.mono hE
    have hEa : a ∈ E := by simp [E, hya, le_of_lt hab]
    have hE_nonempty : E.Nonempty := by use a
    set c := sSup E
    have hc : c ∈ Set.Icc a b := by
      simp; split_ands
      . solve_by_elim [le_csSup]
      convert csSup_le_csSup bddAbove_Icc hE_nonempty hE
      grind [csSup_Icc]
    use c, hc
    have hfc_upper : f c ≤ y := by
      have hxe (n : ℕ) : ∃ x ∈ E, c - 1/(n+1 : ℝ) < x := by
        have : 1/(n+1 : ℝ) > 0 := by positivity
        replace : c - 1/(n+1 : ℝ) < sSup E := by linarith
        solve_by_elim [exists_lt_of_lt_csSup]
      set x := fun n ↦ (hxe n).choose
      have hx1 (n : ℕ) : x n ∈ E := (hxe n).choose_spec.1
      have hx2 (n : ℕ) : c - 1/(n+1 : ℝ) < x n := (hxe n).choose_spec.2
      have : Filter.atTop.Tendsto x (nhds c) := by
        apply Filter.Tendsto.squeeze (g := fun j ↦ c - 1/(j+1 : ℝ)) (h := fun j ↦ c) (f := x)
        . convert tendsto_one_div_add_atTop_nhds_zero_nat.const_sub c;simp
        . exact tendsto_const_nhds
        . exact fun n ↦ le_of_lt (hx2 n)
        exact fun n ↦ le_csSup hE_bdd (hx1 n)
      replace := this.comp_of_continuous (hf.continuousWithinAt hc) (fun n ↦ hE (hx1 n))
      have hfxny (n : ℕ) : f (x n) ≤ y := by specialize hx1 n; simp [E] at hx1; grind
      exact le_of_tendsto' this hfxny
    have hne : c < b := by grind
    have hfc_lower : y ≤ f c := by
      have : ∃ N : ℕ, ∀ n ≥ N, (c+1/(n+1 : ℝ)) < b := by
        choose N hN using exists_nat_gt (1/(b-c))
        use N; intro n hn
        have hpos : 0 < b-c := by linarith
        have : 1/(n+1 : ℝ) < b-c := by rw [one_div_lt] <;> (try positivity); apply hN.trans; norm_cast; linarith
        linarith
      choose N hN using this
      have hmem : ∀ n ≥ N, (c + 1/(n+1 : ℝ)) ∈ Set.Icc a b := by
        intro n hn
        simp [-one_div, le_of_lt (hN n hn)]
        have : 1/(n+1 : ℝ) > 0 := by positivity
        replace : c + 1/(n+1 : ℝ) > c := by linarith
        grind
      have : ∀ n ≥ N, c + 1/(n+1 : ℝ) ∉ E := by
        intro n _
        have : 1/(n+1 : ℝ) > 0 := by positivity
        replace : c + 1/(n+1 : ℝ) > c := by linarith
        solve_by_elim [notMem_of_csSup_lt]
      replace : ∀ n ≥ N, f (c + 1/(n+1 : ℝ)) ≥ y := by
        intro n hn; specialize this n hn; contrapose! this
        simp [E]
        have := hmem n hn
        simp_all
      have hconv : Filter.atTop.Tendsto (fun n : ℕ ↦ c + 1/(n+1 : ℝ)) (nhds c) := by
        convert tendsto_one_div_add_atTop_nhds_zero_nat.const_add c; simp
      replace hf := (hf.continuousWithinAt hc).tendsto
      rw [nhdsWithin.eq_1] at hf
      have hconv' : Filter.atTop.Tendsto (fun n : ℕ ↦ c + 1/(n+1 : ℝ)) (.principal (.Icc a b)) := by
        simp [-one_div, -Set.mem_Icc]; use N
      replace hconv' := Filter.tendsto_inf.mpr ⟨ hconv, hconv' ⟩
      apply ge_of_tendsto (hf.comp hconv') _
      simp [-one_div]; use N
    linarith
  sorry

open Classical in
noncomputable abbrev f_9_7_1 : ℝ → ℝ := fun x ↦ if x ≤ 0 then -1 else 1

example : 0 ∈ Set.Icc (f_9_7_1 (-1)) (f_9_7_1 1) ∧ ¬ ∃ x ∈ Set.Icc (-1) 1, f_9_7_1 x = 0 := by
  sorry

/-- Remark 9.7.2 -/
abbrev f_9_7_2 : ℝ → ℝ := fun x ↦ x^3 - x

example : f_9_7_2 (-2) = -6 := by sorry
example : f_9_7_2 2 = 6 := by sorry
example : f_9_7_2 (-1) = 0 := by sorry
example : f_9_7_2 0 = 0 := by sorry
example : f_9_7_2 1 = 0 := by sorry

/-- Remark 9.7.3 -/
example : ∃ x : ℝ, 0 ≤ x ∧ x ≤ 2 ∧ x^2 = 2 := by sorry

/-- Corollary 9.7.4 (Образы непрерывных функций) / Exercise 9.7.1 -/
theorem continuous_image_Icc {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hf : ContinuousOn f (.Icc a b)) {y : ℝ} (hy : sInf (f '' .Icc a b) ≤ y ∧ y ≤ sSup (f '' .Icc a b)) : ∃ c ∈ Set.Icc a b, f c = y := by
  sorry

theorem continuous_image_Icc' {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hf : ContinuousOn f (.Icc a b)) : f '' .Icc a b = .Icc (sInf (f '' .Icc a b)) (sSup (f '' .Icc a b)) := by
  sorry

/-- Exercise 9.7.2 -/
theorem exists_fixed_pt {f : ℝ → ℝ} (hf : ContinuousOn f (.Icc 0 1)) (hmap : f '' .Icc 0 1 ⊆ .Icc 0 1) : ∃ x ∈ Set.Icc 0 1, f x = x := by
  sorry

end Chapter9
