import Mathlib.Tactic
import Mathlib.Data.Real.Sign
import Analysis.Section_9_3
import Analysis.Section_9_4

/-!
# Analysis I, раздел 9.6: Принцип максимума

Я старался сделать перевод максимально точным перефразированием оригинального текста. Когда
приходилось выбирать между более идиоматичным Lean-решением и более точным переводом, я, как
правило, выбирал второе. В частности, местами Lean-код можно было бы "заголфить", сделав его более
элегантным и идиоматичным, но я сознательно этого избегал.

Основные конструкции и результаты этого раздела:
- Непрерывные функции на замкнутых ограниченных интервалах ограничены.
- Непрерывные функции на замкнутых ограниченных интервалах достигают своего максимума и минимума.
-/

namespace Chapter9

/-- Definition 9.6.1 -/
abbrev BddAboveOn (f : ℝ → ℝ) (X : Set ℝ) : Prop := ∃ M, ∀ x ∈ X, f x ≤ M

abbrev BddBelowOn (f : ℝ → ℝ) (X : Set ℝ) : Prop := ∃ M, ∀ x ∈ X, -M ≤ f x

abbrev BddOn (f : ℝ → ℝ) (X : Set ℝ) : Prop := ∃ M, ∀ x ∈ X, |f x| ≤ M

/-- Remark 9.6.2 -/
theorem BddOn.iff (f : ℝ → ℝ) (X : Set ℝ) : BddOn f X ↔ BddAboveOn f X ∧ BddBelowOn f X := by
  sorry

theorem BddOn.iff' (f : ℝ → ℝ) (X : Set ℝ) :  BddOn f X ↔ Bornology.IsBounded (f '' X) := by
  sorry

theorem BddOn.of_bounded {f : ℝ → ℝ} {X : Set ℝ} {M : ℝ} (h : ∀ x ∈ X, |f x| ≤ M) : BddOn f X := by use M

example : Continuous (fun x : ℝ ↦ x) := by sorry

example : ¬ BddOn (fun x : ℝ ↦ x) .univ  := by sorry

example : BddOn (fun x : ℝ ↦ x) (.Icc 1 2) := by sorry

example : ContinuousOn (fun x : ℝ ↦ 1/x) (.Ioo 0 1) := by sorry

example : ¬ BddOn (fun x : ℝ ↦ 1/x) (.Ioo 0 1) := by sorry

theorem why_7_6_3 {n : ℕ → ℕ} (hn : StrictMono n) (j : ℕ) : n j ≥ j := by sorry

/-- Lemma 9.6.3 -/
theorem BddOn.of_continuous_on_compact {a b : ℝ} (_h : a < b) {f : ℝ → ℝ} (hf : ContinuousOn f (.Icc a b) ) : 
  BddOn f (.Icc a b) := by
  -- Это доказательство написано так, чтобы следовать структуре оригинального текста.
  by_contra! hunbound; simp at hunbound
  set x := fun (n : ℕ) ↦ (hunbound n).choose
  have hx (n : ℕ) : a ≤ x n ∧ x n ≤ b ∧ n < |f (x n)| := by
    obtain ⟨⟨h1, h2⟩, h3⟩ := (hunbound n).choose_spec; exact ⟨h1, h2, h3⟩
  set X := Set.Icc a b
  observe hXclosed : IsClosed X
  observe hXbounded : Bornology.IsBounded X
  have haX (n : ℕ) : x n ∈ X := by simp [X]; specialize hx n; grind
  have ⟨ n, hn, ⟨ L, hLX, hconv ⟩ ⟩ := ((Heine_Borel X).mp ⟨ hXclosed, hXbounded ⟩) x haX
  have why (j : ℕ) : n j ≥ j := why_7_6_3 hn j
  replace hf := hf.continuousWithinAt hLX
  rw [ContinuousWithinAt.iff] at hf
  replace hf := hf.comp (fun j ↦ haX (n j)) hconv
  apply Metric.isBounded_range_of_tendsto at hf
  rw [isBounded_def] at hf; choose M hpos hM using hf
  choose j hj using exists_nat_gt M
  replace hx := (hx (n j)).2.2
  replace hM : f (x (n j)) ∈ Set.Icc (-M) M := by grind
  simp [←abs_le] at hM
  have : n j ≥ (j : ℝ) := by simp [why j]
  linarith

/- Definition 9.6.5.  Используйте тип `IsMaxOn` из Mathlib. -/
#check isMaxOn_iff
#check isMinOn_iff

/-- Remark 9.6.6 -/
theorem BddAboveOn.isMaxOn {f : ℝ → ℝ} {X : Set ℝ} {x₀ : ℝ} (h : IsMaxOn f X x₀) : BddAboveOn f X := by sorry

theorem BddBelowOn.isMinOn {f : ℝ → ℝ} {X : Set ℝ} {x₀ : ℝ} (h : IsMinOn f X x₀) : BddBelowOn f X := by sorry

/-- Proposition 9.6.7 (Принцип максимума) -/
theorem IsMaxOn.of_continuous_on_compact {a b : ℝ} (h : a < b) {f : ℝ → ℝ} (hf : ContinuousOn f (.Icc a b)) : 
  ∃ xmax ∈ Set.Icc a b, IsMaxOn f (.Icc a b) xmax := by
  -- Это доказательство написано так, чтобы следовать структуре оригинального текста.
  choose M hM using BddOn.of_continuous_on_compact h hf
  set E := f '' (.Icc a b)
  have hE : E ⊆ .Icc (-M) M := by rintro _ ⟨ x, hx, rfl ⟩; simp [hM x hx, ←abs_le]
  have hnon : E ≠ ∅ := by simp [E]; contrapose! h; grind [Set.Icc_eq_empty_iff]
  set m := sSup E
  have claim1 {y : ℝ} (hy : y ∈ E) : y ≤ m := le_csSup (BddAbove.mono hE bddAbove_Icc) hy
  suffices h : ∃ xmax, xmax ∈ Set.Icc a b ∧ f xmax = m
  . sorry
  have claim2 (n : ℕ) : ∃ x ∈ Set.Icc a b, m - 1/(n+1 : ℝ) < f x := by
    have : 1/(n+1 : ℝ) > 0 := by positivity
    replace : m - 1/(n+1 : ℝ) < sSup E := by linarith
    rw [←Set.nonempty_iff_ne_empty] at hnon
    apply exists_lt_of_lt_csSup hnon at this
    grind
  set x : ℕ → ℝ := fun n ↦ (claim2 n).choose
  have hx (n : ℕ) : x n ∈ Set.Icc a b := (claim2 n).choose_spec.1
  have hfx (n : ℕ) : m - 1/(n+1 : ℝ) < f (x n) := (claim2 n).choose_spec.2
  observe hclosed : IsClosed (.Icc a b)
  observe hbounded : Bornology.IsBounded (.Icc a b)
  have ⟨ n, hn, ⟨ xmax, hmax, hconv⟩ ⟩ := (Heine_Borel (.Icc a b)).mp ⟨hclosed, hbounded⟩ x hx
  use xmax, hmax
  have hn_lower (j : ℕ) : n j ≥ j := why_7_6_3 hn j
  have hconv' : Filter.atTop.Tendsto (fun j ↦ f (x (n j))) (nhds (f xmax)) :=
    hconv.comp_of_continuous (hf.continuousWithinAt hmax) (fun j ↦ hx (n j))
  have hlower (j : ℕ) : m - 1/(j+1 : ℝ) < f (x (n j)) := by
    apply lt_of_le_of_lt _ (hfx (n j)); gcongr; grind
  have hupper (j : ℕ) : f (x (n j)) ≤ m := by apply claim1; simp [Set.mem_image, E]; use x (n j), hx (n j)
  have hconvm : Filter.atTop.Tendsto (fun j ↦ f (x (n j))) (nhds m) := by
    apply Filter.Tendsto.squeeze (g := fun j ↦ m - 1/(j+1 : ℝ)) (h := fun _ ↦ m) (f := fun j ↦ f (x (n j)))
    . convert tendsto_one_div_add_atTop_nhds_zero_nat.const_sub m (c:=0); simp
    . exact tendsto_const_nhds
    . intro _; grind
    exact hupper
  exact tendsto_nhds_unique hconv' hconvm






theorem IsMinOn.of_continuous_on_compact {a b : ℝ} (h : a < b) {f : ℝ → ℝ} (hf : ContinuousOn f (.Icc a b)) : 
  ∃ xmin ∈ Set.Icc a b, IsMinOn f (.Icc a b) xmin := by
  sorry

example : IsMaxOn (fun x ↦ x^2) (.Icc (-2) 2) 2 := by sorry

example : IsMaxOn (fun x ↦ x^2) (.Icc (-2) 2) (-2) := by sorry

theorem sSup.of_isMaxOn {f : ℝ → ℝ} {X : Set ℝ} {x₀ : ℝ} (hx₀ : x₀ ∈ X) (h : IsMaxOn f X x₀) : 
  sSup (f '' X) = f x₀ := by
  apply IsGreatest.csSup_eq
  simp [IsGreatest, mem_upperBounds]
  refine ⟨ ⟨x₀, hx₀, rfl ⟩, h ⟩

theorem sInf.of_isMinOn {f : ℝ → ℝ} {X : Set ℝ} {x₀ : ℝ} (hx₀ : x₀ ∈ X) (h : IsMinOn f X x₀) : 
  sInf (f '' X) = f x₀ := by
  apply IsLeast.csInf_eq
  simp [IsLeast, mem_lowerBounds]
  refine ⟨ ⟨x₀, hx₀, rfl ⟩, h ⟩

theorem sSup.of_continuous_on_compact {a b : ℝ} (h : a < b) (f : ℝ → ℝ) (hf : ContinuousOn f (.Icc a b)) : ∃ xmax ∈ Set.Icc a b, sSup (f '' .Icc a b) = f xmax := by
  choose x hx h' using IsMaxOn.of_continuous_on_compact h hf
  grind [sSup.of_isMaxOn]

theorem sInf.of_continuous_on_compact {a b : ℝ} (h : a < b) (f : ℝ → ℝ) (hf : ContinuousOn f (.Icc a b)) : ∃ xmin ∈ Set.Icc a b, sInf (f '' .Icc a b) = f xmin := by
  choose x hx h' using IsMinOn.of_continuous_on_compact h hf
  grind [sInf.of_isMinOn]

/-- Exercise 9.6.1 a) -/
example : ∃ f : ℝ → ℝ, ContinuousOn f (.Ioo 1 2) ∧ BddOn f (.Ioo 1 2) ∧
  ∃ x₀ ∈ Set.Ioo 1 2, IsMinOn f (.Ioo 1 2) x₀ ∧
  ¬ ∃ x₀ ∈ Set.Ioo 1 2, IsMaxOn f (.Ioo 1 2) x₀
  := by sorry

/-- Exercise 9.6.1 b) -/
example : ∃ f : ℝ → ℝ, ContinuousOn f (.Ici 0) ∧ BddOn f (.Ici 0) ∧
  ∃ x₀ ∈ Set.Ici 0, IsMaxOn f (.Ici 0) x₀ ∧
  ¬ ∃ x₀ ∈ Set.Ici 0, IsMinOn f (.Ici 0) x₀
  := by sorry

/-- Exercise 9.6.1 c) -/
example : ∃ f : ℝ → ℝ, BddOn f (.Icc (-1) 1) ∧
  (¬ ∃ x₀ ∈ Set.Icc (-1) 1, IsMinOn f (.Icc (-1) 1) x₀) ∧
  (¬ ∃ x₀ ∈ Set.Icc (-1) 1, IsMaxOn f (.Icc (-1) 1) x₀)
  := by sorry

/-- Exercise 9.6.1 d) -/
example : ∃ f : ℝ → ℝ, ¬ BddAboveOn f (.Icc (-1) 1) ∧ ¬ BddBelowOn f (.Icc (-1) 1) := by sorry

/-- Exercise 9.6.2 -/
theorem BddOn.add (f g : ℝ → ℝ) (X : Set ℝ) (hf : BddOn f X) (hg : BddOn g X) : 
    BddOn (f + g) X := by sorry

theorem BddOn.sub (f g : ℝ → ℝ) (X : Set ℝ) (hf : BddOn f X) (hg : BddOn g X) : 
    BddOn (f - g) X := by sorry

theorem BddOn.mul (f g : ℝ → ℝ) (X : Set ℝ) (hf : BddOn f X) (hg : BddOn g X) : 
    BddOn (f * g) X := by sorry

def BddOn.div : Decidable (∀ (f g : ℝ → ℝ) (X : Set ℝ) (_ : ∀ x ∈ X, g x ≠ 0) (_ : BddOn f X)
    (_ : BddOn g X), (BddOn (f / g) X)) := by
  -- первой строкой этой конструкции должна быть либо `apply isTrue`, либо `apply isFalse`, в зависимости от того, считаете ли вы данное утверждение истинным или ложным.
  sorry

end Chapter9
