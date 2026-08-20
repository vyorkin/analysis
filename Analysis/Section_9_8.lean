import Mathlib.Tactic
import Analysis.Section_9_6

/-!
# Analysis I, раздел 9.8: Монотонные функции

Я старался сделать перевод максимально точным перефразированием оригинального текста. Когда
приходилось выбирать между более идиоматичным Lean-решением и более точным переводом, я, как
правило, выбирал второе. В частности, местами Lean-код можно было бы "заголфить", сделав его более
элегантным и идиоматичным, но я сознательно этого избегал.

Основные конструкции и результаты этого раздела:
- Обзор понятий монотонности из Mathlib.
-/

namespace Chapter9

/-- Definition 9.8.1 -/
theorem MonotoneOn.iff {X : Set ℝ} (f : ℝ → ℝ) : MonotoneOn f X  ↔ ∀ x ∈ X, ∀ y ∈ X, y > x → f y ≥ f x := by
  constructor
  . intros; solve_by_elim [le_of_lt]
  intro _ _ _ _ _ hxy; obtain hxy | rfl := le_iff_lt_or_eq.mp hxy
  . solve_by_elim
  simp

theorem StrictMono.iff {X : Set ℝ} (f : ℝ → ℝ) : StrictMonoOn f X  ↔ ∀ x ∈ X, ∀ y ∈ X, y > x → f y > f x := by
  constructor <;> intros <;> solve_by_elim

theorem AntitoneOn.iff {X : Set ℝ} (f : ℝ → ℝ) : AntitoneOn f X  ↔ ∀ x ∈ X, ∀ y ∈ X, y > x → f y ≤ f x := by
  constructor
  . intros; solve_by_elim [le_of_lt]
  intro _ _ _ _ _ hxy; obtain hxy | rfl := le_iff_lt_or_eq.mp hxy
  . solve_by_elim
  simp

theorem StrictAntitone.iff {X : Set ℝ} (f : ℝ → ℝ) : StrictAntiOn f X  ↔ ∀ x ∈ X, ∀ y ∈ X, y > x → f y < f x := by
  constructor <;> intros <;> solve_by_elim

/-- Examples 9.8.2 -/
example : StrictMonoOn (fun x : ℝ ↦ x^2) (.Ici 0) := by sorry

example : StrictAntiOn (fun x : ℝ ↦ x^2) (.Iic 0) := by sorry

example : ¬ MonotoneOn (fun x : ℝ ↦ x^2) .univ := by sorry

example : ¬ AntitoneOn (fun x : ℝ ↦ x^2) .univ := by sorry

example {X : Set ℝ} {f : ℝ → ℝ} (hf : StrictMonoOn f X) : MonotoneOn f X := by sorry

example (X : Set ℝ) : MonotoneOn (fun x : ℝ ↦ (6 : ℝ)) X := by sorry

example (X : Set ℝ) : AntitoneOn (fun x : ℝ ↦ (6 : ℝ)) X := by sorry

#check nontrivial_iff

example {X : Set ℝ} (hX : Nontrivial X) : ¬ StrictMonoOn (fun x : ℝ ↦ (6 : ℝ)) X := by sorry

example (X : Set ℝ) (hX : Nontrivial X) : ¬ StrictAntiOn (fun x : ℝ ↦ (6 : ℝ)) X := by sorry

example : ∃ (X : Set ℝ) (f : ℝ → ℝ), ContinuousOn f X ∧ ¬ MonotoneOn f X ∧ ¬ AntitoneOn f X := by sorry

example : ∃ (X : Set ℝ) (f : ℝ → ℝ), MonotoneOn f X ∧ ¬ ContinuousOn f X := by sorry

/-- Proposition 9.8.3 / Exercise 9.8.4 -/
theorem MonotoneOn.exist_inverse {a b : ℝ} (h : a < b) (f : ℝ → ℝ) (hcont : ContinuousOn f (.Icc a b)) (hmono : StrictMonoOn f (.Icc a b)) : 
  f '' (.Icc a b) = .Icc (f a) (f b) ∧
  ∃ finv : ℝ → ℝ, ContinuousOn finv (.Icc (f a) (f b)) ∧ StrictMonoOn finv (.Icc (f a) (f b)) ∧
  finv '' (.Icc (f a) (f b)) = .Icc a b ∧
  (∀ x ∈ Set.Icc a b, finv (f x) = x) ∧
  ∀ y ∈ Set.Icc (f a) (f b), f (finv y) = y
   := by
  sorry

/-- Example 9.8.4 -/
example {R : ℝ} (hR : R > 0) {n : ℕ} (hn : n > 0) : ∃ g : ℝ → ℝ, ∀ x ∈ Set.Icc 0 (R^n), (g x)^n = x := by
  set f : ℝ → ℝ := fun x ↦ x^n
  have hcont : ContinuousOn f (.Icc 0 R) := by fun_prop
  have hmono : StrictMonoOn f (.Icc 0 R) := by
    intro _ hx _ _ hxy; simp_all [f]
    apply pow_lt_pow_left₀ hxy <;> grind
  obtain ⟨ g, ⟨ _, _, _, _, hg⟩ ⟩ := (MonotoneOn.exist_inverse (by positivity) f hcont hmono).2
  simp only [f, zero_pow (by positivity)] at hg; use g

/-- Exercise 9.8.1 -/
theorem IsMaxOn.of_monotone_on_compact {a b : ℝ} (h : a < b) {f : ℝ → ℝ} (hf : MonotoneOn f (.Icc a b)) : 
  ∃ xmax ∈ Set.Icc a b, IsMaxOn f (.Icc a b) xmax := by sorry

theorem IsMaxOn.of_strictmono_on_compact {a b : ℝ} (h : a < b) {f : ℝ → ℝ} (hf : StrictMonoOn f (.Icc a b)) : 
  ∃ xmax ∈ Set.Icc a b, IsMaxOn f (.Icc a b) xmax := by sorry

theorem IsMaxOn.of_antitone_on_compact {a b : ℝ} (h : a < b) {f : ℝ → ℝ} (hf : AntitoneOn f (.Icc a b)) : 
  ∃ xmax ∈ Set.Icc a b, IsMaxOn f (.Icc a b) xmax := by sorry

theorem IsMaxOn.of_strictantitone_on_compact {a b : ℝ} (h : a < b) {f : ℝ → ℝ} (hf : StrictAntiOn f (.Icc a b)) : 
  ∃ xmax ∈ Set.Icc a b, IsMaxOn f (.Icc a b) xmax := by
  sorry

theorem BddOn.of_monotone {a b : ℝ} {f : ℝ → ℝ} (hf : MonotoneOn f (.Icc a b)) : 
  BddOn f (.Icc a b) := by
  sorry

theorem BddOn.of_antitone {a b : ℝ} {f : ℝ → ℝ} (hf : AntitoneOn f (.Icc a b)) : 
  BddOn f (.Icc a b) := by
  sorry



/-- Exercise 9.8.2 -/
theorem no_strictmono_intermediate_value : 
    ∃ (a b : ℝ) (hab : a < b) (f : ℝ → ℝ) (hf : StrictMonoOn f (.Icc a b)),
      ∃ y, (y ∈ Set.Icc (f a) (f b) ∨ y ∈ Set.Icc (f b) (f a)) ∧
      ¬ ∃ c ∈ Set.Icc a b, f c = y := by sorry

theorem no_monotone_intermediate_value : 
    ∃ (a b : ℝ) (hab : a < b) (f : ℝ → ℝ) (hf : MonotoneOn f (.Icc a b)),
      ∃ y, (y ∈ Set.Icc (f a) (f b) ∨ y ∈ Set.Icc (f b) (f a)) ∧
      ¬ ∃ c ∈ Set.Icc a b, f c = y := by sorry

theorem no_strictanti_intermediate_value : 
    ∃ (a b : ℝ) (hab : a < b) (f : ℝ → ℝ) (hf : StrictAntiOn f (.Icc a b)),
      ∃ y, (y ∈ Set.Icc (f a) (f b) ∨ y ∈ Set.Icc (f b) (f a)) ∧
      ¬ ∃ c ∈ Set.Icc a b, f c = y := by sorry

theorem no_antitone_intermediate_value : 
    ∃ (a b : ℝ) (hab : a < b) (f : ℝ → ℝ) (hf : AntitoneOn f (.Icc a b)),
      ∃ y, (y ∈ Set.Icc (f a) (f b) ∨ y ∈ Set.Icc (f b) (f a)) ∧
      ¬ ∃ c ∈ Set.Icc a b, f c = y := by sorry

/-- Exercise 9.8.3 -/
theorem mono_of_continuous_inj {a b : ℝ} (h : a < b) {f : ℝ → ℝ}
  (hf : ContinuousOn f (.Icc a b))
  (hinj : Function.Injective (fun x : Set.Icc a b ↦ f x )) : 
  StrictMonoOn f (.Icc a b) ∨ StrictAntiOn f (.Icc a b) := by
  sorry

/-- Exercise 9.8.4 (без непрерывности) -/
def MonotoneOn.exist_inverse_without_continuity : 
    Decidable (∀ (a b : ℝ) (_ : a < b) (f : ℝ → ℝ) (_ : StrictMonoOn f (.Icc a b)),
      f '' (.Icc a b) = .Icc (f a) (f b) ∧
      ∃ finv : ℝ → ℝ, ContinuousOn finv (.Icc (f a) (f b)) ∧ StrictMonoOn finv (.Icc (f a) (f b)) ∧
        finv '' (.Icc (f a) (f b)) = .Icc a b ∧
        (∀ x ∈ Set.Icc a b, finv (f x) = x) ∧
        ∀ y ∈ Set.Icc (f a) (f b), f (finv y) = y) := by
  -- apply isFalse: одной лишь строгой монотонности недостаточно, чтобы гарантировать непрерывность обратной функции
  sorry

/-- Exercise 9.8.4 (без строгой монотонности) -/
def MonotoneOn.exist_inverse_without_strictmono : 
    Decidable (∀ (a b : ℝ) (_ : a < b) (f : ℝ → ℝ) (_ : ContinuousOn f (.Icc a b))
        (_ : MonotoneOn f (.Icc a b)),
      f '' (.Icc a b) = .Icc (f a) (f b) ∧
      ∃ finv : ℝ → ℝ, ContinuousOn finv (.Icc (f a) (f b)) ∧ StrictMonoOn finv (.Icc (f a) (f b)) ∧
        finv '' (.Icc (f a) (f b)) = .Icc a b ∧
        (∀ x ∈ Set.Icc a b, finv (f x) = x) ∧
        ∀ y ∈ Set.Icc (f a) (f b), f (finv y) = y) := by
  -- apply isFalse: например, у постоянной монотонной f на [a,b] нет строгой обратной функции
  sorry


/-
Exercise 9.8.4: сформулируйте и докажите аналог `MonotoneOn.exist_inverse` для убывающих
(`Antitone`) функций.
-/
-- theorem AntitoneOn.exist_inverse {a b:ℝ} (h: a < b) (f: ℝ → ℝ) (hcont: ContinuousOn f (.Icc a b)) (hmono: StrictAntiOn f (.Icc a b)) : sorry := by sorry

/-- Биекция между натуральными числами и рациональными числами. -/
noncomputable abbrev q_9_8_5 : ℕ ≃ ℚ := nonempty_equiv_of_countable.some

noncomputable abbrev g_9_8_5 : ℚ → ℝ := fun q ↦ (2 : ℝ)^(-q_9_8_5.symm q : ℤ)

noncomputable abbrev f_9_8_5 : ℝ → ℝ := fun x ↦ ∑' r : {r : ℚ // (r : ℝ) < x}, g_9_8_5 r

/-- Exercise 9.8.5(a) -/
theorem StrictMonoOn.of_f_9_8_5 : StrictMonoOn f_9_8_5 .univ := by
  sorry

/-- Exercise 9.8.5(b) -/
theorem ContinuousAt.of_f_9_8_5' (r : ℚ) : ¬ ContinuousAt f_9_8_5 r := by
  sorry

/-- Exercise 9.8.5(c) -/
theorem ContinuousAt.of_f_9_8_5 {x : ℝ} (hx : ¬ ∃ r : ℚ, x = r) : ContinuousAt f_9_8_5 x := by
  sorry

end Chapter9
