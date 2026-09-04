import Mathlib.Tactic

/-!
# Analysis I, раздел 4.4: пробелы в рациональных числах

Я старался сделать перевод максимально точным перефразированием оригинального текста. Когда
приходилось выбирать между более идиоматичным Lean-решением и более точным переводом, я, как
правило, выбирал второе. В частности, местами Lean-код можно было бы "заголфить", сделав его более
элегантным и идиоматичным, но я сознательно этого избегал.

Основные конструкции и результаты этого раздела:

- Иррациональность √2 и связанные с этим факты о рациональных числах

Многие результаты здесь можно установить быстрее, более активно опираясь на Mathlib API; можно
поставить себе такое упражнение.

## Советы от прошлых пользователей

Пользователи, прошедшие упражнения этого раздела, могут присылать свои советы для будущих
пользователей в виде PR.

- (Добавьте совет сюда)

-/

/-- Утверждение 4.4.1 (Расположение целых чисел среди рациональных) / Упражнение 4.4.1 -/
theorem Rat.between_int (x : ℚ) : ∃! n : ℤ, n ≤ x ∧ x < n+1 := by
  sorry

-- Для любого рационального `x` найдётся натуральное число, строго его превосходящее (архимедово свойство)
theorem Nat.exists_gt (x : ℚ) : ∃ n : ℕ, n > x := by
  sorry

/-- Утверждение 4.4.3 (Расположение рациональных чисел между другими) -/
theorem Rat.exists_between_rat {x y : ℚ} (h : x < y) : ∃ z : ℚ, x < z ∧ z < y := by
  -- Это доказательство написано так, чтобы следовать структуре оригинального текста.
  -- Читателю предлагается найти более короткие доказательства, например,
  -- используя тактику `linarith` из Mathlib.
  use (x + y)/2
  have h' : x/2 < y/2 := by
    rw [show x/2 = x*(1/2) by ring, show y/2 = y*(1/2) by ring]
    apply mul_lt_mul_of_pos_right h -- (hbc : b < c) (ha : 0 < a) : b * a < c * a
    positivity
  constructor
  . convert add_lt_add_right h' (x/2) using 1 <;> ring
  convert add_lt_add_right h' (y/2) using 1 <;> ring

/-- Упражнение 4.4.2 (a) -/
theorem Nat.no_infinite_descent : ¬ ∃ a : ℕ → ℕ, ∀ n, a (n+1) < a n := by
  sorry

/-- Упражнение 4.4.2 (b) -/
def Int.infinite_descent : Decidable (∃ a : ℕ → ℤ, ∀ n, a (n+1) < a n) := by
  -- первой строкой этой конструкции должно быть либо `apply isTrue`, либо `apply isFalse`.
  sorry

/-- Упражнение 4.4.2 (b') -/
def Rat.pos_infinite_descent : Decidable (∃ a : ℕ → {x : ℚ // 0 < x}, ∀ n, a (n+1) < a n) := by
  -- первой строкой этой конструкции должно быть либо `apply isTrue`, либо `apply isFalse`.
  sorry

#check even_iff_exists_two_mul
#check odd_iff_exists_bit1

-- Каждое натуральное число либо чётно, либо нечётно
theorem Nat.even_or_odd'' (n : ℕ) : Even n ∨ Odd n := by
  sorry

-- Натуральное число не может быть одновременно чётным и нечётным
theorem Nat.not_even_and_odd (n : ℕ) : ¬ (Even n ∧ Odd n) := by
  sorry

#check Nat.rec

/-- Утверждение 4.4.4 / Упражнение 4.4.3  -/
theorem Rat.not_exist_sqrt_two : ¬ ∃ x : ℚ, x^2 = 2 := by
  -- Это доказательство написано так,
  -- чтобы следовать структуре оригинального текста.
  by_contra h
  choose x hx using h
  have hnon : x ≠ 0 := by aesop
  wlog hpos : x > 0
  . apply this _ _ _ (show -x>0 by simp; order) <;> grind
  have hrep : ∃ p q : ℕ, p > 0 ∧ q > 0 ∧ p^2 = 2*q^2 := by
    use x.num.toNat, x.den
    observe hnum_pos : x.num > 0
    observe hden_pos : x.den > 0
    refine ⟨ by simp [hpos], hden_pos, ?_ ⟩
    rw [←num_div_den x] at hx
    field_simp at hx
    have hnum_cast : x.num = x.num.toNat := Int.eq_natCast_toNat.mpr (by positivity)
    rw [hnum_cast] at hx
    norm_cast at hx
    grind
  set P : ℕ → Prop := fun p ↦ p > 0 ∧ ∃ q > 0, p^2 = 2*q^2
  have hP : ∃ p, P p := by aesop
  have hiter (p : ℕ) (hPp : P p) : ∃ q, q < p ∧ P q := by
    obtain hp | hp := p.even_or_odd''
    . rw [even_iff_exists_two_mul] at hp
      obtain ⟨ k, rfl ⟩ := hp
      choose q hpos hq using hPp.2
      have : q^2 = 2 * k^2 := by linarith
      use q; constructor
      . sorry
      exact ⟨ hpos, k, by linarith [hPp.1], this ⟩
    have h1 : Odd (p^2) := by
      sorry
    have h2 : Even (p^2) := by
      choose q hpos hq using hPp.2
      rw [even_iff_exists_two_mul]
      use q^2
    observe : ¬(Even (p ^ 2) ∧ Odd (p ^ 2))
    tauto
  classical
  set f : ℕ → ℕ := fun p ↦ if hPp : P p then (hiter p hPp).choose else 0
  have hf (p : ℕ) (hPp : P p) : (f p < p) ∧ P (f p) := by
    simp [f, hPp]
    exact (hiter p hPp).choose_spec
  choose p hP using hP
  set a : ℕ → ℕ := Nat.rec p (fun n p ↦ f p)
  have ha (n : ℕ) : P (a n) := by
    induction n with
    | zero => exact hP
    | succ n ih => exact (hf _ ih).2
  have hlt (n : ℕ) : a (n+1) < a n := by
    have : a (n+1) = f (a n) := n.rec_add_one p (fun n p ↦ f p)
    grind
  exact Nat.no_infinite_descent ⟨ a, hlt ⟩


/-- Утверждение 4.4.5 -/
theorem Rat.exist_approx_sqrt_two {ε : ℚ} (hε : ε>0) : ∃ x ≥ (0 : ℚ), x^2 < 2 ∧ 2 < (x+ε)^2 := by
  -- Это доказательство написано так, чтобы следовать структуре оригинального текста.
  by_contra! h
  have (n : ℕ) : (n*ε)^2 < 2 := by
    induction' n with n hn
    simp
    simp [add_mul]
    apply lt_of_le_of_ne (h (n*ε) (by positivity) hn)
    have := not_exist_sqrt_two
    aesop
  choose n hn using Nat.exists_gt (2/ε)
  rw [gt_iff_lt, div_lt_iff₀', mul_comm, ←sq_lt_sq₀] at hn <;> try positivity
  grind

/-- Пример 4.4.6 -/
example :
  let ε : ℚ := 1/1000
  let x : ℚ := 1414/1000
  x^2 < 2 ∧ 2 < (x+ε)^2 := by norm_num
