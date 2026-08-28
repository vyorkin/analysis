import Mathlib.Tactic
import Analysis.Section_6_4

/-!
# Analysis I, раздел 6.5: Некоторые стандартные пределы

Я старался сделать перевод максимально точным перефразированием оригинального текста. Когда
приходилось выбирать между более идиоматичным Lean-решением и более точным переводом, я, как
правило, выбирал второе. В частности, местами Lean-код можно было бы "заголфить", сделав его более
элегантным и идиоматичным, но я сознательно этого избегал.

Основные конструкции и результаты этого раздела:

- Некоторые стандартные пределы, включая пределы последовательностей вида 1/n^α, x^n и x^(1/n).

-/

namespace Chapter6

-- Постоянная последовательность `c` сходится к `c`.
theorem Sequence.lim_of_const (c : ℝ) :  ((fun (_ : ℕ) ↦ c) : Sequence).TendsTo c := by sorry

instance Sequence.inst_pow : Pow Sequence ℕ where
  pow a k := {
    m := a.m
    seq n := if n ≥ a.m then a n ^ k else 0
    vanish := by grind
  }

-- Возведение последовательности в степень `k` вычисляется поточечно: `(a^k) n = (a n)^k` для `n ≥ a.m`.
@[simp]
lemma Sequence.pow_eval {a : Sequence} {k : ℕ} {n : ℤ} (hn : n ≥ a.m) : (a ^ k) n = a n ^ k := by
  rw [HPow.hPow, instHPow, Pow.pow, inst_pow]
  grind

-- Возведение последовательности в первую степень не меняет её: `a^1 = a`.
@[simp]
lemma Sequence.pow_one (a : Sequence) : a^1 = a := by
  ext n; rfl; simp only [HPow.hPow, Pow.pow]; split_ifs with h; simp; simp [a.vanish n (by grind)]

-- Рекуррентное соотношение для степеней последовательности: `a^(k+1) = a^k * a`.
lemma Sequence.pow_succ (a : Sequence) (k : ℕ) : a^(k+1) = a^k * a := by
  ext x
  . symm; exact Int.min_self a.m
  . simp only [mul_eval]
    by_cases h : x ≥ a.m
    · simp [pow_eval h]
      rfl
    · rw [a.vanish x (by grind), mul_zero]
      exact vanish _ _ (by simp at h; exact h)

/-- Corollary 6.5.1 -/
theorem Sequence.lim_of_power_decay {k : ℕ} : 
    ((fun (n : ℕ) ↦ 1/((n : ℝ)+1)^(1/(k+1 : ℝ))) : Sequence).TendsTo 0 := by
  -- Это доказательство написано так, чтобы следовать структуре оригинального текста.
  set a := ((fun (n : ℕ) ↦ 1/((n : ℝ)+1)^(1/(k+1 : ℝ))) : Sequence)
  have ha : a.BddBelow := by use 0; intro n _; simp [a]; positivity
  have ha' : a.IsAntitone := by
    intro n hn; observe hn' : 0 ≤ n+1; simp [a,hn,hn']
    rw [inv_le_inv₀, Real.rpow_le_rpow_iff] <;> try positivity
    simp
  apply convergent_of_antitone ha at ha'
  have hpow (n : ℕ) : (a^(n+1)).Convergent ∧ lim (a^(n+1)) = (lim a)^(n+1) := by
    induction' n with n ih
    . simp [ha', -dite_pow]
    rw [pow_succ]; convert lim_mul ih.1 ha' using 1; rw [ih.2]; grind
  have hlim : (lim a)^(k+1) = 0 := by
    rw [←(hpow k).2]; convert lim_harmonic.2; ext; rfl
    simp only [HPow.hPow, Pow.pow, a]; split_ifs with h
    · simp
      rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity)]
      convert Real.rpow_one _; field_simp; push_cast; ring
    · simp
  simp [lim_eq, ha', eq_zero_of_pow_eq_zero hlim]

/-- Lemma 6.5.2 (модуль отношения меньше единицы) / Exercise 6.5.2 -/
theorem Sequence.lim_of_geometric {x : ℝ} (hx : |x| < 1) : ((fun (n : ℕ) ↦ x^n) : Sequence).TendsTo 0 := by
  sorry

/-- Lemma 6.5.2 (отношение равно единице) / Exercise 6.5.2 -/
theorem Sequence.lim_of_geometric' {x : ℝ} (hx : x = 1) : ((fun (n : ℕ) ↦ x^n) : Sequence).TendsTo 1 := by
  sorry

/-- Lemma 6.5.2 (отношение минус единица или модуль больше единицы) / Exercise 6.5.2 -/
theorem Sequence.lim_of_geometric'' {x : ℝ} (hx : x = -1 ∨ |x| > 1) :
    ((fun (n : ℕ) ↦ x^n) : Sequence).Divergent := by
  sorry

/-- Lemma 6.5.3 / Exercise 6.5.3 -/
theorem Sequence.lim_of_roots {x : ℝ} (hx : x > 0) : 
    ((fun (n : ℕ) ↦ x^(1/(n+1 : ℝ))) : Sequence).TendsTo 1 := by
  sorry

/-- Exercise 6.5.1 (i) -/
theorem Sequence.lim_of_rat_power_decay {q : ℚ} (hq : q > 0) : 
    (fun (n : ℕ) ↦ 1/((n+1 : ℝ)^(q : ℝ)) : Sequence).TendsTo 0 := by
  sorry

/-- Exercise 6.5.1 (ii) -/
theorem Sequence.lim_of_rat_power_growth {q : ℚ} (hq : q > 0) : 
    (fun (n : ℕ) ↦ ((n+1 : ℝ)^(q : ℝ)) : Sequence).Divergent := by
  sorry

end Chapter6
