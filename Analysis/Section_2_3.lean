import Mathlib.Tactic
import Analysis.Section_2_2

/-!
# Analysis I, Section 2.3: Multiplication

This file is a translation of Section 2.3 of Analysis I to Lean 4. All numbering refers to the
original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of multiplication and exponentiation for the "Chapter 2" natural numbers,
  {name}`Chapter2.Nat`.

Note: at the end of this chapter, the {name}`Chapter2.Nat` class will be deprecated in favor of the
standard Mathlib class {name}`_root_.Nat`, or {lean}`ℕ`.  However, we will develop the properties of
{name}`Chapter2.Nat` "by hand" for pedagogical purposes.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter2

/-- Definition 2.3.1 (Multiplication of natural numbers) -/
abbrev Nat.mul (n m : Nat) : Nat :=
  Nat.recurse (fun _ prod ↦ prod + m) 0 n

-- 0:
-- Nat.recurse f 0 0 = 0 -- стартовое значение
--
-- 1:
-- Nat.recurse f 0 1 = f 0 (Nat.recurse f 0 0)
--                   = f 0 0
--                   = 0 + 4 = 4
-- 2:
-- Nat.recurse f 0 2 = f 1 (Nat.recurse f 0 1)
--                   = f 1 4
--                   = 4 + 4 = 8
-- 3:
-- Nat.recurse f 0 3 = f 2 (Nat.recurse f 0 2)
--                   = f 2 8
--                   = 8 + 4 = 12

/-- This instance allows for the {kw (of := «term_*_»)}`*` notation to be used for natural number multiplication. -/
instance Nat.instMul : Mul Nat where
  mul := mul

/-- Definition 2.3.1 (Multiplication of natural numbers)
Compare with Mathlib's {name}`Nat.zero_mul` -/
theorem Nat.zero_mul (m : Nat) : 0 * m = 0 :=
  recurse_zero (fun _ prod ↦ prod + m) _

/-- Definition 2.3.1 (Multiplication of natural numbers)
Compare with Mathlib's {name}`Nat.succ_mul` -/
theorem Nat.succ_mul (n m : Nat) : (n++) * m = n * m + m :=
  recurse_succ (fun _ prod ↦ prod + m) _ _

theorem Nat.one_mul' (m : Nat) : 1 * m = 0 + m := by
  rw [←zero_succ, succ_mul, zero_mul]

/-- Compare with Mathlib's {name}`Nat.one_mul` -/
theorem Nat.one_mul (m : Nat) : 1 * m = m := by
  rw [one_mul', zero_add]

theorem Nat.two_mul (m : Nat) : 2 * m = 0 + m + m := by
  rw [←one_succ, succ_mul, one_mul']

/-- This lemma will be useful to prove Lemma 2.3.2.
Compare with Mathlib's {name}`Nat.mul_zero` -/
lemma Nat.mul_zero (n : Nat) : n * 0 = 0 := by
  induction n with
  | zero =>
    change 0 * 0 = 0
    exact Nat.zero_mul 0
  | succ n' ih =>
    rw [Nat.succ_mul]
    rw [Nat.add_zero]
    exact ih

/-- This lemma will be useful to prove Lemma 2.3.2.
Compare with Mathlib's {name}`Nat.mul_succ` -/
lemma Nat.mul_succ (n m : Nat) : n * m++ = n * m + n := by
  induction n with
  | zero =>
    change 0 * m++ = 0 * m + 0
    trivial
  | succ n' ih =>
    repeat rw [Nat.succ_mul]
    repeat rw [Nat.add_succ]
    rw [ih]
    repeat rw [Nat.add_assoc]
    rw [Nat.add_comm m n']

lemma Nat.mul_succ' (n m : Nat) : n * m++ = n * m + n := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    calc n'++ * m++
        = n' * m++ + m++    := Nat.succ_mul n' (m++)
      _ = n' * m + n' + m++ := by rw [ih]
      _ = n' * m + m + n'++ := by
            rw [Nat.add_succ, Nat.add_succ, Nat.add_assoc, Nat.add_comm n' m, ← Nat.add_assoc]
      _ = n'++ * m + n'++   := by rw [← Nat.succ_mul]

/-- Lemma 2.3.2 (Multiplication is commutative) / Exercise 2.3.1
Compare with Mathlib's {name}`Nat.mul_comm` -/
lemma Nat.mul_comm (n m : Nat) : n * m = m * n := by
  induction n with
  | zero =>
    change 0 * m = m * 0
    rw [Nat.zero_mul, Nat.mul_zero]
  | succ n' ih =>
    rw [Nat.mul_succ, Nat.succ_mul]
    rw [ih]

/-- Compare with Mathlib's {name}`Nat.mul_one` -/
theorem Nat.mul_one (m : Nat) : m * 1 = m := by
  rw [mul_comm, one_mul]

/-- This lemma will be useful to prove Lemma 2.3.3.
Compare with Mathlib's {name}`Nat.mul_pos` -/
lemma Nat.pos_mul_pos {n m : Nat} (h₁ : n.IsPos) (h₂ : m.IsPos) : (n * m).IsPos := by
  unfold IsPos at *
  intro h
  apply h₂
  induction n with
  | zero =>
    contradiction
  | succ n' ih =>
    apply ih
    · intro hne
      rw [hne, Nat.succ_mul, Nat.zero_mul, Nat.zero_add] at h
      contradiction
    · rw [Nat.succ_mul] at h
      obtain ⟨hnm, hm⟩ := Nat.add_eq_zero (n' * m) m h
      exact hnm

/-- Lemma 2.3.3 (Positive natural numbers have no zero divisors) / Exercise 2.3.2.
    Compare with Mathlib's {name}`Nat.mul_eq_zero`.  -/
lemma Nat.mul_eq_zero (n m : Nat) : n * m = 0 ↔ n = 0 ∨ m = 0 := by
  constructor
  · intro h
    by_contra hc
    rw [or_iff_not_and_not, not_not] at hc
    obtain ⟨h₀, h₁⟩ := hc
    exact Nat.pos_mul_pos h₀ h₁ h
  · intro h
    rcases h with hn | hm
    · rw [hn]
      exact Nat.zero_mul n
    · rw [hm]
      exact Nat.mul_zero n

/-- Proposition 2.3.4 (Distributive law)
Compare with Mathlib's {name}`Nat.mul_add` -/
theorem Nat.mul_add (a b c : Nat) : a * (b + c) = a * b + a * c := by
  -- Зафиксируем a и b и используем индукцию по c.
  revert c; apply induction
  . -- Докажем базовый случай c = 0, т.е :
    show a * (b + 0) = a * b + a * 0
    rw [add_zero]
    -- Левая часть равнa a*b
    show a * b = a * b + a * 0
    rw [mul_zero]
    -- В то время как правая часть равнa a*b + 0 = a*b
    show a * b = a * b + 0
    rw [add_zero]
    -- Так что базовый случай разобран.
  · intro c ih
    -- Теперь предположим индуктивно, что:
    guard_hyp ih : a * (b + c) = a * b + a * c
    -- И докажем, что
    show a * (b + c++) = a * b + a * c++
    rw [add_succ, mul_succ]
    -- Левая часть равна: a * (b + c) + a
    rw [mul_succ, ←add_assoc]
    -- В то время как правая равнa: a * b + a * c + a =
    -- = a * (b + c) + a по индуктивному предположению.
    rw [←ih]
    -- Конец индукции.

/-- Proposition 2.3.4 (Distributive law)
Compare with Mathlib's {name}`Nat.add_mul`  -/
theorem Nat.add_mul (a b c : Nat) : (a + b) * c = a * c + b * c := by
  rw [Nat.mul_comm, Nat.mul_add]
  rw [Nat.mul_comm c a, Nat.mul_comm c b]
  -- simp only [mul_comm, mul_add]

/-- Proposition 2.3.5 (Multiplication is associative) / Exercise 2.3.3
Compare with Mathlib's {name}`Nat.mul_assoc` -/
theorem Nat.mul_assoc (a b c : Nat) : (a * b) * c = a * (b * c) := by
  -- Зафиксируем c и b и используем индукцию по a.
  revert a; apply induction
  · -- repeat rw [Nat.zero_mul]
    rw [Nat.zero_mul]
    rw [Nat.zero_mul]
    rw [Nat.zero_mul]
  · intro a ih
    guard_hyp ih : (a * b) * c = a * (b * c)
    rw [Nat.succ_mul, Nat.succ_mul]
    rw [Nat.add_mul]
    rw [ih]

/-- (Not from textbook)  {name}`Nat` is a commutative semiring.
    This allows tactics such as {tactic}`ring` to apply to the Chapter 2 natural numbers. -/
instance Nat.instCommSemiring : CommSemiring Nat where
  left_distrib := mul_add
  right_distrib := add_mul
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm

/-- This illustration of the {tactic}`ring` tactic is not from the
    textbook. -/
example (a b c d : ℕ) : (a + b) * 1 * (c + d) = d * b + a * c + c * b + a * d + 0 := by ring

/-- Proposition 2.3.6 (Multiplication preserves order)
Compare with Mathlib's {name}`Nat.mul_lt_mul_of_pos_right` -/
-- Умножение сокращает порядок.
theorem Nat.mul_lt_mul_of_pos_right {a b c : Nat} (h : a < b) (hc : c.IsPos) : a * c < b * c := by
  -- This proof is written to follow the structure of the original text.
  -- Поскольку a < b, мы имеем b = a + d для некоторого положительного d
  rw [lt_iff_add_pos] at h
  obtain ⟨d, hdpos, hd⟩ := h
  -- Мы можем умножить обе стороны равенства hd на c
  replace hd := congr($hd * c)
  rw [add_mul] at hd
  -- Применяя распределительный закон, имеем:
  guard_hyp hd : b * c = a * c + d * c
  -- Поскольку d ≠ 0 (положительно) и c ≠ 0 (положительно),
  -- то и d * c ≠ 0 (положительно)
  have hdcpos : (d * c).IsPos := pos_mul_pos hdpos hc
  -- А поскольку мы ранее доказали, что a < b ↔ ∃ d > 0, b = a + d,
  rw [lt_iff_add_pos]
  -- То a * c < b * c.
  use d * c

/-- Proposition 2.3.6 (Multiplication preserves order) -/
theorem Nat.mul_gt_mul_of_pos_right {a b c : Nat} (h : a > b) (hc : c.IsPos) : a * c > b * c :=
  mul_lt_mul_of_pos_right h hc

/-- Proposition 2.3.6 (Multiplication preserves order)
Compare with Mathlib's {name}`Nat.mul_lt_mul_of_pos_left` -/
theorem Nat.mul_lt_mul_of_pos_left {a b c : Nat} (h : a < b) (hc : c.IsPos) : c * a < c * b := by
  simp [mul_comm]
  exact mul_lt_mul_of_pos_right h hc

/-- Proposition 2.3.6 (Multiplication preserves order) -/
theorem Nat.mul_gt_mul_of_pos_left {a b c : Nat} (h : a > b) (hc : c.IsPos) :
    c * a > c * b := mul_lt_mul_of_pos_left h hc

/-- Corollary 2.3.7 (Cancellation law)
Compare with Mathlib's {name}`Nat.mul_right_cancel` -/
lemma Nat.mul_cancel_right {a b c : Nat} (h : a * c = b * c) (hc : c.IsPos) : a = b := by
  -- This proof is written to follow the structure of the original text.
  obtain hlt | heq /- rfl -/ | hgt := trichotomous a b
  . replace hlt := mul_lt_mul_of_pos_right hlt hc
    apply ne_of_lt at hlt
    contradiction
  . rw [heq] -- rfl
  · replace hgt := mul_gt_mul_of_pos_right hgt hc
    apply ne_of_gt at hgt
    contradiction

/-- (Not from textbook) {name}`Nat` is an ordered semiring.
This allows tactics such as {tactic}`gcongr` to apply to the Chapter 2 natural numbers. -/
instance Nat.isOrderedRing : IsOrderedRing Nat where
  zero_le_one : (0 : Nat) ≤ 1 := Nat.zero_le 1
  mul_le_mul_of_nonneg_left :
    ∀ ⦃a : Nat⦄, 0 ≤ a → ∀ ⦃b c : Nat⦄, b ≤ c → a * b ≤ a * c := by
    intro a ha b c hbc
    rw [Nat.le_iff] at hbc
    obtain ⟨d, hd⟩ := hbc
    rw [hd]
    rw [Nat.mul_add]
    rw [Nat.le_iff]
    use a * d
  mul_le_mul_of_nonneg_right :
    ∀ ⦃c : Nat⦄, 0 ≤ c → ∀ ⦃a b : Nat⦄, a ≤ b → a * c ≤ b * c := by
    intro c hc a b hab
    rw [Nat.le_iff] at hab
    obtain ⟨d, hd⟩ := hab
    rw [hd, Nat.add_mul, Nat.le_iff]
    use d * c

/-- This illustration of the {tactic}`gcongr` tactic is not from the
    textbook. -/
example (a b c d : Nat) (hab : a ≤ b) : c * a * d ≤ c * b * d := by
  -- Тактика gcongr тут использует обобщенные леммы монотонности из IsOrderedRing:
  -- mul_le_mul_of_nonneg_left и mul_le_mul_of_nonneg_right
  gcongr
  . exact d.zero_le
  · exact c.zero_le

-- Альтернативное доказательство без gcongr:
example (a b c d : Nat) (hab : a ≤ b) : c * a * d ≤ c * b * d := by
  have h : c * a ≤ c * b := mul_le_mul_of_nonneg_left hab c.zero_le
  exact mul_le_mul_of_nonneg_right h d.zero_le

-- Второе альтернативное доказательство без have:
example (a b c d : Nat) (hab : a ≤ b) : c * a * d ≤ c * b * d := by
  apply mul_le_mul_of_nonneg_right
  apply mul_le_mul_of_nonneg_left hab c.zero_le
  exact d.zero_le

/-- Proposition 2.3.9 (Euclid's division lemma) / Exercise 2.3.5
Compare with Mathlib's {name}`Nat.mod_eq_iff` -/
-- Зафиксируйте q и индуктивно рассмотрите n.
theorem Nat.exists_div_mod (n : Nat) {q : Nat} (hq : q.IsPos) :
    ∃ m r : Nat, 0 ≤ r ∧ r < q ∧ n = m * q + r := by
  revert n; apply induction
  · use 0, 0
    show 0 ≤ 0 ∧ 0 < q ∧ 0 = 0 * q + 0
    and_intros
    · rw [Nat.le_iff]
      use 0
      rw [Nat.add_zero]
    · rw [Nat.le_iff]
      use q
      rw [Nat.zero_add]
    · exact hq.symm
    · rw [Nat.zero_mul]
      rw [Nat.zero_add]
  · intro n hn
    obtain ⟨m, r, h₀, h₁, h₂⟩ := hn
    rw [h₂]; show ∃ x y, 0 ≤ y ∧ y < q ∧ (m * q + r)++ = x * q + y
    rw [← Nat.add_succ]
    -- Кандидат на остаток — r++. Но он может не влезть в [0, q), поэтому смотрим, где r++ стоит относительно q.
    rcases trichotomous (r++) q with h | h | h
    · -- r++ < q : свидетели m и r++
      use m, (r++)
      exact ⟨Nat.zero_le (r++), h, rfl⟩
    · -- r++ = q : свидетели m++ и 0; нужен "перенос" (r++ достиг q)
      use (m++), 0
      refine ⟨Nat.zero_le 0, ?_, ?_⟩
      · -- 0 < q
        exact ⟨zero_le q, hq.symm⟩
      · -- m * q + r++ = m++ * q + 0
        rw [h]
        rw [add_zero]
        rw [← succ_mul]
    · -- r++ > q : невозможно, т.к. r < q влечёт r++ ≤ q
      exfalso
      have hrs : r++ ≤ q := (lt_iff_succ_le r q).mp h₁
      exact not_lt_self (lt_of_le_of_lt hrs h)

theorem Nat.exists_div_mod' (n : Nat) {q : Nat} (hq : q.IsPos) :
    ∃ m r : Nat, 0 ≤ r ∧ r < q ∧ n = m * q + r := by
  have h0q : 0 < q := by
    rw [lt_iff_add_pos]
    use q, hq
    rw [Nat.zero_add]
  revert n; apply induction
  · use 0, 0
    and_intros
    · exact Nat.zero_le 0 --  0 ≤ a
    · exact Nat.zero_le q
    · exact Ne.symm hq
    · rfl
  · intro n hn
    obtain ⟨m, r, _, h₁, h₂⟩ := hn
    rw [h₂, ← Nat.add_succ]
    -- Кандидат на остаток — r++.
    -- Но он может не влезть в [0, q).
    -- Поэтому смотрим, где r++ стоит относительно q.
    rcases trichotomous (r++) q with hlt | heq | hgt
    · -- r++ < q : свидетели m и r++
      use m, (r++)
      exact ⟨Nat.zero_le _, hlt, rfl⟩
    · -- r++ = q : свидетели m++ и 0, с переносом
      use (m++), 0
      and_intros
      · exact Nat.zero_le 0
      · exact Nat.zero_le q
      · exact hq.symm
      · rw [heq, Nat.add_zero, ← Nat.succ_mul]
    · -- r++ > q : невозможно, т.к. r < q влечёт r++ ≤ q
      exfalso
      apply not_lt_self (a := q)
      apply lt_of_lt_of_le hgt
      apply (lt_iff_succ_le r q).mp
      exact h₁

/-- Definition 2.3.11 (Exponentiation for natural numbers) -/
abbrev Nat.pow (m n : Nat) : Nat :=
  Nat.recurse (fun _ prod ↦ prod * m) 1 n

instance Nat.instPow : HomogeneousPow Nat where
  pow := Nat.pow

/-- Definition 2.3.11 (Exponentiation for natural numbers)
Compare with Mathlib's {name}`Nat.pow_zero` -/
@[simp]
theorem Nat.pow_zero (m : Nat) : m ^ (0 : Nat) = 1 :=
  recurse_zero (fun _ prod ↦ prod * m) _

/-- Definition 2.3.11 (Exponentiation for natural numbers) -/
@[simp]
theorem Nat.zero_pow_zero : (0 : Nat) ^ 0 = 1 :=
  recurse_zero (fun _ prod ↦ prod * 0) _

/-- Definition 2.3.11 (Exponentiation for natural numbers)
Compare with Mathlib's {name}`Nat.pow_succ` -/
theorem Nat.pow_succ (m n : Nat) : (m : Nat) ^ n++ = m ^ n * m :=
  recurse_succ (fun _ prod ↦ prod * m) _ _

/-- Compare with Mathlib's {name}`Nat.pow_one` -/
@[simp]
theorem Nat.pow_one (m : Nat) : m ^ (1 : Nat) = m := by
  rw [←zero_succ, pow_succ]; simp

/-- Exercise 2.3.4 -/
theorem Nat.sq_add_eq (a b : Nat) :
  (a + b) ^ (2 : Nat) = a ^ (2 : Nat) + 2 * a * b + b ^ (2 : Nat) := by
    have h2 : (2 : Nat) = 1++ := rfl
    rw [h2]
    repeat rw [pow_succ, pow_one]
    rw [succ_mul, one_mul]
    rw [add_mul, add_mul]
    rw [mul_add, mul_add]
    rw [mul_comm b a]
    rw [← add_assoc (a * a + a * b) (a * b) (b * b)]
    rw [add_assoc (a * a) (a * b) (a * b)]

end Chapter2
