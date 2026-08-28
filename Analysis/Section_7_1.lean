import Mathlib.Tactic

set_option doc.verso.suggestions false

/-!
# Analysis I, раздел 7.1: Конечные ряды

Я старался сделать перевод максимально точным перефразированием оригинального текста. Когда
приходилось выбирать между более идиоматичным Lean-решением и более точным переводом, я, как
правило, выбирал второе. В частности, местами Lean-код можно было бы "заголфить", сделав его более
элегантным и идиоматичным, но я сознательно этого избегал.

Техническое замечание: в Lean удобно расширять конечные последовательности (обычно нулями) до
функций, определённых на всём множестве целых чисел.

Основные конструкции и результаты этого раздела:
-/

-- Это открывает удобную нотацию `∑ n ∈ A, f n` для суммы `f n` по `n`,
-- пробегающему конечное множество `A`.
open BigOperators

/-!
- API для суммирования по конечным множествам (закодированным с помощью типа Mathlib {name}`Finset`)
  через метод {name}`Finset.sum` и нотацию `∑ n ∈ A, f n`.
- Теорема Фубини для конечных рядов

Мы не пытаемся здесь воспроизвести полное API для {name}`Finset.sum`, но в последующих разделах
будем активно этим API пользоваться.

-/

-- Это техническая уловка, чтобы обойти требование Mathlib о разрешимости равенства для
-- конечных множеств.
open Classical

namespace Finset

-- Мы используем `Finset.Icc` для описания конечных интервалов целых чисел. `Finset.mem_Icc` —
-- стандартный инструмент Mathlib для проверки принадлежности такому интервалу.
#check mem_Icc

/-- Definition 7.1.1 -/
theorem sum_of_empty {n m : ℤ} (h : n < m) (a : ℤ → ℝ) : ∑ i ∈ Icc m n, a i = 0 := by
  rw [sum_eq_zero]; intro _; rw [mem_Icc]; grind

/--
  Definition 7.1.1. Похоже на {name}`Finset.sum_Icc_succ_top` из Mathlib, за исключением того, что
  последняя суммирует по натуральным числам, а не по целым.
-/
theorem sum_of_nonempty {n m : ℤ} (h : n ≥ m-1) (a : ℤ → ℝ) : 
    ∑ i ∈ Icc m (n+1), a i = ∑ i ∈ Icc m n, a i + a (n+1) := by
  rw [add_comm _ (a (n+1))]
  convert sum_insert _
  . ext; simp; omega
  . infer_instance
  simp

example (a : ℤ → ℝ) (m : ℤ) : ∑ i ∈ Icc m (m-2), a i = 0 := by sorry

example (a : ℤ → ℝ) (m : ℤ) : ∑ i ∈ Icc m (m-1), a i = 0 := by sorry

example (a : ℤ → ℝ) (m : ℤ) : ∑ i ∈ Icc m m, a i = a m := by sorry

example (a : ℤ → ℝ) (m : ℤ) : ∑ i ∈ Icc m (m+1), a i = a m + a (m+1) := by sorry

example (a : ℤ → ℝ) (m : ℤ) : ∑ i ∈ Icc m (m+2), a i = a m + a (m+1) + a (m+2) := by sorry

/-- Remark 7.1.3 -/
example (a : ℤ → ℝ) (m n : ℤ) : ∑ i ∈ Icc m n, a i = ∑ j ∈ Icc m n, a j := rfl

/-- Lemma 7.1.4(a) / Exercise 7.1.1 -/
theorem concat_finite_series {m n p : ℤ} (hmn : m ≤ n+1) (hpn : n ≤ p) (a : ℤ → ℝ) : 
  ∑ i ∈ Icc m n, a i + ∑ i ∈ Icc (n+1) p, a i = ∑ i ∈ Icc m p, a i := by sorry

/-- Lemma 7.1.4(b) / Exercise 7.1.1 -/
theorem shift_finite_series {m n k : ℤ} (a : ℤ → ℝ) : 
  ∑ i ∈ Icc m n, a i = ∑ i ∈ Icc (m+k) (n+k), a (i-k) := by sorry

/-- Lemma 7.1.4(c) / Exercise 7.1.1 -/
theorem finite_series_add {m n : ℤ} (a b : ℤ → ℝ) : 
  ∑ i ∈ Icc m n, (a i + b i) = ∑ i ∈ Icc m n, a i + ∑ i ∈ Icc m n, b i := by sorry

/-- Lemma 7.1.4(d) / Exercise 7.1.1 -/
theorem finite_series_const_mul {m n : ℤ} (a : ℤ → ℝ) (c : ℝ) : 
  ∑ i ∈ Icc m n, c * a i = c * ∑ i ∈ Icc m n, a i := by sorry

/-- Lemma 7.1.4(e) / Exercise 7.1.1 -/
theorem abs_finite_series_le {m n : ℤ} (a : ℤ → ℝ) : 
  |∑ i ∈ Icc m n, a i| ≤ ∑ i ∈ Icc m n, |a i| := by sorry

/-- Lemma 7.1.4(f) / Exercise 7.1.1 -/
theorem finite_series_of_le {m n : ℤ}  {a b : ℤ → ℝ} (h : ∀ i, m ≤ i → i ≤ n → a i ≤ b i) : 
  ∑ i ∈ Icc m n, a i ≤ ∑ i ∈ Icc m n, b i := by sorry

#check sum_congr

set_option maxHeartbeats 210000 in
/--
  Proposition 7.1.8.
-/
theorem finite_series_of_rearrange {n : ℕ} {X' : Type*} (X : Finset X') (hcard : X.card = n)
  (f : X' → ℝ) (g h : Icc (1 : ℤ) n → X) (hg : Function.Bijective g) (hh : Function.Bijective h) : 
    ∑ i ∈ Icc (1 : ℤ) n, (if hi : i ∈ Icc (1 : ℤ) n then f (g ⟨ i, hi ⟩) else 0)
    = ∑ i ∈ Icc (1 : ℤ) n, (if hi : i ∈ Icc (1 : ℤ) n then f (h ⟨ i, hi ⟩) else 0) := by
  -- Это доказательство написано так, чтобы следовать структуре оригинального текста.
  revert X n; intro n
  induction' n with n hn
  . simp
  intro X hX g h hg hh
  -- Технический шаг: расширяем g, h на все целые числа с помощью немного искусственного отображения π
  set π : ℤ → Icc (1 : ℤ) (n+1) :=
    fun i ↦ if hi : i ∈ Icc (1 : ℤ) (n+1) then ⟨ i, hi ⟩ else ⟨ 1, by simp ⟩
  have hπ (g : Icc (1 : ℤ) (n+1) → X) : 
      ∑ i ∈ Icc (1 : ℤ) (n+1), (if hi : i ∈ Icc (1 : ℤ) (n+1) then f (g ⟨ i, hi ⟩) else 0)
      = ∑ i ∈ Icc (1 : ℤ) (n+1), f (g (π i)) := by
    apply sum_congr rfl _
    intro i hi; simp [hi, π, -mem_Icc]
  simp [-mem_Icc, hπ]
  rw [sum_of_nonempty (by linarith) _]
  set x := g (π (n+1))
  have ⟨⟨j, hj'⟩, hj⟩ := hh.surjective x
  simp at hj'; obtain ⟨ hj1, hj2 ⟩ := hj'
  set h' : ℤ → X := fun i ↦ if (i : ℤ) < j then h (π i) else h (π (i+1))
  have : ∑ i ∈ Icc (1 : ℤ) (n + 1), f (h (π i)) = ∑ i ∈ Icc (1 : ℤ) n, f (h' i) + f x := calc
    _ = ∑ i ∈ Icc (1 : ℤ) j, f (h (π i)) + ∑ i ∈ Icc (j+1 : ℤ) (n + 1), f (h (π i)) := by
      symm; apply concat_finite_series <;> linarith
    _ = ∑ i ∈ Icc (1 : ℤ) (j-1), f (h (π i)) + f ( h (π j) )
        + ∑ i ∈ Icc (j+1 : ℤ) (n + 1), f (h (π i)) := by
      congr; convert sum_of_nonempty _ _ <;> simp [hj1]
    _ = ∑ i ∈ Icc (1 : ℤ) (j-1), f (h (π i)) + f x + ∑ i ∈ Icc (j : ℤ) n, f (h (π (i+1))) := by
      congr 1
      . simp [←hj, π,hj1, hj2]
      symm; convert shift_finite_series _; simp
    _ = ∑ i ∈ Icc (1 : ℤ) (j-1), f (h (π i)) + ∑ i ∈ Icc (j : ℤ) n, f (h (π (i+1))) + f x := by abel
    _ = ∑ i ∈ Icc (1 : ℤ) (j-1), f (h' i) + ∑ i ∈ Icc (j : ℤ) n, f (h' i) + f x := by
      congr 2
      all_goals apply sum_congr rfl _; intro i hi; simp [h'] at *
      . simp [show i < j by linarith]
      simp [show ¬ i < j by linarith]
    _ = _ := by congr; convert concat_finite_series _ _ _ <;> linarith
  rw [this]
  congr 1
  have g_ne_x {i : ℤ} (hi : i ∈ Icc (1 : ℤ) n) : g (π i) ≠ x := by
    simp at hi
    simp [x, hg.injective.eq_iff, π, hi.1, show i ≤ n+1 by linarith]
    linarith
  have h'_ne_x {i : ℤ} (hi : i ∈ Icc (1 : ℤ) n) : h' i ≠ x := by
    simp at hi
    have hi' : 0 ≤ i := by linarith
    have hi'' : i ≤ n+1 := by linarith
    by_cases hlt : i < j <;> by_contra! heq
    all_goals simp [h', hlt, ←hj, hh.injective.eq_iff, ←Subtype.val_inj,
                    π, hi.1, hi.2, hi',hi''] at heq
    . linarith
    contrapose! hlt; linarith
  set gtil : Icc (1 : ℤ) n → X.erase x :=
    fun i ↦ ⟨ (g (π i)).val, by simp [mem_erase, g_ne_x] ⟩
  set htil : Icc (1 : ℤ) n → X.erase x :=
    fun i ↦ ⟨ (h' i).val, by simp [mem_erase, h'_ne_x] ⟩
  set ftil : X.erase x → ℝ := fun y ↦ f y.val
  have why : Function.Bijective gtil := by sorry
  have why2 : Function.Bijective htil := by sorry
  calc
    _ = ∑ i ∈ Icc (1 : ℤ) n, if hi : i ∈ Icc (1 : ℤ) n then ftil (gtil ⟨ i, hi ⟩ ) else 0 := by
      apply sum_congr rfl; grind
    _ = ∑ i ∈ Icc (1 : ℤ) n, if hi : i ∈ Icc (1 : ℤ) n then ftil (htil ⟨ i, hi ⟩ ) else 0 := by
      convert hn _ _ gtil htil why why2
      rw [Finset.card_erase_of_mem _, hX] <;> simp
    _ = _ := by apply sum_congr rfl; grind

/--
  Этот факт гарантирует, что Definition 7.1.6 было бы корректно определено, даже если бы мы не
  обращались к существующему методу {name}`Finset.sum`.
-/
theorem exist_bijection {n : ℕ} {Y : Type*} (X : Finset Y) (hcard : X.card = n) : 
    ∃ g : Icc (1 : ℤ) n → X, Function.Bijective g := by
  have := Finset.equivOfCardEq (show (Icc (1 : ℤ) n).card = X.card by simp [hcard])
  exact ⟨ this, this.bijective ⟩

/-- Definition 7.1.6 -/
theorem finite_series_eq {n : ℕ} {Y : Type*} (X : Finset Y) (f : Y → ℝ) (g : Icc (1 : ℤ) n → X)
  (hg : Function.Bijective g) : 
    ∑ i ∈ X, f i = ∑ i ∈ Icc (1 : ℤ) n, (if hi : i ∈ Icc (1 : ℤ) n then f (g ⟨ i, hi ⟩) else 0) := by
  symm
  convert sum_bij (t:=X) (fun i hi ↦ g ⟨ i, hi ⟩ ) _ _ _ _
  . aesop
  . intro _ _ _ _ h; simpa [Subtype.val_inj, hg.injective.eq_iff] using h
  . intro b hb; have := hg.surjective ⟨ b, hb ⟩; grind
  intros; simp_all

/-- Proposition 7.1.11(a) / Exercise 7.1.2 -/
theorem finite_series_of_empty {X' : Type*} (f : X' → ℝ) : ∑ i ∈ ∅, f i = 0 := by sorry

/-- Proposition 7.1.11(b) / Exercise 7.1.2 -/
theorem finite_series_of_singleton {X' : Type*} (f : X' → ℝ) (x₀ : X') : ∑ i ∈ {x₀}, f i = f x₀ := by
  sorry

/--
  Техническая лемма, связывающая сумму по finset с суммой по fintype. Хорошо сочетается с такими
  инструментами, как `map_finite_series` ниже.
-/
theorem finite_series_of_fintype {X' : Type*} (f : X' → ℝ) (X : Finset X') : 
    ∑ x ∈ X, f x = ∑ x : X, f x.val := (sum_coe_sort X f).symm

/-- Proposition 7.1.11(c) / Exercise 7.1.2 -/
theorem map_finite_series {X : Type*} [Fintype X] [Fintype Y] (f : X → ℝ) {g : Y → X}
  (hg : Function.Bijective g) : 
    ∑ x, f x = ∑ y, f (g y) := by sorry

-- Proposition 7.1.11(d) в нашей формализации — это `rfl`, поэтому она опущена.

/-- Proposition 7.1.11(e) / Exercise 7.1.2 -/
theorem finite_series_of_disjoint_union {Z : Type*} {X Y : Finset Z} (hdisj : Disjoint X Y) (f : Z → ℝ) : 
    ∑ z ∈ X ∪ Y, f z = ∑ z ∈ X, f z + ∑ z ∈ Y, f z := by sorry

/-- Proposition 7.1.11(f) / Exercise 7.1.2 -/
theorem finite_series_of_add {X' : Type*} (f g : X' → ℝ) (X : Finset X') : 
    ∑ x ∈ X, (f + g) x = ∑ x ∈ X, f x + ∑ x ∈ X, g x := by sorry

/-- Proposition 7.1.11(g) / Exercise 7.1.2 -/
theorem finite_series_of_const_mul {X' : Type*} (f : X' → ℝ) (X : Finset X') (c : ℝ) : 
    ∑ x ∈ X, c * f x = c * ∑ x ∈ X, f x := by sorry

/-- Proposition 7.1.11(h) / Exercise 7.1.2 -/
theorem finite_series_of_le' {X' : Type*} (f g : X' → ℝ) (X : Finset X') (h : ∀ x ∈ X, f x ≤ g x) : 
    ∑ x ∈ X, f x ≤ ∑ x ∈ X, g x := by sorry

/-- Proposition 7.1.11(i) / Exercise 7.1.2 -/
theorem abs_finite_series_le' {X' : Type*} (f : X' → ℝ) (X : Finset X') : 
    |∑ x ∈ X, f x| ≤ ∑ x ∈ X, |f x| := by sorry

/-- Lemma 7.1.13 -/
theorem finite_series_of_finite_series {XX YY : Type*} (X : Finset XX) (Y : Finset YY)
  (f : XX × YY → ℝ) : 
    ∑ x ∈ X, ∑ y ∈ Y, f (x, y) = ∑ z ∈ X.product Y, f z := by
  generalize h : X.card = n
  revert X; induction' n with n hn
  . sorry
  intro X hX
  have hnon : X.Nonempty := by grind [card_ne_zero]
  choose x₀ hx₀ using hnon.exists_mem
  set X' := X.erase x₀
  have hcard : X'.card = n := by simp [X', card_erase_of_mem hx₀, hX]
  have hunion : X = X' ∪ {x₀} := by ext x; by_cases x = x₀ <;> grind
  have hdisj : Disjoint X' {x₀} := by simp [X']
  calc
    _ = ∑ x ∈ X', ∑ y ∈ Y, f (x, y) + ∑ x ∈ {x₀}, ∑ y ∈ Y, f (x, y) := by
      convert finite_series_of_disjoint_union hdisj _
    _ = ∑ x ∈ X', ∑ y ∈ Y, f (x, y) + ∑ y ∈ Y, f (x₀, y) := by
      rw [finite_series_of_singleton]
    _ = ∑ z ∈ X'.product Y, f z + ∑ y ∈ Y, f (x₀, y) := by rw [hn X' hcard]
    _ = ∑ z ∈ X'.product Y, f z + ∑ z ∈ .product {x₀} Y, f z := by
      congr 1
      rw [finite_series_of_fintype, finite_series_of_fintype f]
      set π : Finset.product {x₀} Y → Y :=
        fun z ↦ ⟨ z.val.2, by obtain ⟨ z, hz ⟩ := z; simp at hz ⊢; grind ⟩
      have hπ : Function.Bijective π := by
        constructor
        . intro ⟨ ⟨ x, y ⟩, hz ⟩ ⟨ ⟨ x', y' ⟩, hz' ⟩ hzz'; simp [π] at hz hz' hzz' ⊢; grind
        intro ⟨ y, hy ⟩; use ⟨ (x₀, y), by simp [hy] ⟩
      convert map_finite_series _ hπ with z
      obtain ⟨⟨x, y⟩, hz ⟩ := z
      simp at hz ⊢; grind
    _ = _ := by
      symm; convert finite_series_of_disjoint_union _ _
      . sorry
      sorry

/-- Corollary 7.1.14 (Fubini's theorem for finite series). -/
theorem finite_series_refl {XX YY : Type*} (X : Finset XX) (Y : Finset YY) (f : XX × YY → ℝ) : 
    ∑ z ∈ X.product Y, f z = ∑ z ∈ Y.product X, f (z.2, z.1) := by
  set h : Y.product X → X.product Y :=
    fun z ↦ ⟨ (z.val.2, z.val.1), by obtain ⟨ z, hz ⟩ := z; simp at hz ⊢; tauto ⟩
  have hh : Function.Bijective h := by
    constructor
    . intro ⟨ ⟨ _, _ ⟩, _ ⟩ ⟨ ⟨ _, _ ⟩, _ ⟩ _
      simp_all [h]
    intro ⟨ z, hz ⟩; simp at hz
    use ⟨ (z.2, z.1), by simp [hz] ⟩
  rw [finite_series_of_fintype]
  nth_rewrite 2 [finite_series_of_fintype]
  convert map_finite_series _ hh with z

-- Теорема Фубини для конечных сумм: порядок суммирования по `X` и `Y` можно менять местами
theorem finite_series_comm {XX YY : Type*} (X : Finset XX) (Y : Finset YY) (f : XX × YY → ℝ) :
    ∑ x ∈ X, ∑ y ∈ Y, f (x, y) = ∑ y ∈ Y, ∑ x ∈ X, f (x, y) := by
  rw [finite_series_of_finite_series, finite_series_refl,
      finite_series_of_finite_series _ _ (fun z ↦ f (z.2, z.1))]


-- Exercise 7.1.3: разработайте как можно больше аналогов приведённой выше теории для конечных
-- произведений вместо конечных сумм.

#check Nat.factorial_zero
#check Nat.factorial_succ

/--
  Exercise 7.1.4. Замечание: при переходе туда-обратно между натуральными и целыми числами могут
  возникнуть технические трудности. Обратите внимание на тактики {tactic}`zify`, {tactic}`norm_cast`
  и {tactic}`omega`
-/
theorem binomial_theorem (x y : ℝ) (n : ℕ) : 
    (x + y)^n
    = ∑ j ∈ Icc (0 : ℤ) n,
    n.factorial / (j.toNat.factorial * (n-j).toNat.factorial) * x^j * y^(n - j) := by
  sorry

/-- Exercise 7.1.5 -/
theorem lim_of_finite_series {X : Type*} [Fintype X] (a : X → ℕ → ℝ) (L : X → ℝ)
  (h : ∀ x, Filter.atTop.Tendsto (a x) (nhds (L x))) : 
    Filter.atTop.Tendsto (fun n ↦ ∑ x, a x n) (nhds (∑ x, L x)) := by
  sorry

/-- Exercise 7.1.6 -/
theorem sum_union_disjoint {n : ℕ} {S : Type*} [Fintype S]
    (E : Fin n → Finset S)
    (disj : ∀ i j : Fin n, i ≠ j → Disjoint (E i) (E j))
    (cover : ∀ s : S, ∃ i, s ∈ E i)
    (f : S → ℝ) : 
    ∑ s, f s = ∑ i, ∑ s ∈ E i, f s := by
  sorry

/-- {given}`aᵢ` Exercise 7.1.7. Использует {lean}`Fin m` (то есть {lean}`aᵢ < m`) вместо {lean}`aᵢ ≤ m`
  из книги; граница здесь "зашита" в сам тип, а {kw (of := «term_<_»)}`<` заменяет
  {kw (of := «term_≤_»)}`≤`, чтобы соответствовать сдвигу на индексацию с нуля. -/
theorem sum_finite_col_row_counts {n m : ℕ} (a : Fin n → Fin m) : 
    ∑ i, (a i : ℕ) = ∑ j : Fin m, {i : Fin n | j < a i}.toFinset.card := by
  sorry

end Finset
