import Mathlib.Tactic
import Analysis.Section_5_1
import Analysis.Section_5_3
import Analysis.Section_5_epilogue

/-!
# Analysis I, раздел 6.1: Сходимость и законы предела

Я старался сделать перевод максимально точным перефразированием оригинального текста. Когда
приходилось выбирать между более идиоматичным Lean-решением и более точным переводом, я, как
правило, выбирал второе. В частности, местами Lean-код можно было бы "заголфить", сделав его более
элегантным и идиоматичным, но я сознательно этого избегал.

Основные конструкции и результаты этого раздела:

- Определение $`ε`-близости, $`ε`-устойчивости и их "в конце концов" эквивалентов.
- Понятия последовательности Коши, сходящейся последовательности и ограниченной последовательности
  вещественных чисел.

-/


/- Определение 6.1.1 (расстояние). Здесь мы используем расстояние из Mathlib. -/
#check Real.dist_eq

abbrev Real.Close (ε x y : ℝ) : Prop := dist x y ≤ ε

/--
  Определение 6.1.2 (ε-близость). Это похоже на предыдущее понятие ε-близости, но здесь все
  величины вещественные, а не рациональные.
-/
theorem Real.close_def (ε x y : ℝ) : ε.Close x y ↔ dist x y ≤ ε := by rfl

namespace Chapter6

/--
  Определение 6.1.3 (последовательность).
  Это похоже на последовательность из Главы 5, за исключением того,
  что теперь последовательность принимает вещественные значения.
  Как и в Главе 5, по умолчанию последовательности начинаются с 0.
-/
@[ext]
structure Sequence where
  m : ℤ
  seq : ℤ → ℝ
  vanish : ∀ n < m, seq n = 0

/-- Последовательности можно рассматривать как функции из {lean}`ℤ` в {lean}`ℝ`. -/
instance Sequence.instCoeFun : CoeFun Sequence (fun _ ↦ ℤ → ℝ) where
  coe a := a.seq

@[coe]
abbrev Sequence.ofNatFun (a : ℕ → ℝ) : Sequence :=
 {
    m := 0
    seq n := if n ≥ 0 then a n.toNat else 0
    vanish := by simp_all
 }

/-- Функции из {lean}`ℕ` в {lean}`ℝ` можно рассматривать как последовательности. -/
instance Sequence.instCoe : Coe (ℕ → ℝ) Sequence where
  coe := ofNatFun

abbrev Sequence.mk' (m : ℤ) (a : { n // n ≥ m } → ℝ) : Sequence where
  m := m
  seq n := if h : n ≥ m then a ⟨n, h⟩ else 0
  vanish := by simp_all

-- Значение последовательности, построенной через `mk'`, в точке `n ≥ m` совпадает со значением исходной функции `a` в этой точке.
lemma Sequence.eval_mk {n m : ℤ} (a : { n // n ≥ m } → ℝ) (h : n ≥ m) :
    (Sequence.mk' m a) n = a ⟨ n, h ⟩ := by simp [h]

-- Последовательность, полученная приведением функции `a : ℕ → ℝ`, в точке `n` принимает значение `a n`.
@[simp]
lemma Sequence.eval_coe (n : ℕ) (a : ℕ → ℝ) : (a : Sequence) n = a n := by simp

/--
  {given -show}`n₁, n₀`
  {lean}`a.from n₁` начинает {lean}`a : Sequence` с {name}`n₁`. Это предназначено для использования
  при {lean}`n₁ ≥ n₀`, а в противном случае возвращает "мусорное" значение исходной
  последовательности {name}`a`.
-/
abbrev Sequence.from (a : Sequence) (m₁ : ℤ) : Sequence := mk' (max a.m m₁) (a ↑·)

-- Сдвиг начала последовательности через `a.from m₁` не меняет значений `a` в точках `n ≥ m₁`.
lemma Sequence.from_eval (a : Sequence) {m₁ n : ℤ} (hn : n ≥ m₁) :
  (a.from m₁) n = a n := by
  simp [hn]; intros; symm; solve_by_elim [a.vanish]

end Chapter6

/-- Определение 6.1.3 (ε-устойчивость) -/
abbrev Real.Steady (ε : ℝ) (a : Chapter6.Sequence) : Prop :=
  ∀ n ≥ a.m, ∀ m ≥ a.m, ε.Close (a n) (a m)

/-- Определение 6.1.3 (ε-устойчивость, определение) -/
lemma Real.steady_def (ε : ℝ) (a : Chapter6.Sequence) :
  ε.Steady a ↔ ∀ n ≥ a.m, ∀ m ≥ a.m, ε.Close (a n) (a m) := by rfl

/-- Определение 6.1.3 (в конце концов ε-устойчивость) -/
abbrev Real.EventuallySteady (ε : ℝ) (a : Chapter6.Sequence) : Prop :=
  ∃ N ≥ a.m, ε.Steady (a.from N)

/-- Определение 6.1.3 (в конце концов ε-устойчивость, определение) -/
lemma Real.eventuallySteady_def (ε : ℝ) (a : Chapter6.Sequence) :
  ε.EventuallySteady a ↔ ∃ N, (N ≥ a.m) ∧ ε.Steady (a.from N) := by rfl

/-- При фиксированном {name}`a` функция `ε ↦ ε.Steady s` монотонна -/
theorem Real.Steady.mono {a : Chapter6.Sequence} {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) (hsteady : ε₁.Steady a) :
    ε₂.Steady a := by grind

/-- При фиксированном {name}`a` функция `ε ↦ ε.EventuallySteady s` монотонна -/
theorem Real.EventuallySteady.mono {a : Chapter6.Sequence} {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂)
  (hsteady : ε₁.EventuallySteady a) :
    ε₂.EventuallySteady a := by peel 2 hsteady; grind [Steady.mono]

namespace Chapter6

/-- Определение 6.1.3 (последовательность Коши) -/
abbrev Sequence.IsCauchy (a : Sequence) : Prop := ∀ ε > (0 : ℝ), ε.EventuallySteady a

/-- Определение 6.1.3 (последовательность Коши, определение) -/
lemma Sequence.isCauchy_def (a : Sequence) :
  a.IsCauchy ↔ ∀ ε > (0 : ℝ), ε.EventuallySteady a := by rfl

/-- Это почти то же самое, что {name}`Chapter5.Sequence.IsCauchy.coe` -/
lemma Sequence.IsCauchy.coe (a : ℕ → ℝ) :
    (a : Sequence).IsCauchy ↔ ∀ ε > 0, ∃ N, ∀ j ≥ N, ∀ k ≥ N, dist (a j) (a k) ≤ ε := by
  peel with ε hε
  constructor
  · rintro ⟨ N, hN, h' ⟩
    lift N to ℕ using hN; use N
    intro j hj k hk
    simp [Real.steady_def] at h'
    specialize h' j ?_ k ?_ <;> try omega
    simp_all
  rintro ⟨ N, h' ⟩; refine ⟨ max N 0, by simp, ?_ ⟩
  intro n hn m hm; simp at hn hm
  have npos : 0 ≤ n := by omega
  have mpos : 0 ≤ m := by omega
  simp [hn, hm, npos, mpos]
  lift n to ℕ using npos
  lift m to ℕ using mpos
  specialize h' n ?_ m ?_ <;> try grind

-- Последовательность `mk' n₀ a` является последовательностью Коши тогда и только тогда, когда для любого `ε > 0` найдётся `N`, начиная с которого любые два члена отстоят друг от друга не более чем на `ε`.
lemma Sequence.IsCauchy.mk {n₀ : ℤ} (a : {n // n ≥ n₀} → ℝ) :
    (mk' n₀ a).IsCauchy
    ↔ ∀ ε > 0, ∃ N ≥ n₀, ∀ j ≥ N, ∀ k ≥ N, dist (mk' n₀ a j) (mk' n₀ a k) ≤ ε := by
  peel with ε hε
  constructor
  · rintro ⟨ N, hN, h' ⟩; refine ⟨ N, hN, ?_ ⟩
    dsimp at hN
    intro j hj k hk
    simp only [Real.Steady, show max n₀ N = N by omega] at h'
    specialize h' j ?_ k ?_ <;> try omega
    simp_all [show n₀ ≤ j by omega, show n₀ ≤ k by omega]
  rintro ⟨ N, _, _ ⟩; use max n₀ N; grind

@[coe]
abbrev Sequence.ofChapter5Sequence (a : Chapter5.Sequence) : Sequence :=
{
  m := a.n₀
  seq n := a n
  vanish n hn := by simp [a.vanish n hn]
}

instance Chapter5.Sequence.inst_coe_sequence : Coe Chapter5.Sequence Sequence where
  coe := Sequence.ofChapter5Sequence

-- Приведение рациональной последовательности `a` из Главы 5 к вещественной сохраняет значения: `(a : Sequence) n = (a n : ℝ)`.
@[simp]
theorem Chapter5.coe_sequence_eval (a : Chapter5.Sequence) (n : ℤ) : (a : Sequence) n = (a n : ℝ) := rfl

-- Рациональная `ε`-устойчивость последовательности `a` эквивалентна вещественной `ε`-устойчивости её приведения к `Sequence`.
theorem Sequence.is_steady_of_rat (ε : ℚ) (a : Chapter5.Sequence) :
    ε.Steady a ↔ (ε : ℝ).Steady (a : Sequence) := by sorry

-- Аналогично для «в конце концов ε-устойчивости»: рациональная версия эквивалентна вещественной для приведённой последовательности.
theorem Sequence.is_eventuallySteady_of_rat (ε : ℚ) (a : Chapter5.Sequence) :
    ε.EventuallySteady a ↔ (ε : ℝ).EventuallySteady (a : Sequence) := by sorry

/-- Утверждение 6.1.4 -/
theorem Sequence.isCauchy_of_rat (a : Chapter5.Sequence) : a.IsCauchy ↔ (a : Sequence).IsCauchy := by
  -- Это доказательство написано так, чтобы следовать структуре оригинального текста.
  constructor
  swap
  . intro h; rw [isCauchy_def] at h
    rw [Chapter5.Sequence.isCauchy_def]
    intro ε hε
    specialize h ε (by positivity)
    rwa [is_eventuallySteady_of_rat]
  intro h
  rw [Chapter5.Sequence.isCauchy_def] at h
  rw [isCauchy_def]
  intro ε hε
  choose ε' hε' hlt using exists_pos_rat_lt hε
  specialize h ε' hε'
  rw [is_eventuallySteady_of_rat] at h
  exact h.mono (le_of_lt hlt)

end Chapter6

/-- Определение 6.1.5 (CloseSeq) -/
abbrev Real.CloseSeq (ε : ℝ) (a : Chapter6.Sequence) (L : ℝ) : Prop := ∀ n ≥ a.m, ε.Close (a n) L

/-- Определение 6.1.5 (CloseSeq, определение) -/
theorem Real.closeSeq_def (ε : ℝ) (a : Chapter6.Sequence) (L : ℝ) :
  ε.CloseSeq a L ↔ ∀ n ≥ a.m, dist (a n) L ≤ ε := by rfl

/-- Определение 6.1.5 (EventuallyClose) -/
abbrev Real.EventuallyClose (ε : ℝ) (a : Chapter6.Sequence) (L : ℝ) : Prop :=
  ∃ N ≥ a.m, ε.CloseSeq (a.from N) L

/-- Определение 6.1.5 (EventuallyClose, определение) -/
theorem Real.eventuallyClose_def (ε : ℝ) (a : Chapter6.Sequence) (L : ℝ) :
  ε.EventuallyClose a L ↔ ∃ N, (N ≥ a.m) ∧ ε.CloseSeq (a.from N) L := by rfl

-- Для последовательности, приведённой из функции `a : ℕ → ℝ`, `ε`-близость к `L` означает `dist (a n) L ≤ ε` для всех `n`.
theorem Real.CloseSeq.coe (ε : ℝ) (a : ℕ → ℝ) (L : ℝ) :
  (ε.CloseSeq a L) ↔ ∀ n, dist (a n) L ≤ ε := by
  constructor
  . intro h n; specialize h n; grind
  . intro h n hn; lift n to ℕ using (by omega); specialize h n; grind

-- Если `a` является `ε₁`-близкой к `L` и `ε₁ ≤ ε₂`, то она и `ε₂`-близка к `L`.
theorem Real.CloseSeq.mono {a : Chapter6.Sequence} {ε₁ ε₂ L : ℝ} (hε : ε₁ ≤ ε₂)
  (hclose : ε₁.CloseSeq a L) :
    ε₂.CloseSeq a L := by peel 2 hclose; rw [Real.Close, Real.dist_eq] at *; linarith

-- Аналогичная монотонность по `ε` для «в конце концов `ε`-близка».
theorem Real.EventuallyClose.mono {a : Chapter6.Sequence} {ε₁ ε₂ L : ℝ} (hε : ε₁ ≤ ε₂)
  (hclose : ε₁.EventuallyClose a L) :
    ε₂.EventuallyClose a L := by peel 2 hclose; grind [CloseSeq.mono]
namespace Chapter6

abbrev Sequence.TendsTo (a : Sequence) (L : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ε.EventuallyClose a L

-- `a.TendsTo L` означает, что для любого `ε > 0` последовательность `a` в конце концов `ε`-близка к `L`.
theorem Sequence.tendsTo_def (a : Sequence) (L : ℝ) :
  a.TendsTo L ↔ ∀ ε > (0 : ℝ), ε.EventuallyClose a L := by rfl

/-- Упражнение 6.1.2 -/
theorem Sequence.tendsTo_iff (a : Sequence) (L : ℝ) :
  a.TendsTo L ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| ≤ ε := by sorry

noncomputable def seq_6_1_6 : Sequence := (fun (n : ℕ) ↦ 1-(10 : ℝ)^(-(n : ℤ)-1) : Sequence)

/-- Примеры 6.1.6 (0.1-близость) -/
example : (0.1 : ℝ).CloseSeq seq_6_1_6 1 := by
  rw [seq_6_1_6, Real.CloseSeq.coe]
  intro n
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by
    rw [sub_nonneg]
    rw (occs := .pos [2]) [show (1 : ℝ) = 1 - 0 by norm_num]
    gcongr
    positivity
  ), sub_sub_cancel, show (0.1 : ℝ) = (10 : ℝ)^(-1 : ℤ) by norm_num]
  gcongr <;> grind


/-- Примеры 6.1.6 (0.01-неблизость) -/
example : ¬ (0.01 : ℝ).CloseSeq seq_6_1_6 1 := by
  intro h; specialize h 0 (by positivity); simp [seq_6_1_6] at h; norm_num at h

/-- Примеры 6.1.6 (0.01-близость в конце концов) -/
example : (0.01 : ℝ).EventuallyClose seq_6_1_6 1 := by sorry

/-- Примеры 6.1.6 (стремится к 1) -/
example : seq_6_1_6.TendsTo 1 := by sorry

/-- Утверждение 6.1.7 (единственность пределов) -/
theorem Sequence.tendsTo_unique (a : Sequence) {L L' : ℝ} (h : L ≠ L') :
    ¬ (a.TendsTo L ∧ a.TendsTo L') := by
  -- Это доказательство написано так, чтобы следовать структуре оригинального текста.
  by_contra this
  choose hL hL' using this
  replace h : L - L' ≠ 0 := by grind
  replace h : |L-L'| > 0 := by positivity
  set ε := |L-L'| / 3
  have hε : ε > 0 := by positivity
  rw [tendsTo_iff] at hL hL'
  specialize hL ε hε; choose N hN using hL
  specialize hL' ε hε; choose M hM using hL'
  set n := max N M
  specialize hN n (by omega)
  specialize hM n (by omega)
  have : |L-L'| ≤ 2 * |L-L'|/3 := calc
    _ = dist L L' := by rw [Real.dist_eq]
    _ ≤ dist L (a.seq n) + dist (a.seq n) L' := dist_triangle _ _ _
    _ ≤ ε + ε := by rw [←Real.dist_eq] at hN hM; rw [dist_comm] at hN; gcongr
    _ = 2 * |L-L'|/3 := by grind
  linarith

/-- Определение 6.1.8 (Convergent) -/
abbrev Sequence.Convergent (a : Sequence) : Prop := ∃ L, a.TendsTo L

/-- Определение 6.1.8 (Convergent, определение) -/
theorem Sequence.convergent_def (a : Sequence) : a.Convergent ↔ ∃ L, a.TendsTo L := by rfl

/-- Определение 6.1.8 (Divergent) -/
abbrev Sequence.Divergent (a : Sequence) : Prop := ¬ a.Convergent

/-- Определение 6.1.8 (Divergent, определение) -/
theorem Sequence.divergent_def (a : Sequence) : a.Divergent ↔ ¬ a.Convergent := by rfl

open Classical in
/--
  Определение 6.1.8. Мы придаём пределу последовательности мусорное значение {lean}`0`, если она
  не сходится.
-/
noncomputable abbrev lim (a : Sequence) : ℝ := if h : a.Convergent then h.choose else 0

/-- Определение 6.1.8 (lim, определение) -/
theorem Sequence.lim_def {a : Sequence} (h : a.Convergent) : a.TendsTo (lim a) := by
  simp [lim, h]; exact h.choose_spec

/-- Определение 6.1.8 (lim, характеризация) -/
theorem Sequence.lim_eq {a : Sequence} {L : ℝ} :
a.TendsTo L ↔ a.Convergent ∧ lim a = L := by
  constructor
  . intro h; by_contra! eq
    have : a.Convergent := by rw [convergent_def]; use L
    replace eq := a.tendsTo_unique (eq this)
    apply lim_def at this; tauto
  intro ⟨ h, rfl ⟩; convert lim_def h


/-- Утверждение 6.1.11 -/
theorem Sequence.lim_harmonic :
    ((fun (n : ℕ) ↦ (n+1 : ℝ)⁻¹) : Sequence).Convergent ∧ lim ((fun (n : ℕ) ↦ (n+1 : ℝ)⁻¹) : Sequence) = 0 := by
  -- Это доказательство написано так, чтобы следовать структуре оригинального текста.
  rw [←lim_eq, tendsTo_iff]
  intro ε hε
  choose N hN using exists_int_gt (1 / ε); use N; intro n hn
  have hNpos : (N : ℝ) > 0 := by apply LT.lt.trans _ hN; positivity
  simp at hNpos
  have hnpos : n ≥ 0 := by linarith
  simp [hnpos, abs_inv]
  calc
    _ ≤ (N : ℝ)⁻¹ := by
      rw [inv_le_inv₀] <;> try positivity
      calc
        _ ≤ (n : ℝ) := by simp [hn]
        _ = (n.toNat : ℤ) := by simp [hnpos]
        _ = n.toNat := rfl
        _ ≤ (n.toNat : ℝ) + 1 := by linarith
        _ ≤ _ := le_abs_self _
    _ ≤ ε := by
      rw [inv_le_comm₀] <;> try positivity
      rw [←inv_eq_one_div _] at hN; order

/-- Утверждение 6.1.12 / Упражнение 6.1.5 -/
theorem Sequence.IsCauchy.convergent {a : Sequence} (h : a.Convergent) : a.IsCauchy := by
  sorry

/-- Пример 6.1.13 (не устойчива в конце концов) -/
example : ¬ (0.1 : ℝ).EventuallySteady ((fun n ↦ (-1 : ℝ)^n) : Sequence) := by sorry

/-- Пример 6.1.13 (не Коши) -/
example : ¬ ((fun n ↦ (-1 : ℝ)^n) : Sequence).IsCauchy := by sorry

/-- Пример 6.1.13 (не сходится) -/
example : ¬ ((fun n ↦ (-1 : ℝ)^n) : Sequence).Convergent := by sorry

/-- Утверждение 6.1.15 / Упражнение 6.1.6 (формальные пределы являются настоящими пределами) -/
theorem Sequence.lim_eq_LIM {a : ℕ → ℚ} (h : (a : Chapter5.Sequence).IsCauchy) :
    ((a : Chapter5.Sequence) : Sequence).TendsTo (Chapter5.Real.equivR (Chapter5.LIM a)) := by sorry

/-- Определение 6.1.16 (BoundedBy) -/
abbrev Sequence.BoundedBy (a : Sequence) (M : ℝ) : Prop :=
  ∀ n, |a n| ≤ M

/-- Определение 6.1.16 (BoundedBy, определение) -/
lemma Sequence.boundedBy_def (a : Sequence) (M : ℝ) :
  a.BoundedBy M ↔ ∀ n, |a n| ≤ M := by rfl

/-- Определение 6.1.16 (IsBounded) -/
abbrev Sequence.IsBounded (a : Sequence) : Prop := ∃ M ≥ 0, a.BoundedBy M

/-- Определение 6.1.16 (IsBounded, определение) -/
lemma Sequence.isBounded_def (a : Sequence) :
  a.IsBounded ↔ ∃ M ≥ 0, a.BoundedBy M := by rfl

-- Всякая последовательность Коши ограничена.
theorem Sequence.bounded_of_cauchy {a : Sequence} (h : a.IsCauchy) : a.IsBounded := by
  sorry

/-- Следствие 6.1.17 -/
theorem Sequence.bounded_of_convergent {a : Sequence} (h : a.Convergent) : a.IsBounded := by
  sorry

/-- Пример 6.1.18 (не ограничена) -/
example : ¬ ((fun (n : ℕ) ↦ (n+1 : ℝ)) : Sequence).IsBounded := by sorry

/-- Пример 6.1.18 (не сходится) -/
example : ¬ ((fun (n : ℕ) ↦ (n+1 : ℝ)) : Sequence).Convergent := by sorry

instance Sequence.inst_add : Add Sequence where
  add a b := {
    m := min a.m b.m
    seq n := a n + b n
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

-- Сумма последовательностей `a + b` в точке `n` равна сумме их значений `a n + b n`.
@[simp]
theorem Sequence.add_eval {a b : Sequence} (n : ℤ) : (a + b) n = a n + b n := rfl

-- Сложение последовательностей, приведённых из функций `ℕ → ℝ`, совпадает с приведением их поточечной суммы.
theorem Sequence.add_coe (a b : ℕ → ℝ) : (a : Sequence) + (b : Sequence) = (fun n ↦ a n + b n) := by
  ext n; rfl
  by_cases h : n ≥ 0 <;> simp [h]

/-- Теорема 6.1.19(a) (законы предела). Версия {name}`Sequence.TendsTo` удобнее в использовании, чем версия
    через {name}`lim`, в приложениях. -/
theorem Sequence.tendsTo_add {a b : Sequence} {L M : ℝ} (ha : a.TendsTo L) (hb : b.TendsTo M) :
  (a+b).TendsTo (L+M) := by
  sorry

-- Сумма сходящихся последовательностей сходится, и её предел равен сумме пределов.
theorem Sequence.lim_add {a b : Sequence} (ha : a.Convergent) (hb : b.Convergent) :
  (a + b).Convergent ∧ lim (a + b) = lim a + lim b := by
  sorry

instance Sequence.inst_mul : Mul Sequence where
  mul a b := {
    m := min a.m b.m
    seq n := a n * b n
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

-- Произведение последовательностей `a * b` в точке `n` равно произведению их значений `a n * b n`.
@[simp]
theorem Sequence.mul_eval {a b : Sequence} (n : ℤ) : (a * b) n = a n * b n := rfl

-- Умножение приведённых последовательностей совпадает с приведением их поточечного произведения.
theorem Sequence.mul_coe (a b : ℕ → ℝ) : (a : Sequence) * (b : Sequence) = (fun n ↦ a n * b n) := by
  ext n; rfl
  by_cases h : n ≥ 0 <;> simp [h]

/-- Теорема 6.1.19(b) (законы предела). Версия {name}`Sequence.TendsTo` удобнее в использовании, чем версия
    через {name}`lim`, в приложениях. -/
theorem Sequence.tendsTo_mul {a b : Sequence} {L M : ℝ} (ha : a.TendsTo L) (hb : b.TendsTo M) :
    (a * b).TendsTo (L * M) := by
  sorry

-- Произведение сходящихся последовательностей сходится, и его предел равен произведению пределов.
theorem Sequence.lim_mul {a b : Sequence} (ha : a.Convergent) (hb : b.Convergent) :
    (a * b).Convergent ∧ lim (a * b) = lim a * lim b := by
  sorry


instance Sequence.inst_smul : SMul ℝ Sequence where
  smul c a := {
    m := a.m
    seq n := c * a n
    vanish n hn := by simp [a.vanish n hn]
  }

-- Скалярное умножение `c • a` в точке `n` равно `c * a n`.
@[simp]
theorem Sequence.smul_eval {a : Sequence} (c : ℝ) (n : ℤ) : (c • a) n = c * a n := rfl

-- Скалярное умножение приведённой последовательности совпадает с приведением поточечного умножения на `c`.
theorem Sequence.smul_coe (c : ℝ) (a : ℕ → ℝ) : (c • (a : Sequence)) = (fun n ↦ c * a n) := by
  ext n; rfl
  by_cases h : n ≥ 0 <;> simp [h, HSMul.hSMul, SMul.smul]

/-- Теорема 6.1.19(c) (законы предела). Версия {name}`Sequence.TendsTo` удобнее в использовании, чем версия
    через {name}`lim`, в приложениях. -/
theorem Sequence.tendsTo_smul (c : ℝ) {a : Sequence} {L : ℝ} (ha : a.TendsTo L) :
    (c • a).TendsTo (c * L) := by
  sorry

-- Скалярное умножение сходящейся последовательности на `c` сохраняет сходимость, а предел умножается на `c`.
theorem Sequence.lim_smul (c : ℝ) {a : Sequence} (ha : a.Convergent) :
    (c • a).Convergent ∧ lim (c • a) = c * lim a := by
  sorry

instance Sequence.inst_sub : Sub Sequence where
  sub a b := {
    m := min a.m b.m
    seq n := a n - b n
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

-- Разность последовательностей `a - b` в точке `n` равна `a n - b n`.
@[simp]
theorem Sequence.sub_eval {a b : Sequence} (n : ℤ) : (a - b) n = a n - b n := rfl

-- Вычитание приведённых последовательностей совпадает с приведением их поточечной разности.
theorem Sequence.sub_coe (a b : ℕ → ℝ) : (a : Sequence) - (b : Sequence) = (fun n ↦ a n - b n) := by
  ext n; rfl
  by_cases h : n ≥ 0 <;> simp [h]

/-- Теорема 6.1.19(d) (законы предела). Версия {name}`Sequence.TendsTo` удобнее в использовании, чем версия
    через {name}`lim`, в приложениях. -/
theorem Sequence.tendsTo_sub {a b : Sequence} {L M : ℝ} (ha : a.TendsTo L) (hb : b.TendsTo M) :
    (a - b).TendsTo (L - M) := by
  sorry

-- Разность сходящихся последовательностей сходится, и её предел равен разности пределов.
theorem Sequence.LIM_sub {a b : Sequence} (ha : a.Convergent) (hb : b.Convergent) :
    (a - b).Convergent ∧ lim (a - b) = lim a - lim b := by
  sorry

noncomputable instance Sequence.inst_inv : Inv Sequence where
  inv a := {
    m := a.m
    seq n := (a n)⁻¹
    vanish n hn := by simp [a.vanish n hn]
  }

-- Обратная последовательность `a⁻¹` в точке `n` равна `(a n)⁻¹`.
@[simp]
theorem Sequence.inv_eval {a : Sequence} (n : ℤ) : (a⁻¹) n = (a n)⁻¹ := rfl

-- Обращение приведённой последовательности совпадает с приведением поточечного обращения.
theorem Sequence.inv_coe (a : ℕ → ℝ) : (a : Sequence)⁻¹ = (fun n ↦ (a n)⁻¹) := by
  ext n; rfl
  by_cases h : n ≥ 0 <;> simp [h]

/-- Теорема 6.1.19(e) (законы предела). Версия {name}`Sequence.TendsTo` удобнее в использовании, чем версия
    через {name}`lim`, в приложениях. -/
theorem Sequence.tendsTo_inv {a : Sequence} {L : ℝ} (ha : a.TendsTo L) (hnon : L ≠ 0) :
    (a⁻¹).TendsTo (L⁻¹) := by
  sorry

-- Если предел `a` не равен нулю, то `a⁻¹` сходится, и её предел равен обратному к пределу `a`.
theorem Sequence.lim_inv {a : Sequence} (ha : a.Convergent) (hnon : lim a ≠ 0) :
  (a⁻¹).Convergent ∧ lim (a⁻¹) = (lim a)⁻¹ := by
  sorry

noncomputable instance Sequence.inst_div : Div Sequence where
  div a b := {
    m := min a.m b.m
    seq n := a n / b n
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

-- Частное последовательностей `a / b` в точке `n` равно `a n / b n`.
@[simp]
theorem Sequence.div_eval {a b : Sequence} (n : ℤ) : (a / b) n = a n / b n := rfl

-- Деление приведённых последовательностей совпадает с приведением их поточечного деления.
theorem Sequence.div_coe (a b : ℕ → ℝ) : (a : Sequence) / (b : Sequence) = (fun n ↦ a n / b n) := by
  ext n; rfl
  by_cases h : n ≥ 0 <;> simp [h]

/-- Теорема 6.1.19(f) (законы предела). Версия {name}`Sequence.TendsTo` удобнее в использовании, чем версия
    через {name}`lim`, в приложениях. -/
theorem Sequence.tendsTo_div {a b : Sequence} {L M : ℝ} (ha : a.TendsTo L) (hb : b.TendsTo M) (hnon : M ≠ 0) :
    (a / b).TendsTo (L / M) := by
  sorry

-- Если `b` сходится к ненулевому пределу, то `a / b` сходится, и её предел равен частному пределов.
theorem Sequence.lim_div {a b : Sequence} (ha : a.Convergent) (hb : b.Convergent) (hnon : lim b ≠ 0) :
  (a / b).Convergent ∧ lim (a / b) = lim a / lim b := by
  sorry

instance Sequence.inst_max : Max Sequence where
  max a b := {
    m := min a.m b.m
    seq n := max (a n) (b n)
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

-- Последовательность `a ⊔ b` в точке `n` равна `max (a n) (b n)`.
@[simp]
theorem Sequence.max_eval {a b : Sequence} (n : ℤ) : (a ⊔ b) n = (a n) ⊔ (b n) := rfl

-- Максимум приведённых последовательностей совпадает с приведением поточечного максимума.
theorem Sequence.max_coe (a b : ℕ → ℝ) : (a : Sequence) ⊔ (b : Sequence) = (fun n ↦ max (a n) (b n)) := by
  ext n; rfl
  by_cases h : n ≥ 0 <;> simp [h]

/-- Теорема 6.1.19(g) (законы предела). Версия {name}`Sequence.TendsTo` удобнее в использовании, чем версия
    через {name}`lim`, в приложениях. -/
theorem Sequence.tendsTo_max {a b : Sequence} {L M : ℝ} (ha : a.TendsTo L) (hb : b.TendsTo M) :
    (max a b).TendsTo (max L M) := by
  sorry

-- Максимум сходящихся последовательностей сходится, и его предел равен максимуму пределов.
theorem Sequence.lim_max {a b : Sequence} (ha : a.Convergent) (hb : b.Convergent) :
    (max a b).Convergent ∧ lim (max a b) = max (lim a) (lim b) := by
  sorry

instance Sequence.inst_min : Min Sequence where
  min a b := {
    m := min a.m b.m
    seq n := min (a n) (b n)
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

-- Последовательность `a ⊓ b` в точке `n` равна `min (a n) (b n)`.
@[simp]
theorem Sequence.min_eval {a b : Sequence} (n : ℤ) : (a ⊓ b) n = (a n) ⊓ (b n) := rfl

-- Минимум приведённых последовательностей совпадает с приведением поточечного минимума.
theorem Sequence.min_coe (a b : ℕ → ℝ) : (a : Sequence) ⊓ (b : Sequence) = (fun n ↦ min (a n) (b n)) := by
  ext n; rfl
  by_cases h : n ≥ 0 <;> simp [h]

/-- Теорема 6.1.19(h) (законы предела) -/
theorem Sequence.tendsTo_min {a b : Sequence} {L M : ℝ} (ha : a.TendsTo L) (hb : b.TendsTo M) :
    (min a b).TendsTo (min L M) := by
  sorry

-- Минимум сходящихся последовательностей сходится, и его предел равен минимуму пределов.
theorem Sequence.lim_min {a b : Sequence} (ha : a.Convergent) (hb : b.Convergent) :
    (min a b).Convergent ∧ lim (min a b) = min (lim a) (lim b) := by
  sorry

/-- Упражнение 6.1.1 -/
theorem Sequence.mono_if {a : ℕ → ℝ} (ha : ∀ n, a (n+1) > a n) {n m : ℕ} (hnm : m > n) : a m > a n := by
  sorry

/-- Упражнение 6.1.3 -/
theorem Sequence.tendsTo_of_from {a : Sequence} {c : ℝ} (m : ℤ) :
    a.TendsTo c ↔ (a.from m).TendsTo c := by
  sorry

/-- Упражнение 6.1.4 -/
theorem Sequence.tendsTo_of_shift {a : Sequence} {c : ℝ} (k : ℕ) :
    a.TendsTo c ↔ (Sequence.mk' a.m (fun n : {n // n ≥ a.m} ↦ a (n+k))).TendsTo c := by
  sorry

/-- Упражнение 6.1.7 -/
theorem Sequence.isBounded_of_rat (a : Chapter5.Sequence) :
    a.IsBounded ↔ (a : Sequence).IsBounded := by
  sorry

/-- Упражнение 6.1.9 -/
theorem Sequence.lim_div_fail :
    ∃ a b, a.Convergent
    ∧ b.Convergent
    ∧ lim b = 0
    ∧ ¬ ((a / b).Convergent ∧ lim (a / b) = lim a / lim b) := by
  sorry

-- Последовательность Коши из Главы 5 эквивалентна вещественной формулировке: для любого `ε > 0` найдётся `N`, начиная с которого любые два члена отстоят друг от друга не более чем на `ε`.
theorem Chapter5.Sequence.IsCauchy_iff (a : Chapter5.Sequence) :
    a.IsCauchy ↔ ∀ ε > (0 : ℝ), ∃ N ≥ a.n₀, ∀ n ≥ N, ∀ m ≥ N, |a n - a m| ≤ ε := by
  sorry
end Chapter6

-- дополнительные определения для exercise 6.1.10
abbrev Real.SeqCloseSeq (ε : ℝ) (a b : Chapter5.Sequence) : Prop :=
  ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.Close (a n) (b n)

abbrev Real.SeqEventuallyClose (ε : ℝ) (a b : Chapter5.Sequence) : Prop :=
  ∃ N, ε.SeqCloseSeq (a.from N) (b.from N)

-- расширенное определение эквивалентности рациональных последовательностей, но с положительным вещественным ε
abbrev Chapter5.Sequence.RatEquiv (a b : ℕ → ℚ) : Prop :=
  ∀ (ε : ℝ), ε > 0 → ε.SeqEventuallyClose (a : Chapter5.Sequence) (b : Chapter5.Sequence)

namespace Chapter6
/-- Упражнение 6.1.10 -/
theorem Chapter5.Sequence.equiv_rat (a b : ℕ → ℚ) :
  Chapter5.Sequence.Equiv a b ↔ Chapter5.Sequence.RatEquiv a b := by sorry

end Chapter6
