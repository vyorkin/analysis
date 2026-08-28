import Mathlib.Tactic
import Mathlib.Algebra.Field.Power

/-!
# Analysis I, раздел 7.2: Бесконечные ряды

Я старался сделать перевод максимально точным перефразированием оригинального текста. Когда
приходилось выбирать между более идиоматичным Lean-решением и более точным переводом, я, как
правило, выбирал второе. В частности, местами Lean-код можно было бы "заголфить", сделав его более
элегантным и идиоматичным, но я сознательно этого избегал.

Основные конструкции и результаты этого раздела:

- Формальные ряды и их пределы.
- Абсолютная сходимость; базовые законы рядов.

-/

namespace Chapter7

open BigOperators

/--
  Definition 7.2.1 (формальный бесконечный ряд). Похоже на последовательность из Главы 6, но
  обращаются с ним иначе. Как и в Главе 5, по умолчанию ряды будут начинаться с 0.
-/
@[ext]
structure Series where
  m : ℤ
  seq : ℤ → ℝ
  vanish : ∀ n < m, seq n = 0

/-- Функции из ℕ в ℝ можно рассматривать как ряды. -/
instance Series.instCoe : Coe (ℕ → ℝ) Series where
  coe := fun a ↦ {
    m := 0
    seq n := if n ≥ 0 then a n.toNat else 0
    vanish := by grind
  }

-- Вложение `ℕ → ℝ` в `Series` сохраняет значения на натуральных индексах
@[simp]
theorem Series.eval_coe (a : ℕ → ℝ) (n : ℕ) : (a : Series).seq n = a n := by simp

abbrev Series.mk' {m : ℤ} (a : { n // n ≥ m } → ℝ) : Series where
  m := m
  seq n := if h : n ≥ m then a ⟨n, h⟩ else 0
  vanish := by grind

-- Ряд, построенный через `mk'`, на индексах `n ≥ m` совпадает с исходной функцией `a`
theorem Series.eval_mk' {m : ℤ} (a : { n // n ≥ m } → ℝ) {n : ℤ} (h : n ≥ m) :
    (Series.mk' a).seq n = a ⟨ n, h ⟩ := by simp [h]

/-- Definition 7.2.2 (сходимость ряда) -/
noncomputable abbrev Series.partial (s : Series) (N : ℤ) : ℝ := ∑ n ∈ Finset.Icc s.m N, s.seq n

-- Частичная сумма ряда при увеличении верхней границы на 1 растёт на очередной член: `s.partial (N+1) = s.partial N + s.seq (N+1)`
theorem Series.partial_succ (s : Series) {N : ℤ} (h : N ≥ s.m-1) : s.partial (N+1) = s.partial N + s.seq (N+1) := by
  unfold Series.partial
  rw [add_comm (s.partial N) _]
  convert Finset.sum_insert (show N+1 ∉ Finset.Icc s.m N by simp)
  symm; apply Finset.insert_Icc_right_eq_Icc_add_one; linarith

-- Частичная сумма ряда до индекса, меньшего `s.m`, равна нулю
theorem Series.partial_of_lt {s : Series} {N : ℤ} (h : N < s.m) : s.partial N = 0 := by
  unfold Series.partial
  rw [Finset.sum_eq_zero]
  intro n hn; simp at hn; grind

abbrev Series.convergesTo (s : Series) (L : ℝ) : Prop := Filter.atTop.Tendsto (s.partial) (nhds L)

abbrev Series.converges (s : Series) : Prop := ∃ L, s.convergesTo L

abbrev Series.diverges (s : Series) : Prop := ¬s.converges

open Classical in
noncomputable abbrev Series.sum (s : Series) : ℝ := if h : s.converges then h.choose else 0

-- Если частичные суммы ряда сходятся к конкретному `L`, то ряд сходится
theorem Series.converges_of_convergesTo {s : Series} {L : ℝ} (h : s.convergesTo L) :
    s.converges := by use L

/-- Remark 7.2.3 -/
theorem Series.sum_of_converges {s : Series} {L : ℝ} (h : s.convergesTo L) : s.sum = L := by
  simp [sum, converges_of_convergesTo h]
  exact tendsto_nhds_unique ((converges_of_convergesTo h).choose_spec) h

-- Предел ряда единственен: если ряд сходится и к `L`, и к `L'`, то `L = L'`
theorem Series.convergesTo_uniq {s : Series} {L L' : ℝ} (h : s.convergesTo L) (h' : s.convergesTo L') :
    L = L' := tendsto_nhds_unique h h'

-- Если ряд сходится, то он сходится именно к `s.sum`
theorem Series.convergesTo_sum {s : Series} (h : s.converges) : s.convergesTo s.sum := by
  simp [sum, h]; exact h.choose_spec

/-- Example 7.2.4 -/
noncomputable abbrev Series.example_7_2_4 := mk' (m := 1) (fun n ↦ (2 : ℝ)^(-n : ℤ))

-- Пример 7.2.4: частичная сумма ряда `∑ 2⁻ⁿ` равна `1 - 2⁻ᴺ`
theorem Series.example_7_2_4a {N : ℤ} (hN : N ≥ 1) : example_7_2_4.partial N = 1 - (2 : ℝ)^(-N) := by
  sorry

-- Пример 7.2.4: ряд `∑ 2⁻ⁿ` сходится к `1`
theorem Series.example_7_2_4b : example_7_2_4.convergesTo 1 := by sorry

-- Пример 7.2.4: сумма ряда `∑ 2⁻ⁿ` равна `1`
theorem Series.example_7_2_4c : example_7_2_4.sum = 1 := by sorry

noncomputable abbrev Series.example_7_2_4' := mk' (m := 1) (fun n ↦ (2 : ℝ)^(n : ℤ))

-- Частичная сумма ряда `∑ 2ⁿ` равна `2^(N+1) - 2`
theorem Series.example_7_2_4'a {N : ℤ} (hN : N ≥ 1) : example_7_2_4'.partial N = (2 : ℝ)^(N+1) - 2 := by
  sorry

-- Ряд `∑ 2ⁿ` расходится
theorem Series.example_7_2_4'b : example_7_2_4'.diverges := by sorry

/-- Proposition 7.2.5 / Exercise 7.2.2 -/
theorem Series.converges_iff_tail_decay (s : Series) : 
    s.converges ↔ ∀ ε > 0, ∃ N ≥ s.m, ∀ p ≥ N, ∀ q ≥ N, |∑ n ∈ Finset.Icc p q, s.seq n| ≤ ε := by
  sorry

/-- Corollary 7.2.6 (признак стремления к нулю) / Exercise 7.2.3 -/
theorem Series.decay_of_converges {s : Series} (h : s.converges) : 
    Filter.atTop.Tendsto s.seq (nhds 0) := by
  sorry

-- Если члены ряда не стремятся к нулю, ряд расходится (следствие признака стремления к нулю)
theorem Series.diverges_of_nodecay {s : Series} (h : ¬ Filter.atTop.Tendsto s.seq (nhds 0)) :
    s.diverges := by
  sorry

/-- Example 7.2.7 -/
theorem Series.example_7_2_7 : ((fun _ : ℕ ↦ (1 : ℝ)) : Series).diverges := by
  apply diverges_of_nodecay
  sorry

-- Ряд `∑ (-1)ⁿ` расходится, так как его члены не стремятся к нулю
theorem Series.example_7_2_7' : ((fun n : ℕ ↦ (-1 : ℝ)^n) : Series).diverges := by
  apply diverges_of_nodecay
  sorry

/-- Definition 7.2.8 (абсолютная сходимость) -/
abbrev Series.abs (s : Series) : Series := mk' (m:=s.m) (fun n ↦ |s.seq n|)

abbrev Series.absConverges (s : Series) : Prop := s.abs.converges

abbrev Series.condConverges (s : Series) : Prop := s.converges ∧ ¬ s.absConverges

/-- Proposition 7.2.9 (признак абсолютной сходимости) / Exercise 7.2.4 -/
theorem Series.converges_of_absConverges {s : Series} (h : s.absConverges) : s.converges := by
  sorry

-- Для абсолютно сходящегося ряда модуль суммы не превосходит суммы модулей членов
theorem Series.abs_le {s : Series} (h : s.absConverges) : |s.sum| ≤ s.abs.sum := by
  sorry

/-- Proposition 7.2.12 (признак Лейбница для знакочередующихся рядов) -/
theorem Series.converges_of_alternating {m : ℤ} {a : { n // n ≥ m} → ℝ} (ha : ∀ n, a n ≥ 0)
  (ha' : Antitone a) :
    ((mk' (fun n ↦ (-1)^(n : ℤ) * a n)).converges ↔ Filter.atTop.Tendsto a (nhds 0)) := by
  -- Это доказательство написано так, чтобы следовать структуре оригинального текста.
  constructor
  . intro h; apply decay_of_converges at h
    rw [tendsto_iff_dist_tendsto_zero] at h ⊢
    rw [←Filter.tendsto_comp_val_Ici_atTop (a := m)] at h
    refine h.congr (fun n => ?_)
    simp [n.property]
  intro h
  unfold converges convergesTo
  set b := mk' fun n ↦ (-1) ^ (n : ℤ) * a n
  set S := b.partial
  have claim0 {N : ℤ} (hN : N ≥ m) : S (N+1) = S N + (-1)^(N+1) * a ⟨ N+1, by grind ⟩ := by
    convert b.partial_succ ?_; simp [b, show N+1 ≥ m by grind]; linarith
  have claim1 {N : ℤ} (hN : N ≥ m) : S (N+2) = S N + (-1)^(N+1) * (a ⟨ N+1, by grind ⟩ - a ⟨ N+2, by grind ⟩) := calc
      S (N+2) = S N + (-1)^(N+1) * a ⟨ N+1, by grind ⟩ + (-1)^(N+2) * a ⟨ N+2, by grind ⟩ := by
        simp_rw [←claim0 hN, show N+2=N+1+1 by abel]; apply claim0; linarith
      _ = S N + (-1)^(N+1) * a ⟨ N+1, by grind ⟩ + (-1) * (-1)^(N+1) * a ⟨ N+2, by grind ⟩ := by
        congr; rw [←zpow_one_add₀] <;> grind
      _ = _ := by ring
  have claim2 {N : ℤ} (hN : N ≥ m) (h' : Odd N) : S (N+2) ≥ S N := by
    simp [claim1 hN, h'.add_one.neg_one_zpow]; apply ha'; simp
  have claim3 {N : ℤ} (hN : N ≥ m) (h' : Even N) : S (N+2) ≤ S N := by
    simp [claim1 hN, h'.add_one.neg_one_zpow]; apply ha'; simp
  have why1 {N : ℤ} (hN : N ≥ m) (h' : Even N) (k : ℕ) : S (N+2*k) ≤ S N := by sorry
  have why2 {N : ℤ} (hN : N ≥ m) (h' : Even N) (k : ℕ) : S (N+2*k+1) ≥ S N - a ⟨ N+1, by grind ⟩ := by sorry
  have why3 {N : ℤ} (hN : N ≥ m) (h' : Even N) (k : ℕ) : S (N+2*k+1) ≤ S (N+2*k) := by sorry
  have claim4 {N : ℤ} (hN : N ≥ m) (h' : Even N) (k : ℕ) : S N -
 a ⟨ N+1, by grind ⟩ ≤ S (N + 2*k + 1) ∧ S (N + 2*k + 1) ≤ S (N + 2*k) ∧ S (N + 2*k) ≤ S N := ⟨ ge_iff_le.mp (why2 hN h' k), why3 hN h' k, why1 hN h' k ⟩
  have why4 {N n : ℤ} (hN : N ≥ m) (h' : Even N) (hn : n ≥ N) : S N - a ⟨ N+1, by grind ⟩ ≤ S n ∧ S n ≤ S N := by
    sorry
  have why5 {ε : ℝ} (hε : ε > 0) : ∃ N, ∀ n ≥ N, ∀ m ≥ N, |S n - S m| ≤ ε := by sorry
  have : CauchySeq S := by
    rw [Metric.cauchySeq_iff']
    intro ε hε; choose N hN using why5 (half_pos hε); use N
    intro n hn; rw [Real.dist_eq]; linarith [hN n hn N (by simp)]
  exact cauchySeq_tendsto_of_complete this

/-- Example 7.2.13 -/
noncomputable abbrev Series.example_7_2_13 : Series := (mk' (m:=1) (fun n ↦ (-1 : ℝ)^(n : ℤ) / (n : ℤ)))

-- Пример 7.2.13: знакочередующийся ряд `∑ (-1)ⁿ/n` сходится
theorem Series.example_7_2_13a : example_7_2_13.converges := by
  sorry

-- Пример 7.2.13: ряд `∑ (-1)ⁿ/n` не сходится абсолютно
theorem Series.example_7_2_13b : ¬ example_7_2_13.absConverges := by
  sorry

-- Пример 7.2.13: ряд `∑ (-1)ⁿ/n` сходится условно
theorem Series.example_7_2_13c :  example_7_2_13.condConverges := by
  sorry

instance Series.inst_add : Add Series where
  add a b := {
    m := min a.m b.m
    seq n := a.seq n + b.seq n
    vanish n hn := by simp [a.vanish n (by omega), b.vanish n (by omega)]
  }

-- Сумма рядов, полученных из последовательностей `a` и `b`, — это ряд их поточечной суммы
theorem Series.add_coe (a b : ℕ → ℝ) : (a : Series) + (b : Series) = (fun n ↦ a n + b n) := by
  ext n; rfl
  change (a : Series).seq n + (b : Series).seq n = _
  by_cases h : n ≥ 0 <;> simp [h]

/-- Proposition 7.2.14 (a) (законы рядов) / Exercise 7.2.5. Форма {name}`convergesTo` может быть удобнее для приложений. -/
theorem Series.convergesTo.add {s t : Series} {L M : ℝ} (hs : s.convergesTo L) (ht : t.convergesTo M) : 
    (s + t).convergesTo (L + M) := by
  sorry

-- Сумма двух сходящихся рядов сходится, и её сумма равна сумме сумм слагаемых
theorem Series.add {s t : Series} (hs : s.converges) (ht : t.converges) :
    (s + t).converges ∧ (s+t).sum = s.sum + t.sum := by sorry

instance Series.inst.smul : SMul ℝ Series where
  smul c s := {
    m := s.m
    seq n := if n ≥ s.m then c * s.seq n else 0
    vanish := by grind
  }

-- Умножение ряда, полученного из последовательности `a`, на константу `c` — это ряд `c * a n`
theorem Series.smul_coe (a : ℕ → ℝ) (c : ℝ) : (c • a : Series) = (fun n ↦ c * a n) := by
  ext n; rfl
  by_cases h : n ≥ 0 <;> simp [h, HSMul.hSMul, SMul.smul]

/-- Proposition 7.2.14 (b) (законы рядов) / Exercise 7.2.5. Форма {name}`convergesTo` может быть удобнее для приложений. -/
theorem Series.convergesTo.smul {s : Series} {L c : ℝ} (hs : s.convergesTo L) : 
    (c • s).convergesTo (c * L) := by
  sorry

-- Умножение сходящегося ряда на константу `c` сохраняет сходимость и умножает сумму на `c`
theorem Series.smul {c : ℝ} {s : Series} (hs : s.converges) :
    (c • s).converges ∧ (c • s).sum = c * s.sum := by sorry

/-- Соответствующее API для вычитания отсутствовало в учебнике, но полезно в последующих разделах, поэтому включено здесь. -/
instance Series.inst_sub : Sub Series where
  sub a b := {
    m := min a.m b.m
    seq n := a.seq n - b.seq n
    vanish n hn := by simp [a.vanish n (by omega), b.vanish n (by omega)]
  }

-- Разность рядов, полученных из последовательностей `a` и `b`, — это ряд их поточечной разности
theorem Series.sub_coe (a b : ℕ → ℝ) : (a : Series) - (b : Series) = (fun n ↦ a n - b n) := by
  ext n; rfl
  change (a : Series).seq n - (b : Series).seq n = _
  by_cases h : n ≥ 0 <;> simp [h]

-- Если `s` сходится к `L`, а `t` — к `M`, то `s - t` сходится к `L - M`
theorem Series.convergesTo.sub {s t : Series} {L M : ℝ} (hs : s.convergesTo L) (ht : t.convergesTo M) :
    (s - t).convergesTo (L - M) := by
  sorry

-- Разность двух сходящихся рядов сходится, и её сумма равна разности сумм
theorem Series.sub {s t : Series} (hs : s.converges) (ht : t.converges) :
    (s - t).converges ∧ (s-t).sum = s.sum - t.sum := by sorry

abbrev Series.from (s : Series) (m₁ : ℤ) : Series := mk' (m := max s.m m₁) (fun n ↦ s.seq (n : ℤ))

/-- Proposition 7.2.14 (c) (Series laws) / Exercise 7.2.5 -/
theorem Series.converges_from (s : Series) (k : ℕ) : s.converges ↔ (s.from (s.m+k)).converges := by
  sorry

-- Сумма сходящегося ряда равна сумме первых `k` членов плюс сумма хвоста ряда, начинающегося с `s.m + k`
theorem Series.sum_from {s : Series} (k : ℕ) (h : s.converges) :
    s.sum = ∑ n ∈ Finset.Ico s.m (s.m+k), s.seq n + (s.from (s.m+k)).sum := by
  sorry

/-- Proposition 7.2.14 (d) (Series laws) / Exercise 7.2.5 -/
theorem Series.shift {s : Series} {x : ℝ} (h : s.convergesTo x) (L : ℤ) : 
    (mk' (m := s.m + L) (fun n ↦ s.seq (n - L))).convergesTo x := by
  sorry

/-- Lemma 7.2.15 (телескопический ряд) / Exercise 7.2.6 -/
theorem Series.telescope {a : ℕ → ℝ} (ha : Filter.atTop.Tendsto a (nhds 0)) : 
    ((fun n : ℕ ↦ a n - a (n+1)) : Series).convergesTo (a 0) := by
  sorry

/-- Exercise 7.2.1 -/
def Series.exercise_7_2_1_convergent : 
  Decidable ( (mk' (m := 1) (fun n ↦ (-1 : ℝ)^(n : ℤ))).converges ) := by
  -- Первая строка этого доказательства должна быть `apply isTrue` или `apply isFalse`.
  sorry


end Chapter7
