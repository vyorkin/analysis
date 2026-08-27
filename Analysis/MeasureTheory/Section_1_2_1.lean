import Analysis.MeasureTheory.Section_1_2_0
import Analysis.Misc.«Real-EReal-ENNReal»
import Analysis.Misc.Combinatorics

/-!
# Introduction to Measure Theory, раздел 1.2.1: свойства внешней меры Лебега

Файл, сопровождающий введение к разделу 1.2.1 книги «An Introduction to Measure Theory».

-/

open BoundedInterval

/-- Представить {name}`Box.toSet` как прообраз pi-множества относительно гомеоморфизма {name}`PiLp`. -/
lemma Box.toSet_eq_ofLp_preimage {d : ℕ} (B : Box d) :
    B.toSet = (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)) ⁻¹' Set.univ.pi (fun i => (B.side i).toSet) := by
  ext x; simp only [Box.mem_toSet, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]; rfl

/-- Внутренность {name}`Box.toSet`, выраженная как прообраз. -/
lemma Box.interior_toSet {d : ℕ} (B : Box d) : 
    interior B.toSet = (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)) ⁻¹'
      Set.univ.pi (fun i => interior (B.side i).toSet) := by
  rw [Box.toSet_eq_ofLp_preimage,
    ← (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).preimage_interior,
    interior_pi_set Set.finite_univ]

/-- Замыкание {name}`Box.toSet`, выраженное как прообраз. -/
lemma Box.closure_toSet {d : ℕ} (B : Box d) : 
    closure B.toSet = (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)) ⁻¹'
      Set.univ.pi (fun i => closure (B.side i).toSet) := by
  rw [Box.toSet_eq_ofLp_preimage,
    ← (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).preimage_closure,
    closure_pi_set]

/-- Граница {name}`Box.toSet`, выраженная через гомеоморфизм {name}`PiLp`. -/
lemma Box.frontier_toSet {d : ℕ} (B : Box d) : 
    frontier B.toSet = (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)) ⁻¹'
      frontier (Set.univ.pi (fun i => (B.side i).toSet)) := by
  rw [Box.toSet_eq_ofLp_preimage,
    ← (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).preimage_frontier]

/-- Прямоугольник (box) со сторонами {name}`BoundedInterval.Icc` замкнут. -/
lemma Box.isClosed_toSet_of_Icc {d : ℕ} (B : Box d)
    (h : ∀ i, ∃ a b, B.side i = BoundedInterval.Icc a b) : IsClosed B.toSet := by
  rw [Box.toSet_eq_ofLp_preimage]
  apply IsClosed.preimage (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).continuous
  apply isClosed_set_pi; intro i _
  obtain ⟨a, b, hab⟩ := h i
  simp only [hab, BoundedInterval.toSet]; exact isClosed_Icc

/-- Упражнение 1.2.3(i) (Пустое множество) -/
theorem Lebesgue_outer_measure.of_empty (d : ℕ) : Lebesgue_outer_measure (∅ : Set (EuclideanSpace' d)) = 0 := by
  sorry

/-- Упражнение 1.2.3(ii) (Монотонность) -/
theorem Lebesgue_outer_measure.mono {d : ℕ} {E F : Set (EuclideanSpace' d)} (h : E ⊆ F) : 
    Lebesgue_outer_measure E ≤ Lebesgue_outer_measure F := by
  sorry

/-- Внешняя мера Лебега неотрицательна.
    Поскольку это sInf сумм объёмов прямоугольников (box), каждая из которых ≥ 0, результат
    тоже ≥ 0. -/
theorem Lebesgue_outer_measure.nonneg {d : ℕ} (E : Set (EuclideanSpace' d)) : 
    0 ≤ Lebesgue_outer_measure E := by
  unfold Lebesgue_outer_measure
  -- 0 ≤ sInf S, когда все элементы ≥ 0 (для полной решётки sInf ∅ = ⊤ ≥ 0)
  apply le_sInf
  intro V hV
  obtain ⟨X, S, _, rfl⟩ := hV
  apply tsum_nonneg
  intro n
  -- Объём прямоугольника (box) неотрицателен (произведение неотрицательных длин)
  have hvol : 0 ≤ |S n|ᵥ := by
    rw [Box.volume]
    apply Finset.prod_nonneg
    intro i _
    rw [BoundedInterval.length]
    exact le_max_right _ _
  exact EReal.coe_nonneg.mpr hvol

/-- Упражнение 1.2.3(iii) (Счётная субаддитивность) -/
theorem Lebesgue_outer_measure.union_le {d : ℕ} (E : ℕ → Set (EuclideanSpace' d)) : 
    Lebesgue_outer_measure (⋃ i, E i) ≤ ∑' i, Lebesgue_outer_measure (E i) := by
  sorry

/-- Конечная субаддитивность -/
theorem Lebesgue_outer_measure.finite_union_le {d n : ℕ} (E : Fin n → Set (EuclideanSpace' d)) : 
    Lebesgue_outer_measure (⋃ i, E i) ≤ ∑ i, Lebesgue_outer_measure (E i) := by
  -- Продолжаем E до функции ℕ → Set, используя пустое множество для индексов ≥ n,
  -- а затем применяем счётную субаддитивность
  let E' : ℕ → Set (EuclideanSpace' d) := fun k =>
    if h : k < n then E ⟨k, h⟩ else ∅
  -- Объединение по Fin n равно объединению по всем k через E' k
  have h_union : (⋃ i, E i) = (⋃ k, E' k) := by
    ext x
    simp [E']
    constructor
    · intro ⟨i, hi⟩
      use i.val
      simp [hi]
    · intro ⟨k, hx⟩
      by_cases hk : k < n
      · use ⟨k, hk⟩
        simpa [dif_pos hk] using hx
      · simp [dif_neg hk] at hx
  rw [h_union]
  -- Применяем счётную субаддитивность
  calc Lebesgue_outer_measure (⋃ k, E' k)
      ≤ ∑' k, Lebesgue_outer_measure (E' k) := union_le E'
    _ = ∑ i : Fin n, Lebesgue_outer_measure (E i) := by
        -- Сумма по ℕ равна сумме по Fin n, поскольку E' k = ∅ при k ≥ n
        -- Сначала установим, что E' k = ∅ при k ≥ n, поэтому её внешняя мера равна 0
        have h_empty : ∀ k ≥ n, E' k = ∅ := fun k hk => dif_neg (not_lt.mpr hk)
        have h_measure_empty : ∀ k ≥ n, Lebesgue_outer_measure (E' k) = 0 := by
          intro k hk
          rw [h_empty k hk, of_empty]

        -- Преобразуем tsum в сумму по Fin n
        -- Ключевая лемма, которая нам нужна: tsum равна конечной сумме, когда функция имеет
        -- конечный носитель
        -- В нашем случае E' k непусто только при k < n

        -- Определим явную биекцию и используем её
        have : ∑' k, Lebesgue_outer_measure (E' k) = ∑ i : Fin n, Lebesgue_outer_measure (E' i.val) := by
          -- Используем tsum_eq_sum с конечным носителем
          let s : Finset ℕ := Finset.range n
          have h_support : ∀ k ∉ s, Lebesgue_outer_measure (E' k) = 0 := by
            intro k hk
            have : ¬ k < n := by simpa [s, Finset.mem_range] using hk
            exact h_measure_empty k (le_of_not_gt this)
          rw [tsum_eq_sum h_support]
          -- Теперь покажем равенство сумм через переиндексацию
          refine Finset.sum_bij (fun (k : ℕ) (hk : k ∈ s) => ⟨k, ?_⟩) ?_ ?_ ?_ ?_
          · simpa [s, Finset.mem_range] using hk
          · intros; simp
          · intros k₁ k₂ hk₁ hk₂ heq; simp at heq; exact heq
          · intro i _
            use i.val
            refine ⟨?_, ?_⟩
            · simp [s, Finset.mem_range, i.isLt]
            · simp
          · intro i _; simp

        rw [this]
        congr 1
        ext i
        simp [E', dif_pos i.isLt]


noncomputable def set_dist {X : Type*} [PseudoMetricSpace X] (A B : Set X) : ℝ :=
  sInf ((fun p : X × X ↦ dist p.1 p.2) '' (A ×ˢ B))

-- ========================================================================
-- Начало вспомогательных лемм для леммы 1.2.5: Lebesgue_outer_measure.union_of_separated
-- ========================================================================

namespace BoundedInterval
/-- Извлечь левый и правый концы {name}`BoundedInterval`.
    Возвращает (a, b), где a — левый конец, а b — правый конец. -/
def endpoints (I : BoundedInterval) : ℝ × ℝ :=
  match I with
  | Ioo a b => (a, b)
  | Icc a b => (a, b)
  | Ioc a b => (a, b)
  | Ico a b => (a, b)

/-- Вычислить середину {name}`BoundedInterval`. -/
noncomputable def midpoint (I : BoundedInterval) : ℝ :=
  let (a, b) := I.endpoints
  (a + b) / 2

/-- Разбить {name}`BoundedInterval` на левую и правую половины, используя замкнутые интервалы.
    Левая половина: \[a, m\], правая половина: \[m, b\], где m — середина.
    Использование замкнутых интервалов обеспечивает покрытие (объединение равно исходному
    интервалу), сохраняя при этом свойства теории меры (пересечение имеет нулевую меру). -/
noncomputable def bisect (I : BoundedInterval) : BoundedInterval × BoundedInterval :=
  let (a, b) := I.endpoints
  let m := I.midpoint
  (Icc a m, Icc m b)


/-- Левая половина разбиения имеет половину исходной длины -/
lemma bisect_fst_length (I : BoundedInterval) : 
    |(I.bisect.fst)|ₗ = |I|ₗ / 2 := by
  unfold bisect midpoint endpoints length
  cases I with
  | Ioo a b =>
    simp only [BoundedInterval.a, BoundedInterval.b]
    -- Цель: max ((a + b) / 2 - a) 0 = max (b - a) 0 / 2
    have h : (a + b) / 2 - a = (b - a) / 2 := by ring
    rw [h, max_div_two]
  | Icc a b =>
    simp only [BoundedInterval.a, BoundedInterval.b]
    have h : (a + b) / 2 - a = (b - a) / 2 := by ring
    rw [h, max_div_two]
  | Ioc a b =>
    simp only [BoundedInterval.a, BoundedInterval.b]
    have h : (a + b) / 2 - a = (b - a) / 2 := by ring
    rw [h, max_div_two]
  | Ico a b =>
    simp only [BoundedInterval.a, BoundedInterval.b]
    have h : (a + b) / 2 - a = (b - a) / 2 := by ring
    rw [h, max_div_two]

/-- Правая половина разбиения имеет половину исходной длины -/
lemma bisect_snd_length (I : BoundedInterval) : 
    |(I.bisect.snd)|ₗ = |I|ₗ / 2 := by
  unfold bisect midpoint endpoints length
  cases I with
  | Ioo a b =>
    simp only [BoundedInterval.a, BoundedInterval.b]
    -- Цель: max (b - (a + b) / 2) 0 = max (b - a) 0 / 2
    have h : b - (a + b) / 2 = (b - a) / 2 := by ring
    rw [h, max_div_two]
  | Icc a b =>
    simp only [BoundedInterval.a, BoundedInterval.b]
    have h : b - (a + b) / 2 = (b - a) / 2 := by ring
    rw [h, max_div_two]
  | Ioc a b =>
    simp only [BoundedInterval.a, BoundedInterval.b]
    have h : b - (a + b) / 2 = (b - a) / 2 := by ring
    rw [h, max_div_two]
  | Ico a b =>
    simp only [BoundedInterval.a, BoundedInterval.b]
    have h : b - (a + b) / 2 = (b - a) / 2 := by ring
    rw [h, max_div_two]

/-- Разбиение сохраняет суммарную длину -/
lemma bisect_length_sum (I : BoundedInterval) : 
    |(I.bisect.fst)|ₗ + |(I.bisect.snd)|ₗ = |I|ₗ := by
  rw [bisect_fst_length, bisect_snd_length]
  ring

/-- Левый конец bisect.fst совпадает с I.a -/
@[simp]
lemma bisect_fst_a (I : BoundedInterval) : (I.bisect.fst).a = I.a := by
  unfold bisect endpoints
  cases I <;> simp [BoundedInterval.a]

/-- Левый конец bisect.snd совпадает с I.midpoint -/
@[simp]
lemma bisect_snd_a (I : BoundedInterval) : (I.bisect.snd).a = I.midpoint := by
  unfold bisect endpoints
  cases I <;> simp [BoundedInterval.a, midpoint]

/-- Середина равна a + длина/2, когда a ≤ b (невырожденный интервал) -/
lemma midpoint_eq_a_add_half_length (I : BoundedInterval) (h : I.a ≤ I.b) : 
    I.midpoint = I.a + |I|ₗ / 2 := by
  unfold midpoint endpoints length
  cases I with
  | Ioo a b =>
    simp only [BoundedInterval.a, BoundedInterval.b] at h ⊢
    simp [max_eq_left (sub_nonneg.mpr h)]; ring
  | Icc a b =>
    simp only [BoundedInterval.a, BoundedInterval.b] at h ⊢
    simp [max_eq_left (sub_nonneg.mpr h)]; ring
  | Ioc a b =>
    simp only [BoundedInterval.a, BoundedInterval.b] at h ⊢
    simp [max_eq_left (sub_nonneg.mpr h)]; ring
  | Ico a b =>
    simp only [BoundedInterval.a, BoundedInterval.b] at h ⊢
    simp [max_eq_left (sub_nonneg.mpr h)]; ring


/-- Середина лежит в первой половине разбиения (как правый конец {name}`BoundedInterval.Icc`) -/
lemma midpoint_mem_bisect_fst (I : BoundedInterval) (h : I.toSet.Nonempty) : 
    I.midpoint ∈ (I.bisect.fst).toSet := by
  obtain ⟨x, hx⟩ := h
  unfold bisect midpoint endpoints toSet at *
  cases I with
  | Ioo a b =>
    simp only [Set.mem_Ioo] at hx
    simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
  | Icc a b =>
    simp only [Set.mem_Icc] at hx
    simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
  | Ioc a b =>
    simp only [Set.mem_Ioc] at hx
    simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
  | Ico a b =>
    simp only [Set.mem_Ico] at hx
    simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩

/-- Середина лежит во второй половине разбиения (как левый конец {name}`BoundedInterval.Icc`) -/
lemma midpoint_mem_bisect_snd (I : BoundedInterval) (h : I.toSet.Nonempty) : 
    I.midpoint ∈ (I.bisect.snd).toSet := by
  obtain ⟨x, hx⟩ := h
  unfold bisect midpoint endpoints toSet at *
  cases I with
  | Ioo a b =>
    simp only [Set.mem_Ioo] at hx
    simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
  | Icc a b =>
    simp only [Set.mem_Icc] at hx
    simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
  | Ioc a b =>
    simp only [Set.mem_Ioc] at hx
    simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
  | Ico a b =>
    simp only [Set.mem_Ico] at hx
    simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩


/-- Точка лежит в I.bisect.snd тогда и только тогда, когда она лежит в I.toSet и не меньше середины -/
lemma mem_bisect_snd_iff (I : BoundedInterval) (x : ℝ) (hx : x ∈ I.toSet) : 
    x ∈ (I.bisect.snd).toSet ↔ x ≥ I.midpoint := by
  unfold bisect midpoint endpoints toSet at *
  cases I with
  | Ioo a b =>
    simp only [Set.mem_Ioo] at hx
    simp only [Set.mem_Icc]
    constructor
    · intro ⟨h1, _⟩; exact h1
    · intro h; exact ⟨h, by linarith⟩
  | Icc a b =>
    simp only [Set.mem_Icc] at hx
    simp only [Set.mem_Icc]
    constructor
    · intro ⟨h1, _⟩; exact h1
    · intro h; exact ⟨h, by linarith⟩
  | Ioc a b =>
    simp only [Set.mem_Ioc] at hx
    simp only [Set.mem_Icc]
    constructor
    · intro ⟨h1, _⟩; exact h1
    · intro h; exact ⟨h, by linarith⟩
  | Ico a b =>
    simp only [Set.mem_Ico] at hx
    simp only [Set.mem_Icc]
    constructor
    · intro ⟨h1, _⟩; exact h1
    · intro h; exact ⟨h, by linarith⟩

/-- Точка лежит в I.bisect.fst тогда и только тогда, когда она лежит в I.toSet и не больше середины -/
lemma mem_bisect_fst_iff (I : BoundedInterval) (x : ℝ) (hx : x ∈ I.toSet) : 
    x ∈ (I.bisect.fst).toSet ↔ x ≤ I.midpoint := by
  unfold bisect midpoint endpoints toSet at *
  cases I with
  | Ioo a b =>
    simp only [Set.mem_Ioo] at hx
    simp only [Set.mem_Icc]
    constructor
    · intro ⟨_, h2⟩; exact h2
    · intro h; exact ⟨by linarith, h⟩
  | Icc a b =>
    simp only [Set.mem_Icc] at hx
    simp only [Set.mem_Icc]
    constructor
    · intro ⟨_, h2⟩; exact h2
    · intro h; exact ⟨by linarith, h⟩
  | Ioc a b =>
    simp only [Set.mem_Ioc] at hx
    simp only [Set.mem_Icc]
    constructor
    · intro ⟨_, h2⟩; exact h2
    · intro h; exact ⟨by linarith, h⟩
  | Ico a b =>
    simp only [Set.mem_Ico] at hx
    simp only [Set.mem_Icc]
    constructor
    · intro ⟨_, h2⟩; exact h2
    · intro h; exact ⟨by linarith, h⟩

/-- Если у двух интервалов совпадают bisect.fst, то совпадают и их концы -/
lemma bisect_fst_eq_endpoints {I₁ I₂ : BoundedInterval}
    (h : I₁.bisect.fst = I₂.bisect.fst) : I₁.a = I₂.a ∧ I₁.b = I₂.b := by
  -- bisect.fst = Icc I.a I.midpoint, поэтому (bisect.fst).a = I.a
  have ha' : (I₁.bisect.fst).a = (I₂.bisect.fst).a := congrArg (·.a) h
  have hm' : (I₁.bisect.fst).b = (I₂.bisect.fst).b := congrArg (·.b) h
  simp only [bisect, endpoints, midpoint, BoundedInterval.a, BoundedInterval.b] at ha' hm'
  constructor
  · cases I₁ <;> cases I₂ <;> simp_all
  · cases I₁ <;> cases I₂ <;> simp only [BoundedInterval.b] at ha' hm' ⊢ <;> linarith

/-- Если у двух интервалов совпадают bisect.snd, то совпадают и их концы -/
lemma bisect_snd_eq_endpoints {I₁ I₂ : BoundedInterval}
    (h : I₁.bisect.snd = I₂.bisect.snd) : I₁.a = I₂.a ∧ I₁.b = I₂.b := by
  -- bisect.snd = Icc midpoint b, поэтому (bisect.snd).a = midpoint, а (bisect.snd).b = b
  have hm' : (I₁.bisect.snd).a = (I₂.bisect.snd).a := congrArg (·.a) h
  have hb' : (I₁.bisect.snd).b = (I₂.bisect.snd).b := congrArg (·.b) h
  -- Значение .b у bisect.snd — это просто I.b, а .a — это (I.a + I.b)/2
  cases I₁ with | _ a₁ b₁ =>
  cases I₂ with | _ a₂ b₂ =>
  all_goals simp only [bisect, endpoints, midpoint, BoundedInterval.a, BoundedInterval.b] at hm' hb' ⊢
  -- Теперь hm' : (a₁ + b₁)/2 = (a₂ + b₂)/2, а hb' : b₁ = b₂
  all_goals constructor <;> linarith


/-- Смешанный случай: если bisect.fst = bisect.snd, то середина одного интервала совпадает с концом другого -/
lemma bisect_fst_eq_snd_shift {I₁ I₂ : BoundedInterval}
    (h : I₁.bisect.fst = I₂.bisect.snd) : I₁.a = (I₂.a + I₂.b) / 2 := by
  -- (bisect.fst).a = I.a, (bisect.snd).a = I.midpoint = (I.a + I.b)/2
  have ha' : (I₁.bisect.fst).a = (I₂.bisect.snd).a := congrArg (·.a) h
  cases I₁ with | _ a₁ b₁ =>
  cases I₂ with | _ a₂ b₂ =>
  all_goals simp only [bisect, endpoints, midpoint, BoundedInterval.a, BoundedInterval.b] at ha' ⊢
  all_goals linarith

end BoundedInterval

namespace Box
/-- Диаметр прямоугольника (box) — это точная верхняя грань евклидовых расстояний между точками этого прямоугольника -/
noncomputable def diameter {d : ℕ} (B : Box d) : ℝ :=
  sSup { r | ∃ x ∈ B.toSet, ∃ y ∈ B.toSet, r = √(∑ i, (x i - y i)^2) }

/-- Диаметр всегда неотрицателен -/
lemma diameter_nonneg {d : ℕ} (B : Box d) : 0 ≤ B.diameter := by
  unfold diameter
  by_cases h : B.toSet.Nonempty
  · obtain ⟨x, hx⟩ := h
    apply le_csSup
    · -- Множество ограничено сверху
      use (∑ i : Fin d, |B.side i|ₗ)
      intro r ⟨y, hy, z, hz, hr⟩
      -- dist y z ограничено суммой длин сторон
      rw [hr]
      -- y, z ∈ B.toSet означает, что ∀ i, y i ∈ B.side i и z i ∈ B.side i
      have hy_coord : ∀ i, y i ∈ (B.side i).toSet := by
        intro i; exact hy i
      have hz_coord : ∀ i, z i ∈ (B.side i).toSet := by
        intro i; exact hz i
      -- Для каждой координаты разность ограничена длиной соответствующей стороны
      have coord_bound : ∀ i, |(y - z) i| ≤ |B.side i|ₗ := by
        intro i
        have hy_i := hy_coord i
        have hz_i := hz_coord i
        -- Для всех типов интервалов оценка одинакова: |y i - z i| ≤ max (b - a) 0
        -- Это верно потому, что и y i, и z i лежат в [a,b] (или (a,b) для открытых концов)
        cases h_side : B.side i with
        | Ioo a b =>
            simp [BoundedInterval.toSet, h_side] at hy_i hz_i
            simp [BoundedInterval.length]
            left
            rw [abs_sub_le_iff]
            constructor <;> linarith [hy_i.1, hy_i.2, hz_i.1, hz_i.2]
        | Icc a b =>
            simp [BoundedInterval.toSet, h_side] at hy_i hz_i
            simp [BoundedInterval.length]
            left
            rw [abs_sub_le_iff]
            constructor <;> linarith [hy_i.1, hy_i.2, hz_i.1, hz_i.2]
        | Ioc a b =>
            simp [BoundedInterval.toSet, h_side] at hy_i hz_i
            simp [BoundedInterval.length]
            left
            rw [abs_sub_le_iff]
            constructor <;> linarith [hy_i.1, hy_i.2, hz_i.1, hz_i.2]
        | Ico a b =>
            simp [BoundedInterval.toSet, h_side] at hy_i hz_i
            simp [BoundedInterval.length]
            left
            rw [abs_sub_le_iff]
            constructor <;> linarith [hy_i.1, hy_i.2, hz_i.1, hz_i.2]
      -- Теперь докажем, что √(∑ (y i - z i)²) ≤ ∑ |B.side i|ₗ
      -- Используем: √(∑ xᵢ²) ≤ ∑ √(xᵢ²) = ∑ |xᵢ| (субаддитивность корня)
      have sqrt_sum_le : (∑ i, (y i - z i) ^ 2).sqrt ≤ ∑ i, |(y i - z i)| := by
        -- норма ℓ² ≤ норма ℓ¹: √(∑ xᵢ²) ≤ ∑ |xᵢ|
        calc (∑ i, (y i - z i) ^ 2).sqrt
            = (∑ i, |(y i - z i)| ^ 2).sqrt := by
                congr 1; congr 1; ext i; rw [sq_abs]
          _ ≤ ∑ i, (|(y i - z i)| ^ 2).sqrt := by
                -- Применяем лемму о субаддитивности корня
                apply Real.sqrt_sum_le_sum_sqrt
                intro i; exact sq_nonneg _
          _ = ∑ i, |(y i - z i)| := by
                congr 1; ext i
                rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (abs_nonneg _)]
      calc √(∑ i, (y i - z i) ^ 2)
          ≤ ∑ i, |(y i - z i)| := sqrt_sum_le
        _ = ∑ i, |(y - z) i| := by rfl
        _ ≤ ∑ i, |B.side i|ₗ := by
            apply Finset.sum_le_sum
            intro i _
            exact coord_bound i
    · -- 0 входит в множество (расстояние от точки до самой себя)
      use x, hx, x, hx
      simp
  · -- У пустого прямоугольника диаметр равен 0
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h]
    simp [sSup]

/-- У пустого прямоугольника диаметр равен 0 -/
lemma diameter_of_empty {d : ℕ} (B : Box d) (h : B.toSet = ∅) : 
    B.diameter = 0 := by
  unfold diameter
  simp [h, sSup]

/-- Любые две точки прямоугольника (box) находятся на евклидовом расстоянии не более диаметра -/
lemma dist_le_diameter {d : ℕ} (B : Box d) {x y : EuclideanSpace' d}
    (hx : x ∈ B.toSet) (hy : y ∈ B.toSet) : 
    √(∑ i, (x i - y i)^2) ≤ B.diameter := by
  unfold diameter
  apply le_csSup
  · -- Множество ограничено сверху
    use (∑ i : Fin d, |B.side i|ₗ)
    intro r ⟨z, hz, w, hw, hr⟩
    -- dist z w ограничено суммой длин сторон
    rw [hr]
    -- z, w ∈ B.toSet означает, что ∀ i, z i ∈ B.side i и w i ∈ B.side i
    have hz_coord : ∀ i, z i ∈ (B.side i).toSet := by
      intro i; exact hz i
    have hw_coord : ∀ i, w i ∈ (B.side i).toSet := by
      intro i; exact hw i
    -- Для каждой координаты разность ограничена длиной соответствующей стороны
    have coord_bound : ∀ i, |(z - w) i| ≤ |B.side i|ₗ := by
      intro i
      have hz_i := hz_coord i
      have hw_i := hw_coord i
      -- Для всех типов интервалов оценка одинакова: |z i - w i| ≤ max (b - a) 0
      cases h_side : B.side i with
      | Ioo a b =>
          simp [BoundedInterval.toSet, h_side] at hz_i hw_i
          simp [BoundedInterval.length]
          left
          rw [abs_sub_le_iff]
          constructor <;> linarith [hz_i.1, hz_i.2, hw_i.1, hw_i.2]
      | Icc a b =>
          simp [BoundedInterval.toSet, h_side] at hz_i hw_i
          simp [BoundedInterval.length]
          left
          rw [abs_sub_le_iff]
          constructor <;> linarith [hz_i.1, hz_i.2, hw_i.1, hw_i.2]
      | Ioc a b =>
          simp [BoundedInterval.toSet, h_side] at hz_i hw_i
          simp [BoundedInterval.length]
          left
          rw [abs_sub_le_iff]
          constructor <;> linarith [hz_i.1, hz_i.2, hw_i.1, hw_i.2]
      | Ico a b =>
          simp [BoundedInterval.toSet, h_side] at hz_i hw_i
          simp [BoundedInterval.length]
          left
          rw [abs_sub_le_iff]
          constructor <;> linarith [hz_i.1, hz_i.2, hw_i.1, hw_i.2]
    -- Теперь докажем, что √(∑ (z i - w i)²) ≤ ∑ |B.side i|ₗ
    have sqrt_sum_le : (∑ i, (z i - w i) ^ 2).sqrt ≤ ∑ i, |(z i - w i)| := by
      -- норма ℓ² ≤ норма ℓ¹: √(∑ xᵢ²) ≤ ∑ |xᵢ|
      calc (∑ i, (z i - w i) ^ 2).sqrt
          = (∑ i, |(z i - w i)| ^ 2).sqrt := by
              congr 1; congr 1; ext i; rw [sq_abs]
        _ ≤ ∑ i, (|(z i - w i)| ^ 2).sqrt := by
              apply Real.sqrt_sum_le_sum_sqrt
              intro i; exact sq_nonneg _
        _ = ∑ i, |(z i - w i)| := by
              congr 1; ext i
              rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (abs_nonneg _)]
    calc √(∑ i, (z i - w i) ^ 2)
        ≤ ∑ i, |(z i - w i)| := sqrt_sum_le
      _ = ∑ i, |(z - w) i| := by rfl
      _ ≤ ∑ i, |B.side i|ₗ := by
          apply Finset.sum_le_sum
          intro i _
          exact coord_bound i
  · -- √(∑ (x i - y i)²) входит в множество
    exact ⟨x, hx, y, hy, rfl⟩


/-- Для любого непустого интервала и целевого значения, меньшего его длины,
    можно найти две точки интервала, расстояние между которыми превышает это значение.
    Это ключевой факт о плотности: достижимые разности плотны в \[0, длина\]. -/
lemma BoundedInterval.exists_points_with_diff {I : BoundedInterval}
    (h_nonempty : I.toSet.Nonempty) {t : ℝ} (ht_nonneg : 0 ≤ t) (ht : t < |I|ₗ) : 
    ∃ x ∈ I.toSet, ∃ y ∈ I.toSet, t < |x - y| := by
  -- Поскольку t < |I|ₗ = max (b - a) 0 и t ≥ 0, получаем b - a > t ≥ 0
  have h_len_pos : 0 < |I|ₗ := lt_of_le_of_lt ht_nonneg ht
  cases I with
  | Icc a b =>
    simp only [length, BoundedInterval.a, BoundedInterval.b] at ht h_len_pos
    have h_ab : a < b := by
      by_contra h; push_neg at h
      have : max (b - a) 0 = 0 := max_eq_right (by linarith)
      linarith
    have h_t_lt : t < b - a := by
      have hmax : max (b - a) 0 = b - a := max_eq_left (by linarith)
      rw [hmax] at ht
      exact ht
    -- Замкнутый случай: используем концы a и b
    refine ⟨a, Set.left_mem_Icc.mpr (le_of_lt h_ab), b, Set.right_mem_Icc.mpr (le_of_lt h_ab), ?_⟩
    rw [abs_sub_comm, abs_of_pos (by linarith : 0 < b - a)]
    linarith
  | Ioo a b =>
    simp only [length, BoundedInterval.a, BoundedInterval.b] at ht h_len_pos
    have h_ab : a < b := by
      by_contra h; push_neg at h
      have : max (b - a) 0 = 0 := max_eq_right (by linarith)
      linarith
    have h_t_lt : t < b - a := by
      have hmax : max (b - a) 0 = b - a := max_eq_left (by linarith)
      rw [hmax] at ht
      exact ht
    -- Открытый случай: используем точки вблизи концов
    set δ := ((b - a) - t) / 2 with hδ_def
    have h_δ_pos : 0 < δ := by linarith
    have hx_mem : a + δ / 2 ∈ Set.Ioo a b := Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
    have hy_mem : b - δ / 2 ∈ Set.Ioo a b := Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
    refine ⟨a + δ / 2, hx_mem, b - δ / 2, hy_mem, ?_⟩
    have h_diff : (b - δ / 2) - (a + δ / 2) = (b - a) - δ := by ring
    rw [abs_sub_comm, abs_of_pos (by linarith : 0 < (b - δ / 2) - (a + δ / 2)), h_diff]
    linarith
  | Ioc a b =>
    simp only [length, BoundedInterval.a, BoundedInterval.b] at ht h_len_pos
    have h_ab : a < b := by
      by_contra h; push_neg at h
      have : max (b - a) 0 = 0 := max_eq_right (by linarith)
      linarith
    have h_t_lt : t < b - a := by
      have hmax : max (b - a) 0 = b - a := max_eq_left (by linarith)
      rw [hmax] at ht
      exact ht
    -- Слева открыт, справа замкнут: используем точку рядом с a и точку b
    set δ := ((b - a) - t) / 2 with hδ_def
    have h_δ_pos : 0 < δ := by linarith
    have hx_mem : a + δ / 2 ∈ Set.Ioc a b := Set.mem_Ioc.mpr ⟨by linarith, by linarith⟩
    have hy_mem : b ∈ Set.Ioc a b := Set.mem_Ioc.mpr ⟨h_ab, le_refl b⟩
    refine ⟨a + δ / 2, hx_mem, b, hy_mem, ?_⟩
    have h_diff : b - (a + δ / 2) = (b - a) - δ / 2 := by ring
    rw [abs_sub_comm, abs_of_pos (by linarith : 0 < b - (a + δ / 2)), h_diff]
    linarith
  | Ico a b =>
    simp only [length, BoundedInterval.a, BoundedInterval.b] at ht h_len_pos
    have h_ab : a < b := by
      by_contra h; push_neg at h
      have : max (b - a) 0 = 0 := max_eq_right (by linarith)
      linarith
    have h_t_lt : t < b - a := by
      have hmax : max (b - a) 0 = b - a := max_eq_left (by linarith)
      rw [hmax] at ht
      exact ht
    -- Слева замкнут, справа открыт: используем точку a и точку рядом с b
    set δ := ((b - a) - t) / 2 with hδ_def
    have h_δ_pos : 0 < δ := by linarith
    have hx_mem : a ∈ Set.Ico a b := Set.mem_Ico.mpr ⟨le_refl a, h_ab⟩
    have hy_mem : b - δ / 2 ∈ Set.Ico a b := Set.mem_Ico.mpr ⟨by linarith, by linarith⟩
    refine ⟨a, hx_mem, b - δ / 2, hy_mem, ?_⟩
    have h_diff : (b - δ / 2) - a = (b - a) - δ / 2 := by ring
    rw [abs_sub_comm, abs_of_pos (by linarith : 0 < (b - δ / 2) - a), h_diff]
    linarith

/-- Диаметр непустого прямоугольника (box) равен длине диагонали √(∑ |side i|ₗ²).
    Это ключевой факт: точная верхняя грань попарных расстояний равна диагонали.
    Для замкнутых интервалов диагональ достигается в углах.
    Для открытых интервалов диагональ является пределом (супремумом) достижимых расстояний. -/
lemma diameter_eq_sqrt_sum_sq {d : ℕ} (B : Box d) (h : B.toSet.Nonempty) : 
    B.diameter = √(∑ i, |B.side i|ₗ^2) := by
  unfold diameter
  -- Используем csSup_eq_of_forall_le_of_forall_lt_exists_gt:
  -- если s.Nonempty ∧ (∀ a ∈ s, a ≤ b) ∧ (∀ c < b, ∃ a ∈ s, c < a), то sSup s = b
  let s := { r | ∃ x ∈ B.toSet, ∃ y ∈ B.toSet, r = √(∑ i, (x i - y i)^2) }
  let b := √(∑ i, |B.side i|ₗ^2)
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
  · -- s непусто
    obtain ⟨x, hx⟩ := h
    exact ⟨√(∑ i, (x i - x i)^2), x, hx, x, hx, rfl⟩
  · -- ∀ a ∈ s, a ≤ b (верхняя грань)
    intro r ⟨x, hx, y, hy, hr⟩
    rw [hr]
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro i _
    -- |x i - y i|² ≤ |B.side i|ₗ²
    have hx_i : x i ∈ (B.side i).toSet := hx i
    have hy_i : y i ∈ (B.side i).toSet := hy i
    have coord_bound : |x i - y i| ≤ |B.side i|ₗ := by
      cases h_side : B.side i <;>
          simp [BoundedInterval.toSet, h_side] at hx_i hy_i <;>
          simp [BoundedInterval.length] <;>
          (left; rw [abs_sub_le_iff]; constructor <;> linarith [hx_i.1, hx_i.2, hy_i.1, hy_i.2])
    calc (x i - y i)^2 = |x i - y i|^2 := by rw [sq_abs]
      _ ≤ |B.side i|ₗ^2 := by
          apply sq_le_sq' <;> [linarith [abs_nonneg (x i - y i), coord_bound]; exact coord_bound]
  · -- ∀ c < b, ∃ a ∈ s, c < a (плотность : можно приблизиться к b сколь угодно близко)
    intro c hc
    -- Нужно найти x, y ∈ B с √(∑ (x i - y i)²) > c
    -- Стратегия: для каждой координаты берём точки у противоположных концов интервала
    -- Итоговое расстояние будет близко к √(∑ side²)
    -- Поскольку c < √(∑ side²), можно найти ε > 0 такое, что c < √(∑ side²) - ε
    -- Затем выбираем x, y так, чтобы |x i - y i| ≥ |side i| - δ для достаточно малого δ
    -- Это даёт √(∑ (x i - y i)²) ≥ √(∑ (side - δ)²) > c при малом δ
    --
    -- Для формального доказательства используем, что интервалы непусты (из h_nonempty),
    -- и что можно выбирать точки с контролируемым расстоянием от концов.
    by_cases h_zero : (∑ i, |B.side i|ₗ^2) = 0
    · -- Все стороны имеют длину 0, поэтому b = 0
      -- c < 0 невозможно, поскольку любое расстояние ≥ 0
      simp only [h_zero, Real.sqrt_zero] at hc
      -- c < 0, но любое расстояние ≥ 0, поэтому нужно c < некоторого расстояния ≥ 0
      -- Поскольку c < 0, имеем c < 0 ≤ любого расстояния
      obtain ⟨x, hx⟩ := h
      use 0
      constructor
      · exact ⟨x, hx, x, hx, by simp⟩
      · linarith
    · -- У некоторой стороны положительная длина
      -- Используем характеризацию: √(∑ side²) > c означает ∑ side² > c²
      have h_pos : 0 < ∑ i, |B.side i|ₗ^2 := by
        apply lt_of_le_of_ne
        · apply Finset.sum_nonneg; intro i _; exact sq_nonneg _
        · exact Ne.symm h_zero
      -- Получаем ε такое, что c + ε < √(∑ side²)
      have h_c_lt : c < √(∑ i, |B.side i|ₗ^2) := hc
      -- Поскольку c < √(∑ side²), имеем c² < ∑ side² (при c ≥ 0) или c < 0
      by_cases hc_nonneg : 0 ≤ c
      · -- Случай c ≥ 0 : нужно построить точки с большим расстоянием
        -- Стратегия: используем exists_points_with_diff для координат положительной длины
        -- Каждый интервал непуст (из h: B.toSet.Nonempty)
        have h_interval_nonempty : ∀ i, (B.side i).toSet.Nonempty := by
          intro i; obtain ⟨x, hx⟩ := h
          exact ⟨x i, hx i⟩
        -- Построим точки покоординатно: ≥ для всех и > для координат положительной длины
        let ratio := c / √(∑ i, |B.side i|ₗ^2)
        have h_ratio_lt_one : ratio < 1 := by
          show c / √(∑ i, |B.side i|ₗ^2) < 1
          rw [div_lt_one (Real.sqrt_pos.mpr h_pos)]
          exact h_c_lt
        have h_ratio_nonneg : 0 ≤ ratio := by
          show 0 ≤ c / √(∑ i, |B.side i|ₗ^2)
          exact div_nonneg hc_nonneg (Real.sqrt_nonneg _)
        -- Для координат положительной длины: получаем строгое неравенство
        have h_exists_points : ∀ i, ∃ xi ∈ (B.side i).toSet, ∃ yi ∈ (B.side i).toSet,
            |B.side i|ₗ * ratio ≤ |xi - yi| ∧
            (0 < |B.side i|ₗ → |B.side i|ₗ * ratio < |xi - yi|) := by
          intro i
          by_cases h_len_zero : |B.side i|ₗ = 0
          · -- Интервал нулевой длины : xi = yi даёт 0 ≤ 0
            obtain ⟨xi, hxi⟩ := h_interval_nonempty i
            refine ⟨xi, hxi, xi, hxi, ?_, ?_⟩
            · simp [h_len_zero]
            · simp [h_len_zero]
          · -- Интервал положительной длины : используем exists_points_with_diff
            have h_len_pos : 0 < |B.side i|ₗ := by
              apply lt_of_le_of_ne; simp [BoundedInterval.length]; exact Ne.symm h_len_zero
            have h_target_lt : |B.side i|ₗ * ratio < |B.side i|ₗ := by
              calc |B.side i|ₗ * ratio < |B.side i|ₗ * 1 := by
                    apply mul_lt_mul_of_pos_left h_ratio_lt_one h_len_pos
                _ = |B.side i|ₗ := mul_one _
            obtain ⟨xi, hxi, yi, hyi, hlt⟩ := BoundedInterval.exists_points_with_diff
              (h_interval_nonempty i) (mul_nonneg (by simp [BoundedInterval.length]) h_ratio_nonneg)
              h_target_lt
            exact ⟨xi, hxi, yi, hyi, le_of_lt hlt, fun _ => hlt⟩
        -- Используем Classical.choose, чтобы извлечь точки
        classical
        let x' : Fin d → ℝ := fun i => (h_exists_points i).choose
        let y' : Fin d → ℝ := fun i => (h_exists_points i).choose_spec.2.choose
        have hx_mem : ∀ i, x' i ∈ (B.side i).toSet := fun i => (h_exists_points i).choose_spec.1
        have hy_mem : ∀ i, y' i ∈ (B.side i).toSet := fun i =>
          (h_exists_points i).choose_spec.2.choose_spec.1
        have h_diff_le : ∀ i, |B.side i|ₗ * ratio ≤ |x' i - y' i| := fun i =>
          (h_exists_points i).choose_spec.2.choose_spec.2.1
        have h_diff_lt : ∀ i, 0 < |B.side i|ₗ → |B.side i|ₗ * ratio < |x' i - y' i| := fun i =>
          (h_exists_points i).choose_spec.2.choose_spec.2.2
        -- x, y ∈ B.toSet
        let x : EuclideanSpace' d := .toLp 2 x'
        let y : EuclideanSpace' d := .toLp 2 y'
        have hx_box : x ∈ B.toSet := fun i => hx_mem i
        have hy_box : y ∈ B.toSet := fun i => hy_mem i
        -- Расстояние √(∑ (x_i - y_i)²) > c
        use √(∑ i, (x i - y i)^2)
        constructor
        · exact ⟨x, hx_box, y, hy_box, rfl⟩
        · -- Нужно : c < √(∑ (x_i - y_i)²)
          rw [← Real.sqrt_sq hc_nonneg]
          apply Real.sqrt_lt_sqrt (sq_nonneg c)
          -- Нужно: c² < ∑ (x_i - y_i)²
          -- c² = ∑ (side * ratio)² и у нас есть ≤ для всех, < хотя бы для одной положительной стороны
          have h_target : c^2 = ∑ i, (|B.side i|ₗ * ratio)^2 := by
            have h_sum_nonneg : 0 ≤ ∑ i : Fin d, |B.side i|ₗ^2 :=
              Finset.sum_nonneg (fun i _ => sq_nonneg (|B.side i|ₗ))
            have h_sqrt_ne : √(∑ i, |B.side i|ₗ^2) ≠ 0 := Real.sqrt_ne_zero'.mpr h_pos
            calc c^2 = (√(∑ i, |B.side i|ₗ^2) * ratio)^2 := by
                  show c^2 = (√(∑ i, |B.side i|ₗ^2) * (c / √(∑ i, |B.side i|ₗ^2)))^2
                  field_simp
              _ = (∑ i, |B.side i|ₗ^2) * ratio^2 := by
                  rw [mul_pow, Real.sq_sqrt h_sum_nonneg]
              _ = ∑ i, |B.side i|ₗ^2 * ratio^2 := Finset.sum_mul _ _ _
              _ = ∑ i, (|B.side i|ₗ * ratio)^2 := by congr 1; ext i; ring
          rw [h_target]
          -- Поскольку ∑ side² > 0, хотя бы одна сторона положительна
          have h_exists_pos : ∃ j, 0 < |B.side j|ₗ := by
            by_contra h_all_zero; push_neg at h_all_zero
            have h_sum_zero : (∑ i, |B.side i|ₗ^2) = 0 := by
              apply Finset.sum_eq_zero; intro i _
              have : |B.side i|ₗ ≤ 0 := h_all_zero i
              have h_nonneg : 0 ≤ |B.side i|ₗ := by simp [BoundedInterval.length]
              have : |B.side i|ₗ = 0 := le_antisymm this h_nonneg
              simp [this]
            exact h_zero h_sum_zero
          obtain ⟨j, hj_pos⟩ := h_exists_pos
          apply Finset.sum_lt_sum
          · intro i _
            have h_sq : (|B.side i|ₗ * ratio)^2 ≤ |x i - y i|^2 := by
              apply sq_le_sq' _ (h_diff_le i)
              calc -(|x i - y i|) ≤ 0 := neg_nonpos.mpr (abs_nonneg _)
                _ ≤ |B.side i|ₗ * ratio := mul_nonneg (by simp [BoundedInterval.length]) h_ratio_nonneg
            calc (|B.side i|ₗ * ratio)^2 ≤ |x i - y i|^2 := h_sq
              _ = (x i - y i)^2 := by rw [sq_abs]
          · use j, Finset.mem_univ j
            have h_sq_lt : (|B.side j|ₗ * ratio)^2 < |x j - y j|^2 := by
              -- Из h_diff_lt знаем, что side * ratio < |x j - y j|, поэтому |x j - y j| > 0
              have h_diff_pos : 0 < |x j - y j| :=
                lt_of_le_of_lt (mul_nonneg (by simp [BoundedInterval.length]) h_ratio_nonneg)
                  (h_diff_lt j hj_pos)
              apply sq_lt_sq' _ (h_diff_lt j hj_pos)
              calc -(|x j - y j|) < 0 := neg_neg_of_pos h_diff_pos
                _ ≤ |B.side j|ₗ * ratio := mul_nonneg (by simp [BoundedInterval.length]) h_ratio_nonneg
            calc (|B.side j|ₗ * ratio)^2 < |x j - y j|^2 := h_sq_lt
              _ = (x j - y j)^2 := by rw [sq_abs]
      · -- Случай c < 0 : любое расстояние ≥ 0 > c
        push_neg at hc_nonneg
        obtain ⟨x, hx⟩ := h
        use 0
        constructor
        · exact ⟨x, hx, x, hx, by simp⟩
        · linarith

/-- Если прямоугольник (box) пересекается с двумя множествами, то любые две точки (по одной из
    каждого множества) внутри прямоугольника находятся на расстоянии не более диаметра -/
lemma diameter_ge_dist_of_intersects {d : ℕ} (B : Box d) (E F : Set (EuclideanSpace' d))
    (hE : (B.toSet ∩ E).Nonempty) (hF : (B.toSet ∩ F).Nonempty) : 
    set_dist E F ≤ B.diameter := by
  obtain ⟨x, hx_box, hx_E⟩ := hE
  obtain ⟨y, hy_box, hy_F⟩ := hF
  -- set_dist E F ≤ dist x y (по определению set_dist как инфимума)
  have h_dist : set_dist E F ≤ dist x y := by
    unfold set_dist
    apply csInf_le
    · -- Ограничено снизу нулём
      use 0
      intro r ⟨p, hp, hr⟩
      rw [← hr]
      exact dist_nonneg
    · -- Расстояние от x до y входит в множество
      simp only [Set.mem_image]
      use (x, y)
      exact ⟨Set.mem_prod.mpr ⟨hx_E, hy_F⟩, rfl⟩
  -- dist x y ≤ B.diameter (по dist_le_diameter)
  have h_le_diam : √(∑ i, (x i - y i)^2) ≤ B.diameter :=
    dist_le_diameter B hx_box hy_box
  -- Замечание: для EuclideanSpace' d выполняется dist x y = √(∑ i, (x i - y i)^2)
  have h_eq : dist x y = √(∑ i, (x i - y i)^2) := by
    simp only [EuclideanSpace.dist_eq]
    congr 1
    congr 1
    ext i
    rw [Real.dist_eq, sq_abs]
  -- Объединяем
  calc set_dist E F
      ≤ dist x y := h_dist
    _ = √(∑ i, (x i - y i)^2) := h_eq
    _ ≤ B.diameter := h_le_diam

/-- Если B.diameter < set\_dist E F, то B не может пересекаться и с E, и с F одновременно.
    Это ключевой геометрический факт, необходимый для конечной аддитивности разделённых множеств. -/
lemma not_intersects_both_of_diameter_lt {d : ℕ} (B : Box d) (E F : Set (EuclideanSpace' d))
    (h : B.diameter < set_dist E F) : 
    ¬((B.toSet ∩ E).Nonempty ∧ (B.toSet ∩ F).Nonempty) := by
  intro ⟨hE, hF⟩
  -- Если B пересекается с обоими, то set_dist E F ≤ B.diameter
  have := diameter_ge_dist_of_intersects B E F hE hF
  -- Но мы предположили B.diameter < set_dist E F
  linarith

open Classical in
/-- Разрешимое равенство для прямоугольников (box), необходимое для операций {name}`Finset` -/
noncomputable instance {d : ℕ} : DecidableEq (Box d) := instDecidableEqOfLawfulBEq

/-- Подразбить прямоугольник (box), разбивая пополам каждую координатную ось, получая 2^d
    подпрямоугольников. Каждый подпрямоугольник образован взятием одной из половин-интервалов
    по каждой координате. Мы используем {name}`Finset.univ` (все возможные d-битовые
    последовательности) для перечисления всех 2^d комбинаций. -/
noncomputable def subdivide {d : ℕ} (B : Box d) : Finset (Box d) :=
  -- Для каждого choice ∈ Fin d → Bool (какую половину брать по каждой координате)
  -- строим подпрямоугольник, беря левую половину (если false) или правую (если true)
  Finset.univ.image fun (choice : Fin d → Bool) =>
    { side := fun i =>
        let (left, right) := (B.side i).bisect
        if choice i then right else left }

/-- Объём подразбитого прямоугольника (box) равен сумме объёмов его подпрямоугольников -/
lemma volume_subdivide {d : ℕ} (B : Box d) :
    ∑ B' ∈ B.subdivide, |B'|ᵥ = |B|ᵥ := by
  unfold subdivide Box.volume
  -- Устанавливаем, что длина каждой координаты разбивается на две половины
  have h_sum : ∀ i, |(B.side i)|ₗ = |(B.side i).bisect.fst|ₗ + |(B.side i).bisect.snd|ₗ := by
    intro i; exact (BoundedInterval.bisect_length_sum (B.side i)).symm
  -- Переписываем правую часть, используя тождество суммы
  have h_rhs : ∏ i, |(B.side i)|ₗ = ∏ i, (|(B.side i).bisect.fst|ₗ + |(B.side i).bisect.snd|ₗ) := by
    apply Finset.prod_congr rfl; intro i _; exact h_sum i
  rw [h_rhs, Fin.prod_add_eq_sum_prod_choice d _ _]
  -- Отображение из choice в прямоугольник
  let g : (Fin d → Bool) → Box d := fun c =>
    { side := fun i => let (l, r) := (B.side i).bisect; if c i then r else l }
  -- Ключевой факт: объём g c равен произведению половинных длин
  have h_vol_eq : ∀ c : Fin d → Bool, |g c|ᵥ =
      ∏ i, (if c i then |(B.side i).bisect.snd|ₗ else |(B.side i).bisect.fst|ₗ) := by
    intro c; unfold Box.volume; apply Finset.prod_congr rfl; intro i _
    simp only [g]; split_ifs <;> rfl
  -- Два выбора дают одинаковое произведение, если отображаются в один и тот же прямоугольник
  have h_prod_eq : ∀ c₁ c₂ : Fin d → Bool, g c₁ = g c₂ →
      (∏ i, (if c₁ i then |(B.side i).bisect.snd|ₗ else |(B.side i).bisect.fst|ₗ)) =
      (∏ i, (if c₂ i then |(B.side i).bisect.snd|ₗ else |(B.side i).bisect.fst|ₗ)) := by
    intro c₁ c₂ heq
    apply Finset.prod_congr rfl; intro i _
    have hside : (g c₁).side i = (g c₂).side i := congrArg (·.side i) heq
    simp only [g] at hside
    cases hc₁ : c₁ i <;> cases hc₂ : c₂ i <;> simp only [hc₁, hc₂, ↓reduceIte, Bool.false_eq_true] at hside ⊢
    -- случай true/false: hside : bisect.snd = bisect.fst
    · rw [congrArg BoundedInterval.length hside]
    -- случай false/true: hside : bisect.fst = bisect.snd
    · rw [congrArg BoundedInterval.length hside]
  -- Используем sum_image', который умеет работать с неинъективными отображениями
  let h_func : (Fin d → Bool) → ℝ := fun c =>
    ∏ i, (if c i then |(B.side i).bisect.snd|ₗ else |(B.side i).bisect.fst|ₗ)
  have h_fiber : ∀ c ∈ Finset.univ, |g c|ᵥ = ∑ j ∈ Finset.univ with g j = g c, h_func j := by
    intro c _
    rw [h_vol_eq c]
    have h_fib_eq : ∀ j ∈ Finset.univ, g j = g c → h_func j = h_func c := by
      intro j _ hgj; exact h_prod_eq j c hgj
    -- Цель: h_func c = ∑ j with g j = g c, h_func j
    -- У всех элементов слоя значение h_func c, поэтому сумма = card * h_func c
    conv_rhs => rw [show ∑ j ∈ Finset.univ with g j = g c, h_func j =
        ∑ j ∈ Finset.univ.filter (fun j => g j = g c), h_func j from rfl]
    rw [Finset.sum_eq_card_nsmul (fun x hx => by
      rw [Finset.mem_filter] at hx; exact h_fib_eq x hx.1 hx.2)]
    rw [nsmul_eq_mul]
    -- Нужно: h_func c = card * h_func c. Выполняется при card = 1 ИЛИ h_func c = 0.
    by_cases h_card : (Finset.univ.filter (fun j => g j = g c)).card = 1
    · simp only [h_card, Nat.cast_one, one_mul]; rfl
    · -- card ≠ 1, а card ≥ 1 (поскольку c входит в слой), значит card > 1
      have h_card_pos : 0 < (Finset.univ.filter (fun j => g j = g c)).card := by
        apply Finset.card_pos.mpr; use c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h_card_gt : 1 < (Finset.univ.filter (fun j => g j = g c)).card := by omega
      obtain ⟨c₁, hc₁, c₂, hc₂, hne⟩ := Finset.one_lt_card.mp h_card_gt
      rw [Finset.mem_filter] at hc₁ hc₂
      -- c₁ и c₂ отличаются в какой-то координате
      have ⟨i, hi_ne⟩ : ∃ i, c₁ i ≠ c₂ i := by
        by_contra h; push_neg at h; exact hne (funext h)
      -- В этой координате из g c₁ = g c₂ следует bisect.fst = bisect.snd
      have hside : (g c₁).side i = (g c₂).side i := congrArg (·.side i) (hc₁.2.trans hc₂.2.symm)
      simp only [g] at hside
      -- Извлекаем равенство bisect из hside разбором случаев c₁ i и c₂ i
      have h_bisect_eq : (B.side i).bisect.fst = (B.side i).bisect.snd := by
        cases hc₁i : c₁ i <;> cases hc₂i : c₂ i <;>
        simp only [hc₁i, hc₂i, Bool.false_eq_true, ↓reduceIte] at hside hi_ne
        · exact (hi_ne rfl).elim  -- случай false/false : противоречие
        · exact hside             -- случай false/true : hside : fst = snd
        · exact hside.symm        -- случай true/false : hside : snd = fst
        · exact (hi_ne rfl).elim  -- случай true/true : противоречие
      -- Когда fst = snd, интервал вырожден (это точка), поэтому длина = 0
      have h_len_zero : |(B.side i).bisect.snd|ₗ = 0 := by
        rw [← h_bisect_eq]
        -- bisect.fst = bisect.snd означает Icc a m = Icc m b, то есть a = m = b
        unfold BoundedInterval.bisect BoundedInterval.midpoint BoundedInterval.endpoints at h_bisect_eq
        cases hI : B.side i with
        | Ioo a b =>
          simp only [hI] at h_bisect_eq
          have ha : a = (a + b) / 2 := congrArg BoundedInterval.a h_bisect_eq
          have hb : (a + b) / 2 = b := congrArg BoundedInterval.b h_bisect_eq
          have hab : a = b := by linarith
          simp only [BoundedInterval.length, BoundedInterval.bisect, BoundedInterval.midpoint,
            BoundedInterval.endpoints, BoundedInterval.b, BoundedInterval.a, hab]
          ring_nf; simp
        | Icc a b =>
          simp only [hI] at h_bisect_eq
          have ha : a = (a + b) / 2 := congrArg BoundedInterval.a h_bisect_eq
          have hb : (a + b) / 2 = b := congrArg BoundedInterval.b h_bisect_eq
          have hab : a = b := by linarith
          simp only [BoundedInterval.length, BoundedInterval.bisect, BoundedInterval.midpoint,
            BoundedInterval.endpoints, BoundedInterval.b, BoundedInterval.a, hab]
          ring_nf; simp
        | Ioc a b =>
          simp only [hI] at h_bisect_eq
          have ha : a = (a + b) / 2 := congrArg BoundedInterval.a h_bisect_eq
          have hb : (a + b) / 2 = b := congrArg BoundedInterval.b h_bisect_eq
          have hab : a = b := by linarith
          simp only [BoundedInterval.length, BoundedInterval.bisect, BoundedInterval.midpoint,
            BoundedInterval.endpoints, BoundedInterval.b, BoundedInterval.a, hab]
          ring_nf; simp
        | Ico a b =>
          simp only [hI] at h_bisect_eq
          have ha : a = (a + b) / 2 := congrArg BoundedInterval.a h_bisect_eq
          have hb : (a + b) / 2 = b := congrArg BoundedInterval.b h_bisect_eq
          have hab : a = b := by linarith
          simp only [BoundedInterval.length, BoundedInterval.bisect, BoundedInterval.midpoint,
            BoundedInterval.endpoints, BoundedInterval.b, BoundedInterval.a, hab]
          ring_nf; simp
      -- у h_func c нулевой множитель в координате i, поэтому произведение равно 0
      have h_len_fst_zero : |(B.side i).bisect.fst|ₗ = 0 := by rw [h_bisect_eq]; exact h_len_zero
      have h_prod_zero : h_func c = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        cases hci : c i
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact h_len_fst_zero
        · simp only [↓reduceIte]; exact h_len_zero
      simp only [h_prod_zero, mul_zero]
      -- Цель: h_func c = 0, а это в точности h_prod_zero
      exact h_prod_zero
  rw [Finset.sum_image' h_func h_fiber]

/-- Каждый подпрямоугольник разбиения имеет диаметр не более исходного диаметра, делённого на √2.
    Это следует из того, что каждая сторона делится пополам, уменьшая диагональ в связанное с
    √2 число раз. Замечание: гипотеза непустоты B необходима, поскольку разбиение пополам всегда
    создаёт замкнутые интервалы, которые могут превратить вырожденные открытые интервалы
    ({given -show}`a` {lean}`Ioo a a`) в непустые одноэлементные множества. -/
lemma subdivide_diameter_bound {d : ℕ} (B : Box d) (hB : B.toSet.Nonempty) :
    ∀ B' ∈ B.subdivide, B'.diameter ≤ B.diameter / Real.sqrt 2 := by
  intro B' hB'
  -- Извлекаем функцию выбора, задающую B'
  unfold subdivide at hB'
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hB'
  obtain ⟨choice, rfl⟩ := hB'
  -- Сокращённое обозначение подпрямоугольника для читаемости
  set B' : Box d := { side := fun i => if choice i then (B.side i).bisect.snd
      else (B.side i).bisect.fst } with hB'_def
  -- Ключевой факт: B'.diameter ≤ B.diameter / 2 ≤ B.diameter / √2
  -- Поскольку √2 < 2, имеем B.diameter / 2 ≤ B.diameter / √2
  suffices h : B'.diameter ≤ B.diameter / 2 by
    calc B'.diameter
        ≤ B.diameter / 2 := h
      _ ≤ B.diameter / √2 := by
          apply div_le_div_of_nonneg_left (diameter_nonneg B)
          · exact Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
          · calc √2 ≤ √4 := Real.sqrt_le_sqrt (by norm_num : (2 : ℝ) ≤ 4)
              _ = 2 := by norm_num
  -- Теперь докажем B'.diameter ≤ B.diameter / 2
  -- Ключевой факт: |B'.side i|ₗ = |B.side i|ₗ / 2 для всех i, поэтому диагональ уменьшается вдвое
  -- Из непустоты B каждый интервал стороны непуст
  have h_side_nonempty : ∀ i, (B.side i).toSet.Nonempty := by
    intro i; obtain ⟨x, hx⟩ := hB
    exact ⟨x i, hx i⟩
  -- Сначала покажем, что B' непусто (середина каждой стороны лежит в обеих половинах)
  have hB'_nonempty : B'.toSet.Nonempty := by
    use .toLp 2 (fun i => (B.side i).midpoint)
    intro i
    simp only [hB'_def]
    split_ifs with h
    · exact BoundedInterval.midpoint_mem_bisect_snd (B.side i) (h_side_nonempty i)
    · exact BoundedInterval.midpoint_mem_bisect_fst (B.side i) (h_side_nonempty i)
  -- Каждая сторона B' вдвое короче соответствующей стороны B
  have h_side_half : ∀ i, |B'.side i|ₗ = |B.side i|ₗ / 2 := by
    intro i
    simp only [hB'_def]
    split_ifs with h
    · exact BoundedInterval.bisect_snd_length _
    · exact BoundedInterval.bisect_fst_length _
  -- Применяем diameter_eq_sqrt_sum_sq к обоим прямоугольникам
  rw [diameter_eq_sqrt_sum_sq B' hB'_nonempty, diameter_eq_sqrt_sum_sq B hB]
  -- √(∑ (side/2)²) = √(∑ side²) / 2
  have h_sum_eq : ∑ i, |B'.side i|ₗ^2 = (∑ i, |B.side i|ₗ^2) / 4 := by
    simp_rw [h_side_half, div_pow]
    rw [Finset.sum_div]
    ring_nf
  rw [h_sum_eq, Real.sqrt_div (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  norm_num

/-- Подразбить прямоугольник (box) k раз, получая {name}`Finset` прямоугольников.
    После k итераций каждый исходный прямоугольник разбивается на до 2^(d\*k) подпрямоугольников. -/
noncomputable def subdivide_iter {d : ℕ} (B : Box d) : ℕ → Finset (Box d)
  | 0 => {B}
  | k+1 => (subdivide_iter B k).biUnion Box.subdivide

lemma subdivide_iter_zero {d : ℕ} (B : Box d) : subdivide_iter B 0 = {B} := rfl

lemma subdivide_iter_succ {d : ℕ} (B : Box d) (k : ℕ) : 
    subdivide_iter B (k+1) = (subdivide_iter B k).biUnion Box.subdivide := rfl

/-- Все стороны в {name}`Box.subdivide` (один уровень) являются интервалами {name}`BoundedInterval.Icc` -/
lemma subdivide_side_is_Icc {d : ℕ} (B : Box d) (B' : Box d) (hB' : B' ∈ B.subdivide) (i : Fin d) :
    ∃ a b, B'.side i = Icc a b := by
  simp only [subdivide, Finset.mem_image, Finset.mem_univ, true_and] at hB'
  obtain ⟨c, rfl⟩ := hB'
  -- B' = { side := fun j => if c j then ... else ... }
  -- B'.side i = if c i then (B.side i).bisect.snd else (B.side i).bisect.fst
  simp only  -- Это вводит if-then-else в цель
  split_ifs with hc
  · -- случай snd : (B.side i).bisect.snd является Icc
    unfold BoundedInterval.bisect BoundedInterval.endpoints BoundedInterval.midpoint
    cases B.side i <;> exact ⟨_, _, rfl⟩
  · -- случай fst : (B.side i).bisect.fst является Icc
    unfold BoundedInterval.bisect BoundedInterval.endpoints BoundedInterval.midpoint
    cases B.side i <;> exact ⟨_, _, rfl⟩

/-- Все стороны в {name}`Box.subdivide_iter` при k ≥ 1 являются интервалами {name}`BoundedInterval.Icc` -/
lemma subdivide_iter_side_is_Icc {d : ℕ} (B : Box d) (k : ℕ) (B' : Box d)
    (hB' : B' ∈ subdivide_iter B (k+1)) (i : Fin d) : 
    ∃ a b, B'.side i = Icc a b := by
  induction k generalizing B' with
  | zero =>
    simp only [subdivide_iter, Finset.mem_biUnion, Finset.mem_singleton] at hB'
    obtain ⟨B'', rfl, hB'_sub⟩ := hB'
    exact subdivide_side_is_Icc B'' B' hB'_sub i
  | succ k ih =>
    simp only [subdivide_iter_succ, Finset.mem_biUnion] at hB'
    obtain ⟨B'', hB'', hB'_sub⟩ := hB'
    exact subdivide_side_is_Icc B'' B' hB'_sub i

/-- У всех прямоугольников в {name}`Box.subdivide_iter` одинаковые длины сторон по каждой координате -/
lemma subdivide_iter_side_length {d : ℕ} (B : Box d) (k : ℕ) (B' : Box d)
    (hB' : B' ∈ subdivide_iter B k) (i : Fin d) : 
    |B'.side i|ₗ = |B.side i|ₗ / 2^k := by
  induction k generalizing B' with
  | zero =>
    simp only [subdivide_iter, Finset.mem_singleton] at hB'
    simp [hB']
  | succ k ih =>
    simp only [subdivide_iter_succ, Finset.mem_biUnion] at hB'
    obtain ⟨B'', hB'', hB'_sub⟩ := hB'
    have h1 := ih B'' hB''
    simp only [subdivide, Finset.mem_image, Finset.mem_univ, true_and] at hB'_sub
    obtain ⟨c, rfl⟩ := hB'_sub
    simp only
    split_ifs with hc
    · rw [BoundedInterval.bisect_snd_length, h1]; ring
    · rw [BoundedInterval.bisect_fst_length, h1]; ring

/-- Непустой прямоугольник (box) остаётся непустым после разбиения -/
lemma subdivide_one_step_nonempty {d : ℕ} (B : Box d) (hB : B.toSet.Nonempty) :
    ∀ B' ∈ B.subdivide, B'.toSet.Nonempty := by
  intro B' hB'
  unfold subdivide at hB'
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hB'
  obtain ⟨choice, rfl⟩ := hB'
  -- Середина B входит во все подпрямоугольники
  use .toLp 2 (fun i => (B.side i).midpoint)
  intro i
  have h_side_nonempty : (B.side i).toSet.Nonempty := by
    obtain ⟨x, hx⟩ := hB
    exact ⟨x i, hx i⟩
  simp only
  split_ifs with h
  · exact BoundedInterval.midpoint_mem_bisect_snd (B.side i) h_side_nonempty
  · exact BoundedInterval.midpoint_mem_bisect_fst (B.side i) h_side_nonempty

/-- Непустой прямоугольник (box) остаётся непустым после k итераций разбиения -/
lemma subdivide_iter_nonempty {d : ℕ} (B : Box d) (hB : B.toSet.Nonempty) (k : ℕ) : 
    ∀ B' ∈ subdivide_iter B k, B'.toSet.Nonempty := by
  induction k with
  | zero =>
    simp only [subdivide_iter, Finset.mem_singleton]
    intro B' hB'; rw [hB']; exact hB
  | succ k ih =>
    intro B' hB'
    simp only [subdivide_iter_succ, Finset.mem_biUnion] at hB'
    obtain ⟨B'', hB''_mem, hB'_sub⟩ := hB'
    exact subdivide_one_step_nonempty B'' (ih B'' hB''_mem) B' hB'_sub

/-- Выравнивание по сетке: стороны в {name}`Box.subdivide_iter` начинаются в узлах сетки.
    Требует непустоты прямоугольника (box), чтобы гарантировать a ≤ b для сторон
    (перевёрнутые интервалы ломают формулу). -/
lemma subdivide_iter_side_grid {d : ℕ} (B : Box d) (hB : B.toSet.Nonempty) (k : ℕ) (B' : Box d)
    (hB' : B' ∈ subdivide_iter B k) (i : Fin d) : 
    ∃ j : ℕ, j < 2^k ∧ (B'.side i).a = (B.side i).a + j * (|B.side i|ₗ / 2^k) := by
  induction k generalizing B' with
  | zero =>
    simp only [subdivide_iter, Finset.mem_singleton] at hB'
    use 0
    simp [hB']
  | succ k ih =>
    simp only [subdivide_iter_succ, Finset.mem_biUnion] at hB'
    obtain ⟨B'', hB'', hB'_sub⟩ := hB'
    obtain ⟨j'', hj''_bound, hj''_eq⟩ := ih B'' hB''
    simp only [subdivide, Finset.mem_image, Finset.mem_univ, true_and] at hB'_sub
    obtain ⟨c, rfl⟩ := hB'_sub
    have h_len := subdivide_iter_side_length B k B'' hB'' i
    simp only
    split_ifs with hc
    · -- случай snd : начинаем в середине B''
      use 2 * j'' + 1
      constructor
      · omega
      · -- (bisect.snd).a = midpoint = B''.a + |B''|ₗ/2
        rw [BoundedInterval.bisect_snd_a]
        have h_B''_len : |B''.side i|ₗ = |B.side i|ₗ / 2 ^ k := h_len
        by_cases h_nondeg : (B''.side i).a ≤ (B''.side i).b
        · -- Невырожденный случай : используем midpoint_eq_a_add_half_length
          rw [BoundedInterval.midpoint_eq_a_add_half_length _ h_nondeg, hj''_eq, h_B''_len]
          have h2k : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
          rw [h2k]
          have h2k_ne : (2 : ℝ) ^ k ≠ 0 := by positivity
          field_simp [h2k_ne]
          push_cast; ring
        · -- Вырожденный случай : невозможен для непустых прямоугольников (у всех сторон a ≤ b)
          -- B'' непусто, поскольку B непусто
          have hB''_nonempty : B''.toSet.Nonempty := subdivide_iter_nonempty B hB k B'' hB''
          -- Следовательно, (B''.side i) непусто
          have h_side_nonempty : (B''.side i).toSet.Nonempty :=
            Box.side_nonempty_of_nonempty B'' hB''_nonempty i
          -- У непустых интервалов a ≤ b
          have h_order : (B''.side i).a ≤ (B''.side i).b :=
            BoundedInterval.nonempty_implies_le _ h_side_nonempty
          -- Противоречие с ¬h_nondeg
          exact absurd h_order h_nondeg
    · -- случай fst : начинаем в B''.a (левый конец сохраняется)
      use 2 * j''
      constructor
      · omega
      · rw [BoundedInterval.bisect_fst_a, hj''_eq]
        have h2k : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
        rw [h2k]
        have h2k_ne : (2 : ℝ) ^ k ≠ 0 := by positivity
        field_simp [h2k_ne]
        push_cast; ring

/-- Объём сохраняется при итеративном разбиении -/
lemma volume_subdivide_iter {d : ℕ} (B : Box d) (hB : B.toSet.Nonempty) (k : ℕ) :
    ∑ B' ∈ subdivide_iter B k, |B'|ᵥ = |B|ᵥ := by
  induction k with
  | zero => simp [subdivide_iter]
  | succ k ih =>
    simp only [subdivide_iter_succ]
    rw [Finset.sum_biUnion]
    · -- Каждая внутренняя сумма ∑ i ∈ x.subdivide, |i|ᵥ = |x|ᵥ по volume_subdivide
      calc ∑ x ∈ subdivide_iter B k, ∑ i ∈ x.subdivide, |i|ᵥ
          = ∑ x ∈ subdivide_iter B k, |x|ᵥ := by
            apply Finset.sum_congr rfl
            intro B' _
            exact volume_subdivide B'
        _ = |B|ᵥ := ih
    · -- Попарная непересекаемость разбиений разных родительских прямоугольников
      intro B₁ hB₁ B₂ hB₂ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_iff_ne]
      intro s₁ hs₁ s₂ hs₂
      -- Извлекаем функции выбора из принадлежности subdivide
      simp only [subdivide, Finset.mem_image, Finset.mem_univ, true_and] at hs₁ hs₂
      obtain ⟨c₁, rfl⟩ := hs₁
      obtain ⟨c₂, rfl⟩ := hs₂
      -- Предположим от противного, что s₁ = s₂
      intro heq
      apply hne
      -- Покажем B₁ = B₂ с помощью Box.ext
      ext i
      -- В координате i стороны s₁ и s₂ должны совпадать
      have h_side_eq : (if c₁ i then (B₁.side i).bisect.snd else (B₁.side i).bisect.fst) =
                       (if c₂ i then (B₂.side i).bisect.snd else (B₂.side i).bisect.fst) := by
        have := congrFun (congrArg Box.side heq) i
        simpa using this
      -- На уровне k ≥ 1 все стороны — Icc. Случай k = 0: subdivide_iter B 0 = {B}, поэтому B₁ = B₂
      match k with
      | 0 =>
        -- subdivide_iter B 0 = {B}, поэтому B₁ = B и B₂ = B
        have hB₁' : B₁ = B := by simpa [subdivide_iter] using hB₁
        have hB₂' : B₂ = B := by simpa [subdivide_iter] using hB₂
        simp [hB₁', hB₂']
      | k'+1 =>
      -- Получаем структуру Icc для обеих сторон
      obtain ⟨a₁, b₁, h_side₁⟩ := subdivide_iter_side_is_Icc B k' B₁ hB₁ i
      obtain ⟨a₂, b₂, h_side₂⟩ := subdivide_iter_side_is_Icc B k' B₂ hB₂ i
      -- Получаем позиции в сетке для B₁.side i и B₂.side i
      obtain ⟨j₁, _, hj₁⟩ := subdivide_iter_side_grid B hB (k'+1) B₁ hB₁ i
      obtain ⟨j₂, _, hj₂⟩ := subdivide_iter_side_grid B hB (k'+1) B₂ hB₂ i
      -- У обеих одинаковая длина
      have h_len₁ := subdivide_iter_side_length B (k'+1) B₁ hB₁ i
      have h_len₂ := subdivide_iter_side_length B (k'+1) B₂ hB₂ i
      have h_same_len : |B₁.side i|ₗ = |B₂.side i|ₗ := by rw [h_len₁, h_len₂]
      -- Разбор случаев по c₁ i и c₂ i
      cases hc₁ : c₁ i <;> cases hc₂ : c₂ i <;> simp only [hc₁, hc₂, ite_true] at h_side_eq
      · -- случай fst = fst : равенство концов влечёт равенство родителей
        obtain ⟨ha, hb⟩ := BoundedInterval.bisect_fst_eq_endpoints h_side_eq
        -- Обе стороны — Icc с одинаковыми концами
        simp only [h_side₁, h_side₂, BoundedInterval.a, BoundedInterval.b] at ha hb ⊢
        simp [ha, hb]
      · -- смешанный случай fst = snd : противоречие по чётности через позиции в сетке
        -- Ключевая идея: позиции в сетке — целые числа, но fst=snd требует полуцелого сдвига
        -- Для вырожденного случая (L=0): все интервалы схлопываются, поэтому B₁=B₂
        by_cases hL : |B.side i|ₗ = 0
        · -- Вырожденный случай : все стороны по измерению i — одноэлементные множества
          -- Когда длина = 0 для непустого прямоугольника (box), a = b (одна точка)
          -- У всех подразбиений одна и та же одноэлементная сторона
          have h1a : (B₁.side i).a = (B.side i).a := by rw [hj₁, hL]; simp
          have h2a : (B₂.side i).a = (B.side i).a := by rw [hj₂, hL]; simp
          have h1len : |B₁.side i|ₗ = 0 := by rw [h_len₁, hL]; simp
          have h2len : |B₂.side i|ₗ = 0 := by rw [h_len₂, hL]; simp
          -- Для непустых интервалов Icc нулевой длины: a = b
          have hB1_nonempty : B₁.toSet.Nonempty := subdivide_iter_nonempty B hB (k'+1) B₁ hB₁
          have hB2_nonempty : B₂.toSet.Nonempty := subdivide_iter_nonempty B hB (k'+1) B₂ hB₂
          have h1b : (B₁.side i).b = (B₁.side i).a := by
            have h_side_nonempty := Box.side_nonempty_of_nonempty B₁ hB1_nonempty i
            have h_order := BoundedInterval.nonempty_implies_le _ h_side_nonempty
            -- Для Icc a b нулевая длина при a ≤ b означает a = b
            unfold BoundedInterval.length at h1len
            simp only [max_eq_right_iff] at h1len
            linarith
          have h2b : (B₂.side i).b = (B₂.side i).a := by
            have h_side_nonempty := Box.side_nonempty_of_nonempty B₂ hB2_nonempty i
            have h_order := BoundedInterval.nonempty_implies_le _ h_side_nonempty
            unfold BoundedInterval.length at h2len
            simp only [max_eq_right_iff] at h2len
            linarith
          -- У обоих интервалов Icc одинаковые a и b, поэтому они равны
          simp only [h_side₁, h_side₂, BoundedInterval.a, BoundedInterval.b] at h1a h2a h1b h2b ⊢
          simp [h1a, h2a, h1b, h2b]
        · -- Невырожденный случай : выводим противоречие по чётности
          -- Из h_side_eq: bisect.fst для B₁ = bisect.snd для B₂
          -- Значит (B₁.side i).a = (B₂.side i).midpoint = (B₂.side i).a + |B₂.side i|ₗ/2
          have h_fst_a := BoundedInterval.bisect_fst_a (B₁.side i)
          have h_snd_a := BoundedInterval.bisect_snd_a (B₂.side i)
          have hB2_nonempty : B₂.toSet.Nonempty := subdivide_iter_nonempty B hB (k'+1) B₂ hB₂
          have h_side2_nonempty := Box.side_nonempty_of_nonempty B₂ hB2_nonempty i
          have h_order2 := BoundedInterval.nonempty_implies_le _ h_side2_nonempty
          have h_mid := BoundedInterval.midpoint_eq_a_add_half_length (B₂.side i) h_order2
          -- Из h_side_eq следует равенство левых концов
          have h_a_eq : (B₁.side i).bisect.fst.a = (B₂.side i).bisect.snd.a := congrArg (·.a) h_side_eq
          rw [h_fst_a, h_snd_a, h_mid] at h_a_eq
          -- Теперь имеем: B₁.side i.a = B₂.side i.a + |B₂.side i|ₗ/2
          -- Подставляем формулы сетки
          rw [hj₁, hj₂, h_len₂] at h_a_eq
          -- j₁ * step = j₂ * step + step/2, где step = |B.side i|ₗ / 2^(k'+2)
          have hstep_pos : (0 : ℝ) < |B.side i|ₗ / 2 ^ (k' + 2) := by
            apply div_pos
            · exact lt_of_le_of_ne (BoundedInterval.length_nonneg _) (Ne.symm hL)
            · positivity
          -- Это даёт j₁ = j₂ + 1/2, что невозможно для натуральных чисел
          -- Сокращаем (B.side i).a с обеих сторон
          have h_cancel : j₁ * (|B.side i|ₗ / 2^(k'+1)) =
                          j₂ * (|B.side i|ₗ / 2^(k'+1)) + (|B.side i|ₗ / 2^(k'+1)) / 2 := by
            have := h_a_eq; linarith
          -- Умножаем обе части на 2^(k'+2) / L, получая: 2*j₁ = 2*j₂ + 1
          have h2k1_ne : (2 : ℝ) ^ (k' + 1) ≠ 0 := by positivity
          have hL_pos : (0 : ℝ) < |B.side i|ₗ := lt_of_le_of_ne (BoundedInterval.length_nonneg _) (Ne.symm hL)
          have hL_ne : |B.side i|ₗ ≠ 0 := hL
          have h_step_ne : |B.side i|ₗ / 2^(k'+1) ≠ 0 := by positivity
          have h_parity : (2 * j₁ : ℝ) = 2 * j₂ + 1 := by
            -- Из h_cancel: j₁ * step = j₂ * step + step/2
            -- Умножаем обе части на 2, затем сокращаем step
            have h2 : 2 * (j₁ * (|B.side i|ₗ / 2^(k'+1))) =
                      2 * j₂ * (|B.side i|ₗ / 2^(k'+1)) + (|B.side i|ₗ / 2^(k'+1)) := by linarith
            have h3 : (|B.side i|ₗ / 2^(k'+1)) * (2 * j₁) = (|B.side i|ₗ / 2^(k'+1)) * (2 * j₂ + 1) := by
              ring_nf at h2 ⊢; linarith
            exact mul_left_cancel₀ h_step_ne h3
          -- 2*j₁ чётно, 2*j₂+1 нечётно: противоречие через omega
          have h_eq_nat : 2 * j₁ = 2 * j₂ + 1 := by
            have := h_parity
            norm_cast at this
          omega
      · -- смешанный случай snd = fst : симметричен случаю fst = snd
        by_cases hL : |B.side i|ₗ = 0
        · -- Вырожденный случай : идентичен случаю fst = snd
          have h1a : (B₁.side i).a = (B.side i).a := by rw [hj₁, hL]; simp
          have h2a : (B₂.side i).a = (B.side i).a := by rw [hj₂, hL]; simp
          have h1len : |B₁.side i|ₗ = 0 := by rw [h_len₁, hL]; simp
          have h2len : |B₂.side i|ₗ = 0 := by rw [h_len₂, hL]; simp
          have hB1_nonempty : B₁.toSet.Nonempty := subdivide_iter_nonempty B hB (k'+1) B₁ hB₁
          have hB2_nonempty : B₂.toSet.Nonempty := subdivide_iter_nonempty B hB (k'+1) B₂ hB₂
          have h1b : (B₁.side i).b = (B₁.side i).a := by
            have h_side_nonempty := Box.side_nonempty_of_nonempty B₁ hB1_nonempty i
            have h_order := BoundedInterval.nonempty_implies_le _ h_side_nonempty
            unfold BoundedInterval.length at h1len
            simp only [max_eq_right_iff] at h1len
            linarith
          have h2b : (B₂.side i).b = (B₂.side i).a := by
            have h_side_nonempty := Box.side_nonempty_of_nonempty B₂ hB2_nonempty i
            have h_order := BoundedInterval.nonempty_implies_le _ h_side_nonempty
            unfold BoundedInterval.length at h2len
            simp only [max_eq_right_iff] at h2len
            linarith
          simp only [h_side₁, h_side₂, BoundedInterval.a, BoundedInterval.b] at h1a h2a h1b h2b ⊢
          simp [h1a, h2a, h1b, h2b]
        · -- Невырожденный случай : выводим противоречие по чётности (симметричное рассуждение)
          -- Из h_side_eq: bisect.snd для B₁ = bisect.fst для B₂
          -- Значит (B₁.side i).midpoint = (B₂.side i).a
          have h_snd_a := BoundedInterval.bisect_snd_a (B₁.side i)
          have h_fst_a := BoundedInterval.bisect_fst_a (B₂.side i)
          have hB1_nonempty : B₁.toSet.Nonempty := subdivide_iter_nonempty B hB (k'+1) B₁ hB₁
          have h_side1_nonempty := Box.side_nonempty_of_nonempty B₁ hB1_nonempty i
          have h_order1 := BoundedInterval.nonempty_implies_le _ h_side1_nonempty
          have h_mid := BoundedInterval.midpoint_eq_a_add_half_length (B₁.side i) h_order1
          -- Из h_side_eq следует равенство левых концов
          have h_a_eq : (B₁.side i).bisect.snd.a = (B₂.side i).bisect.fst.a := congrArg (·.a) h_side_eq
          rw [h_snd_a, h_fst_a, h_mid] at h_a_eq
          -- Теперь имеем: B₁.side i.a + |B₁.side i|ₗ/2 = B₂.side i.a
          -- Подставляем формулы сетки
          rw [hj₁, hj₂, h_len₁] at h_a_eq
          -- Это даёт j₁ + 1/2 = j₂, что невозможно для натуральных чисел
          -- Сокращаем (B.side i).a с обеих сторон
          have h_cancel : j₁ * (|B.side i|ₗ / 2^(k'+1)) + (|B.side i|ₗ / 2^(k'+1)) / 2 =
                          j₂ * (|B.side i|ₗ / 2^(k'+1)) := by
            have := h_a_eq; linarith
          -- Умножаем обе части на 2^(k'+2) / L, получая: 2*j₁ + 1 = 2*j₂
          have h2k1_ne : (2 : ℝ) ^ (k' + 1) ≠ 0 := by positivity
          have hL_pos : (0 : ℝ) < |B.side i|ₗ := lt_of_le_of_ne (BoundedInterval.length_nonneg _) (Ne.symm hL)
          have hL_ne : |B.side i|ₗ ≠ 0 := hL
          have h_step_ne : |B.side i|ₗ / 2^(k'+1) ≠ 0 := by positivity
          have h_parity : (2 * j₁ + 1 : ℝ) = 2 * j₂ := by
            -- Из h_cancel: j₁ * step + step/2 = j₂ * step
            -- Умножаем обе части на 2, затем сокращаем step
            have h2 : 2 * j₁ * (|B.side i|ₗ / 2^(k'+1)) + (|B.side i|ₗ / 2^(k'+1)) =
                      2 * j₂ * (|B.side i|ₗ / 2^(k'+1)) := by linarith
            have h3 : (|B.side i|ₗ / 2^(k'+1)) * (2 * j₁ + 1) = (|B.side i|ₗ / 2^(k'+1)) * (2 * j₂) := by
              ring_nf at h2 ⊢; linarith
            exact mul_left_cancel₀ h_step_ne h3
          -- 2*j₁+1 нечётно, 2*j₂ чётно: противоречие через omega
          have h_eq_nat : 2 * j₁ + 1 = 2 * j₂ := by
            have := h_parity
            norm_cast at this
          omega
      · -- случай snd = snd : равенство концов влечёт равенство родителей
        obtain ⟨ha, hb⟩ := BoundedInterval.bisect_snd_eq_endpoints h_side_eq
        -- Обе стороны — Icc с одинаковыми концами
        simp only [h_side₁, h_side₂, BoundedInterval.a, BoundedInterval.b] at ha hb ⊢
        simp [ha, hb]

/-- Оценка диаметра после k итераций разбиения.
    Каждая итерация уменьшает диаметр в √2 раз. -/
lemma diameter_subdivide_iter {d : ℕ} (B : Box d) (hB : B.toSet.Nonempty) (k : ℕ) :
    ∀ B' ∈ subdivide_iter B k, B'.diameter ≤ B.diameter / (Real.sqrt 2) ^ k := by
  induction k with
  | zero =>
    simp only [subdivide_iter, Finset.mem_singleton, pow_zero, div_one]
    intro B' hB'; rw [hB']
  | succ k ih =>
    intro B' hB'
    simp only [subdivide_iter_succ, Finset.mem_biUnion] at hB'
    obtain ⟨B'', hB''_mem, hB'_sub⟩ := hB'
    -- B'' входит в subdivide_iter B k, а B' входит в B''.subdivide
    have hB''_diam := ih B'' hB''_mem
    -- Нужна непустота B'' для применения subdivide_diameter_bound
    have hB''_nonempty : B''.toSet.Nonempty := subdivide_iter_nonempty B hB k B'' hB''_mem
    have hB'_diam := subdivide_diameter_bound B'' hB''_nonempty B' hB'_sub
    calc B'.diameter
        ≤ B''.diameter / Real.sqrt 2 := hB'_diam
      _ ≤ (B.diameter / (Real.sqrt 2) ^ k) / Real.sqrt 2 := by
          apply div_le_div_of_nonneg_right hB''_diam (Real.sqrt_nonneg 2)
      _ = B.diameter / ((Real.sqrt 2) ^ k * Real.sqrt 2) := by rw [div_div]
      _ = B.diameter / (Real.sqrt 2 * (Real.sqrt 2) ^ k) := by ring_nf
      _ = B.diameter / (Real.sqrt 2) ^ (k + 1) := by rw [pow_succ']

/-- Количество разбиений, необходимых, чтобы диаметр стал меньше порога r.
    Каждое разбиение уменьшает диаметр в √2 раз, поэтому после k итераций:
    diameter ≤ original\_diameter / (√2)^k
    Нужно (√2)^k > diameter/r, то есть k > log(diameter/r) / log(√2) = 2·log₂(diameter/r). -/
noncomputable def iter_count {d : ℕ} (B : Box d) (r : ℝ) : ℕ :=
  if B.diameter ≤ 0 then 0
  else if B.diameter < r then 0
  else Nat.ceil (2 * Real.log (B.diameter / r) / Real.log 2) + 1

/-- После iter\_count разбиений у всех подпрямоугольников диаметр < r -/
lemma diameter_lt_of_iter_count {d : ℕ} (B : Box d) (hB : B.toSet.Nonempty) (r : ℝ) (hr : 0 < r) :
    ∀ B' ∈ subdivide_iter B (B.iter_count r), B'.diameter < r := by
  intro B' hB'
  by_cases h_diam_le : B.diameter ≤ 0
  · -- Вырожденный случай : diameter ≤ 0 означает, что у всех подпрямоугольников диаметр тоже ≤ 0 < r
    simp only [iter_count, h_diam_le, ↓reduceIte, subdivide_iter] at hB'
    simp only [Finset.mem_singleton] at hB'
    rw [hB']
    calc B.diameter ≤ 0 := h_diam_le
      _ < r := hr
  · push_neg at h_diam_le
    by_cases h_small : B.diameter < r
    · -- Уже достаточно мал, разбиения не нужны
      simp only [iter_count, not_le.mpr h_diam_le, h_small, ↓reduceIte, subdivide_iter] at hB'
      simp only [Finset.mem_singleton] at hB'
      rw [hB']; exact h_small
    · -- Разбиения нужны : B.diameter ≥ r, поэтому используем логарифмическую формулу
      push_neg at h_small
      have h_iter_bound := diameter_subdivide_iter B hB (B.iter_count r) B' hB'
      -- Покажем, что B.diameter / (√2)^k < r при k = iter_count
      -- Ключевой факт: iter_count = ⌈2 * log(B.diameter / r) / log 2⌉ + 1
      -- Значит k > 2 * log₂(B.diameter / r), а следовательно (√2)^k > B.diameter / r
      calc B'.diameter
          ≤ B.diameter / (Real.sqrt 2) ^ (B.iter_count r) := h_iter_bound
        _ < r := by
            -- Нужно: B.diameter / (√2)^k < r, то есть (√2)^k > B.diameter / r
            have h_k_def : B.iter_count r = Nat.ceil (2 * Real.log (B.diameter / r) / Real.log 2) + 1 := by
              simp only [iter_count, not_le.mpr h_diam_le, not_lt.mpr h_small, ↓reduceIte]
            -- Доказываем (√2)^k > B.diameter / r, используя логарифмическое определение
            have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
            have hsqrt2_pow_pos : 0 < (Real.sqrt 2) ^ (B.iter_count r) := pow_pos hsqrt2_pos _
            have hDr_pos : 0 < B.diameter / r := div_pos h_diam_le hr
            have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
            rw [div_lt_iff₀ hsqrt2_pow_pos]
            -- Цель: B.diameter < r * (√2)^k
            set L := 2 * Real.log (B.diameter / r) / Real.log 2 with hL_def
            -- k > L, поскольку k = ⌈L⌉ + 1 > L
            have hk_gt : ((B.iter_count r) : ℝ) > L := by
              have h_ceil_ge : (Nat.ceil L : ℝ) ≥ L := Nat.le_ceil L
              have hk_eq : ((B.iter_count r) : ℝ) = (Nat.ceil L : ℝ) + 1 := by
                simp only [h_k_def]; norm_cast
              linarith
            -- k/2 > log₂(B.diameter/r)
            have hL_eq : L = 2 * (Real.log (B.diameter / r) / Real.log 2) := by ring
            have hk_half_gt : ((B.iter_count r) : ℝ) / 2 > Real.log (B.diameter / r) / Real.log 2 := by
              have : ((B.iter_count r) : ℝ) > 2 * (Real.log (B.diameter / r) / Real.log 2) := by
                rw [← hL_eq]; exact hk_gt
              linarith
            -- (√2)^k = 2^(k/2)
            have hsqrt_pow : (Real.sqrt 2) ^ (B.iter_count r) =
                             (2 : ℝ) ^ (((B.iter_count r) : ℝ) / 2) := by
              have h1 : Real.sqrt 2 = (2 : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow 2
              conv_lhs => rw [h1]
              rw [← Real.rpow_natCast ((2 : ℝ) ^ ((1 : ℝ)/2)) (B.iter_count r)]
              rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
              congr 1; ring
            -- 2^(k/2) > B.diameter/r
            have h2pow_gt : (2 : ℝ) ^ (((B.iter_count r) : ℝ) / 2) > B.diameter / r := by
              rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
              have hsimp : Real.log (B.diameter / r) / Real.log 2 * Real.log 2 =
                          Real.log (B.diameter / r) := by field_simp
              have h_exp_ineq : Real.log 2 * (((B.iter_count r) : ℝ) / 2) >
                               Real.log (B.diameter / r) := by
                calc Real.log 2 * (((B.iter_count r) : ℝ) / 2)
                    = ((B.iter_count r) : ℝ) / 2 * Real.log 2 := by ring
                  _ > Real.log (B.diameter / r) / Real.log 2 * Real.log 2 := by
                       apply mul_lt_mul_of_pos_right hk_half_gt hlog2_pos
                  _ = Real.log (B.diameter / r) := hsimp
              calc Real.exp (Real.log 2 * (((B.iter_count r) : ℝ) / 2))
                  > Real.exp (Real.log (B.diameter / r)) := Real.exp_strictMono h_exp_ineq
                _ = B.diameter / r := Real.exp_log hDr_pos
            -- Объединяем
            rw [hsqrt_pow]
            calc B.diameter = (B.diameter / r) * r := by field_simp
              _ < (2 : ℝ) ^ (((B.iter_count r) : ℝ) / 2) * r := by
                  apply mul_lt_mul_of_pos_right h2pow_gt hr
              _ = r * (2 : ℝ) ^ (((B.iter_count r) : ℝ) / 2) := by ring

/-- Подпрямоугольники разбиения покрывают исходный прямоугольник (box): любая точка B.toSet
    содержится в каком-то прямоугольнике из subdivide\_iter B k. -/
lemma subdivide_iter_covers {d : ℕ} (B : Box d) (k : ℕ) (x : EuclideanSpace' d)
    (hx : x ∈ B.toSet) : ∃ B' ∈ subdivide_iter B k, x ∈ B'.toSet := by
  induction k with
  | zero =>
    refine ⟨B, ?_, hx⟩
    simp only [subdivide_iter_zero, Finset.mem_singleton]
  | succ k ih =>
    obtain ⟨B'', hB''_mem, hx_B''⟩ := ih
    -- B'' разбит, x лежит в B''.toSet, нужно найти B' ∈ B''.subdivide, содержащее x
    -- Определяем функцию выбора: c i = true тогда и только тогда, когда x i в правой половине
    let c : Fin d → Bool := fun i => decide (x i ≥ (B''.side i).midpoint)
    -- Подпрямоугольник для этого выбора содержит x
    let B' : Box d := {
      side := fun i => if c i then (B''.side i).bisect.snd else (B''.side i).bisect.fst
    }
    refine ⟨B', ?_, ?_⟩
    · -- B' ∈ subdivide_iter B (k+1)
      simp only [subdivide_iter_succ, Finset.mem_biUnion]
      exact ⟨B'', hB''_mem, by simp only [subdivide, Finset.mem_image, Finset.mem_univ, true_and]; exact ⟨c, rfl⟩⟩
    · -- x ∈ B'.toSet : для каждого i точка x i лежит в соответствующей половине
      intro i
      have hx_i : x i ∈ (B''.side i).toSet := by
        have := hx_B''
        simp only [toSet] at this
        exact this i
      simp only [B']
      by_cases hm : x i ≥ (B''.side i).midpoint
      · have hc : c i = true := decide_eq_true hm
        simp only [hc, ite_true]
        exact (BoundedInterval.mem_bisect_snd_iff (B''.side i) (x i) hx_i).mpr hm
      · push_neg at hm
        have hc : c i = false := decide_eq_false (not_le.mpr hm)
        simp only [hc]
        exact (BoundedInterval.mem_bisect_fst_iff (B''.side i) (x i) hx_i).mpr (le_of_lt hm)

/-- Объём прямоугольника (box) неотрицателен (произведение неотрицательных длин интервалов). -/
lemma volume_nonneg {d : ℕ} (B : Box d) : 0 ≤ B.volume := by
  unfold volume
  apply Finset.prod_nonneg
  intro i _
  unfold BoundedInterval.length
  exact le_max_right _ _

/-- Замкнутые прямоугольники (box) (все стороны — {name}`BoundedInterval.Icc`) в евклидовом
    пространстве являются компактными множествами. -/
lemma isCompact {d : ℕ} (B : Box d) (h_closed : ∀ i, ∃ a b, B.side i = BoundedInterval.Icc a b) :
    IsCompact B.toSet := by
  -- Используем теорему Тихонова: произведение компактных множеств компактно
  rw [Box.toSet_eq_ofLp_preimage]
  apply (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isClosedEmbedding.isCompact_preimage
  apply isCompact_univ_pi
  intro i
  obtain ⟨a, b, hi⟩ := h_closed i
  rw [hi]
  exact isCompact_Icc

end Box

namespace Lebesgue_outer_measure

/-- Любое покрытие, индексированное ℕ, даёт верхнюю оценку внешней меры.
    Следует непосредственно из определения через инфимум. -/
lemma le_of_nat_cover {d : ℕ} (hd : 0 < d) (E : Set (EuclideanSpace' d))
    (S : ℕ → Box d) (hcover : E ⊆ ⋃ n, (S n).toSet) :
    Lebesgue_outer_measure E ≤ ∑' n, (S n).volume.toEReal := by
  rw [Lebesgue_outer_measure_eq_nat_indexed hd]
  apply csInf_le
  · -- Показываем, что множество ограничено снизу нулём
    use 0
    intro v hv
    obtain ⟨S', _, rfl⟩ := hv
    apply tsum_nonneg
    intro n
    exact EReal.coe_nonneg.mpr (Box.volume_nonneg _)
  · -- S входит в множество покрытий
    exact ⟨S, hcover, rfl⟩

/-- Верхняя оценка через покрытие, индексированное finset'ами: если множество покрыто
    {lean}`⋃ n, ⋃ B ∈ I n, B.toSet`, где каждое {given -show}`n` {lean}`I n` — конечное множество
    прямоугольников (box), то внешняя мера ограничена суммой объёмов.

    Стратегия доказательства:
    1. Сигма-тип {lean}`(n : ℕ) × ↑(I n)` счётен (а значит, {name}`Encodable`)
    2. Используем экземпляр {name}`Encodable`, чтобы определить {lit}`S` типа {lean}`ℕ → Box d`
       через декодирование
    3. Дополняем прямоугольником нулевого объёма для некорректных декодирований
    4. Применяем {name}`Lebesgue_outer_measure.le_of_nat_cover` и оцениваем перечисленную сумму -/
lemma le_of_finset_cover {d : ℕ} (hd : 0 < d) (E : Set (EuclideanSpace' d))
    (I : ℕ → Finset (Box d)) (hcover : E ⊆ ⋃ n, ⋃ B ∈ I n, B.toSet) : 
    Lebesgue_outer_measure E ≤ ∑' n, (∑ B ∈ I n, B.volume).toEReal := by
  -- Определяем сигма-тип для перечисления
  let SigmaType := (n : ℕ) × (I n : Set (Box d))
  -- SigmaType счётен (ℕ × конечное = счётное)
  haveI : Countable SigmaType := instCountableSigma
  -- Получаем экземпляр Encodable из Countable
  haveI : Encodable SigmaType := Encodable.ofCountable SigmaType

  -- Строим прямоугольник (box) нулевого объёма для дополнения (существует при d > 0)
  have ⟨B₀, hB₀⟩ : ∃ B : Box d, B.volume = 0 := by
    use ⟨fun _ => BoundedInterval.Ioc 0 0⟩
    simp only [Box.volume, BoundedInterval.length]
    -- Интервал [0, 0] имеет длину max(0-0, 0) = 0
    -- Произведение нулей по Fin d (при d > 0) равно 0
    have h_fin_nonempty : (Finset.univ : Finset (Fin d)).Nonempty := by
      use ⟨0, hd⟩
      exact Finset.mem_univ _
    obtain ⟨i, hi⟩ := h_fin_nonempty
    apply Finset.prod_eq_zero hi
    simp [sub_self]

  -- Определяем перечисление через decode₂ (гарантирующее encode ∘ decode₂ = id на значениях Some)
  let S : ℕ → Box d := fun m =>
    match Encodable.decode₂ SigmaType m with
    | some p => p.2.val
    | none => B₀

  -- S покрывает E: каждая точка E лежит в каком-то прямоугольнике из какого-то I n
  -- Ключевой факт: decode₂ (encode p) = some p, поэтому S (encode p) = p.2.val
  have hS_cover : E ⊆ ⋃ m, (S m).toSet := by
    intro x hx
    -- x лежит в E ⊆ ⋃ n, ⋃ B ∈ I n, B.toSet
    -- Значит x ∈ B.toSet для некоторого B ∈ I n при некотором n
    have hx' := hcover hx
    -- Извлекаем структуру вложенного объединения
    rw [Set.mem_iUnion] at hx'
    obtain ⟨n, hx_n⟩ := hx'
    rw [Set.mem_iUnion] at hx_n
    obtain ⟨B, hx_B⟩ := hx_n
    rw [Set.mem_iUnion] at hx_B
    obtain ⟨hB_mem, hx_in_B⟩ := hx_B
    -- Пара (n, ⟨B, hB_mem⟩) входит в SigmaType
    let p : SigmaType := ⟨n, ⟨B, hB_mem⟩⟩
    rw [Set.mem_iUnion]
    use Encodable.encode p
    -- S (encode p) = p.2.val = B (используя decode₂_encode)
    show x ∈ (S (Encodable.encode p)).toSet
    simp only [Encodable.decode₂_encode, S]
    exact hx_in_B

  -- Применяем le_of_nat_cover
  have h_le := le_of_nat_cover hd E S hS_cover

  -- Теперь оцениваем ∑' m, (S m).volume.toEReal ≤ ∑' n, (∑ B ∈ I n, B.volume).toEReal
  -- Используя decode₂, каждый прямоугольник B ∈ I n встречается в левой части ровно один раз
  -- (при encode (n, B)), а некорректные декодирования дают вклад B₀.volume = 0

  calc Lebesgue_outer_measure E
      ≤ ∑' m, (S m).volume.toEReal := h_le
    _ ≤ ∑' n, (∑ B ∈ I n, B.volume).toEReal := by
        -- Левую часть можно переписать через ENNReal.tsum_decode₂_eq
        -- LHS = ∑' m, (match decode₂ m with | some p => p.2.val.volume | none => 0).toEReal
        --     = ∑' p : SigmaType, p.2.val.volume.toEReal  (по tsum_decode₂_eq для объёма)
        --     = ∑' (n, B), B.val.volume.toEReal
        -- RHS = ∑' n, (∑ B ∈ I n, B.volume).toEReal

        -- Сначала покажем равенство сумм, переходя через сигма-тип
        have h_eq : ∑' m, (S m).volume.toEReal =
                    ∑' (p : SigmaType), p.2.val.volume.toEReal := by
          -- Используем Function.Injective.tsum_eq, поскольку encode инъективно
          -- Определяем g : ℕ → EReal как функцию объёма на декодированных значениях
          let g : ℕ → EReal := fun m =>
            match Encodable.decode₂ SigmaType m with
            | some p => p.2.val.volume.toEReal
            | none => 0
          -- g m = (S m).volume.toEReal, поскольку:
          -- - когда decode₂ m = some p: g m = p.2.val.volume.toEReal = (S m).volume.toEReal
          -- - когда decode₂ m = none: g m = 0, S m = B₀, B₀.volume = 0
          have h_g_eq : ∀ m, g m = (S m).volume.toEReal := by
            intro m
            simp only [g, S]
            cases h : Encodable.decode₂ SigmaType m with
            | none => simp [hB₀]
            | some p => rfl
          -- Носитель g содержится в области значений encode
          have h_support : Function.support g ⊆ Set.range (Encodable.encode (α := SigmaType)) := by
            intro m hm
            simp only [Function.mem_support, ne_eq, g] at hm
            cases h : Encodable.decode₂ SigmaType m with
            | none => simp [h] at hm
            | some p =>
              rw [Set.mem_range]
              use p
              exact Encodable.decode₂_eq_some.mp h
          have h_inj := Encodable.encode_injective (α := SigmaType)
          have h_val_eq : ∀ p : SigmaType, g (Encodable.encode p) = p.2.val.volume.toEReal := by
            intro p
            simp only [g, Encodable.decode₂_encode]
          calc ∑' m, (S m).volume.toEReal
              = ∑' m, g m := by simp only [h_g_eq]
            _ = ∑' (p : SigmaType), g (Encodable.encode p) := (h_inj.tsum_eq h_support).symm
            _ = ∑' (p : SigmaType), p.2.val.volume.toEReal := by simp only [h_val_eq]

        -- Сумма по сигма-типу равна вложенной сумме по finset'ам
        have h_sigma_eq_nested : ∑' (p : SigmaType), p.2.val.volume.toEReal =
                                  ∑' n, (∑ B ∈ I n, B.volume).toEReal := by
          -- Ключевой факт: SigmaType = (n : ℕ) × ↑(I n), где каждый слой ↑(I n) конечен

          -- Сначала покажем, что внутренняя tsum равна сумме по finset
          have h_inner : ∀ n, ∑' (B : (I n : Set (Box d))), B.val.volume.toEReal =
                              (∑ B ∈ I n, B.volume).toEReal := by
            intro n
            rw [tsum_fintype]
            have h_nonneg : ∀ B ∈ I n, 0 ≤ B.volume := fun B _ => Box.volume_nonneg B
            have h_sum_real : ∑ B : ↥(I n), (↑B : Box d).volume = ∑ B ∈ I n, B.volume :=
              Finset.sum_coe_sort (I n) (fun B => B.volume)
            calc ∑ B : ↥(I n), (↑B : Box d).volume.toEReal
                = (∑ B : ↥(I n), (↑B : Box d).volume).toEReal := by
                    symm
                    apply EReal.coe_finset_sum
                    intro ⟨B, hB⟩ _
                    exact Box.volume_nonneg B
              _ = (∑ B ∈ I n, B.volume).toEReal := by rw [h_sum_real]

          -- Раскладываем tsum по сигма-типу в виде вложенной tsum
          have h_sigma_decomp : ∑' (p : SigmaType), p.2.val.volume.toEReal =
                                 ∑' n, ∑' (B : (I n : Set (Box d))), B.val.volume.toEReal := by
            -- Поскольку слои конечны, каждая внутренняя сумма конечна
            -- Для неотрицательного EReal с конечными слоями tsum_sigma работает
            haveI : ∀ n, Fintype (I n : Set (Box d)) := fun n => Finset.fintypeCoeSort (I n)

            -- Применяем tsum_fintype к внутренней сумме, чтобы сделать её конечной, а затем
            -- используем стандартное разложение
            have h_eq_finite : ∀ n, ∑' (B : (I n : Set (Box d))), B.val.volume.toEReal =
                                     ∑ B : (I n : Set (Box d)), B.val.volume.toEReal := by
              intro n
              exact tsum_fintype _
            simp_rw [h_eq_finite]

            -- Переходим в ENNReal, чтобы использовать безусловную tsum_sigma
            -- Определяем версию слагаемого в ENNReal
            let f_enn : SigmaType → ENNReal := fun p => ENNReal.ofReal p.2.val.volume

            -- Разложение выполняется в ENNReal
            have h_enn_decomp : ∑' p, f_enn p = ∑' n, ∑' (B : (I n : Set (Box d))), f_enn ⟨n, B⟩ :=
              ENNReal.tsum_sigma' _

            -- Определяем приведение к EReal
            let φ : ENNReal →+ EReal := {
              toFun := fun x => (↑x : EReal)
              map_zero' := rfl
              map_add' := EReal.coe_ennreal_add
            }
            have h_cont : Continuous φ := continuous_coe_ennreal_ereal

            -- Показываем, что левая часть равна приведённой сумме в ENNReal
            have h_lhs : ∑' (p : SigmaType), p.snd.val.volume.toEReal = ↑(∑' (p : SigmaType), f_enn p) := by
              have h_eq : ∀ p : SigmaType, p.snd.val.volume.toEReal = φ (f_enn p) := by
                intro p
                simp only [f_enn, φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
                rw [EReal.coe_ennreal_ofReal, max_eq_left (Box.volume_nonneg _)]
              simp_rw [h_eq]
              exact (Summable.map_tsum ENNReal.summable φ h_cont).symm

            -- Показываем, что правая часть равна приведённой сумме в ENNReal (используя sum
            -- вместо tsum для внутренней суммы)
            have h_rhs : ∑' n, ∑ (B : (I n : Set (Box d))), B.val.volume.toEReal =
                         ↑(∑' n, ∑' (B : (I n : Set (Box d))), f_enn ⟨n, B⟩) := by
              -- Преобразуем внутреннюю tsum в sum в ENNReal
              have h_inner_enn : ∀ n, ∑' (B : (I n : Set (Box d))), f_enn ⟨n, B⟩ =
                                      ∑ B, f_enn ⟨n, B⟩ := fun n => tsum_fintype _
              simp_rw [h_inner_enn]

              -- Проносим приведение через внешнюю сумму
              have h_outer : ∑' n, ∑ (B : (I n : Set (Box d))), B.val.volume.toEReal =
                             ↑(∑' n, ∑ (B : (I n : Set (Box d))), f_enn ⟨n, B⟩) := by
                have h_eq_term : ∀ n, ∑ (B : (I n : Set (Box d))), B.val.volume.toEReal = φ (∑ (B : (I n : Set (Box d))), f_enn ⟨n, B⟩) := by
                  intro n
                  rw [map_sum]
                  apply Finset.sum_congr rfl
                  intro (B : (I n : Set (Box d))) _
                  simp only [f_enn, φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
                  rw [EReal.coe_ennreal_ofReal, max_eq_left (Box.volume_nonneg _)]
                simp_rw [h_eq_term]
                exact (Summable.map_tsum ENNReal.summable φ h_cont).symm

              exact h_outer

            rw [h_lhs, h_rhs, h_enn_decomp]

          rw [h_sigma_decomp]
          congr 1
          ext n
          exact h_inner n

        rw [h_eq, h_sigma_eq_nested]


/-- Для любого множества конечной внешней меры можно найти покрытие, чей объём отличается от
    внешней меры не более чем на ε. Это следует из определения внешней меры как инфимума. -/
lemma exists_cover_close {d : ℕ} (hd : 0 < d)
    (E : Set (EuclideanSpace' d)) (ε : ℝ) (hε : 0 < ε)
    (h_finite : Lebesgue_outer_measure E ≠ ⊤) :
    ∃ (S : ℕ → Box d), E ⊆ ⋃ n, (S n).toSet ∧
      ∑' n, (S n).volume.toEReal ≤ Lebesgue_outer_measure E + ε := by
  -- Используем характеризацию внешней меры через покрытия, индексированные ℕ
  rw [Lebesgue_outer_measure_eq_nat_indexed hd] at h_finite ⊢

  -- Ключевой факт: inf + ε не является нижней гранью (поскольку ε > 0)
  -- Следовательно, существует покрытие с объёмом < inf + ε, откуда и ≤ inf + ε

  have h_not_lb : ¬ IsGLB (((fun S : ℕ → Box d ↦ ∑' n, (S n).volume.toEReal)) ''
      { S | E ⊆ ⋃ n, (S n).toSet }) (sInf (((fun S : ℕ → Box d ↦ ∑' n, (S n).volume.toEReal)) ''
      { S | E ⊆ ⋃ n, (S n).toSet }) + (ε : EReal)) := by
    intro h_glb
    -- Если бы inf + ε была точной нижней гранью, то inf ≤ inf + ε ≤ inf (поскольку inf тоже
    -- нижняя грань), а это означало бы ε ≤ 0 — противоречие
    let img_set := ((fun S : ℕ → Box d ↦ ∑' n, (S n).volume.toEReal)) '' { S | E ⊆ ⋃ n, (S n).toSet }
    let inf_val := sInf img_set
    -- sInf img_set — точная нижняя грань img_set
    have h_inf_glb : IsGLB img_set inf_val := isGLB_sInf img_set
    -- Из h_glb следует, что inf_val + ε также является точной нижней гранью
    -- Но точная нижняя грань единственна, так что обе величины должны совпадать
    -- Однако inf_val < inf_val + ε (поскольку ε > 0, inf_val ≠ ⊥ и inf_val ≠ ⊤)
    -- inf_val — инфимум объёмов прямоугольников (сумм объёмов), которые неотрицательны,
    -- поэтому inf_val ≠ ⊥
    have h_ne_bot : inf_val ≠ ⊥ := by
      intro h_eq
      -- Если inf_val = ⊥, то ⊥ — точная нижняя грань img_set
      have h_glb_bot : IsGLB img_set ⊥ := by rwa [← h_eq]
      -- Но 0 — нижняя грань img_set (поскольку все объёмы прямоугольников неотрицательны)
      have h_zero_lb : (0 : EReal) ∈ lowerBounds img_set := by
        intro v hv
        obtain ⟨S, _, rfl⟩ := hv
        -- v = ∑' n, (S n).volume.toEReal, и каждое слагаемое ≥ 0
        apply tsum_nonneg
        intro n
        exact EReal.coe_nonneg.mpr (by
          unfold Box.volume
          apply Finset.prod_nonneg
          intro i _
          unfold BoundedInterval.length
          exact le_max_right _ _)
      -- Поскольку ⊥ — точная нижняя грань, имеем 0 ≤ ⊥ (так как 0 — нижняя грань)
      have : (0 : EReal) ≤ ⊥ := h_glb_bot.2 h_zero_lb
      -- Но в EReal 0 > ⊥
      exact not_le.mpr EReal.bot_lt_zero this
    have h_lt : inf_val < inf_val + (ε : EReal) := EReal.lt_add_of_pos_coe hε h_ne_bot h_finite
    -- Точная нижняя грань единственна: если x и y — обе точные нижние грани одного множества,
    -- то x = y
    have h_eq : inf_val = inf_val + (ε : EReal) := h_inf_glb.unique h_glb
    -- Но inf_val < inf_val + ε, что противоречит h_eq
    rw [← h_eq] at h_lt
    simp at h_lt

  -- Поскольку sInf — инфимум, а sInf + ε не является нижней гранью,
  -- должно существовать покрытие с объёмом ≤ sInf + ε
  let img_set := ((fun S : ℕ → Box d ↦ ∑' n, (S n).volume.toEReal)) '' { S | E ⊆ ⋃ n, (S n).toSet }
  let inf_val := sInf img_set
  -- Из h_not_lb следует, что inf_val + ε не является точной нижней гранью, а значит, не является
  -- и нижней гранью (иначе, будучи нижней гранью ≥ inf_val, она должна была бы совпасть с inf_val)
  -- Значит, существует элемент img_set, меньший inf_val + ε
  have h_exists_lt : ∃ v ∈ img_set, v < inf_val + (ε : EReal) := by
    -- Если бы такого элемента не было, то inf_val + ε была бы нижней гранью
    by_contra h_not_exists
    push_neg at h_not_exists
    -- h_not_exists говорит: ∀ v ∈ img_set, inf_val + ε ≤ v
    -- Это означает, что inf_val + ε — нижняя грань
    have h_is_lb : inf_val + (ε : EReal) ∈ lowerBounds img_set := by
      intro v hv
      exact h_not_exists v hv
    -- А поскольку inf_val — точная нижняя грань (наибольшая нижняя грань), имеем inf_val + ε ≤ inf_val
    have h_inf_glb : IsGLB img_set inf_val := isGLB_sInf img_set
    have h_le : inf_val + (ε : EReal) ≤ inf_val := h_inf_glb.2 h_is_lb
    -- Но также inf_val < inf_val + ε (поскольку ε > 0, inf_val ≠ ⊥ и inf_val ≠ ⊤)
    -- inf_val — инфимум объёмов прямоугольников, которые неотрицательны, поэтому inf_val ≠ ⊥
    have h_ne_bot : inf_val ≠ ⊥ := by
      intro h_eq
      have h_glb_bot : IsGLB img_set ⊥ := by rwa [← h_eq]
      have h_zero_lb : (0 : EReal) ∈ lowerBounds img_set := by
        intro v hv
        obtain ⟨S, _, rfl⟩ := hv
        apply tsum_nonneg
        intro n
        exact EReal.coe_nonneg.mpr (by
          unfold Box.volume
          apply Finset.prod_nonneg
          intro i _
          unfold BoundedInterval.length
          exact le_max_right _ _)
      have : (0 : EReal) ≤ ⊥ := h_glb_bot.2 h_zero_lb
      exact not_le.mpr EReal.bot_lt_zero this
    have h_lt : inf_val < inf_val + (ε : EReal) := EReal.lt_add_of_pos_coe hε h_ne_bot h_finite
    -- Противоречие: h_le говорит inf_val + ε ≤ inf_val, а h_lt говорит inf_val < inf_val + ε
    have : inf_val < inf_val := calc inf_val
        < inf_val + ↑ε := h_lt
      _ ≤ inf_val := h_le
    exact lt_irrefl _ this
  -- Извлекаем свидетеля из множества образов
  obtain ⟨v, ⟨S, hS_cover, rfl⟩, hv_lt⟩ := h_exists_lt
  -- S — искомое покрытие
  exact ⟨S, hS_cover, le_of_lt hv_lt⟩


end Lebesgue_outer_measure

-- ========================================================================
-- Конец вспомогательных лемм для леммы 1.2.5
-- ========================================================================

/-- Лемма 1.2.5 (Конечная аддитивность для разделённых множеств).
    Если E и F разделены (dist(E,F) > 0), то m\*(E ∪ F) = m\*(E) + m\*(F).

    Стратегия доказательства (из учебника):
    1. Направление ≤: используем субаддитивность
    2. Направление ≥: показываем m\*(E ∪ F) ≥ m\*(E) + m\*(F)
       - Если m\*(E ∪ F) = ⊤, тривиально
       - Если m\*(E ∪ F) < ⊤:
         \* Берём ε-близкое покрытие E ∪ F
         \* Измельчаем покрытие так, чтобы у всех прямоугольников диаметр был < dist(E,F)
         \* Разбиваем прямоугольники на пересекающие E и пересекающие F (не пересекаются
           благодаря геометрической разделённости)
         \* Суммируем объёмы раздельно: m\*(E) + m\*(F) ≤ сумма измельчённого покрытия
           ≤ m\*(E ∪ F) + ε
         \* Переходим к пределу ε → 0
-/
theorem Lebesgue_outer_measure.union_of_separated {d : ℕ} (hd : 0 < d) {E F : Set (EuclideanSpace' d)}
    (hsep : set_dist E F > 0) : 
    Lebesgue_outer_measure (E ∪ F) = Lebesgue_outer_measure E + Lebesgue_outer_measure F := by

  -- Направление 1: m*(E ∪ F) ≤ m*(E) + m*(F) [субаддитивность]
  have h_le : Lebesgue_outer_measure (E ∪ F) ≤ Lebesgue_outer_measure E + Lebesgue_outer_measure F := by
    -- Применяем finite_union_le для двух множеств
    let E' : Fin 2 → Set (EuclideanSpace' d) := ![E, F]
    have h_union : E ∪ F = ⋃ i, E' i := by
      simp only [E']
      ext x
      simp only [Set.mem_union, Set.mem_iUnion]
      constructor
      · intro hx
        cases hx with
        | inl hE => exact ⟨0, hE⟩
        | inr hF => exact ⟨1, hF⟩
      · intro ⟨i, hi⟩
        fin_cases i
        · left; exact hi
        · right; exact hi
    have h_sum : ∑ i : Fin 2, Lebesgue_outer_measure (E' i) =
        Lebesgue_outer_measure E + Lebesgue_outer_measure F := by
      simp only [Fin.sum_univ_two, E', Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [h_union, ← h_sum]
    exact finite_union_le E'

  -- Направление 2: m*(E ∪ F) ≥ m*(E) + m*(F) [ОСНОВНАЯ РАБОТА]
  have h_ge : Lebesgue_outer_measure E + Lebesgue_outer_measure F ≤ Lebesgue_outer_measure (E ∪ F) := by
    -- Случай 1: если m*(E ∪ F) = ⊤, неравенство выполняется тривиально
    by_cases h_inf : Lebesgue_outer_measure (E ∪ F) = ⊤
    · simp only [h_inf]; apply le_top

    -- Случай 2: m*(E ∪ F) < ⊤
    · -- Для любого ε > 0 покажем m*(E) + m*(F) ≤ m*(E ∪ F) + ε
      -- Переход к пределу ε → 0 даёт результат

      -- Доказательство: покажем, что для всех ε > 0 верно m*(E) + m*(F) ≤ m*(E ∪ F) + ε
      -- Отсюда следует m*(E) + m*(F) ≤ m*(E ∪ F)
      have h_eps : ∀ (ε : ℝ), 0 < ε → Lebesgue_outer_measure E + Lebesgue_outer_measure F ≤
          Lebesgue_outer_measure (E ∪ F) + (ε : EReal) := by
        intro ε hε_real

        -- Берём ε-близкое покрытие E ∪ F
        have ⟨S, hS_cover, hS_vol⟩ := exists_cover_close hd (E ∪ F) ε hε_real h_inf

        -- Выбираем r с 0 < r < dist(E,F)
        have hr : ∃ r, 0 < r ∧ r < set_dist E F := by
          use set_dist E F / 2
          constructor
          · linarith
          · linarith
        obtain ⟨r, hr_pos, hr_lt⟩ := hr

        -- Для каждого прямоугольника S(n) разбиваем его k(n) = (S n).iter_count r раз
        let k : ℕ → ℕ := fun n => (S n).iter_count r

        -- У всех измельчённых прямоугольников диаметр < r < set_dist E F
        have h_diam : ∀ n, ∀ B' ∈ Box.subdivide_iter (S n) (k n), B'.diameter < r := by
          intro n B' hB'
          by_cases hnonempty : (S n).toSet.Nonempty
          · exact Box.diameter_lt_of_iter_count (S n) hnonempty r hr_pos B' hB'
          · -- Случай пустого прямоугольника : iter_count = 0, когда diameter ≤ 0,
            -- поэтому subdivide_iter = {S n}
            have h_empty : (S n).toSet = ∅ := Set.not_nonempty_iff_eq_empty.mp hnonempty
            have h_diam_zero : (S n).diameter = 0 := Box.diameter_of_empty (S n) h_empty
            -- iter_count = 0, поскольку diameter = 0 ≤ 0
            have h_k_zero : k n = 0 := by
              simp only [k, Box.iter_count, h_diam_zero, le_refl, ↓reduceIte]
            -- Значит subdivide_iter (S n) 0 = {S n}, то есть B' = S n
            rw [h_k_zero, Box.subdivide_iter_zero, Finset.mem_singleton] at hB'
            rw [hB', h_diam_zero]
            exact hr_pos

        -- Разбиение: для каждого n делим измельчения на пересекающие E и пересекающие F
        -- Используем классическую разрешимость для предиката фильтра
        haveI : ∀ (B' : Box d), Decidable ((B'.toSet ∩ E).Nonempty) := fun _ => Classical.dec _
        haveI : ∀ (B' : Box d), Decidable ((B'.toSet ∩ F).Nonempty) := fun _ => Classical.dec _
        let I_E_n : ℕ → Finset (Box d) := fun n =>
          (Box.subdivide_iter (S n) (k n)).filter (fun B' => (B'.toSet ∩ E).Nonempty)
        let I_F_n : ℕ → Finset (Box d) := fun n =>
          (Box.subdivide_iter (S n) (k n)).filter (fun B' => (B'.toSet ∩ F).Nonempty)

        -- Непересекаемость на каждом уровне n: ни один прямоугольник не пересекает и E, и F
        have h_disj_n : ∀ n, Disjoint (I_E_n n) (I_F_n n) := by
          intro n
          rw [Finset.disjoint_filter]
          intro B' hB'_sub hB'_E hB'_F
          -- B' пересекает и E, и F, но диаметр < r < set_dist E F: противоречие
          have h_small : B'.diameter < set_dist E F := by
            calc B'.diameter < r := h_diam n B' hB'_sub
            _ < set_dist E F := hr_lt
          exact Box.not_intersects_both_of_diameter_lt B' E F h_small ⟨hB'_E, hB'_F⟩

        -- E покрыто измельчениями, пересекающими E
        have hE_cover : E ⊆ ⋃ n, ⋃ B' ∈ I_E_n n, B'.toSet := by
          intro x hxE
          have hx_union : x ∈ E ∪ F := Set.mem_union_left F hxE
          obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hS_cover hx_union)
          obtain ⟨B', hB'_mem, hx_B'⟩ := Box.subdivide_iter_covers (S n) (k n) x hn
          have hB'_in_IE : B' ∈ I_E_n n := by
            rw [Finset.mem_filter]
            exact ⟨hB'_mem, ⟨x, hx_B', hxE⟩⟩
          simp only [Set.mem_iUnion]
          exact ⟨n, ⟨B', ⟨hB'_in_IE, hx_B'⟩⟩⟩

        -- F покрыто измельчениями, пересекающими F
        have hF_cover : F ⊆ ⋃ n, ⋃ B' ∈ I_F_n n, B'.toSet := by
          intro x hxF
          have hx_union : x ∈ E ∪ F := Set.mem_union_right E hxF
          obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hS_cover hx_union)
          obtain ⟨B', hB'_mem, hx_B'⟩ := Box.subdivide_iter_covers (S n) (k n) x hn
          have hB'_in_IF : B' ∈ I_F_n n := by
            rw [Finset.mem_filter]
            exact ⟨hB'_mem, ⟨x, hx_B', hxF⟩⟩
          simp only [Set.mem_iUnion]
          exact ⟨n, ⟨B', ⟨hB'_in_IF, hx_B'⟩⟩⟩

        -- Оценки объёма: m*(E) ≤ сумма по прямоугольникам, пересекающим E
        have hE_bound : Lebesgue_outer_measure E ≤ ∑' n, (∑ B' ∈ I_E_n n, B'.volume).toEReal :=
          le_of_finset_cover hd E I_E_n hE_cover

        have hF_bound : Lebesgue_outer_measure F ≤ ∑' n, (∑ B' ∈ I_F_n n, B'.volume).toEReal :=
          le_of_finset_cover hd F I_F_n hF_cover

        -- Ключевой факт: разбиение на непересекающиеся части означает
        -- ∑ I_E_n + ∑ I_F_n ≤ ∑ по всем измельчениям
        have h_sum_le : ∀ n, (∑ B' ∈ I_E_n n, B'.volume) + (∑ B' ∈ I_F_n n, B'.volume)
            ≤ ∑ B' ∈ Box.subdivide_iter (S n) (k n), B'.volume := by
          intro n
          -- Шаг 1: ∑ A + ∑ B = ∑ (A ∪ B) для непересекающихся множеств
          rw [← Finset.sum_union (h_disj_n n)]
          -- Шаг 2: A ∪ B ⊆ subdivide_iter, поскольку оба — фильтры этого множества
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · -- Объединение фильтров ⊆ исходному множеству
            intro B' hB'
            rw [Finset.mem_union] at hB'
            cases hB' with
            | inl h => exact Finset.filter_subset _ _ h
            | inr h => exact Finset.filter_subset _ _ h
          · -- Объёмы неотрицательны
            intro B' _ _
            unfold Box.volume
            apply Finset.prod_nonneg
            intro i _
            unfold BoundedInterval.length
            exact le_max_right _ _

        -- Равенство объёмов: сумма по измельчениям = исходный объём
        have h_vol_eq : ∀ n, (S n).toSet.Nonempty →
            (∑ B' ∈ Box.subdivide_iter (S n) (k n), B'.volume) = (S n).volume := by
          intro n hn
          exact Box.volume_subdivide_iter (S n) hn (k n)

        -- Итоговое вычисление: объединяем оценки
        calc Lebesgue_outer_measure E + Lebesgue_outer_measure F
            ≤ (∑' n, (∑ B' ∈ I_E_n n, B'.volume).toEReal) +
              (∑' n, (∑ B' ∈ I_F_n n, B'.volume).toEReal) :=
                add_le_add hE_bound hF_bound
          _ ≤ ∑' n, (S n).volume.toEReal := by
              -- Переходим в ENNReal, где лучше свойства tsum
              -- Ключевой факт: для неотрицательных вещественных чисел
              -- x.toEReal = (x.toNNReal : ENNReal).toEReal
              -- Шаг 1: покажем поточечно (∑ I_E_n) + (∑ I_F_n) ≤ vol(S n)
              have h_pw_le : ∀ n, (∑ B' ∈ I_E_n n, B'.volume) + (∑ B' ∈ I_F_n n, B'.volume) ≤ (S n).volume := by
                intro n
                calc (∑ B' ∈ I_E_n n, B'.volume) + (∑ B' ∈ I_F_n n, B'.volume)
                    ≤ ∑ B' ∈ Box.subdivide_iter (S n) (k n), B'.volume := h_sum_le n
                  _ ≤ (S n).volume := by
                    by_cases hn : (S n).toSet.Nonempty
                    · exact le_of_eq (h_vol_eq n hn)
                    · -- Пустой прямоугольник : объём = 0, а сумма по измельчениям ≤ 0 = объём
                      have hempty : (S n).toSet = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
                      have hvol_zero : (S n).volume = 0 := Box.volume_eq_zero_of_empty (S n) hempty
                      rw [hvol_zero]
                      -- subdivide_iter пустого прямоугольника = {S n} с объёмом 0
                      have hk_zero : k n = 0 := by
                        simp only [k, Box.iter_count]
                        have hdiam : (S n).diameter = 0 := Box.diameter_of_empty (S n) hempty
                        simp only [hdiam, le_refl, ↓reduceIte]
                      rw [hk_zero, Box.subdivide_iter_zero, Finset.sum_singleton, hvol_zero]

              -- Шаг 2: применяем вспомогательную лемму о неравенстве tsum в EReal
              have h_E_nonneg : ∀ n, 0 ≤ ∑ B' ∈ I_E_n n, B'.volume := by
                intro n; apply Finset.sum_nonneg; intro B' _; exact Box.volume_nonneg B'
              have h_F_nonneg : ∀ n, 0 ≤ ∑ B' ∈ I_F_n n, B'.volume := by
                intro n; apply Finset.sum_nonneg; intro B' _; exact Box.volume_nonneg B'

              -- Применяем вспомогательную лемму
              exact EReal.tsum_add_le_of_nonneg_pointwise h_E_nonneg h_F_nonneg h_pw_le
          _ ≤ Lebesgue_outer_measure (E ∪ F) + (ε : EReal) := hS_vol

      -- Из h_eps заключаем, что неравенство выполняется
      exact EReal.le_of_forall_pos_le_add' h_eps

  -- Объединяем оба направления
  exact le_antisymm h_le h_ge

example : set_dist (Ico 0 1).toSet (Icc 1 2).toSet = 0 := by
  apply le_antisymm
  · -- set_dist ≤ 0 : от противного, если set_dist > 0, найдём более близкую пару
    by_contra hne
    simp only [not_le] at hne
    -- Значит set_dist > 0
    have hpos := hne
    -- Берём ε = set_dist / 2
    set ε := set_dist (Ico 0 1).toSet (Icc 1 2).toSet / 2 with hε_def
    have hε_pos : 0 < ε := by linarith
    -- set_dist ≤ dist(0, 1) = 1, поэтому ε ≤ 1/2
    have h_upper : set_dist (Ico 0 1).toSet (Icc 1 2).toSet ≤ 1 := by
      unfold set_dist
      apply csInf_le
      · use 0
        intro r hr
        obtain ⟨⟨x, y⟩, ⟨_, _⟩, rfl⟩ := hr
        exact dist_nonneg
      · refine ⟨(0, 1), ⟨?_, ?_⟩, ?_⟩
        · norm_num
        · norm_num
        · simp [Real.dist_eq]
    have hε_le : ε ≤ 1/2 := by linarith
    -- Точка (1 - ε, 1) имеет расстояние ε < set_dist — противоречие
    have hmem : dist (1 - ε) 1 ∈ (fun p : ℝ × ℝ ↦ dist p.1 p.2) '' ((Ico 0 1).toSet ×ˢ (Icc 1 2).toSet) := by
      refine ⟨(1 - ε, 1), ⟨?_, ?_⟩, rfl⟩
      · constructor <;> linarith
      · constructor <;> linarith
    have hdist_val : dist (1 - ε) 1 = ε := by
      rw [Real.dist_eq]
      simp only [sub_sub_cancel_left, abs_neg, abs_of_pos hε_pos]
    unfold set_dist at hpos hε_def
    have hle : sInf ((fun p : ℝ × ℝ ↦ dist p.1 p.2) '' ((Ico 0 1).toSet ×ˢ (Icc 1 2).toSet)) ≤ ε := by
      apply csInf_le
      · use 0
        intro r hr
        obtain ⟨⟨x, y⟩, ⟨_, _⟩, rfl⟩ := hr
        exact dist_nonneg
      · rw [← hdist_val]; exact hmem
    linarith
  · -- 0 ≤ set_dist : инфимум неотрицательных значений неотрицателен
    unfold set_dist
    apply le_csInf
    · -- Непусто
      refine ⟨dist 0 1, (0, 1), ⟨?_, ?_⟩, rfl⟩
      · norm_num
      · norm_num
    · intro r hr
      obtain ⟨⟨x, y⟩, ⟨_, _⟩, rfl⟩ := hr
      exact dist_nonneg

/-- Упражнение 1.2.4 -/
theorem dist_of_disj_compact_pos {d : ℕ} (E F : Set (EuclideanSpace' d)) (hEn : E.Nonempty) (hFn : F.Nonempty)
    (hE : IsCompact E) (hF : IsCompact F) (hdisj : E ∩ F = ∅) : 
    set_dist E F > 0 := by
  sorry

-- ========================================================================
-- Начало вспомогательных лемм для леммы 1.2.6
-- ========================================================================

/-- Сумма геометрического ряда δ/2^\{n+2\} равна δ/2 -/
lemma tsum_geometric_inflate {δ : ℝ} (_hδ : 0 < δ) :
    ∑' n : ℕ, δ / 2^(n+2) = δ / 2 := by
  -- ∑ δ/2^{n+2} = δ/4 * ∑ (1/2)^n = δ/4 * 2 = δ/2
  have h_eq : (fun n => δ / 2^(n+2)) = (fun n => δ / 4 * (1/2 : ℝ)^n) := by
    ext n
    have : (2 : ℝ)^(n+2) = 4 * 2^n := by ring
    rw [this]
    have h2n : (2 : ℝ) ^ n ≠ 0 := by positivity
    field_simp [h2n]
    rw [← mul_pow]; norm_num
  rw [h_eq, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1 : ℝ)/2 < 1)]
  ring
/-- Когда P\_nonempty ⊆ P, потеря от масштабирования ограничена δ/4. -/
lemma card_ratio_bound {P_nonempty P : Finset α} (hP_nonempty_sub : P_nonempty ⊆ P)
    {δ : ℝ} (hδ_pos : 0 < δ) (hcard_pos : 0 < P.card) : 
    P_nonempty.card * (δ / (4 * P.card)) ≤ δ / 4 := by
  have hP_card_pos : (0 : ℝ) < P.card := Nat.cast_pos.mpr hcard_pos
  have h_card_bound : P_nonempty.card ≤ P.card := Finset.card_le_card hP_nonempty_sub
  have h_div_nonneg : (0 : ℝ) ≤ δ / (4 * P.card) := by positivity
  calc P_nonempty.card * (δ / (4 * P.card))
      ≤ P.card * (δ / (4 * P.card)) := by
        apply mul_le_mul_of_nonneg_right (Nat.cast_le.mpr h_card_bound) h_div_nonneg
    _ = δ / 4 := by field_simp [hP_card_pos.ne.symm]

/-- Оценка суммы через фильтр разбиения: если объёмы B' удовлетворяют B.vol ≤ B'.vol + ε,
    то суммирование по P\_nonempty даёт общую оценку со слагаемым card \* ε. -/
lemma partition_volume_bound {d : ℕ} {P : Finset (Box d)}
    {P_nonempty : Finset (Box d)} (_hP_nonempty_sub : P_nonempty ⊆ P)
    {B' : (B : Box d) → B ∈ P_nonempty → Box d}
    {ε : ℝ} (_hε_pos : 0 < ε)
    (h_vol_bound : ∀ B (hB : B ∈ P_nonempty), B.volume ≤ (B' B hB).volume + ε) : 
    ∑ B ∈ P_nonempty, B.volume ≤
      ∑ x : { B // B ∈ P_nonempty }, (B' x.1 x.2).volume + P_nonempty.card * ε := by
  calc ∑ B ∈ P_nonempty, B.volume
      = ∑ x : { B // B ∈ P_nonempty }, x.1.volume := by rw [← Finset.sum_coe_sort]
    _ ≤ ∑ x : { B // B ∈ P_nonempty }, ((B' x.1 x.2).volume + ε) := by
        apply Finset.sum_le_sum
        intro ⟨B, hB⟩ _
        exact h_vol_bound B hB
    _ = ∑ x : { B // B ∈ P_nonempty }, (B' x.1 x.2).volume + ∑ _ : { B // B ∈ P_nonempty }, ε :=
        Finset.sum_add_distrib
    _ = ∑ x : { B // B ∈ P_nonempty }, (B' x.1 x.2).volume + P_nonempty.card * ε := by
        congr 1
        rw [Finset.sum_const, Finset.card_univ, ← smul_eq_mul]
        have : (Finset.univ : Finset { B // B ∈ P_nonempty }).image (fun x => x.val) = P_nonempty := by
          ext B
          simp only [Finset.mem_image]
          constructor
          · intro ⟨a, _, ha_eq⟩; rw [← ha_eq]; exact a.property
          · intro hB; exact ⟨⟨B, hB⟩, Finset.mem_univ _, rfl⟩
        rw [← Finset.card_univ, ← this]
        rw [Finset.card_image_of_injective _ (fun x y h => Subtype.ext h)]
        simp [smul_eq_mul]

/-- Уменьшенные прямоугольники B' наследуют инъективность от непересекаемости родительских
    прямоугольников, когда B' непусты. -/
lemma injective_of_shrunk_nonempty {d : ℕ} {P : Finset (Box d)}
    {P_nonempty : Finset (Box d)} (hP_nonempty_sub : P_nonempty ⊆ P)
    {B' : (B : Box d) → B ∈ P_nonempty → Box d}
    (hP_disj : (P : Set (Box d)).PairwiseDisjoint Box.toSet)
    (h_sub : ∀ B (hB : B ∈ P_nonempty), (B' B hB).toSet ⊆ B.toSet)
    (h_nonempty : ∀ B (hB : B ∈ P_nonempty), (B' B hB).toSet.Nonempty) : 
    Function.Injective (fun x : { B // B ∈ P_nonempty } => B' x.1 x.2) := by
  intro ⟨B₁, hB₁⟩ ⟨B₂, hB₂⟩ h_boxes_eq
  by_contra h_ne
  have hB₁P : B₁ ∈ P := hP_nonempty_sub hB₁
  have hB₂P : B₂ ∈ P := hP_nonempty_sub hB₂
  have h_orig_ne : B₁ ≠ B₂ := fun h_eq_B => h_ne (Subtype.ext h_eq_B)
  have h_orig_disj : Disjoint B₁.toSet B₂.toSet := hP_disj hB₁P hB₂P h_orig_ne
  have h_B'₁_nonempty : (B' B₁ hB₁).toSet.Nonempty := h_nonempty B₁ hB₁
  have h_in_inter : (B' B₁ hB₁).toSet ⊆ B₁.toSet ∩ B₂.toSet := by
    intro x hx
    have h_toSet_eq : (B' B₁ hB₁).toSet = (B' B₂ hB₂).toSet := congr_arg Box.toSet h_boxes_eq
    exact ⟨h_sub B₁ hB₁ hx, h_sub B₂ hB₂ (h_toSet_eq ▸ hx)⟩
  have h_inter_empty : B₁.toSet ∩ B₂.toSet = ∅ := Set.disjoint_iff_inter_eq_empty.mp h_orig_disj
  rw [h_inter_empty] at h_in_inter
  exact Set.not_nonempty_empty (h_B'₁_nonempty.mono h_in_inter)

/-- Каждый ограниченный интервал ({name}`BoundedInterval.Ioo`, {name}`BoundedInterval.Icc`,
    {name}`BoundedInterval.Ioc`, {name}`BoundedInterval.Ico`) является ограниченным множеством -/
lemma BoundedInterval.isBounded (I : BoundedInterval) : Bornology.IsBounded I.toSet := by
  cases I with
  | Ioo a b => simp only [toSet]; exact Metric.isBounded_Ioo a b
  | Icc a b => simp only [toSet]; exact Metric.isBounded_Icc a b
  | Ioc a b => simp only [toSet]; exact Metric.isBounded_Ioc a b
  | Ico a b => simp only [toSet]; exact Metric.isBounded_Ico a b

/-- Каждый прямоугольник (box) ограничен (произведение ограниченных интервалов) -/
lemma Box.isBounded {d : ℕ} (B : Box d) : Bornology.IsBounded B.toSet := by
  rw [Box.toSet_eq_ofLp_preimage]
  exact (PiLp.antilipschitzWith_ofLp 2 (fun _ : Fin d => ℝ)).isBounded_preimage
    (Bornology.IsBounded.pi (fun i => BoundedInterval.isBounded (B.side i)))

/-- Увеличить прямоугольник (box) до открытого прямоугольника с контролируемым приростом объёма -/
lemma Box.inflate {d : ℕ} (B : Box d) (δ : ℝ) (hδ : 0 < δ) :
    ∃ B' : Box d, B.toSet ⊆ interior B'.toSet ∧ IsOpen (interior B'.toSet) ∧ |B'|ᵥ ≤ |B|ᵥ + δ := by
  -- Отдельно обрабатываем размерность 0 (тривиальный случай)
  by_cases hd : d = 0
  · subst hd
    -- В размерности 0 подходит любой прямоугольник — объём всегда 1 (пустое произведение)
    use B
    refine ⟨?_, isOpen_interior, by linarith⟩
    -- B.toSet ⊆ interior B.toSet: в размерности 0 B.toSet = Set.univ, а это открытое множество
    have hB_univ : B.toSet = Set.univ := by
      ext x; simp only [Box.mem_toSet, Set.mem_univ, iff_true]; intro i; exact Fin.elim0 i
    rw [hB_univ, interior_univ]
  -- Размерность d > 0: используем аргумент непрерывности, чтобы найти достаточно малое ε
  push_neg at hd
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
  -- Определяем функцию увеличенного объёма f(ε) = ∏ᵢ (Lᵢ + 2ε)
  let f : ℝ → ℝ := fun ε => ∏ i : Fin d, (|B.side i|ₗ + 2 * ε)
  -- f непрерывна
  have hf_cont : Continuous f := by
    apply continuous_finset_prod
    intro i _
    exact (continuous_const.add (continuous_const.mul continuous_id))
  -- f(0) = |B|ᵥ
  have hf_zero : f 0 = |B|ᵥ := by simp only [f, mul_zero, add_zero, Box.volume]
  -- По непрерывности в 0 существует ε > 0 такое, что f(ε) < |B|ᵥ + δ
  have hf_cont_at : ContinuousAt f 0 := hf_cont.continuousAt
  rw [Metric.continuousAt_iff] at hf_cont_at
  obtain ⟨ε', hε'_pos, hε'_bound⟩ := hf_cont_at δ hδ
  -- Берём ε = ε'/2 > 0, чтобы гарантированно попасть внутрь δ-шара
  let ε := ε' / 2
  have hε_pos : 0 < ε := by positivity
  have hε_lt : ε < ε' := by simp only [ε]; nlinarith [hε'_pos]
  -- Строим увеличенный прямоугольник с интервалами Ioo
  let B' : Box d := ⟨fun i => BoundedInterval.Ioo ((B.side i).a - ε) ((B.side i).b + ε)⟩
  use B'
  constructor
  · -- Докажем B.toSet ⊆ interior B'.toSet
    -- Сначала покажем, что B'.toSet открыто (произведение открытых интервалов)
    have hB'_open : IsOpen B'.toSet := by
      rw [B'.toSet_eq_ofLp_preimage]
      exact (isOpen_set_pi Set.finite_univ (fun i _ => by
        simp only [B', BoundedInterval.toSet]; exact isOpen_Ioo)).preimage (PiLp.continuous_ofLp 2 _)
    -- Значит interior B'.toSet = B'.toSet
    rw [hB'_open.interior_eq]
    -- Теперь покажем B.toSet ⊆ B'.toSet
    intro x hx
    simp only [Box.mem_toSet] at hx ⊢
    intro i
    simp only [B', BoundedInterval.toSet, Set.mem_Ioo, BoundedInterval.a, BoundedInterval.b]
    -- Получаем hx для этого конкретного индекса i после разбора случаев
    cases hside : (B.side i) with
    | Ioo a b =>
      have hxi := hx i
      simp only [BoundedInterval.toSet, hside, Set.mem_Ioo] at hxi ⊢
      exact ⟨by linarith, by linarith⟩
    | Icc a b =>
      have hxi := hx i
      simp only [BoundedInterval.toSet, hside, Set.mem_Icc] at hxi ⊢
      exact ⟨by linarith, by linarith⟩
    | Ioc a b =>
      have hxi := hx i
      simp only [BoundedInterval.toSet, hside, Set.mem_Ioc] at hxi ⊢
      exact ⟨by linarith, by linarith⟩
    | Ico a b =>
      have hxi := hx i
      simp only [BoundedInterval.toSet, hside, Set.mem_Ico] at hxi ⊢
      exact ⟨by linarith, by linarith⟩
  constructor
  · -- IsOpen (interior B'.toSet) тривиально верно
    exact isOpen_interior
  · -- Докажем |B'|ᵥ ≤ |B|ᵥ + δ
    -- |B'|ᵥ = ∏ᵢ |B'.side i|ₗ ≤ ∏ᵢ (|B.side i|ₗ + 2ε) = f(ε)
    have hB'_vol_le : |B'|ᵥ ≤ f ε := by
      simp only [Box.volume, f, B']
      apply Finset.prod_le_prod
      · intro i _; exact BoundedInterval.length_nonneg _
      · intro i _
        simp only [BoundedInterval.length, BoundedInterval.a, BoundedInterval.b]
        -- Нужно: max(b + ε - (a - ε), 0) ≤ max(b - a, 0) + 2ε
        have h_ineq : ∀ (a b : ℝ), max (b + ε - (a - ε)) 0 ≤ max (b - a) 0 + 2 * ε := by
          intro a b
          have h1 : b + ε - (a - ε) = b - a + 2 * ε := by ring
          rw [h1]
          by_cases hab : b ≥ a
          · have h2 : max (b - a) 0 = b - a := max_eq_left (by linarith : 0 ≤ b - a)
            have h3 : max (b - a + 2 * ε) 0 = b - a + 2 * ε := max_eq_left (by linarith)
            rw [h2, h3]
          · push_neg at hab
            have h2 : max (b - a) 0 = 0 := max_eq_right (by linarith : b - a ≤ 0)
            rw [h2, zero_add]
            exact max_le (by linarith) (by linarith)
        exact h_ineq (B.side i).a (B.side i).b
    calc |B'|ᵥ ≤ f ε := hB'_vol_le
         _ ≤ |B|ᵥ + δ := by
           -- Используем оценку непрерывности: |f(ε) - f(0)| < δ, поскольку |ε - 0| < ε'
           have hε_in_ball : dist ε 0 < ε' := by
             simp only [Real.dist_eq, sub_zero, abs_of_pos hε_pos]
             exact hε_lt
           have h_dist := hε'_bound hε_in_ball
           rw [Real.dist_eq, hf_zero] at h_dist
           have h_abs := abs_sub_lt_iff.mp h_dist
           linarith

/-- Уменьшить прямоугольник (box) до замкнутого подпрямоугольника с контролируемым уменьшением
    объёма. Результат всегда непуст, если исходный прямоугольник непуст. -/
lemma Box.shrink_to_closed {d : ℕ} (B : Box d) (hB : B.toSet.Nonempty) (δ : ℝ) (hδ : 0 < δ) :
    ∃ B' : Box d, B'.toSet ⊆ B.toSet ∧ IsClosed B'.toSet ∧ |B'|ᵥ ≥ |B|ᵥ - δ ∧ B'.toSet.Nonempty := by
  -- Отдельно обрабатываем размерность 0 (тривиальный случай)
  by_cases hd : d = 0
  · subst hd
    use B
    have h_closed : IsClosed B.toSet := by
      have : B.toSet = Set.univ := by
        ext x; simp only [Box.mem_toSet, Set.mem_univ, iff_true]; intro i; exact Fin.elim0 i
      rw [this]; exact isClosed_univ
    exact ⟨Set.Subset.refl _, h_closed, by linarith, hB⟩
  -- Размерность d > 0
  push_neg at hd
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
  have h_sides_nonempty : ∀ i : Fin d, (B.side i).toSet.Nonempty :=
    fun i => Box.side_nonempty_of_nonempty B hB i
  -- Проверяем, все ли стороны имеют строго положительную длину
  by_cases h_all_pos : ∀ i : Fin d, 0 < |B.side i|ₗ
  · -- Невырожденный случай : у всех сторон положительная длина
    -- Определяем функцию уменьшенного объёма g(ε) = ∏ᵢ max(Lᵢ - 2ε, 0)
    let g : ℝ → ℝ := fun ε => ∏ i : Fin d, max (|B.side i|ₗ - 2 * ε) 0
    -- g непрерывна (max ∘ (f, g) непрерывна, когда непрерывны f и g)
    have hg_cont : Continuous g := by
      apply continuous_finset_prod
      intro i _
      apply Continuous.max
      · exact continuous_const.sub (continuous_const.mul continuous_id)
      · exact continuous_const
    have hg_zero : g 0 = |B|ᵥ := by
      simp only [g, mul_zero, sub_zero, Box.volume]
      congr 1; ext i
      exact max_eq_left (BoundedInterval.length_nonneg _)
    -- По непрерывности существует ε > 0, при котором g(ε) близко к g(0)
    have hg_cont_at : ContinuousAt g 0 := hg_cont.continuousAt
    rw [Metric.continuousAt_iff] at hg_cont_at
    obtain ⟨ε', hε'_pos, hε'_bound⟩ := hg_cont_at δ hδ
    -- Находим минимальную длину стороны
    let lengths : Finset ℝ := Finset.univ.image (fun i => |B.side i|ₗ)
    have hne_lengths : lengths.Nonempty := by
      simp only [lengths, Finset.image_nonempty]
      exact Finset.univ_nonempty_iff.mpr ⟨⟨0, hd_pos⟩⟩
    let L := lengths.min' hne_lengths
    have hL_pos : 0 < L := by
      have : L ∈ lengths := Finset.min'_mem _ _
      simp only [lengths, Finset.mem_image, Finset.mem_univ, true_and] at this
      obtain ⟨i, hi⟩ := this
      rw [←hi]; exact h_all_pos i
    have hL_bound : ∀ i : Fin d, L ≤ |B.side i|ₗ := fun i =>
      Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    -- Берём ε = min(ε'/2, L/4)
    let ε := min (ε' / 2) (L / 4)
    have hε_pos : 0 < ε := by positivity
    have hε_lt_half : ε < ε' := by
      calc ε ≤ ε' / 2 := min_le_left _ _
           _ < ε' := by linarith
    have hε_lt_L : ε < L / 2 := by
      calc ε ≤ L / 4 := min_le_right _ _
           _ < L / 2 := by linarith
    -- Строим уменьшенный прямоугольник
    let B' : Box d := ⟨fun i => BoundedInterval.Icc ((B.side i).a + ε) ((B.side i).b - ε)⟩
    use B'
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- B'.toSet ⊆ B.toSet
      -- Стратегия: Icc (a+ε) (b-ε) ⊆ Ioo a b ⊆ (B.side i).toSet
      intro x hx
      simp only [Box.mem_toSet] at hx ⊢
      intro i; specialize hx i
      simp only [B', BoundedInterval.toSet, Set.mem_Icc] at hx
      have hne := h_sides_nonempty i
      have hε_small : 2 * ε < |B.side i|ₗ := by
        calc 2 * ε < 2 * (L / 2) := by linarith [hε_lt_L]
             _ = L := by ring
             _ ≤ |B.side i|ₗ := hL_bound i
      -- Покажем x i ∈ (B.side i).toSet разбором случаев по типу интервала
      have h_len_pos := h_all_pos i
      simp only [BoundedInterval.length] at h_len_pos hε_small
      have h_max : max ((B.side i).b - (B.side i).a) 0 = (B.side i).b - (B.side i).a := by
        apply max_eq_left; linarith
      rw [h_max] at h_len_pos hε_small
      -- x i ∈ Icc (a+ε) (b-ε), что строго внутри любого варианта интервала [a,b]
      cases hside : (B.side i) with
      | Ioo a b =>
        simp only [BoundedInterval.toSet, Set.mem_Ioo, hside, BoundedInterval.a, BoundedInterval.b] at hx ⊢
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
      | Icc a b =>
        simp only [BoundedInterval.toSet, Set.mem_Icc, hside, BoundedInterval.a, BoundedInterval.b] at hx ⊢
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
      | Ioc a b =>
        simp only [BoundedInterval.toSet, Set.mem_Ioc, hside, BoundedInterval.a, BoundedInterval.b] at hx ⊢
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
      | Ico a b =>
        simp only [BoundedInterval.toSet, Set.mem_Ico, hside, BoundedInterval.a, BoundedInterval.b] at hx ⊢
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · -- IsClosed B'.toSet
      rw [B'.toSet_eq_ofLp_preimage]
      exact (isClosed_set_pi (fun i _ => by simp only [B', BoundedInterval.toSet]; exact isClosed_Icc)).preimage
        (PiLp.continuous_ofLp 2 _)
    · -- Оценка объёма
      have hB'_vol : |B'|ᵥ = g ε := by
        simp only [Box.volume, g, B']; congr 1; ext i
        simp only [BoundedInterval.length, BoundedInterval.a, BoundedInterval.b]
        -- Теперь обе части содержат одинаковые match-выражения; используем congr для унификации
        have h_len := hL_bound i
        have h_pos_len : |B.side i|ₗ - 2 * ε > 0 := by
          calc |B.side i|ₗ - 2 * ε ≥ L - 2 * ε := by linarith
               _ > L - 2 * (L / 2) := by linarith [hε_lt_L]
               _ = 0 := by ring
        have h_ab : (B.side i).a ≤ (B.side i).b := by
          have := h_all_pos i
          simp only [BoundedInterval.length] at this
          by_contra h_neg; push_neg at h_neg
          have : max ((B.side i).b - (B.side i).a) 0 = 0 := max_eq_right (by linarith)
          linarith
        simp only [BoundedInterval.length] at h_pos_len
        have h_max : max ((B.side i).b - (B.side i).a) 0 = (B.side i).b - (B.side i).a := max_eq_left (by linarith)
        rw [h_max] at h_pos_len
        -- Цель: max (b - ε - (a + ε)) 0 = max (max (b - a) 0 - 2 * ε) 0
        -- Сначала упростим правую часть, используя h_max
        conv_rhs => rw [h_max]
        -- Теперь цель: max (b - ε - (a + ε)) 0 = max (b - a - 2 * ε) 0
        -- Внутренние выражения равны по ring
        congr 1
        ring
      rw [hB'_vol]
      have hε_in_ball : dist ε 0 < ε' := by simp only [Real.dist_eq, sub_zero, abs_of_pos hε_pos]; exact hε_lt_half
      have h_dist := hε'_bound hε_in_ball
      rw [Real.dist_eq, hg_zero] at h_dist
      have h_abs := abs_sub_lt_iff.mp h_dist
      linarith
    · -- B'.toSet.Nonempty (невырожденный случай)
      -- У уменьшенного прямоугольника стороны [a+ε, b-ε], где 2ε < L (минимальная длина стороны)
      -- Значит a+ε < b-ε для каждой стороны, поэтому каждый координатный интервал непуст
      -- Произведение непустых множеств непусто
      suffices h : ∀ i, ((B'.side i).toSet).Nonempty by
        rw [B'.toSet_eq_ofLp_preimage]
        exact (Set.pi_nonempty_iff.mpr (fun i => ⟨(h i).some, fun _ => (h i).some_mem⟩)).preimage
          (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).surjective
      intro i
      simp only [B', BoundedInterval.toSet]
      rw [Set.nonempty_Icc]
      -- Нужно: (B.side i).a + ε ≤ (B.side i).b - ε, то есть 2ε ≤ (B.side i).b - (B.side i).a
      have h_side_pos := h_all_pos i
      simp only [BoundedInterval.length] at h_side_pos
      have h_ab : (B.side i).a ≤ (B.side i).b := by
        by_contra h_neg; push_neg at h_neg
        have : max ((B.side i).b - (B.side i).a) 0 = 0 := max_eq_right (by linarith)
        linarith
      have h_max : max ((B.side i).b - (B.side i).a) 0 = (B.side i).b - (B.side i).a := max_eq_left (by linarith)
      rw [h_max] at h_side_pos
      have h_2ε_lt : 2 * ε < (B.side i).b - (B.side i).a := by
        calc 2 * ε < 2 * (L / 2) := by linarith [hε_lt_L]
             _ = L := by ring
             _ ≤ |B.side i|ₗ := hL_bound i
             _ = (B.side i).b - (B.side i).a := by simp only [BoundedInterval.length, h_max]
      linarith
  · -- Вырожденный случай : у некоторой стороны нулевая длина, объём равен 0
    push_neg at h_all_pos
    obtain ⟨i₀, hi₀⟩ := h_all_pos
    have hvol_zero : |B|ᵥ = 0 := by
      simp only [Box.volume]
      apply Finset.prod_eq_zero (Finset.mem_univ i₀)
      have h := BoundedInterval.length_nonneg (B.side i₀); linarith
    obtain ⟨x, hx⟩ := hB
    let B' : Box d := ⟨fun i => BoundedInterval.Icc (x i) (x i)⟩
    use B'
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro y hy
      simp only [Box.mem_toSet] at hy hx ⊢
      intro i
      specialize hy i
      specialize hx i
      simp only [B', BoundedInterval.toSet, Set.mem_Icc] at hy
      have heq : y i = x i := le_antisymm hy.2 hy.1
      rw [heq]; exact hx
    · rw [B'.toSet_eq_ofLp_preimage]
      exact (isClosed_set_pi (fun i _ => by simp only [B', BoundedInterval.toSet]; exact isClosed_Icc)).preimage
        (PiLp.continuous_ofLp 2 _)
    · have hvol' : |B'|ᵥ = 0 := by
        simp only [Box.volume, B']
        have h0 : (⟨0, hd_pos⟩ : Fin d) ∈ Finset.univ := Finset.mem_univ _
        apply Finset.prod_eq_zero h0
        simp only [BoundedInterval.length, BoundedInterval.a, BoundedInterval.b, sub_self]
        exact max_eq_right (le_refl 0)
      rw [hvol', hvol_zero]; linarith
    · -- B'.toSet.Nonempty (вырожденный случай) : B' = {x} — одноэлементное множество, содержащее x
      use x
      simp only [Box.mem_toSet]
      intro i
      simp only [B', BoundedInterval.toSet, Set.mem_Icc, le_refl, and_self]

namespace IsElementary
/-- Elementary measure of empty set is zero (handles proof term mismatch) -/
lemma measure_of_empty_eq {d : ℕ} {E : Set (EuclideanSpace' d)}
    (hE : IsElementary E) (hempty : E = ∅) : hE.measure = 0 := by
  have : hE.measure = (IsElementary.empty d).measure :=
    IsElementary.measure_eq_of_set_eq hE (IsElementary.empty d) hempty
  rw [this, IsElementary.measure_of_empty]


/-- Конечное индексированное объединение прямоугольников элементарно (используем
    {name}`IsElementary.union'`, принимающую finset множеств) -/
lemma iUnion_boxes {d : ℕ} {ι : Type*} [Fintype ι] (B : ι → Box d) :
    IsElementary (⋃ i, (B i).toSet) := by
  classical
  -- Преобразуем индексированное объединение в объединение по finset
  let S : Finset (Set (EuclideanSpace' d)) := Finset.univ.image (fun i => (B i).toSet)
  have hS_elem : ∀ E ∈ S, IsElementary E := by
    intro E hE
    simp only [S, Finset.mem_image, Finset.mem_univ, true_and] at hE
    obtain ⟨i, rfl⟩ := hE
    exact IsElementary.box (B i)
  have h_eq : ⋃ i, (B i).toSet = ⋃ E ∈ S, E := by
    ext x
    simp only [S, Set.mem_iUnion, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro ⟨i, hi⟩; exact ⟨(B i).toSet, ⟨i, rfl⟩, hi⟩
    · intro ⟨_, ⟨i, rfl⟩, hi⟩; exact ⟨i, hi⟩
  rw [h_eq]
  exact IsElementary.union' hS_elem

/-- Мера конечного объединения прямоугольников (индексированного принадлежностью finset'у) не
    превосходит суммы объёмов. Это конечная субаддитивность, специализированная для
    прямоугольников с индексом-finset'ом. -/
lemma measure_le_finset_boxes_volume' {d : ℕ} (t : Finset ℕ) (B : ℕ → Box d) :
    (IsElementary.iUnion_boxes (fun (n : { n // n ∈ t }) => B n.1)).measure ≤ ∑ n ∈ t, (B n).volume := by
  classical
  -- Переходим к форме через Finset множеств и используем IsElementary.measure_of_union'
  haveI : DecidableEq (Set (EuclideanSpace' d)) := Classical.decEq _
  let S_sets : Finset (Set (EuclideanSpace' d)) := t.image (fun n => (B n).toSet)
  have hS_elem : ∀ E ∈ S_sets, IsElementary E := by
    intro E hE
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hE
    exact IsElementary.box (B n)
  -- Объединение по подтипу равно объединению по S_sets
  have h_union_eq : ⋃ (n : { n // n ∈ t }), (B n.1).toSet = ⋃ E ∈ S_sets, E := by
    ext x
    simp only [Set.mem_iUnion, S_sets]
    constructor
    · intro ⟨⟨n, hn⟩, hx⟩
      exact ⟨(B n).toSet, Finset.mem_image.mpr ⟨n, hn, rfl⟩, hx⟩
    · intro ⟨E, hE_mem, hx⟩
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hE_mem
      exact ⟨⟨n, hn⟩, hx⟩
  -- Применяем measure_eq_of_set_eq, чтобы связать элементарных свидетелей
  have h_measure_eq : (IsElementary.iUnion_boxes (fun (n : { n // n ∈ t }) => B n.1)).measure =
      (IsElementary.union' hS_elem).measure :=
    IsElementary.measure_eq_of_set_eq _ _ h_union_eq
  rw [h_measure_eq]
  -- Применяем конечную субаддитивность из IsElementary.measure_of_union'
  have h_sub := IsElementary.measure_of_union' hS_elem
  -- Переиндексируем сумму: нужно показать ∑ E : S_sets, (hS_elem E _).measure ≤ ∑ n ∈ t, (B n).volume
  calc (IsElementary.union' hS_elem).measure
      ≤ ∑ E : S_sets, (hS_elem E.val E.property).measure := h_sub
    _ ≤ ∑ n ∈ t, (B n).volume := by
        -- Каждая элементарная мера = объём прямоугольника, а образ S_sets — подмножество t
        -- Используем сумму по образу ≤ сумме по области определения
        have h_term_eq : ∀ (E : { E // E ∈ S_sets }),
            (hS_elem E.1 E.2).measure = (B (Finset.mem_image.mp E.2).choose).volume := by
          intro ⟨E, hE⟩
          -- choose_spec даёт (choose ∈ t ∧ (B choose).toSet = E)
          have h_spec := (Finset.mem_image.mp hE).choose_spec
          let n := (Finset.mem_image.mp hE).choose
          have h_eq : (B n).toSet = E := h_spec.2
          have hB_elem := IsElementary.box (B n)
          have hE_eq : E = (B n).toSet := h_eq.symm
          -- Цель: (hS_elem E hE).measure = (B n).volume
          rw [IsElementary.measure_eq_of_set_eq (hS_elem E hE) hB_elem hE_eq]
          rw [IsElementary.measure_of_box (B n)]
        -- Прообразы — подмножество t, поэтому сумма ≤ сумме по t
        -- Строим функцию прообраза: для каждого E ∈ S_sets выбираем n ∈ t такое, что (B n).toSet = E
        let f : { E // E ∈ S_sets } → ℕ := fun E => (Finset.mem_image.mp E.2).choose
        have hf_mem : ∀ E, f E ∈ t := fun ⟨E, hE⟩ =>
          (Finset.mem_image.mp hE).choose_spec.1
        have hf_eq : ∀ E, (B (f E)).toSet = E.1 := fun ⟨E, hE⟩ =>
          (Finset.mem_image.mp hE).choose_spec.2
        -- Покажем, что f инъективна (разные множества → разные индексы через выбранных
        -- представителей)
        have hf_inj : Function.Injective f := by
          intro ⟨E₁, hE₁⟩ ⟨E₂, hE₂⟩ h_eq
          apply Subtype.ext
          calc E₁ = (B (f ⟨E₁, hE₁⟩)).toSet := (hf_eq ⟨E₁, hE₁⟩).symm
            _ = (B (f ⟨E₂, hE₂⟩)).toSet := by rw [h_eq]
            _ = E₂ := hf_eq ⟨E₂, hE₂⟩
        -- Образ f — подмножество t
        have h_image_sub : (Finset.univ : Finset { E // E ∈ S_sets }).image f ⊆ t := by
          intro n hn
          simp only [Finset.mem_image, Finset.mem_univ, true_and] at hn
          obtain ⟨E, rfl⟩ := hn
          exact hf_mem E
        -- Используем Finset.sum_image, пользуясь инъективностью
        calc ∑ E : S_sets, (hS_elem E.val E.property).measure
            = ∑ E : S_sets, (B (f E)).volume := Finset.sum_congr rfl (fun E _ => h_term_eq E)
          _ = ∑ n ∈ (Finset.univ : Finset { E // E ∈ S_sets }).image f, (B n).volume := by
              rw [Finset.sum_image (fun E₁ _ E₂ _ h => hf_inj h)]
          _ ≤ ∑ n ∈ t, (B n).volume :=
              Finset.sum_le_sum_of_subset_of_nonneg h_image_sub
                (fun n _ _ => Box.volume_nonneg (B n))

/-- Для любого покрытия прямоугольниками элементарного множества сумма объёмов ограничивает
    меру снизу. Это ключевой шаг, использующий компактность Гейне–Бореля: увеличиваем
    прямоугольники до открытого покрытия, извлекаем конечное подпокрытие компактного
    приближения, применяем конечную субаддитивность. -/
lemma measure_le_cover_sum {d : ℕ} (_hd : 0 < d) {E : Set (EuclideanSpace' d)}
    (hE : IsElementary E) (S : ℕ → Box d) (hS_cover : E ⊆ ⋃ n, (S n).toSet) :
    (hE.measure : EReal) ≤ ∑' n, (S n).volume.toEReal := by
  -- Отдельно обрабатываем случай пустого множества
  by_cases hE_empty : E = ∅
  · rw [hE.measure_of_empty_eq hE_empty]
    simp only [EReal.coe_zero]
    positivity
  -- E непусто
  have hE_nonempty : E.Nonempty := Set.nonempty_iff_ne_empty.mpr hE_empty
  -- Получаем разбиение E
  obtain ⟨P, hP_disj, hP_eq⟩ := hE.partition
  have hP_nonempty : P.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hP_empty
    rw [hP_empty] at hP_eq
    simp at hP_eq
    exact hE_empty hP_eq
  -- Используем ε-аргумент: покажем hE.measure ≤ ∑|S_n| + ε для всех ε > 0
  apply EReal.le_of_forall_pos_le_add'
  intro δ hδ_pos
  have hδ4_pos : 0 < δ / 4 := by linarith
  -- Шаг 1: увеличиваем каждый S_n до открытого S'_n с контролируемым приростом объёма
  have h_inflate : ∀ n : ℕ, ∃ S'_n : Box d,
      (S n).toSet ⊆ interior S'_n.toSet ∧ IsOpen (interior S'_n.toSet) ∧
      S'_n.volume ≤ (S n).volume + δ / 2^(n+2) := by
    intro n
    exact Box.inflate (S n) (δ / 2^(n+2)) (by positivity)
  choose S' hS'_subset hS'_open hS'_vol using h_inflate
  -- Шаг 2: {interior (S' n)} — открытое покрытие E
  have h_open_cover : E ⊆ ⋃ n, interior (S' n).toSet := by
    intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hS_cover hx)
    exact Set.mem_iUnion.mpr ⟨n, hS'_subset n hn⟩
  -- Шаг 3: уменьшаем прямоугольники разбиения, получая компактное приближение K
  have hcard_pos : 0 < P.card := Finset.card_pos.mpr hP_nonempty
  have h_shrink : ∀ B ∈ P, B.toSet.Nonempty → ∃ B' : Box d,
      B'.toSet ⊆ B.toSet ∧ IsClosed B'.toSet ∧ B'.volume ≥ B.volume - δ / (4 * P.card) ∧ B'.toSet.Nonempty := by
    intro B _ hB_nonempty
    exact Box.shrink_to_closed B hB_nonempty (δ / (4 * P.card)) (by positivity)
  -- Шаг 4: строим компактное множество K из уменьшенных прямоугольников разбиения
  -- Фильтруем непустые прямоугольники (используя классическую разрешимость)
  haveI : DecidablePred (fun (B : Box d) => B.toSet.Nonempty) := Classical.decPred _
  let P_nonempty := P.filter (fun B => B.toSet.Nonempty)
  -- Для каждого непустого прямоугольника в P выбираем замкнутый уменьшенный прямоугольник
  have h_shrink' : ∀ B ∈ P_nonempty, ∃ B' : Box d,
      B'.toSet ⊆ B.toSet ∧ IsClosed B'.toSet ∧ B'.volume ≥ B.volume - δ / (4 * P.card) ∧ B'.toSet.Nonempty := by
    intro B hB
    have hBP : B ∈ P := Finset.mem_filter.mp hB |>.1
    have hB_ne : B.toSet.Nonempty := Finset.mem_filter.mp hB |>.2
    exact h_shrink B hBP hB_ne
  choose B' hB'_sub hB'_closed hB'_vol hB'_nonempty using h_shrink'
  -- Определяем K непосредственно как объединение уменьшенных прямоугольников по P_nonempty
  let K := ⋃ (x : { B // B ∈ P_nonempty }), (B' x.1 x.2).toSet
  -- Шаг 5: K замкнуто (конечное объединение замкнутых множеств)
  have hK_closed : IsClosed K := by
    show IsClosed (⋃ (x : { B // B ∈ P_nonempty }), (B' x.1 x.2).toSet)
    haveI : Finite { B // B ∈ P_nonempty } := Finset.finite_toSet P_nonempty |>.to_subtype
    apply isClosed_iUnion_of_finite
    intro ⟨B, hB⟩
    exact hB'_closed B hB
  -- Шаг 6: K ограничено (K ⊆ E, а E ограничено)
  have hK_subset_E : K ⊆ E := by
    intro x hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨⟨B, hB⟩, hx_in_B'⟩ := hx
    have hBP : B ∈ P := Finset.mem_filter.mp hB |>.1
    rw [hP_eq]
    exact Set.mem_biUnion hBP (hB'_sub B hB hx_in_B')
  have hK_bounded : Bornology.IsBounded K := hE.isBounded.subset hK_subset_E
  -- Шаг 7: K компактно (Гейне–Борель)
  have hK_compact : IsCompact K := Metric.isCompact_of_isClosed_isBounded hK_closed hK_bounded
  -- Шаг 8: K ⊆ ⋃ interior S'_n (поскольку K ⊆ E ⊆ ⋃ interior S'_n)
  have hK_cover : K ⊆ ⋃ n, interior (S' n).toSet := hK_subset_E.trans h_open_cover
  -- Шаг 9: применяем теорему Гейне–Бореля, получая конечное подпокрытие
  obtain ⟨t, ht_cover⟩ := hK_compact.elim_finite_subcover
    (fun n => interior (S' n).toSet) (fun n => isOpen_interior) hK_cover
  -- Шаг 10: цепочка вычисления объёма
  -- Имеем: K ⊆ ⋃ n ∈ t, interior (S' n).toSet ⊆ ⋃ n ∈ t, (S' n).toSet
  -- Стратегия: hE.measure ≤ m(K) + δ/4 ≤ ∑_{n∈t} |S'_n| + δ/4 ≤ ∑_all |S_n| + δ
  -- Шаг 10a: m(E) ≤ m(K) + δ/4 (K приближает E с контролируемой потерей объёма)
  -- У каждого уменьшенного прямоугольника B' выполняется |B'| ≥ |B| - δ/(4*|P|),
  -- поэтому суммарная потеря ≤ δ/4
  have h_K_approx : hE.measure ≤ ∑ (x : { B // B ∈ P_nonempty }), (B' x.1 x.2).volume + δ / 4 := by
    -- Стратегия: hE.measure = ∑ B ∈ P, B.volume (через непересекающееся разбиение)
    -- Для непустых B: B.volume ≤ B'.volume + δ/(4*|P|)
    -- Для пустых B: B.volume = 0
    -- Сумма: hE.measure ≤ ∑ B'.volume + |P_nonempty| * δ/(4*|P|) ≤ ∑ B'.volume + δ/4
    have hE_measure : hE.measure = ∑ B ∈ P, B.volume := hE.measure_eq hP_disj hP_eq
    -- Разбиваем P на непустые и пустые прямоугольники
    have hP_split : P = P_nonempty ∪ (P.filter (fun B => ¬(B.toSet).Nonempty)) := by
      ext B; simp [P_nonempty]; tauto
    -- У пустых прямоугольников объём 0
    have h_empty_vol : ∀ B ∈ P.filter (fun B => ¬(B.toSet).Nonempty), B.volume = 0 := by
      intro B hB
      simp only [Finset.mem_filter] at hB
      exact Box.volume_eq_zero_of_empty B (Set.not_nonempty_iff_eq_empty.mp hB.2)
    -- Сумма по пустым прямоугольникам равна 0
    have h_empty_sum : ∑ B ∈ P.filter (fun B => ¬(B.toSet).Nonempty), B.volume = 0 := by
      exact Finset.sum_eq_zero h_empty_vol
    -- Переписываем сумму по P
    have h_sum_split : ∑ B ∈ P, B.volume = ∑ B ∈ P_nonempty, B.volume + ∑ B ∈ P.filter (fun B => ¬(B.toSet).Nonempty), B.volume := by
      rw [← Finset.sum_union]
      · rw [← hP_split]
      · apply Finset.disjoint_left.2
        intro B hB₁ hB₂
        simp only [P_nonempty, Finset.mem_filter] at hB₁ hB₂
        exact hB₂.2 hB₁.2
    rw [hE_measure, h_sum_split, h_empty_sum, add_zero]
    -- Для каждого непустого B: B.volume ≤ B'.volume + δ/(4*|P|)
    have h_vol_bound : ∀ B (hB : B ∈ P_nonempty), B.volume ≤ (B' B hB).volume + δ / (4 * P.card) := by
      intro B hB; linarith [hB'_vol B hB]
    -- Используем вспомогательные леммы для оценки суммы
    have hP_nonempty_sub : P_nonempty ⊆ P := Finset.filter_subset _ P
    have hδ4P_pos : 0 < δ / (4 * P.card) := div_pos hδ_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr hcard_pos))
    have h_sum_bound := partition_volume_bound hP_nonempty_sub hδ4P_pos h_vol_bound
    have h_loss_bound := card_ratio_bound hP_nonempty_sub hδ_pos hcard_pos
    linarith [h_sum_bound, h_loss_bound]
  -- Шаг 10b: K элементарно (конечное объединение замкнутых прямоугольников)
  have hK_elem : IsElementary K := by
    exact IsElementary.iUnion_boxes (fun (x : { B // B ∈ P_nonempty }) => B' x.1 x.2)
  -- Шаг 10c: m(K) ≤ ∑_{n∈t} |S'_n| (K покрыто конечным числом прямоугольников)
  have h_K_cover_bound : hK_elem.measure ≤ ∑ n ∈ t, (S' n).volume := by
    -- Строим элементарное множество из объединения покрывающих прямоугольников
    have hU_elem : IsElementary (⋃ (n : { n // n ∈ t }), (S' n.1).toSet) :=
      IsElementary.iUnion_boxes (fun (n : { n // n ∈ t }) => S' n.1)
    -- Покажем K ⊆ ⋃ n ∈ t, S'_n
    have hK_sub_U : K ⊆ ⋃ (n : { n // n ∈ t }), (S' n.1).toSet := by
      intro x hx
      obtain ⟨n, hn, hx_in⟩ := Set.mem_iUnion₂.mp (ht_cover hx)
      exact Set.mem_iUnion.mpr ⟨⟨n, hn⟩, interior_subset hx_in⟩
    -- Применяем монотонность меры и формулу объединения непересекающихся множеств
    calc hK_elem.measure
        ≤ hU_elem.measure := hK_elem.measure_mono hU_elem hK_sub_U
      _ ≤ ∑ n ∈ t, (S' n).volume := IsElementary.measure_le_finset_boxes_volume' t S'
  -- Шаг 10d: конечная сумма ≤ бесконечной сумме
  have h_finite_le_tsum : (∑ n ∈ t, (S' n).volume : EReal) ≤ ∑' n, (S' n).volume.toEReal := by
    -- Для неотрицательных слагаемых конечная частичная сумма ≤ бесконечной сумме
    exact EReal.finset_sum_le_tsum (fun n => Box.volume_nonneg (S' n)) t
  -- Шаг 10e: ∑_all |S'_n| ≤ ∑_all |S_n| + δ/2 (из hS'_vol)
  have h_inflate_bound : (∑' n, (S' n).volume.toEReal : EReal) ≤ ∑' n, (S n).volume.toEReal + δ / 2 := by
    -- Каждое |S'_n| ≤ |S_n| + δ/2^{n+2}, а ∑ δ/2^{n+2} = δ/2
    have h_pointwise : ∀ n, (S' n).volume.toEReal ≤ (S n).volume.toEReal + (δ / 2^(n+2) : ℝ) := by
      intro n
      have hvol := hS'_vol n
      rw [← EReal.coe_add]
      exact EReal.coe_le_coe hvol
    -- Ключевой факт: ∑' n, δ / 2^(n+2) = δ/2 (геометрический ряд)
    have h_geom : ∑' n : ℕ, (δ / 2^(n+2) : ℝ) = δ / 2 := tsum_geometric_inflate hδ_pos
    -- Арифметика tsum в EReal: переходим через ENNReal, где свойства tsum чище
    -- Используем EReal.tsum_add_le_of_nonneg_pointwise из нашей вспомогательной библиотеки
    -- Нужно: ∑' (S' n).vol.toEReal ≤ ∑' (S n).vol.toEReal + δ/2
    -- Из h_pointwise: (S' n).vol ≤ (S n).vol + δ/2^(n+2)
    -- И h_geom: ∑' δ/2^(n+2) = δ/2
    -- Стратегия: применяем tsum_add_le_of_nonneg_pointwise, чтобы получить
    --   ∑' (S' n).vol + ∑' 0 ≤ ∑' ((S n).vol + δ/2^(n+2))
    -- Затем раскладываем правую часть, используя свойства tsum
    have h_S'_nonneg : ∀ n, 0 ≤ (S' n).volume := fun n => Box.volume_nonneg (S' n)
    have h_S_nonneg : ∀ n, 0 ≤ (S n).volume := fun n => Box.volume_nonneg (S n)
    have h_geom_nonneg : ∀ n, (0 : ℝ) ≤ δ / 2^(n+2) := fun n => by positivity
    -- Используем вспомогательную лемму с f = S'.vol, g = 0 (тривиально), h = S.vol + δ/2^{n+2}
    have h_bound : (∑' n : ℕ, (S' n).volume.toEReal) + (∑' n : ℕ, (0 : ℝ).toEReal) ≤
        ∑' n : ℕ, ((S n).volume + δ / 2^(n+2)).toEReal := by
      apply EReal.tsum_add_le_of_nonneg_pointwise h_S'_nonneg (fun _ => le_refl 0)
      intro n; simp only [add_zero]; exact hS'_vol n
    simp only [EReal.coe_zero, tsum_zero, add_zero] at h_bound
    -- Теперь покажем: ∑' ((S n).vol + δ/2^{n+2}).toEReal ≤ ∑' (S n).vol.toEReal + δ/2
    have h_rhs_bound : (∑' n : ℕ, ((S n).volume + δ / 2^(n+2)).toEReal) ≤
        ∑' n : ℕ, (S n).volume.toEReal + (δ / 2 : ℝ) := by
      -- Переходим через ENNReal, где tsum_add работает чисто
      let f : ℕ → ENNReal := fun n => ENNReal.ofReal ((S n).volume)
      let g : ℕ → ENNReal := fun n => ENNReal.ofReal (δ / 2^(n+2))
      have h_f_eq : ∀ n, (f n).toEReal = (S n).volume.toEReal := fun n => by
        simp only [f, EReal.coe_ennreal_ofReal, max_eq_left (h_S_nonneg n)]
      have h_g_eq : ∀ n, (g n).toEReal = (δ / 2^(n+2) : ℝ).toEReal := fun n => by
        simp only [g, EReal.coe_ennreal_ofReal, max_eq_left (h_geom_nonneg n)]
      have h_fg_eq : ∀ n, ((S n).volume + δ / 2^(n+2)).toEReal = (f n + g n).toEReal := fun n => by
        simp only [EReal.coe_ennreal_add, h_f_eq, h_g_eq]
        rw [← EReal.coe_add]
      -- Переписываем левую часть
      conv_lhs => congr; ext n; rw [h_fg_eq]
      -- Используем свойства tsum в ENNReal через приведение
      have h_sum_fg : (∑' n, (f n + g n).toEReal) = (∑' n, (f n).toEReal) + (∑' n, (g n).toEReal) := by
        rw [← EReal.tsum_add_coe_ennreal]
      rw [h_sum_fg]
      -- Теперь покажем ∑' (f n).toEReal = ∑' (S n).vol.toEReal
      have h_lhs_eq : ∑' n, (f n).toEReal = ∑' n, (S n).volume.toEReal := tsum_congr h_f_eq
      -- И ∑' (g n).toEReal = (δ/2).toEReal
      have h_rhs_eq : (∑' n, (g n).toEReal) = (δ / 2 : ℝ).toEReal := by
        conv_lhs => congr; ext n; rw [h_g_eq]
        -- Нужно: ∑' n, (δ/2^(n+2)).toEReal = (δ/2).toEReal
        -- Поскольку все слагаемые неотрицательны и у нас есть суммируемость h_geom
        have h_geom_summable : Summable (fun n => δ / 2^(n+2) : ℕ → ℝ) := by
          have : Summable (fun n => δ / 4 * (1/2 : ℝ)^n) :=
            Summable.mul_left (δ / 4) (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1))
          refine Summable.congr this ?_
          intro n; field_simp; ring_nf
          simp
        rw [← h_geom]
        -- Преобразуем: ∑' real.toEReal = (∑' real).toEReal для суммируемых неотрицательных
        symm
        -- Используем Summable.map_tsum, чтобы показать, что приведение коммутирует с tsum
        let φ : ℝ →+ EReal := {
          toFun := (↑·)
          map_zero' := EReal.coe_zero
          map_add' := fun x y => EReal.coe_add x y
        }
        have h_cont : Continuous φ := continuous_coe_real_ereal
        have h_map := Summable.map_tsum h_geom_summable φ h_cont
        -- h_map: φ (∑' (i : ℕ), δ / 2 ^ (i + 2)) = ∑' (i : ℕ), φ (δ / 2 ^ (i + 2))
        -- Поскольку φ = (↑·), это означает: ↑(∑' (i : ℕ), δ / 2 ^ (i + 2)) = ∑' (i : ℕ), ↑(δ / 2 ^ (i + 2))
        -- Цель: ↑(∑' (n : ℕ), δ / 2 ^ (n + 2)) = ∑' (n : ℕ), ↑(δ / 2 ^ (n + 2))
        -- Переписываем обе части через φ, затем применяем h_map.symm, сопоставив имена переменных
        -- Поскольку φ = (↑·), можно использовать h_map.symm после сопоставления имён переменных
        have h_eq_lhs : ↑(∑' (n : ℕ), δ / 2 ^ (n + 2)) = φ (∑' (n : ℕ), δ / 2 ^ (n + 2)) := by
          congr 1
        have h_eq_rhs : ∑' (n : ℕ), ↑(δ / 2 ^ (n + 2)) = ∑' (n : ℕ), φ (δ / 2 ^ (n + 2)) :=
          tsum_congr (fun n => rfl)
        rw [h_eq_lhs, h_eq_rhs, ← h_map.symm]
      rw [h_lhs_eq, h_rhs_eq]
    exact le_trans h_bound h_rhs_bound
  -- Объединяем оценки: работаем полностью в EReal
  -- Шаг: m(E) ≤ сумма объёмов уменьшенных B' + δ/4
  have h_step1 : (hE.measure : EReal) ≤ ((∑ (x : { B // B ∈ P_nonempty }), (B' x.1 x.2).volume) + δ / 4 : ℝ) := by
    exact_mod_cast h_K_approx
  -- Шаг: сумма B' ≤ m(K) (когда K = ⋃ B')
  have h_step2 : (∑ (x : { B // B ∈ P_nonempty }), (B' x.1 x.2).volume : EReal) ≤ (hK_elem.measure : EReal) := by
    -- K = ⋃ B' — непересекающееся объединение (поскольку B' ⊆ B, а исходные B не пересекаются)
    -- Для непересекающихся объединений: m(K) = ∑ |B'|, значит здесь равенство
    -- Прямоугольники B' образуют непересекающееся разбиение K
    have h_B'_disj : ((Finset.univ : Finset { B // B ∈ P_nonempty }) : Set { B // B ∈ P_nonempty }).PairwiseDisjoint
        (fun x => (B' x.1 x.2).toSet) := by
      intro ⟨B₁, hB₁⟩ _ ⟨B₂, hB₂⟩ _ hne
      have hB₁P : B₁ ∈ P := Finset.mem_filter.mp hB₁ |>.1
      have hB₂P : B₂ ∈ P := Finset.mem_filter.mp hB₂ |>.1
      have h_orig_disj := hP_disj hB₁P hB₂P (by
        intro h_eq
        apply hne
        cases h_eq
        rfl)
      exact Set.disjoint_of_subset (hB'_sub B₁ hB₁) (hB'_sub B₂ hB₂) h_orig_disj
    -- Строим finset из прямоугольников B'
    let T := Finset.univ.image (fun (x : { B // B ∈ P_nonempty }) => B' x.1 x.2)
    -- Покажем, что T попарно не пересекается
    have hT_disj : (T : Set (Box d)).PairwiseDisjoint Box.toSet := by
      intro box₁ hbox₁ box₂ hbox₂ hne
      simp only [T, Finset.mem_coe, Finset.mem_image] at hbox₁ hbox₂
      obtain ⟨⟨B₁, hB₁⟩, _, rfl⟩ := hbox₁
      obtain ⟨⟨B₂, hB₂⟩, _, rfl⟩ := hbox₂
      have hB₁P : B₁ ∈ P := Finset.mem_filter.mp hB₁ |>.1
      have hB₂P : B₂ ∈ P := Finset.mem_filter.mp hB₂ |>.1
      have h_disj_orig : Disjoint B₁.toSet B₂.toSet := hP_disj hB₁P hB₂P (by
        intro h_eq
        apply hne
        simp only [h_eq])
      exact Set.disjoint_of_subset (hB'_sub B₁ hB₁) (hB'_sub B₂ hB₂) h_disj_orig
    -- Покажем K = ⋃ B ∈ T
    have hK_eq : K = ⋃ box ∈ T, box.toSet := by
      simp only [K, T]
      ext x
      simp only [Set.mem_iUnion, Finset.mem_image, Finset.mem_univ, true_and, exists_prop]
      refine ⟨fun ⟨⟨B, hB⟩, hx⟩ => ?_, fun ⟨_, ⟨⟨B, hB⟩, rfl⟩, hx⟩ => ?_⟩
      · exact ⟨B' B hB, ⟨⟨B, hB⟩, rfl⟩, hx⟩
      · exact ⟨⟨B, hB⟩, hx⟩
    -- Применяем IsElementary.measure_eq
    have h_measure_eq := hK_elem.measure_eq hT_disj hK_eq
    -- Приводим к нужному неравенству
    rw [h_measure_eq]
    -- B' инъективна, поскольку прямоугольники B' — подмножества попарно непересекающихся
    -- исходных прямоугольников
    have hP_nonempty_sub : P_nonempty ⊆ P := Finset.filter_subset _ P
    have h_B'_inj : Function.Injective (fun x : { B // B ∈ P_nonempty } => B' x.1 x.2) :=
      injective_of_shrunk_nonempty hP_nonempty_sub hP_disj hB'_sub hB'_nonempty
    -- Теперь используем sum_image, пользуясь инъективностью
    have h_sum_eq : ∑ B ∈ T, B.volume = ∑ x : { B // B ∈ P_nonempty }, (B' x.1 x.2).volume := by
      simp only [T]
      rw [Finset.sum_image (fun x _ y _ h => h_B'_inj h)]
    rw [h_sum_eq]
    -- Приводим сумму по finset к EReal через coe_finset_sum (объёмы неотрицательны)
    have h_vol_nonneg : ∀ x : { B // B ∈ P_nonempty }, 0 ≤ (B' x.1 x.2).volume := fun x => Box.volume_nonneg _
    rw [← EReal.coe_finset_sum (fun x _ => h_vol_nonneg x)]
  -- Шаг: m(K) ≤ ∑_{n∈t} |S'_n|
  have h_step3 : (hK_elem.measure : EReal) ≤ (∑ n ∈ t, (S' n).volume : ℝ) := by
    exact_mod_cast h_K_cover_bound
  -- Шаг: конечная сумма ≤ tsum (у h_finite_le_tsum уже совпадающие типы)
  have h_step4 : (∑ n ∈ t, (S' n).volume.toEReal) ≤ ∑' n, (S' n).volume.toEReal :=
    h_finite_le_tsum
  -- Итоговая цепочка: m(E) ≤ ∑ B' + δ/4 ≤ m(K) + δ/4 ≤ ∑_{n∈t} S'_n + δ/4
  --              ≤ ∑'_n S'_n + δ/4 ≤ ∑'_n S_n + δ/2 + δ/4 ≤ ∑'_n S_n + δ
  -- Сначала преобразуем h_step1, разделив сумму и слагаемое δ/4
  have h_sum_B'_nonneg : 0 ≤ ∑ (x : { B // B ∈ P_nonempty }), (B' x.1 x.2).volume :=
    Finset.sum_nonneg (fun x _ => Box.volume_nonneg _)
  have h_vol_nonneg' : ∀ x : { B // B ∈ P_nonempty }, 0 ≤ (B' x.1 x.2).volume := fun x => Box.volume_nonneg _
  have h_coe_sum : (∑ (x : { B // B ∈ P_nonempty }), (B' x.1 x.2).volume : EReal) =
      ∑ (x : { B // B ∈ P_nonempty }), ((B' x.1 x.2).volume : EReal) := rfl
  -- Цепочка: m(E) ≤ ∑ B' + δ/4 ≤ m(K) + δ/4 ≤ ∑_{t} S' + δ/4 ≤ ∑' S' + δ/4 ≤ ∑' S + δ/2 + δ/4
  calc (hE.measure : EReal)
      ≤ ((∑ (x : { B // B ∈ P_nonempty }), (B' x.1 x.2).volume) + δ / 4 : ℝ) := h_step1
    _ = (∑ (x : { B // B ∈ P_nonempty }), (B' x.1 x.2).volume : EReal) + (δ / 4 : ℝ) := by
        rw [EReal.coe_add (∑ (x : { B // B ∈ P_nonempty }), (B' x.1 x.2).volume) (δ / 4)]
        congr 1
        rw [EReal.coe_finset_sum (fun x _ => h_vol_nonneg' x)]
    _ ≤ (hK_elem.measure : EReal) + (δ / 4 : ℝ) := by
        apply add_le_add_left
        rw [h_coe_sum]
        exact h_step2
    _ ≤ (∑ n ∈ t, (S' n).volume : ℝ) + (δ / 4 : ℝ) := by
        apply add_le_add_left h_step3
    _ = (∑ n ∈ t, ((S' n).volume : EReal)) + (δ / 4 : ℝ) := by
        congr 1
        rw [EReal.coe_finset_sum (fun n _ => Box.volume_nonneg _)]
    _ ≤ (∑' n, (S' n).volume : EReal) + (δ / 4 : ℝ) := by
        apply add_le_add_left
        exact h_step4
    _ ≤ (∑' n, (S n).volume : EReal) + (δ / 2 : ℝ) + (δ / 4 : ℝ) := by
        have h1 : (∑' n, (S' n).volume : EReal) ≤ (∑' n, (S n).volume : EReal) + (δ / 2 : ℝ) := h_inflate_bound
        calc (∑' n, (S' n).volume : EReal) + (δ / 4 : ℝ)
            ≤ ((∑' n, (S n).volume : EReal) + (δ / 2 : ℝ)) + (δ / 4 : ℝ) := add_le_add_left h1 _
          _ = (∑' n, (S n).volume : EReal) + (δ / 2 : ℝ) + (δ / 4 : ℝ) := rfl
    _ = (∑' n, (S n).volume : EReal) + ((δ / 2 : ℝ) + (δ / 4 : ℝ)) := by rw [add_assoc]
    _ = (∑' n, (S n).volume : EReal) + (3 * δ / 4 : ℝ) := by
        congr 1
        rw [← EReal.coe_add (δ / 2) (δ / 4)]
        congr 1
        ring
    _ ≤ (∑' n, (S n).volume : EReal) + (δ : ℝ) := by
        apply add_le_add_right
        exact_mod_cast (by linarith : (3 * δ / 4 : ℝ) ≤ δ)

/-- Направление 1: элементарная мера является нижней гранью для внешней меры
    (разбиение даёт конечное покрытие, внешняя мера — инфимум по покрытиям)
    Используем measure\_le\_cover\_sum для ключевого аргумента Гейне–Бореля. -/
lemma measure_le_outer_measure {d : ℕ} (hd : 0 < d) {E : Set (EuclideanSpace' d)}
    (hE : IsElementary E) : (hE.measure : EReal) ≤ Lebesgue_outer_measure E := by
  -- Используем ε-аргумент: покажем ∀ ε > 0, hE.measure ≤ m*(E) + ε
  apply EReal.le_of_forall_pos_le_add'
  intro ε hε_pos
  -- У E конечная внешняя мера (ограничена элементарной мерой через жорданову)
  have h_finite : Lebesgue_outer_measure E ≠ ⊤ := by
    have h1 : Lebesgue_outer_measure E ≤ (Jordan_outer_measure E : EReal) :=
      Lebesgue_outer_measure_le_Jordan hE.isBounded
    have h2 : Jordan_outer_measure E ≤ hE.measure := Jordan_outer_le hE (Set.Subset.refl E)
    have h3 : Lebesgue_outer_measure E ≤ (hE.measure : EReal) := calc Lebesgue_outer_measure E
        ≤ (Jordan_outer_measure E : EReal) := h1
      _ ≤ (hE.measure : EReal) := by exact_mod_cast h2
    exact ne_top_of_le_ne_top (EReal.coe_ne_top hE.measure) h3
  -- Берём ε/2-близкое покрытие
  have hε2_pos : 0 < ε / 2 := by linarith
  obtain ⟨S, hS_cover, hS_sum⟩ := Lebesgue_outer_measure.exists_cover_close hd E (ε / 2) hε2_pos h_finite
  -- Используем вспомогательную лемму для основной оценки
  have h_cover_bound : (hE.measure : EReal) ≤ ∑' n, (S n).volume.toEReal :=
    hE.measure_le_cover_sum hd S hS_cover
  calc (hE.measure : EReal)
      ≤ ∑' n, (S n).volume.toEReal := h_cover_bound
    _ ≤ Lebesgue_outer_measure E + (ε / 2 : ℝ) := hS_sum
    _ ≤ Lebesgue_outer_measure E + ε := by
        apply add_le_add_right
        exact_mod_cast (by linarith : ε / 2 ≤ ε)

/-- Направление 2: внешняя мера ограничена элементарной мерой
    (используем: m\*(E) ≤ J\*(E) для ограниченного E, и J\*(E) ≤ hE.measure для элементарного E) -/
lemma outer_measure_le_measure {d : ℕ} (_hd : 0 < d) {E : Set (EuclideanSpace' d)}
    (hE : IsElementary E) : Lebesgue_outer_measure E ≤ (hE.measure : EReal) := by
  -- Шаг 1: внешняя мера Лебега ≤ внешняя мера Жордана (для ограниченных множеств)
  have h_le_jordan : Lebesgue_outer_measure E ≤ Jordan_outer_measure E :=
    Lebesgue_outer_measure_le_Jordan hE.isBounded
  -- Шаг 2: внешняя мера Жордана ≤ элементарная мера (по Jordan_outer_le при E ⊆ E)
  have h_jordan_le : Jordan_outer_measure E ≤ hE.measure :=
    Jordan_outer_le hE (Set.Subset.refl E)
  -- Объединяем: m*(E) ≤ J*(E) ≤ hE.measure (с приведением к EReal)
  calc Lebesgue_outer_measure E
      ≤ Jordan_outer_measure E := h_le_jordan
    _ ≤ hE.measure := by exact_mod_cast h_jordan_le

end IsElementary

/-- Случай размерности 0 для леммы 1.2.6 -/
lemma Lebesgue_outer_measure.elementary_dim_zero (E : Set (EuclideanSpace' 0)) (hE : IsElementary E) :
    Lebesgue_outer_measure E = hE.measure := by
  -- В размерности 0 EuclideanSpace' 0 — одноточечное пространство (только пустая функция Fin 0 → ℝ)
  -- Внешняя мера равна 1 для непустых множеств, 0 для пустого
  rw [Lebesgue_outer_measure_of_dim_zero]
  by_cases hne : E.Nonempty
  · -- Случай : E непусто → E = Set.univ (одноточечный тип), внешняя мера = 1
    simp only [hne, ↓reduceIte]
    -- В размерности 0 любое непустое элементарное множество — это Set.univ (всё пространство одноточечно)
    -- Разбиение состоит из одного прямоугольника, покрывающего univ, с объёмом = пустое
    -- произведение = 1
    -- Значит hE.measure = 1
    -- Нужно показать 1 = hE.measure, то есть hE.measure = 1
    symm
    -- E = Set.univ, поскольку в EuclideanSpace' 0 единственная точка
    have hE_eq_univ : E = Set.univ := by
      ext x
      constructor
      · intro _; exact Set.mem_univ x
      · intro _
        -- Покажем x ∈ E, используя непустоту E и то, что пространство одноточечно
        obtain ⟨y, hy⟩ := hne
        -- В EuclideanSpace' 0 = (Fin 0 → ℝ) все элементы равны (единственная функция из пустого типа)
        have : x = y := by ext i; exact i.elim0
        rw [this]; exact hy
    -- Теперь покажем, что мера Set.univ в размерности 0 равна 1
    -- В размерности 0 у любого прямоугольника B выполняется B.toSet = Set.univ и |B|ᵥ = 1
    -- (пустое произведение)
    -- Строим прямоугольник в размерности 0 и показываем, что его мера равна 1
    let B : Box 0 := ⟨fun i => i.elim0⟩
    have hB_univ : B.toSet = Set.univ := by
      ext x
      simp only [Box.toSet, Set.mem_univ, iff_true]
      intro i; exact i.elim0
    have hB_vol : |B|ᵥ = 1 := by
      simp only [Box.volume, Finset.univ_eq_empty, Finset.prod_empty]
    -- E = Set.univ = B.toSet, поэтому hE.measure = (IsElementary.box B).measure = |B|ᵥ = 1
    have h_eq : hE.measure = (IsElementary.box B).measure := by
      apply IsElementary.measure_eq_of_set_eq
      rw [hE_eq_univ, hB_univ]
    rw [h_eq, IsElementary.measure_of_box, hB_vol]
    rfl
  · -- Случай : E пусто → внешняя мера = 0 = hE.measure
    have hE_empty : E = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp only [hne, if_false]
    -- Нужно: (0 : EReal) = hE.measure
    -- Используем, что E = ∅ влечёт hE.measure = 0
    have h_meas_eq : hE.measure = (IsElementary.empty 0).measure :=
      IsElementary.measure_eq_of_set_eq hE (IsElementary.empty 0) hE_empty
    rw [h_meas_eq, IsElementary.measure_of_empty]
    rfl

-- ========================================================================
-- Конец вспомогательных лемм для леммы 1.2.6
-- ========================================================================
/-- Лемма 1.2.6 (Внешняя мера элементарных множеств).
    Для любого элементарного множества E внешняя мера Лебега равна элементарной мере. -/
theorem Lebesgue_outer_measure.elementary {d : ℕ} (E : Set (EuclideanSpace' d)) (hE : IsElementary E) :
    Lebesgue_outer_measure E = hE.measure := by
  by_cases hd : d = 0
  · -- Случай размерности 0 : тривиальный краевой случай (EuclideanSpace' 0 — одноточечное пространство)
    -- В размерности 0 у всех прямоугольников объём 1, E либо пусто (мера 0), либо равно univ (мера 1)
    subst hd
    -- Этот краевой случай требует аккуратной работы со структурой разбиения в размерности 0
    -- Пока что делегируем вспомогательной лемме
    exact Lebesgue_outer_measure.elementary_dim_zero E hE
  · -- Случай размерности > 0
    push_neg at hd
    have hd' : 0 < d := Nat.pos_of_ne_zero hd
    apply le_antisymm
    · exact IsElementary.outer_measure_le_measure hd' hE
    · exact IsElementary.measure_le_outer_measure hd' hE

/-- Теорема Кантора -/
theorem EuclideanSpace'.uncountable (d : ℕ) (hd : 0 < d) : Uncountable (EuclideanSpace' d) := by
  -- Вкладываем ℝ в EuclideanSpace' d через x ↦ (x, 0, 0, ..., 0)
  let f : ℝ → EuclideanSpace' d := fun x => .toLp 2 (fun i => if i = ⟨0, hd⟩ then x else 0)
  have hf : Function.Injective f := fun x y hxy => by
    have : f x ⟨0, hd⟩ = f y ⟨0, hd⟩ := by have := congrArg (· ⟨0, hd⟩) hxy; exact this
    simp only [f, ↓reduceIte] at this
    exact this
  exact hf.uncountable

/-- Нет несчётной субаддитивности: единичный куб имеет меру 1, но если разложить его на
одноэлементные множества (каждое с мерой 0), сумма равна 0. -/
example {d : ℕ} {hd : 0 < d} : ∃ (S : Type) (E : S → Set (EuclideanSpace' d)), ¬ Lebesgue_outer_measure (⋃ i, E i) ≤ ∑' i, Lebesgue_outer_measure (E i) := by
  use (Box.unit_cube d).toSet
  use fun x => {x.val}
  -- ⋃ x, {x.val} = единичный куб
  have h_union : ⋃ x : (Box.unit_cube d).toSet, ({x.val} : Set (EuclideanSpace' d)) = (Box.unit_cube d).toSet := by
    ext y; simp
  rw [h_union]
  -- m(единичный куб) = 1 через Lebesgue_outer_measure.elementary
  have h_cube : Lebesgue_outer_measure (Box.unit_cube d).toSet = 1 := by
    rw [Lebesgue_outer_measure.elementary _ (IsElementary.box _)]
    simp only [IsElementary.measure_of_box]
    simp only [Box.volume, BoundedInterval.length, BoundedInterval.b, BoundedInterval.a]
    simp
  -- У каждого одноэлементного множества мера 0
  have h_sing : ∀ x : (Box.unit_cube d).toSet, Lebesgue_outer_measure ({x.val} : Set (EuclideanSpace' d)) = 0 := by
    intro x
    exact Countable.Lebesgue_measure hd (Set.countable_singleton x.val)
  -- tsum нулей равна нулю
  have h_sum : ∑' x : (Box.unit_cube d).toSet, Lebesgue_outer_measure ({x.val} : Set (EuclideanSpace' d)) = 0 := by
    simp_rw [h_sing]
    exact tsum_zero
  rw [h_cube, h_sum]
  simp

/- ========================================================================
   Начало вспомогательных лемм для замечания 1.2.8
   ======================================================================== -/

/-- Расстояние на {lean}`EuclideanSpace' 1` равно расстоянию в ℝ через {name}`EuclideanSpace'.equiv_Real` -/
lemma EuclideanSpace'_dist_eq_Real_dist (x y : EuclideanSpace' 1) : 
    dist x y = dist (EuclideanSpace'.equiv_Real x) (EuclideanSpace'.equiv_Real y) := by
  rw [EuclideanSpace.dist_eq, Real.dist_eq]
  simp only [Fin.zero_eta, Real.sqrt_sq_eq_abs, EuclideanSpace'.equiv_Real, Equiv.coe_fn_mk,
    Fin.sum_univ_one, Real.dist_eq, abs_abs]

/-- Прообраз замкнутого интервала \[a,b\] относительно {name}`EuclideanSpace'.equiv_Real` равен
    соответствующему одномерному прямоугольнику (box) -/
lemma preimage_Icc_eq_box (a b : ℝ) : 
    EuclideanSpace'.equiv_Real ⁻¹' Set.Icc a b = (BoundedInterval.Icc a b).toBox.toSet := by
  rw [BoundedInterval.coe_of_box]
  ext x
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · intro hx
    use EuclideanSpace'.equiv_Real x
    exact ⟨hx, Equiv.symm_apply_apply _ _⟩
  · rintro ⟨y, hy, rfl⟩
    simp [Real.equiv_EuclideanSpace', EuclideanSpace'.equiv_Real] at hy ⊢
    exact hy

/-- Геометрический ряд: ∑ ε/2^\{n+1\} = ε -/
lemma tsum_geometric_eps (ε : ℝ) (_hε : 0 < ε) : ∑' n : ℕ, ε / 2^(n+1) = ε := by
  have h_eq : (fun n => ε / 2^(n+1)) = (fun n => ε / 2 * (1/2 : ℝ)^n) := by
    ext n
    have : (2 : ℝ)^(n+1) = 2 * 2^n := by ring
    rw [this]
    field_simp; simp
  rw [h_eq, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  ring

/-- Сумма длин интервалов равна 2ε -/
lemma tsum_interval_lengths (ε : ℝ) (hε : 0 < ε) : ∑' n : ℕ, (2 * ε / 2^(n+1)) = 2 * ε := by
  have h_eq : (fun n => 2 * ε / 2^(n+1)) = (fun n => 2 * (ε / 2^(n+1))) := by
    ext n; ring
  rw [h_eq, tsum_mul_left, tsum_geometric_eps ε hε]

/-- Суммируемость геометрического ряда -/
lemma tsum_interval_summable (ε : ℝ) : Summable (fun n => 2 * ε / 2^(n+1) : ℕ → ℝ) := by
  have h_eq : (fun n => 2 * ε / 2^(n+1)) = (fun n => ε * (1/2 : ℝ)^n) := by
    ext n
    have h_pow : (2 : ℝ)^(n+1) = 2 * 2^n := by ring
    rw [h_pow]; field_simp; ring_nf; simp
  rw [h_eq]
  have h_abs : |(1/2 : ℝ)| < 1 := by
    simp only [abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
    norm_num
  have h_geom : Summable (fun n => (1/2 : ℝ)^n) := summable_geometric_of_abs_lt_one h_abs
  exact h_geom.mul_left ε

namespace Lebesgue_outer_measure

/-- Внешняя мера Лебега замкнутого интервала \[a,b\] равна b - a -/
lemma of_Icc (a b : ℝ) (hab : a ≤ b) : 
    Lebesgue_outer_measure (EuclideanSpace'.equiv_Real ⁻¹' Set.Icc a b) = ((b - a : ℝ) : EReal) := by
  -- [a,b] — единственный прямоугольник (box) в одномерном случае, значит элементарен с мерой b - a
  let B : Box 1 := (BoundedInterval.Icc a b).toBox
  rw [preimage_Icc_eq_box]
  -- B.toSet элементарно (прямоугольник элементарен)
  have h_elem : IsElementary B.toSet := IsElementary.box B
  -- Внешняя мера Лебега элементарного множества равна его элементарной мере
  rw [Lebesgue_outer_measure.elementary B.toSet h_elem]
  -- Элементарная мера прямоугольника равна его объёму
  rw [IsElementary.measure_of_box B]
  -- Объём B = b - a
  unfold Box.volume BoundedInterval.length
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.prod_singleton]
  -- max (b - a) 0 = b - a, поскольку a ≤ b
  rw [max_eq_left (sub_nonneg.mpr hab)]

/-- Мера Лебега открытого интервала ≤ длине (при a < b) -/
lemma of_Ioo_le (a b : ℝ) (h : a < b) : 
    Lebesgue_outer_measure (EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo a b) ≤ ((b - a : ℝ) : EReal) := by
  have hab : a ≤ b := le_of_lt h
  calc Lebesgue_outer_measure (EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo a b)
      ≤ Lebesgue_outer_measure (EuclideanSpace'.equiv_Real ⁻¹' Set.Icc a b) := by
        apply Lebesgue_outer_measure.mono
        apply Set.preimage_mono
        exact Set.Ioo_subset_Icc_self
    _ = (b - a : EReal) := Lebesgue_outer_measure.of_Icc a b hab

end Lebesgue_outer_measure

/-- Монотонность внешней меры Жордана для двух ограниченных множеств -/
lemma Jordan_outer_measure_mono {E F : Set (EuclideanSpace' 1)}
    (hEF : E ⊆ F) (_hF : Bornology.IsBounded F) :
    Jordan_outer_measure E ≤ Jordan_outer_measure F := by
  -- Jordan_outer_measure E = sInf { m | ∃ A elem, E ⊆ A ∧ m = |A| }
  -- Если E ⊆ F и F ⊆ A, то E ⊆ A, значит множество для F — подмножество множества для E
  -- Следовательно sInf для E ≤ sInf для F
  apply csInf_le_csInf
  · -- Множество для E ограничено снизу (нулём, поскольку меры неотрицательны)
    use 0
    intro m hm
    obtain ⟨A, hA, _hEA, hm_eq⟩ := hm
    rw [hm_eq]
    exact hA.measure_nonneg
  · -- Множество для F непусто (поскольку F ограничено, существует элементарное покрытие)
    obtain ⟨A, hA, hFA⟩ := IsElementary.contains_bounded _hF
    exact ⟨hA.measure, A, hA, hFA, rfl⟩
  · -- Множество для F — подмножество множества для E
    intro m hm
    obtain ⟨A, hA, hFA, hm_eq⟩ := hm
    exact ⟨A, hA, Set.Subset.trans hEF hFA, hm_eq⟩


namespace Remark_1_2_8

/-- Рациональные числа в \[0,1\] образуют непустое счётное множество. -/
lemma rationals_unit_interval_nonempty : (Set.Icc (0 : ℝ) 1 ∩ Set.range (fun q : ℚ ↦ (q : ℝ))).Nonempty := by
  use 0
  constructor
  · simp
  · use 0; simp

lemma rationals_unit_interval_countable : (Set.Icc (0 : ℝ) 1 ∩ Set.range (fun q : ℚ ↦ (q : ℝ))).Countable :=
  Set.Countable.mono Set.inter_subset_right (Set.countable_range _)

/-- Функция перечисления рациональных чисел в \[0,1\] -/
noncomputable def q_enum : ℕ → { x : ℝ // x ∈ Set.Icc (0 : ℝ) 1 ∩ Set.range (fun q : ℚ ↦ (q : ℝ)) } :=
  (rationals_unit_interval_countable.exists_surjective rationals_unit_interval_nonempty).choose

lemma q_enum_surj : Function.Surjective q_enum :=
  (rationals_unit_interval_countable.exists_surjective rationals_unit_interval_nonempty).choose_spec

/-- Перечисление рациональных чисел в \[0,1\] как вещественных чисел -/
noncomputable def q (n : ℕ) : ℝ := (q_enum n).val

lemma q_mem (n : ℕ) : q n ∈ Set.Icc (0 : ℝ) 1 ∩ Set.range (fun r : ℚ ↦ (r : ℝ)) :=
  (q_enum n).property

lemma q_in_unit_interval (n : ℕ) : q n ∈ Set.Icc (0 : ℝ) 1 := (q_mem n).1

lemma q_surj : ∀ x ∈ Set.Icc (0 : ℝ) 1 ∩ Set.range (fun r : ℚ ↦ (r : ℝ)), ∃ n, q n = x := by
  intro x hx
  obtain ⟨n, hn⟩ := q_enum_surj ⟨x, hx⟩
  use n
  unfold q
  rw [hn]

/-- Множество-контрпример U: объединение открытых интервалов вокруг рациональных чисел
    в \[0,1\]. U(ε) = ⋃\_\{n:ℕ\} (q\_n - ε/2^\{n+1\}, q\_n + ε/2^\{n+1\}) -/
noncomputable def U_real (ε : ℝ) : Set ℝ :=
  ⋃ n : ℕ, Set.Ioo (q n - ε / 2^(n+1)) (q n + ε / 2^(n+1))

/-- Множество U, поднятое в {lean}`EuclideanSpace' 1` -/
noncomputable def U (ε : ℝ) : Set (EuclideanSpace' 1) :=
  EuclideanSpace'.equiv_Real ⁻¹' (U_real ε)

/-- U\_real открыто (объединение открытых интервалов) -/
lemma U_real_isOpen (ε : ℝ) : IsOpen (U_real ε) := by
  apply isOpen_iUnion
  intro _
  exact isOpen_Ioo

/-- U открыто в {lean}`EuclideanSpace' 1` -/
lemma U_isOpen (ε : ℝ) : IsOpen (U ε) := by
  apply IsOpen.preimage _ (U_real_isOpen ε)
  exact PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) _

/-- Радиус на шаге n -/
noncomputable def radius (ε : ℝ) (n : ℕ) : ℝ := ε / 2^(n+1)

-- lemma radius_pos (ε : ℝ) (hε : 0 < ε) (n : ℕ) : 0 < radius ε n := by
  -- unfold radius
  -- apply div_pos hε
  -- exact pow_pos (by norm_num : (0:ℝ) < 2) (n+1)

/-- U\_real содержится в (-ε, 1+ε) -/
lemma U_real_subset (ε : ℝ) (hε : 0 < ε) : U_real ε ⊆ Set.Ioo (-ε) (1 + ε) := by
  intro x hx
  simp only [U_real, Set.mem_iUnion] at hx
  obtain ⟨n, hn⟩ := hx
  simp only [Set.mem_Ioo] at hn ⊢
  have hq := q_in_unit_interval n
  have hr : radius ε n ≤ ε := by
    unfold radius
    apply div_le_self (le_of_lt hε)
    calc (1 : ℝ) ≤ 2^1 := by norm_num
      _ ≤ 2^(n+1) := by
        apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        omega
  constructor
  · calc -ε ≤ 0 - ε := by linarith
      _ ≤ q n - ε := by linarith [hq.1]
      _ ≤ q n - radius ε n := by linarith
      _ < x := hn.1
  · calc x < q n + radius ε n := hn.2
      _ ≤ q n + ε := by linarith
      _ ≤ 1 + ε := by linarith [hq.2]

/-- U ограничено -/
lemma U_isBounded (ε : ℝ) (hε : 0 < ε) : Bornology.IsBounded (U ε) := by
  have h_subset : U ε ⊆ EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo (-ε) (1 + ε) := by
    apply Set.preimage_mono
    exact U_real_subset ε hε
  apply Bornology.IsBounded.subset _ h_subset
  rw [Metric.isBounded_iff_subset_closedBall 0]
  use max (|(-ε)|) (|1 + ε|) + 1
  intro x hx
  simp only [Set.mem_preimage, Set.mem_Ioo] at hx
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [EuclideanSpace'.norm_eq]
  have hsum : (∑ i : Fin 1, x i ^ 2) = x ⟨0, by omega⟩ ^ 2 := Fin.sum_univ_one _
  rw [hsum, Real.sqrt_sq_eq_abs]
  have h1 : EuclideanSpace'.equiv_Real x = x ⟨0, by omega⟩ := rfl
  have hx' : -ε < x ⟨0, by omega⟩ ∧ x ⟨0, by omega⟩ < 1 + ε := by
    rw [← h1]; exact hx
  have h_bd : |x ⟨0, by omega⟩| ≤ max (|-ε|) (|1 + ε|) := by
    apply abs_le_max_abs_abs <;> linarith [hx'.1, hx'.2]
  linarith

/-- Оценка меры Лебега каждого компонентного интервала -/
lemma component_lebesgue_le (ε : ℝ) (hε : 0 < ε) (n : ℕ) : 
    Lebesgue_outer_measure (EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo (q n - ε / 2^(n+1)) (q n + ε / 2^(n+1)))
    ≤ ((2 * ε / 2^(n+1) : ℝ) : EReal) := by
  have h_rad_pos : 0 < ε / 2^(n+1) := div_pos hε (pow_pos (by norm_num : (0 : ℝ) < 2) (n+1))
  have h_lt : q n - ε / 2^(n+1) < q n + ε / 2^(n+1) := by linarith
  have h_length : (q n + ε / 2^(n+1)) - (q n - ε / 2^(n+1)) = 2 * ε / 2^(n+1) := by ring
  have h1 := Lebesgue_outer_measure.of_Ioo_le (q n - ε / 2^(n+1)) (q n + ε / 2^(n+1)) h_lt
  simp only [h_length] at h1
  exact h1

/-- Замыкание U\_real содержит \[0,1\] (плотность рациональных чисел) -/
lemma U_real_closure_contains_unit_interval (ε : ℝ) (hε : 0 < ε) :
    Set.Icc 0 1 ⊆ closure (U_real ε) := by
  intro x hx
  rw [mem_closure_iff_nhds]
  intro t ht
  -- t — окрестность x, значит содержит шар вокруг x
  rw [Metric.mem_nhds_iff] at ht
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := ht
  -- Найдём рациональное число в [0,1], близкое к x
  have h_rat_exists : ∃ r : ℚ, (r : ℝ) ∈ Set.Icc (0 : ℝ) 1 ∧ |(r : ℝ) - x| < δ := by
    by_cases h : x < δ
    · use 0
      constructor
      · simp only [Rat.cast_zero, Set.mem_Icc, le_refl, zero_le_one, and_self]
      · rw [Rat.cast_zero, zero_sub, abs_neg, abs_of_nonneg hx.1]
        exact h
    · push_neg at h
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (sub_lt_self x hδ_pos)
      use r
      constructor
      · constructor
        · have : (0 : ℝ) ≤ x - δ := by linarith
          linarith
        · linarith [hx.2]
      · rw [abs_sub_comm, abs_sub_lt_iff]
        constructor <;> linarith
  obtain ⟨r, hr_in, hr_close⟩ := h_rat_exists
  -- r входит в Set.range приведения Rat.cast
  have hr_range : (r : ℝ) ∈ Set.range (fun s : ℚ ↦ (s : ℝ)) := ⟨r, rfl⟩
  -- Значит существует n такое, что q n = r
  have hr_inter : (r : ℝ) ∈ Set.Icc (0 : ℝ) 1 ∩ Set.range (fun s : ℚ ↦ (s : ℝ)) := ⟨hr_in, hr_range⟩
  obtain ⟨n, hn⟩ := q_surj r hr_inter
  -- q n = r, и q n входит в U_real (в интервал вокруг самого себя)
  have hqn_in_U : q n ∈ U_real ε := by
    simp only [U_real, Set.mem_iUnion, Set.mem_Ioo]
    use n
    constructor
    · have : 0 < ε / 2^(n+1) := div_pos hε (pow_pos (by norm_num : (0 : ℝ) < 2) (n+1))
      linarith
    · have : 0 < ε / 2^(n+1) := div_pos hε (pow_pos (by norm_num : (0 : ℝ) < 2) (n+1))
      linarith
  -- q n близко к x (поскольку q n = r)
  have hqn_in_ball : q n ∈ Metric.ball x δ := by
    rw [Metric.mem_ball, dist_comm]
    calc dist x (q n) = |x - q n| := Real.dist_eq x (q n)
      _ = |x - r| := by rw [hn]
      _ = |r - x| := abs_sub_comm x r
      _ < δ := hr_close
  -- Значит q n входит в t
  have hqn_in_t : q n ∈ t := hδ_sub hqn_in_ball
  exact ⟨q n, hqn_in_t, hqn_in_U⟩

/-- Единичный интервал \[0,1\] как {name}`BoundedInterval` -/
abbrev unit_interval : BoundedInterval := BoundedInterval.Icc 0 1

/-- Единичный прямоугольник (box) в одномерном случае: \[0,1\], поднятый до {lean}`Box 1` -/
abbrev unit_box_1D : Box 1 := unit_interval.toBox

/-- Единичный интервал как прообраз \[0,1\] равен единичному прямоугольнику -/
lemma unit_interval_eq_box : EuclideanSpace'.equiv_Real ⁻¹' Set.Icc 0 1 = unit_box_1D.toSet :=
  preimage_Icc_eq_box 0 1

/-- Объём единичного прямоугольника равен 1 -/
lemma unit_box_volume : |unit_box_1D|ᵥ = 1 := by
  unfold unit_box_1D unit_interval Box.volume BoundedInterval.length
  norm_num

/-- Внешняя мера Жордана единичного прямоугольника равна 1 -/
lemma Jordan_outer_unit_box : Jordan_outer_measure unit_box_1D.toSet = 1 := by
  have h_elem := IsElementary.box unit_box_1D
  have h_jm := h_elem.jordanMeasurable
  rw [← h_jm.eq_outer]
  rw [JordanMeasurable.mes_of_elementary h_elem]
  rw [IsElementary.measure_of_box unit_box_1D]
  exact unit_box_volume

/-- Замыкание U содержит прообраз \[0,1\] -/
lemma U_closure_contains_unit_box (ε : ℝ) (hε : 0 < ε) :
    unit_box_1D.toSet ⊆ closure (U ε) := by
  -- Ключевая идея: для гомеоморфизма f выполняется closure(f⁻¹(S)) = f⁻¹(closure(S))
  -- Поскольку U ε = equiv_Real⁻¹(U_real ε), а equiv_Real — гомеоморфизм:
  -- closure(U ε) = equiv_Real⁻¹(closure(U_real ε)) ⊇ equiv_Real⁻¹([0,1]) = unit_box_1D
  have h_closure_real := U_real_closure_contains_unit_interval ε hε
  rw [← unit_interval_eq_box]
  intro x hx
  rw [Set.mem_preimage] at hx
  have hx_in_closure : EuclideanSpace'.equiv_Real x ∈ closure (U_real ε) :=
    h_closure_real hx
  rw [mem_closure_iff_nhds] at hx_in_closure ⊢
  intro t ht
  rw [Metric.mem_nhds_iff] at ht
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := ht
  have h_ball_nhd : Metric.ball (EuclideanSpace'.equiv_Real x) δ ∈ nhds (EuclideanSpace'.equiv_Real x) :=
    Metric.ball_mem_nhds _ hδ_pos
  obtain ⟨y, hy_ball, hy_U⟩ := hx_in_closure _ h_ball_nhd
  use EuclideanSpace'.equiv_Real.symm y
  constructor
  · apply hδ_sub
    rw [Metric.mem_ball, EuclideanSpace'_dist_eq_Real_dist, Equiv.apply_symm_apply]
    exact hy_ball
  · simp only [U, Set.mem_preimage, Equiv.apply_symm_apply]
    exact hy_U

/-- Внешняя мера Жордана U ≥ 1.
    Доказательство использует: плотность ℚ → closure(U) ⊇ \[0,1\] →
    Jordan\_outer(U) ≥ Jordan\_outer(\[0,1\]) = 1. -/
lemma U_jordan_outer_ge (ε : ℝ) (hε : 0 < ε) :
    Jordan_outer_measure (U ε) ≥ 1 := by
  -- По JordanMeasurable.outer_measure_of_closure имеем Jordan_outer(closure U) = Jordan_outer(U)
  have h_closure_eq := JordanMeasurable.outer_measure_of_closure (U_isBounded ε hε)
  -- closure(U) ⊇ unit_box, значит по монотонности:
  have h_closure_contains := U_closure_contains_unit_box ε hε
  have h_unit_bound : Jordan_outer_measure unit_box_1D.toSet ≤ Jordan_outer_measure (closure (U ε)) := by
    apply Jordan_outer_measure_mono h_closure_contains
    exact Bornology.IsBounded.closure (U_isBounded ε hε)
  calc 1 = Jordan_outer_measure unit_box_1D.toSet := Jordan_outer_unit_box.symm
    _ ≤ Jordan_outer_measure (closure (U ε)) := h_unit_bound
    _ = Jordan_outer_measure (U ε) := h_closure_eq

/-- Внешняя мера Лебега U ≤ 2ε (счётная субаддитивность).
    U = ⋃\_n (q\_n - ε/2^\{n+1\}, q\_n + ε/2^\{n+1\}), у каждого интервала длина 2ε/2^\{n+1\},
    и ∑ 2ε/2^\{n+1\} = 2ε.

    Структура доказательства:
    1. Выразим U как счётное объединение: U = ⋃\_n E\_n
    2. По счётной субаддитивности (union\_le): m\*(U) ≤ ∑' m\*(E\_n)
    3. Каждая компонента ограничена: m\*(E\_n) ≤ 2ε/2^\{n+1\} (component\_lebesgue\_le)
    4. Геометрическая сумма: ∑' 2ε/2^\{n+1\} = 2ε (tsum\_interval\_lengths)
    5. Сравнение tsum в {name}`EReal`: ∑' m\*(E\_n) ≤ ∑' (2ε/2^\{n+1\}) = 2ε -/
lemma U_lebesgue_le (ε : ℝ) (hε : 0 < ε) :
    Lebesgue_outer_measure (U ε) ≤ ((2 * ε : ℝ) : EReal) := by
  -- U = ⋃_n (компонентные интервалы в EuclideanSpace' 1)
  let E : ℕ → Set (EuclideanSpace' 1) := fun n =>
    EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo (q n - ε / 2^(n+1)) (q n + ε / 2^(n+1))
  -- U ε = ⋃ n, E n
  have h_U_eq : U ε = ⋃ n, E n := by
    ext x
    simp only [U, U_real, Set.mem_preimage, Set.mem_iUnion, E]
  -- По счётной субаддитивности: m*(U) ≤ ∑' n, m*(E n)
  have h_subadditive := Lebesgue_outer_measure.union_le E
  -- У каждой компоненты m*(E n) ≤ 2ε/2^{n+1}
  have h_component_bound : ∀ n, Lebesgue_outer_measure (E n) ≤ ((2 * ε / 2^(n+1) : ℝ) : EReal) :=
    fun n => component_lebesgue_le ε hε n
  -- Оценка суммы: ∑' n, m*(E n) ≤ 2ε
  have h_sum_bound : ∑' n, Lebesgue_outer_measure (E n) ≤ ((2 * ε : ℝ) : EReal) := by
    have h_g_nonneg : ∀ n, 0 ≤ 2 * ε / 2^(n+1) := by
      intro n
      apply div_nonneg (by linarith : 0 ≤ 2 * ε)
      exact pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
    have h_tsum_eq := tsum_interval_lengths ε hε
    rw [← h_tsum_eq]
    -- Внешняя мера Лебега неотрицательна (sInf сумм объёмов прямоугольников ≥ 0)
    have h_f_nonneg : ∀ n, 0 ≤ Lebesgue_outer_measure (E n) := fun n =>
      Lebesgue_outer_measure.nonneg (E n)
    -- Суммируемость геометрического ряда
    have h_summable : Summable (fun n => 2 * ε / 2^(n+1)) := tsum_interval_summable ε
    -- Используем лемму coe_tsum: ↑(∑' g) = ∑' (↑g)
    rw [EReal.coe_tsum_of_nonneg h_g_nonneg h_summable]
    -- Применяем вспомогательную лемму для поточечного сравнения
    exact EReal.tsum_le_coe_tsum_of_forall_le h_f_nonneg h_g_nonneg h_summable h_component_bound
  calc Lebesgue_outer_measure (U ε) = Lebesgue_outer_measure (⋃ n, E n) := by rw [h_U_eq]
    _ ≤ ∑' n, Lebesgue_outer_measure (E n) := h_subadditive
    _ ≤ ((2 * ε : ℝ) : EReal) := h_sum_bound

end Remark_1_2_8
/- ========================================================================
   Конец вспомогательных лемм для замечания 1.2.8
   ======================================================================== -/

/-- Замечание 1.2.8: существует ограниченное открытое множество, не измеримое по Жордану.
    Набросок доказательства: возьмём U = ⋃\_\{n\} (q\_n - ε/2^\{n+1\}, q\_n + ε/2^\{n+1\}), где \{q\_n\}
    перечисляет ℚ ∩ \[0,1\]. U открыто и ограничено. По счётной субаддитивности m\*(U) ≤ 2ε.
    По плотности ℚ closure(U) ⊇ \[0,1\], поэтому m\*,J(U) ≥ 1.
    При ε = 1/3 получаем m\*(U) ≤ 2/3 < 1 ≤ m\*,J(U), что противоречит измеримости по Жордану. -/
example : ∃ (E : Set (EuclideanSpace' 1)), Bornology.IsBounded E ∧
    IsOpen E ∧ ¬ JordanMeasurable E := by
  use Remark_1_2_8.U (1/3)
  refine ⟨Remark_1_2_8.U_isBounded (1/3) (by norm_num),
         Remark_1_2_8.U_isOpen (1/3), ?_⟩
  intro hJM
  -- Шаг 1: внешняя мера Жордана U ≥ 1 (из аргумента плотности)
  have h_outer : Jordan_outer_measure (Remark_1_2_8.U (1/3)) ≥ 1 :=
    Remark_1_2_8.U_jordan_outer_ge (1/3) (by norm_num)
  -- Шаг 2: внешняя мера Лебега U ≤ 2/3 (из счётной субаддитивности)
  have h_lebesgue : Lebesgue_outer_measure (Remark_1_2_8.U (1/3)) ≤ (2/3 : EReal) := by
    have := Remark_1_2_8.U_lebesgue_le (1/3) (by norm_num : (0 : ℝ) < 1/3)
    have h_eq : (2 * (1/3 : ℝ) : EReal) = (2/3 : EReal) := by
      simp only [one_div]
      norm_cast
    calc Lebesgue_outer_measure (Remark_1_2_8.U (1/3)) ≤ 2 * (1/3 : ℝ) := this
      _ = (2/3 : EReal) := h_eq
  -- Шаг 3: внутренняя мера Жордана ≤ 2/3
  -- Ключевая идея: для любого элементарного A ⊆ U выполняется
  -- hA.measure = Lebesgue_outer(A) ≤ Lebesgue_outer(U) ≤ 2/3
  have h_inner_le : Jordan_inner_measure (Remark_1_2_8.U (1/3)) ≤ 2/3 := by
    -- Jordan_inner = sSup { m | ∃ A элементарно, A ⊆ U ∧ m = hA.measure }
    -- Покажем, что 2/3 — верхняя грань
    apply csSup_le
    · -- Множество непусто (пустое множество элементарно и имеет меру 0)
      use 0, ∅, IsElementary.empty 1
      exact ⟨Set.empty_subset _, (IsElementary.measure_of_empty 1).symm⟩
    · -- Покажем, что 2/3 ограничивает все элементы
      intro m ⟨A, hA, hA_sub, hm⟩
      rw [hm]
      -- hA.measure = Lebesgue_outer(A) по лемме 1.2.6
      have h_elem : Lebesgue_outer_measure A = hA.measure :=
        Lebesgue_outer_measure.elementary A hA
      -- Lebesgue_outer(A) ≤ Lebesgue_outer(U) по монотонности
      have h_mono : Lebesgue_outer_measure A ≤ Lebesgue_outer_measure (Remark_1_2_8.U (1/3)) :=
        Lebesgue_outer_measure.mono hA_sub
      -- Объединяем: hA.measure ≤ 2/3
      have h_bound : (hA.measure : EReal) ≤ (2/3 : EReal) := by
        calc (hA.measure : EReal) = Lebesgue_outer_measure A := h_elem.symm
          _ ≤ Lebesgue_outer_measure (Remark_1_2_8.U (1/3)) := h_mono
          _ ≤ (2/3 : EReal) := h_lebesgue
      have h_coe : ((2/3 : ℝ) : EReal) = (2/3 : EReal) := by norm_cast
      rw [← h_coe] at h_bound
      exact EReal.coe_le_coe_iff.mp h_bound
  -- Шаг 4: выводим противоречие
  -- JordanMeasurable означает Jordan_inner = Jordan_outer
  have h_jm_eq : Jordan_inner_measure (Remark_1_2_8.U (1/3)) =
      Jordan_outer_measure (Remark_1_2_8.U (1/3)) := hJM.2
  -- Из Jordan_outer ≥ 1 и Jordan_inner = Jordan_outer: Jordan_inner ≥ 1
  have h_inner_ge : Jordan_inner_measure (Remark_1_2_8.U (1/3)) ≥ 1 := by
    rw [h_jm_eq]; exact h_outer
  -- Противоречие: 1 ≤ Jordan_inner ≤ 2/3 невозможно
  linarith

/-- Замечание 1.2.8: дополнение U в \[-2,2\] компактно, но не измеримо по Жордану. -/
example : ∃ (E : Set (EuclideanSpace' 1)), Bornology.IsBounded E ∧
    IsCompact E ∧ ¬ JordanMeasurable E := by
  -- Пусть B = [-2, 2], поднятое в EuclideanSpace' 1
  let B : Set (EuclideanSpace' 1) := EuclideanSpace'.equiv_Real ⁻¹' Set.Icc (-2) 2
  -- Пусть U — не измеримое по Жордану открытое множество из первой части
  let U := Remark_1_2_8.U (1/3)
  -- E = B \ U компактно, но не измеримо по Жордану
  use B \ U
  refine ⟨?bounded, ?compact, ?not_jm⟩
  case bounded =>
    -- E ⊆ B, а B ограничено
    apply Bornology.IsBounded.subset _ Set.diff_subset
    rw [Metric.isBounded_iff_subset_closedBall 0]
    use 3
    intro x hx
    -- hx : x ∈ B означает equiv_Real x ∈ [-2, 2]
    have hx' : EuclideanSpace'.equiv_Real x ∈ Set.Icc (-2 : ℝ) 2 := hx
    rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace'.norm_eq]
    have hsum : (∑ i : Fin 1, x i ^ 2) = x ⟨0, by omega⟩ ^ 2 := Fin.sum_univ_one _
    rw [hsum, Real.sqrt_sq_eq_abs]
    have h1 : EuclideanSpace'.equiv_Real x = x ⟨0, by omega⟩ := rfl
    simp only [Set.mem_Icc] at hx'
    rw [h1] at hx'
    have : |x ⟨0, by omega⟩| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  case compact =>
    -- B компактно (непрерывный прообраз компакта)
    have hB_compact : IsCompact B := by
      have h_cont : Continuous EuclideanSpace'.equiv_Real := PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) _
      apply Metric.isCompact_of_isClosed_isBounded (isClosed_Icc.preimage h_cont)
      rw [Metric.isBounded_iff_subset_closedBall 0]
      use 3
      intro x hx
      have hx' : EuclideanSpace'.equiv_Real x ∈ Set.Icc (-2 : ℝ) 2 := hx
      rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace'.norm_eq]
      have hsum : (∑ i : Fin 1, x i ^ 2) = x ⟨0, by omega⟩ ^ 2 := Fin.sum_univ_one _
      rw [hsum, Real.sqrt_sq_eq_abs]
      have h1 : EuclideanSpace'.equiv_Real x = x ⟨0, by omega⟩ := rfl
      simp only [Set.mem_Icc] at hx'
      rw [h1] at hx'
      have : |x ⟨0, by omega⟩| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    -- U открыто
    have hU_open : IsOpen U := Remark_1_2_8.U_isOpen (1/3)
    -- B \ U = B ∩ Uᶜ замкнуто в B (поскольку Uᶜ замкнуто)
    have hU_compl_closed : IsClosed Uᶜ := hU_open.isClosed_compl
    -- B \ U компактно (замкнутое подмножество компакта)
    rw [Set.diff_eq]
    exact hB_compact.inter_right hU_compl_closed
  case not_jm =>
    intro hE_jm
    -- B элементарно (это прямоугольник (box)), значит измеримо по Жордану
    have hB_elem : IsElementary B := by
      have : B = (BoundedInterval.Icc (-2) 2).toBox.toSet := preimage_Icc_eq_box (-2) 2
      rw [this]
      exact IsElementary.box _
    have hB_jm : JordanMeasurable B := hB_elem.jordanMeasurable
    -- Если E = B \ U измеримо по Жордану, то U ∩ B = B \ E тоже измеримо по Жордану
    have h_eq : U ∩ B = B \ (B \ U) := by ext; simp [Set.mem_inter_iff]; tauto
    have hUB_jm : JordanMeasurable (U ∩ B) := by
      rw [h_eq]
      exact JordanMeasurable.sdiff hB_jm hE_jm
    -- U ⊆ B (поскольку U ⊆ (-1/3, 4/3) ⊆ [-2, 2])
    have hU_sub_B : U ⊆ B := by
      intro x hx
      have h_sub := Remark_1_2_8.U_real_subset (1/3) (by norm_num : (0 : ℝ) < 1/3)
      -- hx : x ∈ U означает equiv_Real x ∈ U_real
      have hx' : EuclideanSpace'.equiv_Real x ∈ Remark_1_2_8.U_real (1/3) := hx
      have hx_real := h_sub hx'
      simp only [Set.mem_Ioo] at hx_real
      -- Нужно показать x ∈ B, то есть equiv_Real x ∈ [-2, 2]
      show EuclideanSpace'.equiv_Real x ∈ Set.Icc (-2) 2
      simp only [Set.mem_Icc]
      constructor <;> linarith [hx_real.1, hx_real.2]
    -- Значит U ∩ B = U, то есть U измеримо по Жордану
    have hU_eq : U ∩ B = U := Set.inter_eq_self_of_subset_left hU_sub_B
    rw [hU_eq] at hUB_jm
    -- Но мы доказали, что U не измеримо по Жордану (из первого примера)
    have hU_not_jm : ¬ JordanMeasurable U := by
      intro hJM
      have h_outer : Jordan_outer_measure U ≥ 1 :=
        Remark_1_2_8.U_jordan_outer_ge (1/3) (by norm_num)
      have h_lebesgue : Lebesgue_outer_measure U ≤ (2/3 : EReal) := by
        have := Remark_1_2_8.U_lebesgue_le (1/3) (by norm_num : (0 : ℝ) < 1/3)
        have h_eq : (2 * (1/3 : ℝ) : EReal) = (2/3 : EReal) := by simp only [one_div]; norm_cast
        calc Lebesgue_outer_measure U ≤ 2 * (1/3 : ℝ) := this
          _ = (2/3 : EReal) := h_eq
      have h_inner_le : Jordan_inner_measure U ≤ 2/3 := by
        apply csSup_le
        · use 0, ∅, IsElementary.empty 1
          exact ⟨Set.empty_subset _, (IsElementary.measure_of_empty 1).symm⟩
        · intro m ⟨A, hA, hA_sub, hm⟩
          rw [hm]
          have h_elem : Lebesgue_outer_measure A = hA.measure :=
            Lebesgue_outer_measure.elementary A hA
          have h_mono : Lebesgue_outer_measure A ≤ Lebesgue_outer_measure U :=
            Lebesgue_outer_measure.mono hA_sub
          have h_bound : (hA.measure : EReal) ≤ (2/3 : EReal) := by
            calc (hA.measure : EReal) = Lebesgue_outer_measure A := h_elem.symm
              _ ≤ Lebesgue_outer_measure U := h_mono
              _ ≤ (2/3 : EReal) := h_lebesgue
          have h_coe : ((2/3 : ℝ) : EReal) = (2/3 : EReal) := by norm_cast
          rw [← h_coe] at h_bound
          exact EReal.coe_le_coe_iff.mp h_bound
      have h_jm_eq : Jordan_inner_measure U = Jordan_outer_measure U := hJM.2
      have h_inner_ge : Jordan_inner_measure U ≥ 1 := by rw [h_jm_eq]; exact h_outer
      linarith
    exact hU_not_jm hUB_jm

def AlmostDisjoint {d : ℕ} (B B' : Box d) : Prop := interior B.toSet ∩ interior B'.toSet = ∅

-- Вспомогательные леммы для теоремы IsElementary.almost_disjoint
/-- Мера аддитивна на объединениях элементарных множеств с непересекающимися внутренностями:
    μ(E ∪ F) = μ(E) + μ(F). -/
lemma IsElementary.measure_of_almostDisjUnion {d : ℕ} {E F : Set (EuclideanSpace' d)}
    (hE : IsElementary E) (hF : IsElementary F)
    (h : interior E ∩ interior F = ∅) :
    (hE.union hF).measure = hE.measure + hF.measure := by
  -- Стратегия: используем разложение E ∪ F = E ∪ (F \ E), которое непересекающееся,
  -- а затем покажем, что (F \ E).measure = hF.measure, используя, что E ∩ F имеет нулевую
  -- меру, когда внутренности не пересекаются.
  classical
  -- Шаг 1: раскладываем E ∪ F = E ∪ (F \ E) (непересекающееся объединение)
  have h_union_decomp : E ∪ F = E ∪ (F \ E) := by
    ext x
    constructor
    · rintro (hx_E | hx_F)
      · exact Or.inl hx_E
      · by_cases hx_E : x ∈ E
        · exact Or.inl hx_E
        · exact Or.inr ⟨hx_F, hx_E⟩
    · rintro (hx_E | ⟨hx_F, _⟩)
      · exact Or.inl hx_E
      · exact Or.inr hx_F
  -- Шаг 2: F \ E элементарно и не пересекается с E
  have hF_sdiff_E : IsElementary (F \ E) := IsElementary.sdiff hF hE
  have h_disj : Disjoint E (F \ E) := by
    rw [Set.disjoint_iff]
    intro x ⟨hx_E, _, hx_not_E⟩
    exact hx_not_E hx_E
  -- Шаг 3: применяем measure_of_disjUnion
  have h_decomp_measure : (hE.union hF_sdiff_E).measure = hE.measure + hF_sdiff_E.measure :=
    IsElementary.measure_of_disjUnion hE hF_sdiff_E h_disj
  -- Шаг 4: покажем, что оба объединения представляют одно и то же множество
  set T := (hE.union hF).partition.choose
  have hT_disj : (T : Set (Box d)).PairwiseDisjoint Box.toSet := (hE.union hF).partition.choose_spec.1
  have h_eq : E ∪ F = ⋃ B ∈ T, B.toSet := (hE.union hF).partition.choose_spec.2
  have h_measure_eq : (hE.union hF_sdiff_E).measure = (hE.union hF).measure := by
    rw [(hE.union hF_sdiff_E).measure_eq hT_disj (by rw [← h_union_decomp, h_eq]),
        (hE.union hF).measure_eq hT_disj h_eq]
  -- Шаг 5: покажем (F \ E).measure = hF.measure, когда внутренности не пересекаются
  -- Это следует из того, что E ∩ F ⊆ frontier E ∪ frontier F, а пересечение имеет нулевую меру
  have h_sdiff_measure : hF_sdiff_E.measure = hF.measure := by
    -- По монотонности: (F \ E).measure ≤ hF.measure (поскольку F \ E ⊆ F)
    have h_mono : hF_sdiff_E.measure ≤ hF.measure :=
      IsElementary.measure_mono hF_sdiff_E hF (fun _ hx => hx.1)
    -- По аддитивности: hF.measure ≤ (E ∩ F).measure + (F \ E).measure
    -- Но E ∩ F элементарно и имеет пустую внутренность, поэтому мера ≤ 0
    -- Для непересекающихся внутренностей можно показать measure_mono в обратном направлении
    have h_decomp_F : F = (E ∩ F) ∪ (F \ E) := by
      ext x; simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
      constructor
      · intro hx
        by_cases hxE : x ∈ E
        · exact Or.inl ⟨hxE, hx⟩
        · exact Or.inr ⟨hx, hxE⟩
      · rintro (⟨_, hx⟩ | ⟨hx, _⟩) <;> exact hx
    have h_disj_decomp : Disjoint (E ∩ F) (F \ E) := by
      rw [Set.disjoint_iff]
      intro x ⟨⟨hxE, _⟩, _, hxnE⟩
      exact hxnE hxE
    have hEF_inter : IsElementary (E ∩ F) := IsElementary.inter hE hF
    have h_F_measure : hF.measure = (hEF_inter.union hF_sdiff_E).measure := by
      set T_F := hF.partition.choose
      have hT_F_disj : (T_F : Set (Box d)).PairwiseDisjoint Box.toSet := hF.partition.choose_spec.1
      have hF_eq : F = ⋃ B ∈ T_F, B.toSet := hF.partition.choose_spec.2
      rw [(hEF_inter.union hF_sdiff_E).measure_eq hT_F_disj (by rw [← h_decomp_F, hF_eq]),
          hF.measure_eq hT_F_disj hF_eq]
    have h_union_add : (hEF_inter.union hF_sdiff_E).measure = hEF_inter.measure + hF_sdiff_E.measure :=
      IsElementary.measure_of_disjUnion hEF_inter hF_sdiff_E h_disj_decomp
    -- Ключевой факт: покажем hEF_inter.measure = 0, когда interior E ∩ interior F = ∅
    -- Для этого нужно показать, что у элементарных множеств с пустой внутренностью мера нулевая
    have h_inter_empty_interior : interior (E ∩ F) = ∅ := by
      rw [interior_inter, h]
    -- Для элементарного множества с пустой внутренностью все прямоугольники его разбиения
    -- должны быть вырожденными
    have h_inter_measure_zero : hEF_inter.measure = 0 := by
      set T_EF := hEF_inter.partition.choose
      have hT_EF_disj : (T_EF : Set (Box d)).PairwiseDisjoint Box.toSet := hEF_inter.partition.choose_spec.1
      have hEF_eq : E ∩ F = ⋃ B ∈ T_EF, B.toSet := hEF_inter.partition.choose_spec.2
      rw [hEF_inter.measure_eq hT_EF_disj hEF_eq]
      apply Finset.sum_eq_zero
      intro B hB
      -- Покажем, что у B пустая внутренность и, следовательно, объём 0
      have hB_subset : B.toSet ⊆ E ∩ F := by
        rw [hEF_eq]
        exact Set.subset_biUnion_of_mem hB
      have hB_interior_empty : interior B.toSet = ∅ := by
        apply Set.eq_empty_of_subset_empty
        calc interior B.toSet ⊆ interior (E ∩ F) := interior_mono hB_subset
          _ = ∅ := h_inter_empty_interior
      -- Используем, что у прямоугольника с пустой внутренностью объём нулевой
      -- interior B = ∅ означает, что у некоторой стороны пустая внутренность, то есть она —
      -- одна точка или пуста
      -- Для прямоугольника это означает, что у некоторого BoundedInterval выполняется a = b
      -- (вырожденность)
      -- Внутренность прямоугольника пуста тогда и только тогда, когда у некоторого интервала
      -- стороны пустая внутренность
      have hB_empty_or_degenerate : B.toSet = ∅ ∨ ∃ i, interior (B.side i).toSet = ∅ := by
        by_cases hB_nonempty : B.toSet.Nonempty
        · right
          by_contra h_all_nonempty
          push_neg at h_all_nonempty
          have : (Set.univ.pi fun i => interior (B.side i).toSet).Nonempty :=
            Set.univ_pi_nonempty_iff.mpr (fun i => h_all_nonempty i)
          rw [B.interior_toSet] at hB_interior_empty
          exact (this.preimage (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).surjective).ne_empty hB_interior_empty
        · left
          exact Set.not_nonempty_iff_eq_empty.mp hB_nonempty
      rcases hB_empty_or_degenerate with hB_empty | ⟨i, hi⟩
      · exact Box.volume_eq_zero_of_empty B hB_empty
      · -- У BoundedInterval с пустой внутренностью длина 0
        rw [Box.volume]
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        -- Покажем |B.side i|ₗ = 0, когда interior (B.side i).toSet = ∅
        have h_length_zero : |B.side i|ₗ = 0 := by
          cases hI : B.side i with
          | Ioo a b =>
            simp only [hI, BoundedInterval.toSet, interior_Ioo, Set.Ioo_eq_empty_iff] at hi
            simp only [BoundedInterval.length, BoundedInterval.a, BoundedInterval.b]
            have hab : b ≤ a := le_of_not_gt hi
            simp only [max_eq_right (sub_nonpos.mpr hab)]
          | Icc a b =>
            simp only [hI, BoundedInterval.toSet, interior_Icc, Set.Ioo_eq_empty_iff] at hi
            simp only [BoundedInterval.length, BoundedInterval.a, BoundedInterval.b]
            have hab : b ≤ a := le_of_not_gt hi
            simp only [max_eq_right (sub_nonpos.mpr hab)]
          | Ioc a b =>
            simp only [hI, BoundedInterval.toSet, interior_Ioc, Set.Ioo_eq_empty_iff] at hi
            simp only [BoundedInterval.length, BoundedInterval.a, BoundedInterval.b]
            have hab : b ≤ a := le_of_not_gt hi
            simp only [max_eq_right (sub_nonpos.mpr hab)]
          | Ico a b =>
            simp only [hI, BoundedInterval.toSet, interior_Ico, Set.Ioo_eq_empty_iff] at hi
            simp only [BoundedInterval.length, BoundedInterval.a, BoundedInterval.b]
            have hab : b ≤ a := le_of_not_gt hi
            simp only [max_eq_right (sub_nonpos.mpr hab)]
        exact h_length_zero
    -- Теперь объединяем: hF.measure = 0 + hF_sdiff_E.measure = hF_sdiff_E.measure
    rw [h_F_measure, h_union_add, h_inter_measure_zero, zero_add]
  -- Финальный шаг: объединяем всё
  rw [← h_measure_eq, h_decomp_measure, h_sdiff_measure]

/-- Разбить объединение, индексированное {lean}`Fin (n+1)`, на объединение, индексированное
    {lean}`Fin n`, плюс последний элемент. Это общая вспомогательная лемма для индукции по
    конечным объединениям. -/
lemma Fin.iUnion_succ_eq_union_last {α : Type*} {n : ℕ} (f : Fin (n + 1) → Set α) : 
    (⋃ i, f i) = (⋃ i : Fin n, f (Fin.castSucc i)) ∪ f (Fin.last n) := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_union]
  constructor
  · intro ⟨i, hi⟩
    by_cases hlt : (i : ℕ) < n
    · left; exact ⟨⟨i, hlt⟩, by simp [Fin.castSucc]; exact hi⟩
    · right
      have : i = Fin.last n := Fin.ext (Nat.eq_of_lt_succ_of_not_lt i.isLt hlt)
      exact this ▸ hi
  · intro h
    rcases h with ⟨i, hi⟩ | h
    · exact ⟨Fin.castSucc i, hi⟩
    · exact ⟨Fin.last n, h⟩

/-- Когда прямоугольники попарно почти не пересекаются, ограничение на первые n прямоугольников
    сохраняет это свойство. -/
lemma AlmostDisjoint.pairwise_castSucc {d n : ℕ} {B : Fin (n + 1) → Box d}
    (hdisj : Pairwise (Function.onFun AlmostDisjoint B)) : 
    Pairwise (Function.onFun AlmostDisjoint (fun i => B (Fin.castSucc i))) := by
  intro i j hij
  simp only [Function.onFun]
  apply hdisj
  simp [Fin.ext_iff]
  intro heq
  exact hij (Fin.ext heq)

/-- Когда прямоугольники попарно почти не пересекаются, любой из первых n почти не пересекается
    с последним. -/
lemma AlmostDisjoint.castSucc_last {d n : ℕ} {B : Fin (n + 1) → Box d}
    (hdisj : Pairwise (Function.onFun AlmostDisjoint B)) (i : Fin n) : 
    AlmostDisjoint (B (Fin.castSucc i)) (B (Fin.last n)) := by
  apply hdisj
  intro heq
  have h1 : (Fin.castSucc i).val < n := Fin.castSucc_lt_last i
  rw [heq] at h1
  simp at h1

/-- Для любого {name}`BoundedInterval` выполняется interior (closure I) ⊆ closure (interior I).
    Это верно, поскольку у всех типов интервалов ({name}`BoundedInterval.Ioo`,
    {name}`BoundedInterval.Icc`, {name}`BoundedInterval.Ioc`, {name}`BoundedInterval.Ico`)
    closure = {name}`BoundedInterval.Icc`, а interior = {name}`BoundedInterval.Ioo`, поэтому
    interior(closure(I)) = {name}`BoundedInterval.Ioo` ⊆ {name}`BoundedInterval.Icc` =
    closure(interior(I)). -/
lemma BoundedInterval.interior_closure_subset_closure_interior (I : BoundedInterval) : 
    interior (closure (I : Set ℝ)) ⊆ closure (interior (I : Set ℝ)) := by
  cases I with
  | Ioo a b =>
    simp only [BoundedInterval.set_Ioo]
    by_cases hab : a < b
    · simp only [closure_Ioo (ne_of_lt hab), interior_Icc, interior_Ioo]
      exact Set.Ioo_subset_Icc_self
    · simp only [Set.Ioo_eq_empty hab, closure_empty, interior_empty]; exact Set.empty_subset _
  | Icc a b =>
    simp only [BoundedInterval.set_Icc]
    by_cases hab : a < b
    · simp only [closure_Icc, interior_Icc, closure_Ioo (ne_of_lt hab)]
      exact Set.Ioo_subset_Icc_self
    · simp only [interior_Icc, Set.Ioo_eq_empty hab, closure_Icc, closure_empty]
      exact Set.empty_subset _
  | Ioc a b =>
    simp only [BoundedInterval.set_Ioc]
    by_cases hab : a < b
    · simp only [closure_Ioc (ne_of_lt hab), interior_Icc, interior_Ioc, closure_Ioo (ne_of_lt hab)]
      exact Set.Ioo_subset_Icc_self
    · simp only [Set.Ioc_eq_empty hab, closure_empty, interior_empty]; exact Set.empty_subset _
  | Ico a b =>
    simp only [BoundedInterval.set_Ico]
    by_cases hab : a < b
    · simp only [closure_Ico (ne_of_lt hab), interior_Icc, interior_Ico, closure_Ioo (ne_of_lt hab)]
      exact Set.Ioo_subset_Icc_self
    · simp only [Set.Ico_eq_empty hab, closure_empty, interior_empty]; exact Set.empty_subset _

/-- Для любого прямоугольника (box) внутренность его границы пуста. Это верно независимо от
    того, использует ли прямоугольник замкнутые интервалы ({name}`BoundedInterval.Icc`),
    открытые ({name}`BoundedInterval.Ioo`) или полуоткрытые, поскольку граница прямоугольника —
    множество меньшей размерности (объединение граней). -/
lemma Box.interior_frontier_eq_empty {d : ℕ} (B : Box d) : interior (frontier B.toSet) = ∅ := by
  rw [Box.frontier_toSet, ← (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).preimage_interior]
  rw [frontier, closure_pi_set, interior_pi_set Set.finite_univ, Set.diff_eq,
      interior_inter, interior_pi_set Set.finite_univ, interior_compl, closure_pi_set]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  simp only [Set.mem_preimage] at hx
  have ⟨hx1, hx2⟩ := hx
  apply hx2
  exact Set.pi_mono (fun i _ => BoundedInterval.interior_closure_subset_closure_interior _) hx1

/-- Внутренность конечного объединения границ прямоугольников пуста. Это потому, что граница
    каждого прямоугольника — замкнутое множество с пустой внутренностью, и мы можем применить
    {name}`interior_union_isClosed_of_interior_empty` итеративно. -/
lemma interior_iUnion_Box_frontier_eq_empty {d n : ℕ} (B : Fin n → Box d) : 
    interior (⋃ i, frontier (B i).toSet) = ∅ := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Fin.iUnion_succ_eq_union_last, Set.union_comm,
        interior_union_isClosed_of_interior_empty isClosed_frontier]
    · exact Box.interior_frontier_eq_empty (B (Fin.last m))
    · exact ih (fun i => B (Fin.castSucc i))

theorem IsElementary.almost_disjoint {d k : ℕ} {E : Set (EuclideanSpace' d)} (hE : IsElementary E) (B : Fin k → Box d) (hEB : E = ⋃ i, (B i).toSet) (hdisj : Pairwise (Function.onFun AlmostDisjoint B)) : hE.measure = ∑ i, |B i|ᵥ := by
  induction k generalizing E with
  | zero =>
    -- E = ⋃ i : Fin 0, (B i).toSet = ∅, поэтому hE.measure = 0 = ∑ i : Fin 0, ...
    simp_all
  | succ n ih =>
    -- Определяем B' : Fin n → Box d как первые n прямоугольников, а B_last — последний
    let B' : Fin n → Box d := fun i => B (Fin.castSucc i)
    let E' : Set (EuclideanSpace' d) := ⋃ i : Fin n, (B' i).toSet
    let B_last := B (Fin.last n)

    -- Разбиваем E, используя вспомогательную лемму
    have hE_split : E = E' ∪ B_last.toSet := by
      simp only [hEB, E', B', B_last]
      exact Fin.iUnion_succ_eq_union_last (fun i => (B i).toSet)

    -- Покажем, что B' почти не пересекаются, используя вспомогательную лемму
    have hdisj' : Pairwise (Function.onFun AlmostDisjoint B') :=
      AlmostDisjoint.pairwise_castSucc hdisj

    -- E' элементарно (конечное объединение прямоугольников)
    have hE'_elem : IsElementary E' := by
      classical
      have h_eq : E' = ⋃ E ∈ (Finset.univ : Finset (Fin n)).image (fun i => (B' i).toSet), E := by
        ext x
        simp only [E', Set.mem_iUnion, Finset.mem_image, Finset.mem_univ, true_and, exists_prop]
        constructor
        · intro ⟨i, hi⟩; exact ⟨(B' i).toSet, ⟨i, rfl⟩, hi⟩
        · intro ⟨_, ⟨i, rfl⟩, hi⟩; exact ⟨i, hi⟩
      rw [h_eq]
      apply IsElementary.union'
      intro E hE
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hE
      obtain ⟨i, rfl⟩ := hE
      exact IsElementary.box _

    -- Применяем предположение индукции, чтобы получить меру E'
    have hE'_eq : E' = ⋃ i, (B' i).toSet := rfl
    have hE'_measure : hE'_elem.measure = ∑ i : Fin n, (B' i).volume := ih hE'_elem B' hE'_eq hdisj'

    -- B_last элементарно (единственный прямоугольник)
    have hB_last_elem : IsElementary B_last.toSet := IsElementary.box B_last

    -- Каждый B' i почти не пересекается с B_last, используя вспомогательную лемму
    have h_almost_disj_last : ∀ i : Fin n, AlmostDisjoint (B' i) B_last :=
      fun i => AlmostDisjoint.castSucc_last hdisj i

    -- Покажем interior E' ∩ interior B_last = ∅ (почти не пересекаются как множества)
    have h_interior_disj : interior E' ∩ interior B_last.toSet = ∅ := by
      rw [← interior_inter]
      have h_inter_eq : E' ∩ B_last.toSet = ⋃ i : Fin n, ((B' i).toSet ∩ B_last.toSet) := by
        simp only [E', Set.iUnion_inter]
      rw [h_inter_eq]
      -- Докажем, что внутренность объединения пуста
      apply Set.eq_empty_of_forall_notMem
      intro y hy
      rw [mem_interior_iff_mem_nhds] at hy
      obtain ⟨U, hU_sub, hU_open, hy_in_U⟩ := mem_nhds_iff.mp hy
      -- y ∈ interior B_last (поскольку объединение содержится в B_last)
      have hy_int_Blast : y ∈ interior B_last.toSet := by
        apply interior_mono (Set.iUnion_subset fun i => Set.inter_subset_right)
        rw [mem_interior_iff_mem_nhds]
        exact mem_nhds_iff.mpr ⟨U, hU_sub, hU_open, hy_in_U⟩
      -- Определяем U' = U ∩ interior B_last
      let U' := U ∩ interior B_last.toSet
      have hU'_open : IsOpen U' := hU_open.inter isOpen_interior
      have hU'_nonempty : U'.Nonempty := ⟨y, hy_in_U, hy_int_Blast⟩
      -- U' ⊆ ⋃ i, frontier (B' i) (каждая точка лежит в некотором B' i, но не в его внутренности)
      have h_U'_in_frontier : U' ⊆ ⋃ i : Fin n, frontier (B' i).toSet := by
        intro z ⟨hz_U, hz_int_Blast⟩
        have hz_union : z ∈ ⋃ i : Fin n, ((B' i).toSet ∩ B_last.toSet) := hU_sub hz_U
        simp only [Set.mem_iUnion] at hz_union ⊢
        obtain ⟨i, hz_Bi, _⟩ := hz_union
        use i
        rw [frontier_eq_closure_inter_closure]
        refine ⟨subset_closure hz_Bi, ?_⟩
        rw [mem_closure_iff]
        intro V hV_open hz_V
        by_contra h_empty
        push_neg at h_empty
        rw [Set.eq_empty_iff_forall_notMem] at h_empty
        have hV_sub : V ⊆ (B' i).toSet := fun w hw => by
          by_contra h_not_in
          exact h_empty w ⟨hw, h_not_in⟩
        have hz_int_Bi : z ∈ interior (B' i).toSet := by
          rw [mem_interior_iff_mem_nhds]
          exact Filter.mem_of_superset (hV_open.mem_nhds hz_V) hV_sub
        have h_disj := h_almost_disj_last i
        rw [AlmostDisjoint, Set.eq_empty_iff_forall_notMem] at h_disj
        exact h_disj z ⟨hz_int_Bi, hz_int_Blast⟩
      -- Используем вспомогательную лемму: у конечного объединения границ прямоугольников
      -- пустая внутренность
      have h_union_empty_int : interior (⋃ i : Fin n, frontier (B' i).toSet) = ∅ :=
        interior_iUnion_Box_frontier_eq_empty B'
      -- U' ⊆ множеству с пустой внутренностью, но U' — непустое открытое множество. Противоречие!
      have : interior U' ⊆ interior (⋃ i : Fin n, frontier (B' i).toSet) := interior_mono h_U'_in_frontier
      rw [h_union_empty_int] at this
      exact Set.not_nonempty_empty ((Set.eq_empty_of_subset_empty this).symm ▸ (hU'_open.interior_eq ▸ hU'_nonempty))

    -- Применяем аддитивность меры для почти непересекающихся множеств
    have h_union_elem : IsElementary (E' ∪ B_last.toSet) := hE'_elem.union hB_last_elem
    have h_measure_add : h_union_elem.measure = hE'_elem.measure + hB_last_elem.measure :=
      IsElementary.measure_of_almostDisjUnion hE'_elem hB_last_elem h_interior_disj
    have h_measure_eq : hE.measure = h_union_elem.measure :=
      IsElementary.measure_eq_of_set_eq hE h_union_elem hE_split
    have h_B_last_measure : hB_last_elem.measure = B_last.volume :=
      IsElementary.measure_of_box B_last

    -- Итоговое вычисление
    rw [Fin.sum_univ_castSucc, h_measure_eq, h_measure_add, hE'_measure, h_B_last_measure]

/-- Ограничение попарной почти-непересекаемости с ℕ на {lean}`Fin N` сохраняет это свойство. -/
lemma AlmostDisjoint.restrict_fin {d : ℕ} {B : ℕ → Box d}
    (h : Pairwise (Function.onFun AlmostDisjoint B)) (N : ℕ) : 
    Pairwise (Function.onFun AlmostDisjoint (fun i : Fin N => B i.val)) := by
  intro i j hij
  simp only [Function.onFun]
  apply h
  intro heq
  exact hij (Fin.ext heq)

/-- Для неотрицательных вещественных последовательностей, если все частичные суммы ≤ c
    (граница {name}`EReal`), то {name}`tsum` ≤ c. Это обратное направление
    {name}`EReal.finset_sum_le_tsum`. -/
lemma EReal.tsum_le_of_sum_range_le {f : ℕ → ℝ} {c : EReal}
    (hf : ∀ n, 0 ≤ f n) (h : ∀ N, (∑ i ∈ Finset.range N, f i : EReal) ≤ c) :
    ∑' n, (f n).toEReal ≤ c := by
  -- Переходим в ENNReal, где доступна tsum_le_of_sum_range_le
  let g : ℕ → ENNReal := fun n => ENNReal.ofReal (f n)
  -- Покажем (f n).toEReal = (g n : EReal)
  have hf_eq : ∀ n, (f n).toEReal = (g n : EReal) := fun n => by
    simp only [g, EReal.coe_ennreal_ofReal, max_eq_left (hf n)]
  -- Переписываем tsum, используя равенство слагаемых
  have h_tsum_eq : ∑' n, (f n).toEReal = (∑' n, g n : ENNReal).toEReal := by
    have h1 : ∑' n, (f n).toEReal = ∑' n, (g n : EReal) := tsum_congr hf_eq
    have h2 : ∑' n, (g n : EReal) = (∑' n, g n : ENNReal).toEReal := by
      let φ : ENNReal →+ EReal := {
        toFun := (↑·)
        map_zero' := by simp
        map_add' := EReal.coe_ennreal_add
      }
      have h_map : φ (∑' n, g n) = ∑' n, φ (g n) :=
        Summable.map_tsum (f := g) ENNReal.summable φ continuous_coe_ennreal_ereal
      exact h_map.symm
    exact h1.trans h2
  rw [h_tsum_eq]
  -- Если c = ⊤, тривиально верно
  by_cases hc : c = ⊤
  · rw [hc]; exact le_top
  -- c ≥ 0, поскольку c ограничивает неотрицательные частичные суммы
  have hc_nn : 0 ≤ c := by
    have h0 : (∑ i ∈ Finset.range 0, f i : EReal) ≤ c := h 0
    simp at h0; exact h0
  -- Получаем оценки частичных сумм в ENNReal
  have h_enn : ∀ N, ∑ i ∈ Finset.range N, g i ≤ c.toENNReal := by
    intro N
    have h_sum_eq : (∑ i ∈ Finset.range N, g i : ENNReal).toEReal = (∑ i ∈ Finset.range N, f i : EReal) := by
      rw [EReal.coe_ennreal_finset_sum]
      exact Finset.sum_congr rfl (fun n _ => (hf_eq n).symm)
    have h_le : (∑ i ∈ Finset.range N, g i : ENNReal).toEReal ≤ c := by rw [h_sum_eq]; exact h N
    rw [← EReal.coe_toENNReal hc_nn] at h_le
    exact EReal.coe_ennreal_le_coe_ennreal_iff.mp h_le
  have h_tsum_enn : ∑' n, g n ≤ c.toENNReal := ENNReal.tsum_le_of_sum_range_le h_enn
  -- Возвращаемся обратно: ↑(∑' g) ≤ ↑(c.toENNReal), и c.toENNReal.toEReal = c (при 0 ≤ c)
  have h_coe_le : (∑' n, g n : ENNReal).toEReal ≤ (c.toENNReal).toEReal :=
    EReal.coe_ennreal_le_coe_ennreal_iff.mpr h_tsum_enn
  calc (∑' n, g n : ENNReal).toEReal ≤ (c.toENNReal).toEReal := h_coe_le
    _ = c := EReal.coe_toENNReal hc_nn

/-- Лемма 1.2.9 (Внешняя мера счётных объединений почти непересекающихся прямоугольников).
    Для попарно почти непересекающихся прямоугольников m*(⋃ Bᵢ) = ∑' m*(Bᵢ) = ∑' |Bᵢ|. -/
theorem Lebesgue_outer_measure.union_of_almost_disjoint {d : ℕ} {B : ℕ → Box d} (h : Pairwise (Function.onFun AlmostDisjoint B)) :
    Lebesgue_outer_measure (⋃ i, (B i).toSet) = ∑' i, Lebesgue_outer_measure (B i).toSet := by
  -- Упрощаем: m*(Bᵢ) = |Bᵢ| для каждого прямоугольника (лемма 1.2.6 + measure_of_box)
  have h_box_measure : ∀ i, Lebesgue_outer_measure (B i).toSet = (B i).volume.toEReal := by
    intro i
    rw [Lebesgue_outer_measure.elementary _ (IsElementary.box (B i)),
        IsElementary.measure_of_box]
  simp_rw [h_box_measure]
  -- Доказательство устанавливает равенство, показывая ≤ и ≥
  apply le_antisymm
  -- Верхняя оценка: m*(⋃ Bᵢ) ≤ ∑' |Bᵢ| по счётной субаддитивности
  · calc Lebesgue_outer_measure (⋃ i, (B i).toSet)
        ≤ ∑' i, Lebesgue_outer_measure (B i).toSet := Lebesgue_outer_measure.union_le _
      _ = ∑' i, (B i).volume.toEReal := by simp_rw [h_box_measure]
  -- Нижняя оценка: ∑' |Bᵢ| ≤ m*(⋃ Bᵢ) через предел конечных частичных сумм
  · -- Для каждого N конечное объединение ⋃ i : Fin N, (B i) содержится в ⋃ i, (B i)
    -- Значит m*(⋃ i : Fin N, (B i)) ≤ m*(⋃ i, (B i)) по монотонности
    -- А m*(⋃ i : Fin N, (B i)) = ∑ i : Fin N, |B i| по IsElementary.almost_disjoint
    -- Переход к пределу N → ∞ даёт результат

    -- Шаг 1: для каждого N покажем, что конечная частичная сумма ≤ внешней мере
    have h_finite_le : ∀ N : ℕ, (∑ i : Fin N, (B i.val).volume : EReal) ≤
        Lebesgue_outer_measure (⋃ i, (B i).toSet) := by
      intro N
      -- Конечное объединение содержится в счётном объединении
      have h_subset : (⋃ i : Fin N, (B i.val).toSet) ⊆ (⋃ i, (B i).toSet) := by
        apply Set.iUnion_subset
        intro i
        exact Set.subset_iUnion (fun n => (B n).toSet) i.val
      -- По монотонности: m*(конечное объединение) ≤ m*(счётное объединение)
      have h_mono := Lebesgue_outer_measure.mono h_subset
      -- Конечное объединение элементарно (объединение прямоугольников)
      have hElem : IsElementary (⋃ i : Fin N, (B i.val).toSet) :=
        IsElementary.iUnion_boxes (fun i : Fin N => B i.val)
      -- m*(конечное объединение) = m(конечное объединение), поскольку оно элементарно
      have h_elem_eq : Lebesgue_outer_measure (⋃ i : Fin N, (B i.val).toSet) = hElem.measure :=
        Lebesgue_outer_measure.elementary _ hElem
      -- Попарная почти-непересекаемость для Fin N
      have h_pw : Pairwise (Function.onFun AlmostDisjoint (fun i : Fin N => B i.val)) :=
        AlmostDisjoint.restrict_fin h N
      -- m(конечное объединение) = ∑ |B i| по IsElementary.almost_disjoint
      have h_sum_eq : hElem.measure = ∑ i : Fin N, (B i.val).volume :=
        IsElementary.almost_disjoint hElem (fun i : Fin N => B i.val) rfl h_pw
      have h_coe_sum : (∑ i : Fin N, (B i.val).volume : EReal) = (∑ i : Fin N, (B i.val).volume : ℝ).toEReal := by
        rw [EReal.coe_finset_sum (fun i _ => Box.volume_nonneg (B i.val))]
      calc (∑ i : Fin N, (B i.val).volume : EReal)
          = ((∑ i : Fin N, (B i.val).volume : ℝ) : EReal) := h_coe_sum
        _ = (hElem.measure : EReal) := by rw [h_sum_eq]
        _ = Lebesgue_outer_measure (⋃ i : Fin N, (B i.val).toSet) := h_elem_eq.symm
        _ ≤ Lebesgue_outer_measure (⋃ i, (B i).toSet) := h_mono

    -- Шаг 2: переходим к пределу — преобразуем сумму по Fin N в сумму по Finset.range N и
    -- используем лемму для EReal
    have h_range_le : ∀ N : ℕ, (∑ i ∈ Finset.range N, (B i).volume : EReal) ≤
        Lebesgue_outer_measure (⋃ i, (B i).toSet) := by
      intro N
      have h_eq : (∑ i ∈ Finset.range N, ((B i).volume : EReal)) = (∑ i : Fin N, ((B i.val).volume : EReal)) := by
        conv_lhs => rw [← Fin.sum_univ_eq_sum_range (fun i => ((B i).volume : EReal)) N]
      rw [h_eq]
      exact h_finite_le N

    -- Шаг 3: применяем EReal.tsum_le_of_sum_range_le
    exact EReal.tsum_le_of_sum_range_le (fun n => Box.volume_nonneg (B n)) h_range_le

theorem Lebesgue_outer_measure.univ {d : ℕ} {hd : 0 < d} : Lebesgue_outer_measure (Set.univ : Set (EuclideanSpace' d)) = ⊤ := by
  -- Стратегия: покажем m*(univ) ≥ N для любого N, взяв N непересекающихся единичных
  -- прямоугольников, откуда m*(univ) = ⊤

  -- Определяем единичный прямоугольник в точке целочисленной решётки a
  let UnitBox : (Fin d → ℤ) → Box d := fun a => { side := fun i => Icc (a i : ℝ) ((a i : ℝ) + 1) }

  -- У каждого единичного прямоугольника объём 1
  have h_vol : ∀ a : Fin d → ℤ, (UnitBox a).volume = 1 := by
    intro a
    simp only [Box.volume, UnitBox]
    simp only [BoundedInterval.length, BoundedInterval.b, BoundedInterval.a]
    simp only [add_sub_cancel_left]
    simp only [max_eq_left (by norm_num : (0 : ℝ) ≤ 1)]
    simp only [Finset.prod_const_one]

  -- У единичных прямоугольников в разных узлах решётки непересекающиеся внутренности
  have h_almost_disj : ∀ a b : Fin d → ℤ, a ≠ b → AlmostDisjoint (UnitBox a) (UnitBox b) := by
    intro a b hab
    simp only [AlmostDisjoint]
    -- Внутренность прямоугольника Icc — это прямоугольник Ioo
    have h_int : ∀ c : Fin d → ℤ, interior (UnitBox c).toSet =
        {x | ∀ i, x i ∈ Set.Ioo (c i : ℝ) ((c i : ℝ) + 1)} := by
      intro c
      rw [Box.interior_toSet]
      ext x; simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
        Set.mem_setOf_eq, UnitBox, BoundedInterval.toSet, interior_Icc]; rfl
    rw [h_int a, h_int b]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro ha hb
    apply hab
    funext i
    -- ha говорит: ∀ j, x j ∈ Ioo (a j) (a j + 1)
    -- Значит для координаты i: a i < x i < a i + 1, то есть ⌊x i⌋ = a i
    have hai : x i ∈ Set.Ioo (a i : ℝ) ((a i : ℝ) + 1) := ha i
    have hbi : x i ∈ Set.Ioo (b i : ℝ) ((b i : ℝ) + 1) := hb i
    rw [Set.mem_Ioo] at hai hbi
    have ha_floor : (⌊x i⌋ : ℤ) = a i := by
      apply Int.floor_eq_iff.mpr
      constructor
      · exact_mod_cast hai.1.le
      · exact_mod_cast hai.2
    have hb_floor : (⌊x i⌋ : ℤ) = b i := by
      apply Int.floor_eq_iff.mpr
      constructor
      · exact_mod_cast hbi.1.le
      · exact_mod_cast hbi.2
    exact ha_floor.symm.trans hb_floor

  -- Для любого N берём N непересекающихся единичных прямоугольников (с первой координатой
  -- 0,..,N-1, остальные координаты — 0)
  have h_arb_large : ∀ N : ℕ, (N : EReal) ≤ Lebesgue_outer_measure (Set.univ : Set (EuclideanSpace' d)) := by
    intro N
    -- Определяем N единичных прямоугольников в точках (0,0,...), (1,0,...), ..., (N-1,0,...)
    let pts : Fin N → (Fin d → ℤ) := fun n => fun i =>
      if i = ⟨0, hd⟩ then (n : ℤ) else 0
    -- Эти точки все различны
    have h_pts_inj : Function.Injective pts := by
      intro m n hmn
      have : pts m ⟨0, hd⟩ = pts n ⟨0, hd⟩ := by rw [hmn]
      simp only [pts, ↓reduceIte] at this
      exact Fin.ext (Int.ofNat_injective this)
    -- Объединение этих N единичных прямоугольников содержится в univ
    have h_subset : (⋃ n : Fin N, (UnitBox (pts n)).toSet) ⊆ Set.univ := Set.subset_univ _
    -- По монотонности
    -- Прямоугольники попарно почти не пересекаются
    have h_pw : Pairwise (Function.onFun AlmostDisjoint (fun n : Fin N => UnitBox (pts n))) := by
      intro i j hij
      simp only [Function.onFun]
      apply h_almost_disj
      intro heq
      exact hij (h_pts_inj heq)
    -- Применяем IsElementary.almost_disjoint для конечных объединений
    have hElem : IsElementary (⋃ n : Fin N, (UnitBox (pts n)).toSet) :=
      IsElementary.iUnion_boxes (fun n => UnitBox (pts n))

    -- N = ∑ |UnitBox|, поскольку у каждого объём 1
    have h_sum_vol : (∑ n : Fin N, (UnitBox (pts n)).volume) = N := by
      simp only [h_vol, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one]

    -- ∑ объёмов = мера объединения (по IsElementary.almost_disjoint)
    have h_elem_eq : hElem.measure = ∑ n : Fin N, (UnitBox (pts n)).volume :=
      IsElementary.almost_disjoint hElem (fun n => UnitBox (pts n)) rfl h_pw

    calc (N : EReal)
        = ((N : ℕ) : ℝ) := (EReal.coe_coe_eq_natCast N).symm
      _ = ↑(∑ n : Fin N, (UnitBox (pts n)).volume) := by rw [h_sum_vol]
      _ = ↑hElem.measure := by rw [h_elem_eq]
      _ = Lebesgue_outer_measure (⋃ n : Fin N, (UnitBox (pts n)).toSet) := by
          rw [← Lebesgue_outer_measure.elementary _ hElem]
      _ ≤ Lebesgue_outer_measure (Set.univ : Set (EuclideanSpace' d)) :=
          Lebesgue_outer_measure.mono h_subset

  -- Поскольку m*(univ) ≥ N для всех N, имеем m*(univ) = ⊤
  rw [EReal.eq_top_iff_forall_lt]
  intro r
  -- Находим N > r
  obtain ⟨N, hN⟩ := exists_nat_gt r
  calc (r : EReal) < (N : ℝ) := EReal.coe_lt_coe hN
    _ = (N : EReal) := EReal.coe_coe_eq_natCast N
    _ ≤ Lebesgue_outer_measure (Set.univ : Set (EuclideanSpace' d)) := h_arb_large N

/-- Замечание 1.2.10 -/
theorem Box.sum_volume_eq {d : ℕ} (B B' : ℕ → Box d) (hdisj : Pairwise (Function.onFun AlmostDisjoint B)) (hdisj' : Pairwise (Function.onFun AlmostDisjoint B')) (hcover : (⋃ n, (B n).toSet) = (⋃ n, (B' n).toSet)) :
    ∑' n, (B n).volume = ∑' n, (B' n).volume := by
  -- Устанавливаем равенство внешних мер через union_of_almost_disjoint (лемма 1.2.9)
  have hB := Lebesgue_outer_measure.union_of_almost_disjoint hdisj
  have hB' := Lebesgue_outer_measure.union_of_almost_disjoint hdisj'
  -- Упрощаем: m*(Bᵢ) = |Bᵢ|.toEReal для каждого прямоугольника
  have h_box : ∀ i, Lebesgue_outer_measure (B i).toSet = (B i).volume.toEReal := by
    intro i
    rw [Lebesgue_outer_measure.elementary _ (IsElementary.box _), IsElementary.measure_of_box]
  have h_box' : ∀ i, Lebesgue_outer_measure (B' i).toSet = (B' i).volume.toEReal := by
    intro i
    rw [Lebesgue_outer_measure.elementary _ (IsElementary.box _), IsElementary.measure_of_box]
  simp_rw [h_box] at hB
  simp_rw [h_box'] at hB'
  -- Теперь: ∑' |B n|.toEReal = m*(⋃ B n) = m*(⋃ B' n) = ∑' |B' n|.toEReal
  have h_eq : (∑' n, ((B n).volume : EReal)) = (∑' n, ((B' n).volume : EReal)) := by
    rw [← hB, hcover, hB']
  -- Определяем версии в ENNReal и работаем через ENNReal
  have h_vol_nn : ∀ n, 0 ≤ (B n).volume := fun n => Box.volume_nonneg _
  have h_vol_nn' : ∀ n, 0 ≤ (B' n).volume := fun n => Box.volume_nonneg _
  let f : ℕ → ENNReal := fun n => ENNReal.ofReal (B n).volume
  let f' : ℕ → ENNReal := fun n => ENNReal.ofReal (B' n).volume
  -- Ключевой факт: (B n).volume.toEReal = (f n : EReal) для неотрицательных объёмов
  have hf_eq : ∀ n, ((B n).volume : EReal) = (f n : EReal) := fun n => by
    simp only [f, EReal.coe_ennreal_ofReal, max_eq_left (h_vol_nn n)]
  have hf'_eq : ∀ n, ((B' n).volume : EReal) = (f' n : EReal) := fun n => by
    simp only [f', EReal.coe_ennreal_ofReal, max_eq_left (h_vol_nn' n)]
  -- Переписываем h_eq через ENNReal
  simp_rw [hf_eq, hf'_eq] at h_eq
  -- tsum в ENNReal коммутирует с приведением к EReal
  have h_ennreal_eq : (∑' n, f n : ENNReal) = ∑' n, f' n := by
    have h_coe : ∀ (g : ℕ → ENNReal), (∑' n, g n : ENNReal).toEReal = ∑' n, (g n : EReal) := by
      intro g
      let φ : ENNReal →+ EReal := {
        toFun := (↑·)
        map_zero' := by simp
        map_add' := EReal.coe_ennreal_add
      }
      exact Summable.map_tsum ENNReal.summable φ continuous_coe_ennreal_ereal
    rw [← h_coe f, ← h_coe f'] at h_eq
    exact EReal.coe_ennreal_eq_coe_ennreal_iff.mp h_eq
  -- Переносим обратно в ℝ через ENNReal.toReal
  have h_toReal_eq : (∑' n, f n).toReal = (∑' n, f' n).toReal := by rw [h_ennreal_eq]
  -- Используем ENNReal.tsum_toReal_eq для функций с конечными значениями
  have hf_ne_top : ∀ n, f n ≠ ⊤ := fun n => ENNReal.ofReal_ne_top
  have hf'_ne_top : ∀ n, f' n ≠ ⊤ := fun n => ENNReal.ofReal_ne_top
  rw [ENNReal.tsum_toReal_eq hf_ne_top, ENNReal.tsum_toReal_eq hf'_ne_top] at h_toReal_eq
  -- Упрощаем: (ENNReal.ofReal x).toReal = x при x ≥ 0
  simp only [f, f', ENNReal.toReal_ofReal (h_vol_nn _), ENNReal.toReal_ofReal (h_vol_nn' _)] at h_toReal_eq
  exact h_toReal_eq

/-- Упражнение 1.2.5: для любого множества, равного счётному объединению почти непересекающихся
    прямоугольников, внешняя мера Лебега равна внутренней мере Жордана. -/
theorem Lebesgue_outer_measure.eq_Jordan_inner_of_boxes {d : ℕ} (E : Set (EuclideanSpace' d)) (B : ℕ → Box d)
    (hE : E = ⋃ n, (B n).toSet) (hdisj : Pairwise (Function.onFun AlmostDisjoint B)) : 
    Lebesgue_outer_measure E = Jordan_inner_measure E := by
  sorry

def IsCube {d : ℕ} (B : Box d) : Prop := ∃ r, ∀ i, |B.side i|ₗ = r

noncomputable def DyadicCube {d : ℕ} (n : ℤ) (a : Fin d → ℤ) : Box d := { side := fun i ↦ Icc (a i/2^n) ((a i + 1)/2^n) }

lemma DyadicCube.isCube {d : ℕ} (n : ℤ) (a : Fin d → ℤ) : IsCube (DyadicCube n a) := by
  -- У всех сторон длина 1/2^n
  use |2^(-n : ℤ)|
  intro i
  simp only [DyadicCube, BoundedInterval.length, BoundedInterval.b, BoundedInterval.a]
  -- Покажем ((a i + 1)/2^n - a i/2^n) = 1/2^n
  have h : (↑(a i) + 1) / (2 : ℝ) ^ n - ↑(a i) / (2 : ℝ) ^ n = (2 : ℝ) ^ (-n) := by
    simp only [zpow_neg, ← sub_div]; norm_cast; simp [add_sub_cancel_left]
  rw [h]
  simp only [max_eq_left (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-n))]
  exact (abs_of_nonneg (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-n))).symm

def Box.IsDyadicAtScale {d : ℕ} (B : Box d) (n : ℤ) : Prop := ∃ a : Fin d → ℤ, B = DyadicCube n a

def Box.IsDyadic {d : ℕ} (B : Box d) : Prop := ∃ n : ℕ, B.IsDyadicAtScale n

/-- У диадических прямоугольников все стороны — замкнутые интервалы ({name}`BoundedInterval.Icc`). -/
lemma Box.IsDyadic.all_sides_Icc {d : ℕ} {B : Box d} (hB : B.IsDyadic) : 
    ∀ i, ∃ a b, B.side i = BoundedInterval.Icc a b := by
  obtain ⟨n, ⟨a, rfl⟩⟩ := hB
  intro i
  use a i / 2^n, (a i + 1) / 2^n
  rfl

-- Вспомогательные леммы для леммы 1.2.11
namespace DyadicCube
/-- Длина стороны диадического куба на масштабе n равна 2^(-n). -/
lemma sidelength {d : ℕ} (n : ℤ) (a : Fin d → ℤ) (i : Fin d) : 
    |(DyadicCube n a).side i|ₗ = (2 : ℝ)^(-n) := by
  simp only [DyadicCube, BoundedInterval.length, BoundedInterval.b, BoundedInterval.a]
  have h : (↑(a i) + 1) / (2 : ℝ) ^ n - ↑(a i) / (2 : ℝ) ^ n = (2 : ℝ) ^ (-n) := by
    simp only [zpow_neg, ← sub_div]; norm_cast; simp [add_sub_cancel_left]
  rw [h, max_eq_left (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-n))]

/-- Диадические кубы на масштабе n ≥ 0 имеют длину стороны не более 1. -/
lemma sidelength_le_one {d : ℕ} {n : ℕ} (a : Fin d → ℤ) (i : Fin d) : 
    |(DyadicCube (n : ℤ) a).side i|ₗ ≤ 1 := by
  rw [DyadicCube.sidelength]
  have h1 : (1 : ℝ) ≤ 2^n := by
    calc (1 : ℝ) = 2^(0 : ℕ) := by norm_num
      _ ≤ 2^n := pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) (Nat.zero_le n)
  calc (2 : ℝ)^(-(n : ℤ)) = 1 / 2^n := by rw [zpow_neg, zpow_natCast]; ring
    _ ≤ 1 / 1 := by apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) h1
    _ = 1 := by norm_num

/-- Внутренность диадического куба. -/
lemma interior {d : ℕ} (n : ℤ) (a : Fin d → ℤ) : 
    interior (DyadicCube n a).toSet =
    {x | ∀ i, x i ∈ Set.Ioo ((a i : ℝ) / 2^n) (((a i : ℝ) + 1) / 2^n)} := by
  rw [Box.interior_toSet]
  ext x; simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_setOf_eq, DyadicCube, BoundedInterval.toSet, interior_Icc]; rfl

/-- У диадических кубов одного масштаба с разными индексами непересекающиеся внутренности. -/
lemma almost_disjoint_same_scale {d : ℕ} {n : ℤ} {a b : Fin d → ℤ} (hab : a ≠ b) : 
    AlmostDisjoint (DyadicCube n a) (DyadicCube n b) := by
  simp only [AlmostDisjoint]
  rw [DyadicCube.interior, DyadicCube.interior]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro ha hb
  apply hab
  funext i
  have hai : x i ∈ Set.Ioo ((a i : ℝ) / 2^n) (((a i : ℝ) + 1) / 2^n) := ha i
  have hbi : x i ∈ Set.Ioo ((b i : ℝ) / 2^n) (((b i : ℝ) + 1) / 2^n) := hb i
  rw [Set.mem_Ioo] at hai hbi
  -- Оба интервала содержат x i, поэтому a i = b i
  have h2n_pos : (0 : ℝ) < 2^n := zpow_pos (by norm_num : (0 : ℝ) < 2) n
  have ha_floor : ⌊x i * 2^n⌋ = a i := by
    apply Int.floor_eq_iff.mpr
    constructor
    · calc (a i : ℝ) = (a i : ℝ) / 2^n * 2^n := by field_simp
        _ ≤ x i * 2^n := by nlinarith [hai.1]
    · calc x i * 2^n < ((a i : ℝ) + 1) / 2^n * 2^n := by nlinarith [hai.2]
        _ = (a i : ℝ) + 1 := by field_simp
  have hb_floor : ⌊x i * 2^n⌋ = b i := by
    apply Int.floor_eq_iff.mpr
    constructor
    · calc (b i : ℝ) = (b i : ℝ) / 2^n * 2^n := by field_simp
        _ ≤ x i * 2^n := by nlinarith [hbi.1]
    · calc x i * 2^n < ((b i : ℝ) + 1) / 2^n * 2^n := by nlinarith [hbi.2]
        _ = (b i : ℝ) + 1 := by field_simp
  exact ha_floor.symm.trans hb_floor

/-- Диадические кубы на масштабе n покрывают всё ℝᵈ. -/
lemma cover_univ {d : ℕ} (n : ℤ) : 
    (⋃ (a : Fin d → ℤ), (DyadicCube n a).toSet) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  use fun i => ⌊x i * 2^n⌋
  intro i
  simp only [DyadicCube, BoundedInterval.toSet, Set.mem_Icc]
  have h2n_pos : (0 : ℝ) < 2^n := zpow_pos (by norm_num : (0 : ℝ) < 2) n
  constructor
  · have h1 : (⌊x i * 2^n⌋ : ℝ) ≤ x i * 2^n := Int.floor_le _
    calc (⌊x i * 2^n⌋ : ℝ) / 2^n ≤ x i * 2^n / 2^n :=
        div_le_div_of_nonneg_right h1 h2n_pos.le
      _ = x i := by field_simp
  · have h2 : x i * 2^n < ⌊x i * 2^n⌋ + 1 := Int.lt_floor_add_one _
    have hle : x i < ((⌊x i * 2^n⌋ : ℝ) + 1) / 2^n := by
      calc x i = x i * 2^n / 2^n := by field_simp
        _ < (⌊x i * 2^n⌋ + 1) / 2^n := div_lt_div_of_pos_right h2 h2n_pos
        _ = ((⌊x i * 2^n⌋ : ℝ) + 1) / 2^n := by ring
    exact hle.le

/-- Диадические кубы одного масштаба попарно почти не пересекаются. -/
lemma pairwise_almost_disjoint {d : ℕ} (n : ℤ) : 
    Pairwise (Function.onFun AlmostDisjoint (DyadicCube n : (Fin d → ℤ) → Box d)) := by
  intro a b hab
  simp only [Function.onFun]
  exact DyadicCube.almost_disjoint_same_scale hab

/-- Любые два диадических куба либо почти не пересекаются, либо один содержит другой. -/
lemma nesting {d : ℕ} {n m : ℤ} {a : Fin d → ℤ} {b : Fin d → ℤ} :
    AlmostDisjoint (DyadicCube n a) (DyadicCube m b) ∨
    (DyadicCube n a).toSet ⊆ (DyadicCube m b).toSet ∨
    (DyadicCube m b).toSet ⊆ (DyadicCube n a).toSet := by
  -- Разбор случаев по отношению между n и m
  rcases lt_trichotomy n m with hn | rfl | hm
  · -- n < m : у куба на масштабе m ячейки меньше (2^(-m) < 2^(-n))
    -- Либо DyadicCube m b ⊆ DyadicCube n a (если b в нужной позиции), либо почти не пересекаются
    -- Проверяем DyadicCube m b ⊆ DyadicCube n a, проверяя вложенность интервалов
    by_cases h_subset : ∀ i, (a i : ℝ) / 2^n ≤ (b i : ℝ) / 2^m ∧ ((b i : ℝ) + 1) / 2^m ≤ ((a i : ℝ) + 1) / 2^n
    · -- DyadicCube m b ⊆ DyadicCube n a
      right; right
      intro x hx i
      simp only [DyadicCube, BoundedInterval.toSet, Set.mem_Icc] at hx ⊢
      have hxi := hx i
      exact ⟨le_trans (h_subset i).1 hxi.1, le_trans hxi.2 (h_subset i).2⟩
    · -- Не содержится, значит почти не пересекаются
      left
      push_neg at h_subset
      obtain ⟨i, hi⟩ := h_subset
      simp only [AlmostDisjoint, DyadicCube.interior]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro ha hb
      have hai := ha i
      have hbi := hb i
      have h2n_pos : (0 : ℝ) < 2^n := zpow_pos (by norm_num : (0 : ℝ) < 2) n
      have h2m_pos : (0 : ℝ) < 2^m := zpow_pos (by norm_num : (0 : ℝ) < 2) m
      have h_mn_pos : 0 < m - n := Int.sub_pos_of_lt hn
      have h_zpow_eq : (2 : ℝ)^(m-n) * 2^n = 2^m := by
        rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        congr 1
        omega
      -- hi говорит: если a_i/2^n ≤ b_i/2^m, то (a_i+1)/2^n < (b_i+1)/2^m
      -- Случай 1: a_i/2^n > b_i/2^m (условие hi не выполняется)
      -- Случай 2: a_i/2^n ≤ b_i/2^m, но (a_i+1)/2^n < (b_i+1)/2^m (hi применима)
      by_cases h_left : (b i : ℝ) / 2^m < (a i : ℝ) / 2^n
      · -- b_i/2^m < a_i/2^n : левый конец b лежит до левого конца a
        by_cases h_disj : ((b i : ℝ) + 1) / 2^m ≤ (a i : ℝ) / 2^n
        · -- Интервалы (b_i/2^m, (b_i+1)/2^m) и (a_i/2^n, (a_i+1)/2^n) не пересекаются
          linarith [hai.1, hbi.2]
        · -- Интервалы пересекаются : b_i/2^m < a_i/2^n < (b_i+1)/2^m
          push_neg at h_disj
          -- a_i * 2^(m-n) лежит строго между b_i и b_i+1
          -- Но a_i * 2^(m-n) — целое число (поскольку m > n влечёт m-n > 0)
          have hlo : (b i : ℝ) < (a i : ℝ) * 2^(m-n) := by
            have h1 : (b i : ℝ) / 2^m * 2^m < (a i : ℝ) / 2^n * 2^m := by nlinarith
            simp only [div_mul_cancel₀ _ (ne_of_gt h2m_pos)] at h1
            calc (b i : ℝ) < (a i : ℝ) / 2^n * 2^m := h1
              _ = (a i : ℝ) * (2^m / 2^n) := by ring
              _ = (a i : ℝ) * 2^(m-n) := by rw [← zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
          have hhi : (a i : ℝ) * 2^(m-n) < (b i : ℝ) + 1 := by
            have h1 : (a i : ℝ) / 2^n * 2^m < ((b i : ℝ) + 1) / 2^m * 2^m := by nlinarith
            simp only [div_mul_cancel₀ _ (ne_of_gt h2m_pos)] at h1
            calc (a i : ℝ) * 2^(m-n) = (a i : ℝ) * (2^m / 2^n) := by
                    rw [← zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
              _ = (a i : ℝ) / 2^n * 2^m := by ring
              _ < (b i : ℝ) + 1 := h1
          -- a_i * 2^(m-n) — целое число из (b_i, b_i+1), противоречие
          have h_int : ∃ k : ℤ, (a i : ℝ) * 2^(m-n) = k := by
            have h_pos_exp : ∃ p : ℕ, m - n = p ∧ 0 < p := ⟨(m-n).toNat, (Int.toNat_of_nonneg (le_of_lt h_mn_pos)).symm, by omega⟩
            obtain ⟨p, hp, _⟩ := h_pos_exp
            use a i * 2^p
            simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
            congr 1
            rw [hp, zpow_natCast]
          obtain ⟨k, hk⟩ := h_int
          rw [hk] at hlo hhi
          have : (b i : ℤ) < k ∧ k < b i + 1 := ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
          omega
      · -- ¬(b_i/2^m < a_i/2^n), значит a_i/2^n ≤ b_i/2^m
        push_neg at h_left
        -- По hi: (a_i+1)/2^n < (b_i+1)/2^m
        have h_right := hi h_left
        by_cases h_disj : ((a i : ℝ) + 1) / 2^n ≤ (b i : ℝ) / 2^m
        · -- Интервалы не пересекаются
          linarith [hai.2, hbi.1]
        · -- Интервалы пересекаются : b_i/2^m < (a_i+1)/2^n < (b_i+1)/2^m
          push_neg at h_disj
          -- (a_i+1) * 2^(m-n) лежит строго между b_i и b_i+1
          have hlo : (b i : ℝ) < ((a i : ℝ) + 1) * 2^(m-n) := by
            have h1 : (b i : ℝ) / 2^m * 2^m < ((a i : ℝ) + 1) / 2^n * 2^m := by nlinarith
            simp only [div_mul_cancel₀ _ (ne_of_gt h2m_pos)] at h1
            calc (b i : ℝ) < ((a i : ℝ) + 1) / 2^n * 2^m := h1
              _ = ((a i : ℝ) + 1) * (2^m / 2^n) := by ring
              _ = ((a i : ℝ) + 1) * 2^(m-n) := by rw [← zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
          have hhi : ((a i : ℝ) + 1) * 2^(m-n) < (b i : ℝ) + 1 := by
            have h1 : ((a i : ℝ) + 1) / 2^n * 2^m < ((b i : ℝ) + 1) / 2^m * 2^m := by nlinarith
            simp only [div_mul_cancel₀ _ (ne_of_gt h2m_pos)] at h1
            calc ((a i : ℝ) + 1) * 2^(m-n) = ((a i : ℝ) + 1) * (2^m / 2^n) := by
                    rw [← zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
              _ = ((a i : ℝ) + 1) / 2^n * 2^m := by ring
              _ < (b i : ℝ) + 1 := h1
          -- (a_i+1) * 2^(m-n) — целое число из (b_i, b_i+1), противоречие
          have h_int : ∃ k : ℤ, ((a i : ℝ) + 1) * 2^(m-n) = k := by
            have h_pos_exp : ∃ p : ℕ, m - n = p ∧ 0 < p := ⟨(m-n).toNat, (Int.toNat_of_nonneg (le_of_lt h_mn_pos)).symm, by omega⟩
            obtain ⟨p, hp, _⟩ := h_pos_exp
            use (a i + 1) * 2^p
            simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_add, Int.cast_one]
            congr 1
            rw [hp, zpow_natCast]
          obtain ⟨k, hk⟩ := h_int
          rw [hk] at hlo hhi
          have : (b i : ℤ) < k ∧ k < b i + 1 := ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
          omega
  · -- n = m : один масштаб, используем almost_disjoint_same_scale или равенство
    by_cases hab : a = b
    · subst hab
      right; left
      exact Set.Subset.refl _
    · left
      exact DyadicCube.almost_disjoint_same_scale hab
  · -- m < n : у куба на масштабе n ячейки меньше (2^(-n) < 2^(-m))
    -- Либо DyadicCube n a ⊆ DyadicCube m b (если a в нужной позиции), либо почти не пересекаются
    by_cases h_subset : ∀ i, (b i : ℝ) / 2^m ≤ (a i : ℝ) / 2^n ∧ ((a i : ℝ) + 1) / 2^n ≤ ((b i : ℝ) + 1) / 2^m
    · -- DyadicCube n a ⊆ DyadicCube m b
      right; left
      intro x hx i
      simp only [DyadicCube, BoundedInterval.toSet, Set.mem_Icc] at hx ⊢
      have hxi := hx i
      exact ⟨le_trans (h_subset i).1 hxi.1, le_trans hxi.2 (h_subset i).2⟩
    · -- Не содержится, значит почти не пересекаются
      left
      push_neg at h_subset
      obtain ⟨i, hi⟩ := h_subset
      simp only [AlmostDisjoint, DyadicCube.interior]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro ha hb
      have hai := ha i
      have hbi := hb i
      have h2n_pos : (0 : ℝ) < 2^n := zpow_pos (by norm_num : (0 : ℝ) < 2) n
      have h2m_pos : (0 : ℝ) < 2^m := zpow_pos (by norm_num : (0 : ℝ) < 2) m
      have h_nm_pos : 0 < n - m := Int.sub_pos_of_lt hm
      -- hi говорит: если b_i/2^m ≤ a_i/2^n, то (a_i+1)/2^n > (b_i+1)/2^m
      by_cases h_left : (a i : ℝ) / 2^n < (b i : ℝ) / 2^m
      · -- a_i/2^n < b_i/2^m : левый конец a лежит до левого конца b
        by_cases h_disj : ((a i : ℝ) + 1) / 2^n ≤ (b i : ℝ) / 2^m
        · -- Интервалы не пересекаются
          linarith [hai.2, hbi.1]
        · -- Интервалы пересекаются : a_i/2^n < b_i/2^m < (a_i+1)/2^n
          push_neg at h_disj
          -- b_i * 2^(n-m) лежит строго между a_i и a_i+1
          have hlo : (a i : ℝ) < (b i : ℝ) * 2^(n-m) := by
            have h1 : (a i : ℝ) / 2^n * 2^n < (b i : ℝ) / 2^m * 2^n := by nlinarith
            simp only [div_mul_cancel₀ _ (ne_of_gt h2n_pos)] at h1
            calc (a i : ℝ) < (b i : ℝ) / 2^m * 2^n := h1
              _ = (b i : ℝ) * (2^n / 2^m) := by ring
              _ = (b i : ℝ) * 2^(n-m) := by rw [← zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
          have hhi : (b i : ℝ) * 2^(n-m) < (a i : ℝ) + 1 := by
            have h1 : (b i : ℝ) / 2^m * 2^n < ((a i : ℝ) + 1) / 2^n * 2^n := by nlinarith
            simp only [div_mul_cancel₀ _ (ne_of_gt h2n_pos)] at h1
            calc (b i : ℝ) * 2^(n-m) = (b i : ℝ) * (2^n / 2^m) := by
                    rw [← zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
              _ = (b i : ℝ) / 2^m * 2^n := by ring
              _ < (a i : ℝ) + 1 := h1
          -- b_i * 2^(n-m) — целое число из (a_i, a_i+1), противоречие
          have h_int : ∃ k : ℤ, (b i : ℝ) * 2^(n-m) = k := by
            have h_pos_exp : ∃ p : ℕ, n - m = p ∧ 0 < p := ⟨(n-m).toNat, (Int.toNat_of_nonneg (le_of_lt h_nm_pos)).symm, by omega⟩
            obtain ⟨p, hp, _⟩ := h_pos_exp
            use b i * 2^p
            simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
            congr 1
            rw [hp, zpow_natCast]
          obtain ⟨k, hk⟩ := h_int
          rw [hk] at hlo hhi
          have : (a i : ℤ) < k ∧ k < a i + 1 := ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
          omega
      · -- ¬(a_i/2^n < b_i/2^m), значит b_i/2^m ≤ a_i/2^n
        push_neg at h_left
        -- По hi: (a_i+1)/2^n > (b_i+1)/2^m
        have h_right := hi h_left
        by_cases h_disj : ((b i : ℝ) + 1) / 2^m ≤ (a i : ℝ) / 2^n
        · -- Интервалы не пересекаются
          linarith [hai.1, hbi.2]
        · -- Интервалы пересекаются : a_i/2^n < (b_i+1)/2^m < (a_i+1)/2^n
          push_neg at h_disj
          -- (b_i+1) * 2^(n-m) лежит строго между a_i и a_i+1
          have hlo : (a i : ℝ) < ((b i : ℝ) + 1) * 2^(n-m) := by
            have h1 : (a i : ℝ) / 2^n * 2^n < ((b i : ℝ) + 1) / 2^m * 2^n := by nlinarith
            simp only [div_mul_cancel₀ _ (ne_of_gt h2n_pos)] at h1
            calc (a i : ℝ) < ((b i : ℝ) + 1) / 2^m * 2^n := h1
              _ = ((b i : ℝ) + 1) * (2^n / 2^m) := by ring
              _ = ((b i : ℝ) + 1) * 2^(n-m) := by rw [← zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
          have hhi : ((b i : ℝ) + 1) * 2^(n-m) < (a i : ℝ) + 1 := by
            have h1 : ((b i : ℝ) + 1) / 2^m * 2^n < ((a i : ℝ) + 1) / 2^n * 2^n := by nlinarith
            simp only [div_mul_cancel₀ _ (ne_of_gt h2n_pos)] at h1
            calc ((b i : ℝ) + 1) * 2^(n-m) = ((b i : ℝ) + 1) * (2^n / 2^m) := by
                    rw [← zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
              _ = ((b i : ℝ) + 1) / 2^m * 2^n := by ring
              _ < (a i : ℝ) + 1 := h1
          -- (b_i+1) * 2^(n-m) — целое число из (a_i, a_i+1), противоречие
          have h_int : ∃ k : ℤ, ((b i : ℝ) + 1) * 2^(n-m) = k := by
            have h_pos_exp : ∃ p : ℕ, n - m = p ∧ 0 < p := ⟨(n-m).toNat, (Int.toNat_of_nonneg (le_of_lt h_nm_pos)).symm, by omega⟩
            obtain ⟨p, hp, _⟩ := h_pos_exp
            use (b i + 1) * 2^p
            simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_add, Int.cast_one]
            congr 1
            rw [hp, zpow_natCast]
          obtain ⟨k, hk⟩ := h_int
          rw [hk] at hlo hhi
          have : (a i : ℤ) < k ∧ k < a i + 1 := ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
          omega

end DyadicCube
/-- Для любой точки x в открытом множестве E существует диадический куб, содержащий x,
    который целиком лежит в E. -/
lemma IsOpen.exists_dyadic_cube_subset {d : ℕ} {E : Set (EuclideanSpace' d)} (hE : IsOpen E)
    {x : EuclideanSpace' d} (hx : x ∈ E) :
    ∃ n : ℕ, ∃ a : Fin d → ℤ, x ∈ (DyadicCube (n : ℤ) a).toSet ∧
    (DyadicCube (n : ℤ) a).toSet ⊆ E := by
  -- Поскольку E открыто, существует ε > 0 такое, что B(x, ε) ⊆ E
  rw [Metric.isOpen_iff] at hE
  obtain ⟨ε, hε_pos, hball⟩ := hE x hx
  -- Выбираем n достаточно большим, чтобы диадический куб, содержащий x, имел диаметр < ε
  -- Диаметр диадического куба на масштабе n равен ≤ √d * 2^(-n)
  -- Нужно √d * 2^(-n) < ε, то есть √d / ε < 2^n
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (Real.sqrt d / ε) (by norm_num : (1 : ℝ) < 2)
  use n
  -- Находим диадический куб, содержащий x, на масштабе n
  let a : Fin d → ℤ := fun i => ⌊x i * 2^n⌋
  use a
  have h2n_pos : (0 : ℝ) < 2^n := by positivity
  constructor
  · -- x ∈ DyadicCube n a
    intro i
    simp only [DyadicCube, BoundedInterval.toSet, Set.mem_Icc]
    constructor
    · have h1 : (⌊x i * 2^n⌋ : ℝ) ≤ x i * 2^n := Int.floor_le _
      have h2 := div_le_div_of_nonneg_right h1 (le_of_lt h2n_pos)
      simp only [mul_div_cancel_right₀ _ (ne_of_gt h2n_pos)] at h2
      exact h2
    · have h2 : x i * 2^n < ⌊x i * 2^n⌋ + 1 := Int.lt_floor_add_one _
      have h3 := div_lt_div_of_pos_right h2 h2n_pos
      simp only [mul_div_cancel_right₀ _ (ne_of_gt h2n_pos)] at h3
      exact h3.le
  · -- DyadicCube n a ⊆ E
    intro y hy
    apply hball
    simp only [Metric.mem_ball]
    -- y лежит в диадическом кубе, содержащем x, поэтому |y i - x i| ≤ 2^(-n) для всех i
    have h2n_inv : (2 : ℝ)^(-n : ℤ) = 1 / 2^n := by rw [zpow_neg, zpow_natCast]; ring
    have h_zpow : (2 : ℝ) ^ (↑n : ℤ) = 2 ^ n := zpow_natCast 2 n
    have hyi : ∀ i, |y i - x i| ≤ 2^(-n : ℤ) := fun i => by
      have hyi_mem := hy i
      simp only [DyadicCube, BoundedInterval.toSet, Set.mem_Icc, h_zpow] at hyi_mem
      -- hyi_mem : ⌊x i * 2^n⌋ / 2^n ≤ y i ∧ y i ≤ (⌊x i * 2^n⌋ + 1) / 2^n
      have hxi_floor : (⌊x i * 2^n⌋ : ℝ) / 2^n ≤ x i := by
        have h1 := Int.floor_le (x i * 2^n)
        have h2 := div_le_div_of_nonneg_right h1 (le_of_lt h2n_pos)
        simp only [mul_div_cancel_right₀ _ (ne_of_gt h2n_pos)] at h2
        exact h2
      rw [abs_le, h2n_inv]
      -- Нужно: -1/2^n ≤ y i - x i ≤ 1/2^n
      have hbound : x i - 1 / 2^n ≤ (⌊x i * 2^n⌋ : ℝ) / 2^n := by
        have h1 := (Int.lt_floor_add_one (x i * 2^n)).le
        have h2 := div_le_div_of_nonneg_right h1 (le_of_lt h2n_pos)
        simp only [mul_div_cancel_right₀ _ (ne_of_gt h2n_pos)] at h2
        have heq : ((⌊x i * 2^n⌋ : ℝ) + 1) / 2^n = (⌊x i * 2^n⌋ : ℝ) / 2^n + 1 / 2^n := by ring
        linarith [heq, h2]
      have hwidth : ((⌊x i * 2^n⌋ : ℝ) + 1) / 2^n - (⌊x i * 2^n⌋ : ℝ) / 2^n = 1 / 2^n := by ring
      -- Нижняя граница: floor/2^n ≤ y i, а x i - 1/2^n ≤ floor/2^n, значит x i - 1/2^n ≤ y i
      refine ⟨?_, ?_⟩
      · linarith [hyi_mem.1, hbound]
      · -- Верхняя граница : y i ≤ (floor+1)/2^n, а floor/2^n ≤ x i
        -- Значит y i - x i ≤ (floor+1)/2^n - floor/2^n = 1/2^n
        linarith [hyi_mem.2, hxi_floor, hwidth]
    -- dist y x ≤ √d * 2^(-n) < ε
    have hdist : dist y x ≤ Real.sqrt d * (2 : ℝ)^(-n : ℤ) := by
      rw [EuclideanSpace.dist_eq]
      have hdist_eq : ∀ i, dist (y i) (x i) = |y i - x i| := fun i => Real.dist_eq (y i) (x i)
      simp_rw [hdist_eq]
      have hsqrt_mul : Real.sqrt d * (2 : ℝ)^(-n : ℤ) = Real.sqrt (d * ((2 : ℝ)^(-n : ℤ))^2) := by
        rw [Real.sqrt_mul (by positivity : (d : ℝ) ≥ 0), Real.sqrt_sq (by positivity)]
      rw [hsqrt_mul]
      apply Real.sqrt_le_sqrt
      calc ∑ i, |y i - x i|^2
          ≤ ∑ _i : Fin d, ((2 : ℝ)^(-n : ℤ))^2 := by
            apply Finset.sum_le_sum
            intro i _
            have h := hyi i
            have h2n_nn : (0 : ℝ) ≤ (2 : ℝ)^(-n : ℤ) := by positivity
            exact sq_le_sq' (by nlinarith [abs_nonneg (y i - x i)]) h
        _ = d * ((2 : ℝ)^(-n : ℤ))^2 := by rw [Finset.sum_const, Finset.card_fin]; ring
    calc dist y x ≤ Real.sqrt d * (2 : ℝ)^(-n : ℤ) := hdist
      _ = Real.sqrt d / 2^n := by rw [h2n_inv]; ring
      _ < ε := by
          rw [div_lt_iff₀ h2n_pos]
          calc Real.sqrt d = Real.sqrt d / ε * ε := by field_simp
            _ < ε * 2^n := by nlinarith [hn, hε_pos]

/-- Для точки x — единственный диадический куб на масштабе n, содержащий x. -/
noncomputable def dyadicCubeContaining {d : ℕ} (n : ℤ) (x : EuclideanSpace' d) : Box d :=
  DyadicCube n (fun i => ⌊x i * 2^n⌋)

/-- Диадический куб, содержащий x на масштабе n, действительно содержит x. -/
lemma dyadicCubeContaining_mem {d : ℕ} (n : ℤ) (x : EuclideanSpace' d) : 
    x ∈ (dyadicCubeContaining n x).toSet := by
  intro i
  simp only [dyadicCubeContaining, DyadicCube, BoundedInterval.toSet, Set.mem_Icc]
  have h2n_pos : (0 : ℝ) < 2^n := zpow_pos (by norm_num : (0 : ℝ) < 2) n
  constructor
  · have h1 : (⌊x i * 2^n⌋ : ℝ) ≤ x i * 2^n := Int.floor_le _
    calc (⌊x i * 2^n⌋ : ℝ) / 2^n ≤ x i * 2^n / 2^n := div_le_div_of_nonneg_right h1 (le_of_lt h2n_pos)
      _ = x i := by field_simp
  · have h2 : x i * 2^n < ⌊x i * 2^n⌋ + 1 := Int.lt_floor_add_one _
    have h3 : x i < ((⌊x i * 2^n⌋ : ℝ) + 1) / 2^n := by
      calc x i = x i * 2^n / 2^n := by field_simp
        _ < (⌊x i * 2^n⌋ + 1) / 2^n := div_lt_div_of_pos_right h2 h2n_pos
        _ = ((⌊x i * 2^n⌋ : ℝ) + 1) / 2^n := by ring
    exact h3.le

/-- Внутренность диадического куба непуста. -/
lemma dyadicCubeInteriorNonempty {d : ℕ} (n : ℤ) (a : Fin d → ℤ) : 
    (interior (s := (DyadicCube n a).toSet)).Nonempty := by
  rw [Box.interior_toSet]
  exact (Set.univ_pi_nonempty_iff.mpr (fun k => by
    simp only [DyadicCube, BoundedInterval.toSet, interior_Icc]
    exact Set.nonempty_Ioo.mpr (div_lt_div_of_pos_right (by linarith) (zpow_pos (by norm_num) _))
  )).preimage (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).surjective

lemma Box.toSet_nonempty_of_IsDyadic {d : ℕ} {B : Box d} (hB : B.IsDyadic) : B.toSet.Nonempty := by
  obtain ⟨n, ⟨a, rfl⟩⟩ := hB
  exact (dyadicCubeInteriorNonempty n a).mono (interior_subset (s := (DyadicCube n a).toSet))

/-- На одном масштабе диадические кубы с разными индексами не могут содержать друг друга
    (иначе вложенность влекла бы пустую внутренность одного из них). -/
lemma dyadicCubeNoProperContainmentSameScale {d : ℕ} {n : ℤ} {a b : Fin d → ℤ}
    (h_sub : (DyadicCube n a).toSet ⊆ (DyadicCube n b).toSet) : a = b := by
  by_contra hne
  have h_ad := DyadicCube.almost_disjoint_same_scale (n := n) (a := a) (b := b) hne
  simp only [AlmostDisjoint] at h_ad
  have h_int_sub : interior (s := (DyadicCube n a).toSet) ⊆ interior (s := (DyadicCube n b).toSet) :=
    interior_mono h_sub
  have h_int_eq : interior (s := (DyadicCube n a).toSet) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    have hx' := h_int_sub hx
    have hx_both : x ∈ interior (s := (DyadicCube n a).toSet) ∩
        interior (s := (DyadicCube n b).toSet) := ⟨hx, hx'⟩
    rw [h_ad] at hx_both
    exact hx_both
  exact Set.not_nonempty_empty (h_int_eq ▸ dyadicCubeInteriorNonempty n a)

/-- Больший диадический куб (более грубый масштаб n) не может содержаться в меньшем диадическом
    кубе (более тонкий масштаб m) при d > 0. Это потому, что длина стороны 2^(-n) > 2^(-m),
    когда n < m. -/
lemma dyadicCubeLargerNotInSmaller {d : ℕ} (hd : 0 < d) {n m : ℤ} (hnm : n < m)
    {a b : Fin d → ℤ} : ¬((DyadicCube n a).toSet ⊆ (DyadicCube m b).toSet) := by
  intro h_sub
  -- Выбираем любую координату (d > 0 гарантирует её существование)
  let i : Fin d := ⟨0, hd⟩
  -- Сравниваем длины сторон: 2^(-n) > 2^(-m), когда n < m
  have h_side_ineq : (2 : ℝ)^(-m) < (2 : ℝ)^(-n) := by
    apply zpow_lt_zpow_right₀ (by norm_num : 1 < (2 : ℝ))
    omega
  -- Строим левый конец DyadicCube n a
  let x_left : EuclideanSpace' d := .toLp 2 (fun j => (a j : ℝ) / 2^n)
  -- x_left входит в DyadicCube n a (это левый угол)
  have hx_left : x_left ∈ (DyadicCube n a).toSet := by
    intro j
    simp only [x_left, DyadicCube, BoundedInterval.toSet, Set.mem_Icc]
    constructor
    · exact le_refl _
    · have h2n_pos : (0 : ℝ) < 2^n := zpow_pos (by norm_num) n
      apply le_of_lt
      apply div_lt_div_of_pos_right _ h2n_pos
      linarith
  -- Строим правый конец DyadicCube n a
  let x_right : EuclideanSpace' d := .toLp 2 (fun j => ((a j : ℝ) + 1) / 2^n)
  -- x_right входит в DyadicCube n a (это правый угол)
  have hx_right : x_right ∈ (DyadicCube n a).toSet := by
    intro j
    simp only [x_right, DyadicCube, BoundedInterval.toSet, Set.mem_Icc]
    constructor
    · have h2n_pos : (0 : ℝ) < 2^n := zpow_pos (by norm_num) n
      apply le_of_lt
      apply div_lt_div_of_pos_right _ h2n_pos
      linarith
    · exact le_refl _
  -- Оба конца лежат в DyadicCube m b по h_sub
  have h_left_in := h_sub hx_left i
  have h_right_in := h_sub hx_right i
  simp only [x_left, x_right, DyadicCube, BoundedInterval.toSet, Set.mem_Icc] at h_left_in h_right_in
  -- Из h_left_in: (a i)/2^n ≥ (b i)/2^m
  -- Из h_right_in: ((a i)+1)/2^n ≤ ((b i)+1)/2^m
  -- Значит: 2^(-n) = ((a i)+1)/2^n - (a i)/2^n ≤ ((b i)+1)/2^m - (b i)/2^m = 2^(-m)
  have h_len_sub : (2 : ℝ)^(-n) ≤ (2 : ℝ)^(-m) := by
    have h2n_pos : (0 : ℝ) < 2^n := zpow_pos (by norm_num) n
    have h2m_pos : (0 : ℝ) < 2^m := zpow_pos (by norm_num) m
    calc (2 : ℝ)^(-n) = ((a i : ℝ) + 1) / 2^n - (a i : ℝ) / 2^n := by
            simp only [zpow_neg, ← sub_div]; norm_cast; simp [add_sub_cancel_left]
      _ ≤ ((b i : ℝ) + 1) / 2^m - (b i : ℝ) / 2^m := by linarith [h_left_in.1, h_right_in.2]
      _ = (2 : ℝ)^(-m) := by
            simp only [zpow_neg, ← sub_div]; norm_cast; simp [add_sub_cancel_left]
  linarith

/-- Лемма 1.2.11: каждое открытое множество является счётным объединением почти непересекающихся
диадических кубов. Замечание: каждый диадический куб непуст.
    Набросок доказательства:
    1. Для каждого x ∈ E по {name}`IsOpen.exists_dyadic_cube_subset` существует диадический куб,
       содержащий x, ⊆ E
    2. Множество всех таких диадических кубов счётно (подмножество {lean}`ℕ × (Fin d → ℤ)`)
    3. Берём максимальные кубы (не содержащиеся строго в другом кубе семейства)
    4. По {name}`DyadicCube.nesting` различные максимальные кубы почти не пересекаются
    5. E равно объединению этих максимальных кубов -/
theorem IsOpen.eq_union_boxes {d : ℕ} (hd : 0 < d) (E : Set (EuclideanSpace' d)) (hE : IsOpen E)
    (hE_nonempty : E.Nonempty) : 
    ∃ B : ℕ → Box d, (E = ⋃ n, (B n).toSet) ∧ (∀ n, (B n).IsDyadic) ∧
    Pairwise (Function.onFun AlmostDisjoint B) := by
  classical
  -- Строим максимальные диадические кубы
  obtain ⟨x₀, hx₀⟩ := hE_nonempty
  -- Определяем множество всех диадических кубов (на масштабе n ≥ 0), содержащихся в E
  let Q : Set (ℕ × (Fin d → ℤ)) := { p | (DyadicCube (p.1 : ℤ) p.2).toSet ⊆ E }
  -- Q счётно как подмножество ℕ × (Fin d → ℤ)
  have hQ_countable : Q.Countable := Set.countable_of_injective_of_countable_image
    (f := id) (fun _ _ _ _ h => h) (Set.countable_univ.mono (Set.subset_univ _))
  -- Для каждого x ∈ E находим минимальный масштаб n такой, что диадический куб на масштабе n,
  -- содержащий x, входит в Q
  -- Минимальный масштаб соответствует максимальному кубу (меньшее n = грубее = больший куб)
  have h_exists_min_scale : ∀ x ∈ E, ∃ n₀ : ℕ, ∃ a : Fin d → ℤ,
      x ∈ (DyadicCube (n₀ : ℤ) a).toSet ∧ (DyadicCube (n₀ : ℤ) a).toSet ⊆ E ∧
      (∀ m < n₀, ∀ b : Fin d → ℤ, x ∈ (DyadicCube (m : ℤ) b).toSet → ¬(DyadicCube (m : ℤ) b).toSet ⊆ E) := by
    intro x hx
    -- По exists_dyadic_cube_subset существует некоторый масштаб с кубом ⊆ E
    obtain ⟨n, a, hxa, hcube⟩ := hE.exists_dyadic_cube_subset hx
    -- Находим минимальный такой масштаб через Nat.find
    let P : ℕ → Prop := fun m => ∃ b : Fin d → ℤ, x ∈ (DyadicCube (m : ℤ) b).toSet ∧ (DyadicCube (m : ℤ) b).toSet ⊆ E
    have hP : ∃ m, P m := ⟨n, a, hxa, hcube⟩
    let n₀ := Nat.find hP
    obtain ⟨a₀, ha₀_mem, ha₀_sub⟩ := Nat.find_spec hP
    use n₀, a₀, ha₀_mem, ha₀_sub
    intro m hm b hb_mem hsub
    exact Nat.find_min hP hm ⟨b, hb_mem, hsub⟩
  -- Определяем максимальные кубы: для каждого x ∈ E выбираем куб минимального масштаба
  -- Определяем множество индексов максимальных кубов
  let Q_max : Set (ℕ × (Fin d → ℤ)) := { p | (DyadicCube (p.1 : ℤ) p.2).toSet ⊆ E ∧
    ∀ q : ℕ × (Fin d → ℤ), q.1 < p.1 →
      (DyadicCube (p.1 : ℤ) p.2).toSet ⊆ (DyadicCube (q.1 : ℤ) q.2).toSet →
      ¬(DyadicCube (q.1 : ℤ) q.2).toSet ⊆ E }
  -- Q_max счётно
  have hQ_max_countable : Q_max.Countable :=
    Set.countable_of_injective_of_countable_image (f := id) (fun _ _ _ _ h => h)
      (Set.countable_univ.mono (Set.subset_univ _))
  -- Q_max непусто (поскольку E непусто)
  have hQ_max_nonempty : Q_max.Nonempty := by
    obtain ⟨n₀, a₀, hx₀_mem, hsub, hmin⟩ := h_exists_min_scale x₀ hx₀
    use ⟨n₀, a₀⟩
    simp only [Set.mem_setOf_eq, Q_max]
    constructor
    · exact hsub
    · intro q hq hsub'
      -- Если DyadicCube n₀ a₀ ⊆ DyadicCube q.1 q.2 при q.1 < n₀, то q.1 — меньший масштаб,
      -- содержащий x₀, что противоречит минимальности
      have hx₀_in_q : x₀ ∈ (DyadicCube (q.1 : ℤ) q.2).toSet := hsub' hx₀_mem
      exact hmin q.1 hq q.2 hx₀_in_q
  -- Q_max бесконечно: покажем это разбором случаев по d
  have hQ_max_infinite : Q_max.Infinite := by
    -- d > 0 по гипотезе hd, поэтому продолжаем напрямую
      -- На масштабе 0 диадические кубы — это [a₁, a₁+1] × ... × [aₐ, aₐ+1] для a ∈ ℤᵈ
      -- Если E = univ, все кубы масштаба 0 входят в Q_max
      -- Если E ≠ univ, вблизи границы кубы сколь угодно тонкого масштаба максимальны
      by_cases hE_univ : E = Set.univ
      · -- E = univ : все кубы масштаба 0 максимальны (более грубого масштаба не существует)
        -- Сначала покажем, что Fin d → ℤ бесконечно (поскольку d > 0, а ℤ бесконечно)
        haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
        haveI : Infinite (Fin d → ℤ) := Function.infinite_of_right
        -- Теперь вкладываем Fin d → ℤ в Q_max через a ↦ (0, a)
        apply Set.infinite_of_injective_forall_mem
          (f := fun a : Fin d → ℤ => (0, a))
          (fun a b hab => (Prod.mk.inj hab).2)
        intro a
        constructor
        · simp only [hE_univ]; exact Set.subset_univ _
        · intro q hq _; omega
      · -- E ≠ univ : вблизи границы кубы сколь угодно тонкого масштаба максимальны
        -- Ключевая идея: поскольку E ≠ univ, существует y ∉ E. Для любого x ∈ E максимальный
        -- куб, содержащий x, не может содержать y. Приближая x к y (оставаясь в E), максимальные
        -- кубы должны становиться всё меньше, давая сколь угодно тонкие масштабы.
        -- Покажем, что Q_max бесконечно, показав, что масштабы неограничены.
        by_contra hfin
        rw [Set.not_infinite] at hfin
        -- Q_max конечно, значит среди всех максимальных кубов есть максимальный масштаб N
        obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ p ∈ Q_max, p.1 ≤ N := by
          obtain ⟨p, hp⟩ := Set.Finite.exists_maximalFor Prod.fst Q_max hfin hQ_max_nonempty
          use p.1
          intro q hq
          by_contra hlt
          push_neg at hlt
          have hle := hp.le_of_le hq hlt.le
          omega
        -- Но существуют точки в E, у которых масштаб максимального куба > N
        -- Это точки вблизи границы (дополнения E)
        -- Поскольку E ≠ univ, ∃ y ∉ E. Возьмём x ∈ E близко к y.
        have hEc_nonempty : Eᶜ.Nonempty := by
          rw [Set.nonempty_compl]
          exact hE_univ
        obtain ⟨y, hy⟩ := hEc_nonempty
        -- Стратегия доказательства:
        -- 1. У каждого x ∈ E максимальный куб имеет масштаб ≤ N, значит длину стороны ≥ 2^(-N)
        -- 2. Этот куб содержится в E и содержит открытый шар вокруг x
        -- 3. Значит у каждого x ∈ E выполняется dist(x, Eᶜ) ≥ 2^(-N)·sqrt(d)/2 (примерно)
        -- 4. Это означает, что E замкнуто (closure E = E)
        -- 5. E открыто, замкнуто, непусто → E = univ по связности
        -- 6. Противоречит E ≠ univ
        --
        -- Шаг 1: покажем, что E замкнуто
        have hE_closed : IsClosed E := by
          -- Стратегия: Q_max конечно, поэтому E — конечное объединение диадических кубов
          -- Каждый диадический куб замкнут (произведение замкнутых интервалов Icc)
          -- Конечное объединение замкнутых множеств замкнуто
          -- Сначала покажем, что toSet каждого диадического куба замкнуто
          have h_cube_closed : ∀ p ∈ Q_max, IsClosed (DyadicCube (p.1 : ℤ) p.2).toSet := by
            intro p _
            -- DyadicCube — произведение интервалов Icc, которые замкнуты
            exact Box.isClosed_toSet_of_Icc _ (fun i => ⟨_, _, rfl⟩)
          -- E равно объединению кубов из Q_max
          have hE_union_Qmax : E = ⋃ p ∈ Q_max, (DyadicCube (p.1 : ℤ) p.2).toSet := by
            ext x
            constructor
            · intro hx
              -- x ∈ E, значит у x есть максимальный куб
              obtain ⟨n₀, a₀, hx_mem, hsub, hmin⟩ := h_exists_min_scale x hx
              -- Этот куб входит в Q_max
              have h_in_Qmax : (n₀, a₀) ∈ Q_max := by
                constructor
                · exact hsub
                · intro q hq hsub'
                  have : x ∈ (DyadicCube (q.1 : ℤ) q.2).toSet := hsub' hx_mem
                  exact hmin q.1 hq q.2 this
              exact Set.mem_biUnion h_in_Qmax hx_mem
            · intro hx
              simp only [Set.mem_iUnion] at hx
              obtain ⟨p, hp_mem, hx_in_p⟩ := hx
              exact hp_mem.1 hx_in_p
          -- Q_max конечно, значит и объединение конечно
          rw [hE_union_Qmax]
          -- Конечное объединение замкнутых множеств замкнуто
          exact hfin.isClosed_biUnion h_cube_closed
        -- Шаг 2: E открыто-замкнуто (clopen)
        have hE_clopen : IsClopen E := ⟨hE_closed, hE⟩
        -- Шаг 3: используем предсвязность
        -- EuclideanSpace d предсвязно при d > 0
        haveI : PreconnectedSpace (EuclideanSpace' d) := inferInstance
        -- Шаг 4: открыто-замкнутые множества в предсвязном пространстве — либо пусты, либо univ
        rw [isClopen_iff] at hE_clopen
        cases hE_clopen with
        | inl h_empty =>
          -- E = ∅ противоречит E.Nonempty
          have : E.Nonempty := ⟨x₀, hx₀⟩
          rw [h_empty] at this
          exact Set.not_nonempty_empty this
        | inr h_univ =>
          -- E = univ противоречит hE_univ : E ≠ univ
          exact hE_univ h_univ
  -- Перечисляем Q_max, используя структуру Denumerable (поскольку Q_max бесконечно и счётно)
  obtain ⟨p₀, hp₀⟩ := hQ_max_nonempty
  -- Для бесконечных счётных множеств можно получить инъективное перечисление
  haveI : Infinite Q_max := Set.infinite_coe_iff.mpr hQ_max_infinite
  haveI : Countable Q_max := hQ_max_countable.to_subtype
  haveI : Denumerable Q_max := Denumerable.ofEncodableOfInfinite Q_max
  -- Используем эквивалентность Denumerable, чтобы получить биекцию
  let B_enum : ℕ ≃ Q_max := (Denumerable.eqv Q_max).symm
  let B_idx : ℕ → ℕ × (Fin d → ℤ) := fun n => (B_enum n).val
  have hB_idx_inj : Function.Injective B_idx := by
    intro i j hij
    have : B_enum i = B_enum j := Subtype.ext hij
    exact (Equiv.injective B_enum) this
  let B : ℕ → Box d := fun n => DyadicCube ((B_idx n).1 : ℤ) (B_idx n).2
  use B
  constructor
  · -- E = ⋃ n, (B n).toSet
    ext x
    constructor
    · -- x ∈ E → x ∈ ⋃ n, (B n).toSet
      intro hx
      obtain ⟨n₀, a₀, hxa₀, hsub, hmin⟩ := h_exists_min_scale x hx
      -- (n₀, a₀) ∈ Q_max
      have h_in_Qmax : (⟨n₀, a₀⟩ : ℕ × (Fin d → ℤ)) ∈ Q_max := by
        simp only [Set.mem_setOf_eq, Q_max]
        constructor
        · exact hsub
        · intro q hq hsub'
          have hx_in_q : x ∈ (DyadicCube (q.1 : ℤ) q.2).toSet := hsub' hxa₀
          exact hmin q.1 hq q.2 hx_in_q
      -- B_enum — биекция ℕ ≃ Q_max, поэтому у (n₀, a₀) ∈ Q_max есть прообраз
      rw [Set.mem_iUnion]
      -- h_in_Qmax : (n₀, a₀) ∈ Q_max, а B_enum сюръективна
      let elem : Q_max := ⟨(n₀, a₀), h_in_Qmax⟩
      have h_in_range : elem ∈ Set.range B_enum := by
        rw [Equiv.range_eq_univ]
        exact Set.mem_univ _
      obtain ⟨k, hk⟩ := h_in_range
      use k
      show x ∈ (DyadicCube ((B_idx k).1 : ℤ) (B_idx k).2).toSet
      have heq : B_idx k = (n₀, a₀) := by
        simp only [B_idx]
        exact congrArg Subtype.val hk
      rw [heq]
      exact hxa₀
    · -- x ∈ ⋃ n, (B n).toSet → x ∈ E
      intro hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨n, hn⟩ := hx
      have h_Bn_mem : B_idx n ∈ Q_max := (B_enum n).property
      exact h_Bn_mem.1 hn
  constructor
  · -- ∀ n, (B n).IsDyadic
    intro n
    simp only [B, Box.IsDyadic]
    use (B_idx n).1, (B_idx n).2
  · -- Попарная почти-непересекаемость
    intro i j hij
    simp only [Function.onFun]
    have hi_mem : B_idx i ∈ Q_max := (B_enum i).property
    have hj_mem : B_idx j ∈ Q_max := (B_enum j).property
    -- Два различных максимальных куба почти не пересекаются
    -- По DyadicCube.nesting: либо почти не пересекаются, либо один ⊆ другому
    rcases DyadicCube.nesting (n := (B_idx i).1) (m := (B_idx j).1)
        (a := (B_idx i).2) (b := (B_idx j).2) with h_ad | h_ij | h_ji
    · exact h_ad
    · -- B i ⊆ B j : анализируем через сравнение масштабов
      exfalso
      -- h_ij : (DyadicCube (B_idx i).1 (B_idx i).2).toSet ⊆ (DyadicCube (B_idx j).1 (B_idx j).2).toSet
      -- Если B_i ⊆ B_j строго, то (B_idx j).1 < (B_idx i).1 (j грубее)
      -- По максимальности B_i, поскольку B_i ⊆ B_j и j.1 < i.1, имеем B_j ⊈ E
      -- Но B_j ∈ Q_max влечёт B_j ⊆ E. Противоречие.
      rcases lt_trichotomy (B_idx j).1 (B_idx i).1 with hji_lt | hji_eq | hji_gt
      · -- (B_idx j).1 < (B_idx i).1 : j — более грубый масштаб
        -- B_i ⊆ B_j и j.1 < i.1 противоречат максимальности B_i
        exact hi_mem.2 (B_idx j) hji_lt h_ij hj_mem.1
      · -- Одинаковый масштаб : кубы либо равны, либо не пересекаются
        -- Если B_i ⊆ B_j на одном масштабе, они должны быть равны
        have h_ij' : (DyadicCube (↑(B_idx i).1) (B_idx i).2).toSet ⊆
            (DyadicCube (↑(B_idx i).1) (B_idx j).2).toSet := by
          convert h_ij using 3; simp only [Nat.cast_inj]; exact hji_eq.symm
        have heq : (B_idx i).2 = (B_idx j).2 := dyadicCubeNoProperContainmentSameScale h_ij'
        -- Если масштабы и индексы равны, B_i = B_j, значит B_idx i = B_idx j
        have hidx_eq : B_idx i = B_idx j := Prod.ext hji_eq.symm (funext fun x => congrFun heq x)
        -- По инъективности B_idx (из перечисления Denumerable) i = j
        exact hij (hB_idx_inj hidx_eq)
      · -- (B_idx i).1 < (B_idx j).1 : i — более грубый масштаб (больший куб), j — более тонкий
        -- (меньший куб)
        -- h_ij говорит, что больший куб ⊆ меньшему, что геометрически невозможно при d > 0
        have h_scale_lt : (↑(B_idx i).1 : ℤ) < ↑(B_idx j).1 := by exact_mod_cast hji_gt
        exact dyadicCubeLargerNotInSmaller hd h_scale_lt h_ij
    · -- B j ⊆ B i : симметричный случай
      exfalso
      rcases lt_trichotomy (B_idx i).1 (B_idx j).1 with hij_lt | hij_eq | hij_gt
      · -- i грубее (больше), j тоньше (меньше), B_j ⊆ B_i геометрически допустимо
        -- Это противоречит максимальности B_j: B_j ⊆ B_i ⊆ E, а i грубее
        exact hj_mem.2 (B_idx i) hij_lt h_ji hi_mem.1
      · -- Одинаковый масштаб : используем инъективность, как в симметричном случае выше
        have h_ji' : (DyadicCube (↑(B_idx j).1) (B_idx j).2).toSet ⊆
            (DyadicCube (↑(B_idx j).1) (B_idx i).2).toSet := by
          convert h_ji using 3; simp only [Nat.cast_inj]; exact hij_eq.symm
        have heq : (B_idx j).2 = (B_idx i).2 := dyadicCubeNoProperContainmentSameScale h_ji'
        have hidx_eq : B_idx j = B_idx i := Prod.ext hij_eq.symm (funext fun x => congrFun heq x)
        exact hij (hB_idx_inj hidx_eq).symm
      · -- j грубее (больше), i тоньше (меньше), B_j ⊆ B_i означает больший внутри меньшего
        -- Геометрически невозможно при d > 0
        have h_scale_lt : (↑(B_idx j).1 : ℤ) < ↑(B_idx i).1 := by exact_mod_cast hij_gt
        exact dyadicCubeLargerNotInSmaller hd h_scale_lt h_ji

theorem Lebesgue_outer_measure.of_open {d : ℕ} (E : Set (EuclideanSpace' d)) (hE : IsOpen E) : Lebesgue_outer_measure E = Jordan_inner_measure E := by
  by_cases hd : d = 0
  · -- Размерность 0 : в размерности 0 открытые множества — это либо ∅, либо Set.univ
    subst hd
    rw [Lebesgue_outer_measure_of_dim_zero]
    by_cases hne : E.Nonempty
    · -- Случай : E непусто → E = Set.univ в размерности 0
      simp only [hne, ↓reduceIte]
      -- Покажем Jordan_inner_measure E = 1
      -- E = Set.univ, поскольку EuclideanSpace' 0 — одноточечное пространство, а E непусто
      have hE_univ : E = Set.univ := by
        ext x
        constructor
        · intro _; exact Set.mem_univ x
        · intro _
          obtain ⟨y, hy⟩ := hne
          have : x = y := by ext i; exact i.elim0
          rw [this]; exact hy
      -- Set.univ элементарно с мерой 1 в размерности 0
      let B : Box 0 := ⟨fun i => i.elim0⟩
      have hB_univ : B.toSet = Set.univ := by
        ext x; simp only [Box.toSet, Set.mem_univ, iff_true]; intro i; exact i.elim0
      have hB_vol : |B|ᵥ = 1 := by simp only [Box.volume, Finset.univ_eq_empty, Finset.prod_empty]
      -- Jordan_inner_measure E ≥ мере B (поскольку B ⊆ E = univ)
      have h_ge : (IsElementary.box B).measure ≤ Jordan_inner_measure E := by
        unfold Jordan_inner_measure
        apply le_csSup
        · use 1
          intro m hm
          obtain ⟨A, hA, hA_subset, rfl⟩ := hm
          -- У любого элементарного подмножества Set.univ в размерности 0 мера ≤ 1
          by_cases hA_ne : A.Nonempty
          · have hA_univ : A = Set.univ := by
              ext x; constructor; intro _; exact Set.mem_univ x
              intro _; obtain ⟨y, hy⟩ := hA_ne; have : x = y := by ext i; exact i.elim0
              rw [this]; exact hy
            have : hA.measure = 1 := by
              have h_eq : hA.measure = (IsElementary.box B).measure := by
                apply IsElementary.measure_eq_of_set_eq; rw [hA_univ, hB_univ]
              rw [h_eq, IsElementary.measure_of_box, hB_vol]
            rw [this]
          · have hA_empty : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA_ne
            have : hA.measure = 0 := by
              have h_eq : hA.measure = (IsElementary.empty 0).measure :=
                IsElementary.measure_eq_of_set_eq hA (IsElementary.empty 0) hA_empty
              rw [h_eq, IsElementary.measure_of_empty]
            rw [this]; norm_num
        · use B.toSet, IsElementary.box B; simp [hE_univ, hB_univ]
      -- Jordan_inner_measure E ≤ 1 (поскольку E ⊆ Set.univ, а у univ внешняя мера 1)
      have h_le : Jordan_inner_measure E ≤ 1 := by
        unfold Jordan_inner_measure
        apply csSup_le
        · use 0, ∅, IsElementary.empty 0; simp [IsElementary.measure_of_empty]
        · intro m hm
          obtain ⟨A, hA, hA_subset, rfl⟩ := hm
          by_cases hA_ne : A.Nonempty
          · have hA_univ : A = Set.univ := by
              ext x; constructor; intro _; exact Set.mem_univ x
              intro _; obtain ⟨y, hy⟩ := hA_ne; have : x = y := by ext i; exact i.elim0
              rw [this]; exact hy
            have : hA.measure = 1 := by
              have h_eq : hA.measure = (IsElementary.box B).measure := by
                apply IsElementary.measure_eq_of_set_eq; rw [hA_univ, hB_univ]
              rw [h_eq, IsElementary.measure_of_box, hB_vol]
            rw [this]
          · have hA_empty : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA_ne
            have : hA.measure = 0 := by
              have h_eq : hA.measure = (IsElementary.empty 0).measure :=
                IsElementary.measure_eq_of_set_eq hA (IsElementary.empty 0) hA_empty
              rw [h_eq, IsElementary.measure_of_empty]
            rw [this]; norm_num
      -- Объединяем h_ge и h_le, чтобы получить Jordan_inner_measure E = 1
      have h_jordan_eq_1 : Jordan_inner_measure E = 1 := by
        rw [IsElementary.measure_of_box, hB_vol] at h_ge
        exact (h_ge.antisymm h_le).symm
      rw [h_jordan_eq_1]
      norm_num
    · -- Случай : E пусто
      have hE_empty : E = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      simp only [hne, if_false]
      subst hE_empty
      -- Покажем (0 : EReal) = ↑(Jordan_inner_measure ∅)
      -- Сначала докажем Jordan_inner_measure ∅ = 0
      have h_jordan_empty : Jordan_inner_measure (∅ : Set (EuclideanSpace' 0)) = 0 := by
        unfold Jordan_inner_measure
        apply le_antisymm
        · apply csSup_le
          · use 0, ∅, IsElementary.empty 0; simp [IsElementary.measure_of_empty]
          · intro m hm
            obtain ⟨A, hA, hA_subset, rfl⟩ := hm
            have hA_empty : A = ∅ := Set.subset_empty_iff.mp hA_subset
            subst hA_empty
            exact le_of_eq (IsElementary.measure_of_empty 0)
        · apply le_csSup
          · use 0; intro m hm
            obtain ⟨A, hA, hA_subset, rfl⟩ := hm
            have hA_empty : A = ∅ := Set.subset_empty_iff.mp hA_subset
            subst hA_empty
            exact le_of_eq (IsElementary.measure_of_empty 0)
          · use ∅, IsElementary.empty 0; simp [IsElementary.measure_of_empty]
      rw [h_jordan_empty]
      norm_num
  · push_neg at hd
    have hd' : 0 < d := Nat.pos_of_ne_zero hd
    by_cases hE_empty : E = ∅
    · -- Случай пустого множества : используем Lebesgue_outer_measure.of_empty и
      -- Jordan_inner_measure ∅ = 0
      subst hE_empty
      rw [Lebesgue_outer_measure.of_empty]
      -- Покажем (0 : EReal) = ↑(Jordan_inner_measure ∅)
      -- Сначала докажем Jordan_inner_measure ∅ = 0
      have h_jordan_empty : Jordan_inner_measure (∅ : Set (EuclideanSpace' d)) = 0 := by
        unfold Jordan_inner_measure
        apply le_antisymm
        · apply csSup_le
          · use 0, ∅, IsElementary.empty d; simp [IsElementary.measure_of_empty]
          · intro m hm
            obtain ⟨A, hA, hA_subset, rfl⟩ := hm
            have hA_empty : A = ∅ := Set.subset_empty_iff.mp hA_subset
            subst hA_empty
            exact le_of_eq (IsElementary.measure_of_empty d)
        · apply le_csSup
          · use 0; intro m hm
            obtain ⟨A, hA, hA_subset, rfl⟩ := hm
            have hA_empty : A = ∅ := Set.subset_empty_iff.mp hA_subset
            subst hA_empty
            exact le_of_eq (IsElementary.measure_of_empty d)
          · use ∅, IsElementary.empty d; simp [IsElementary.measure_of_empty]
      rw [h_jordan_empty]
      norm_num
    · -- Основной случай : E — непустое открытое множество в размерности > 0
      have hE_nonempty : E.Nonempty := Set.nonempty_iff_ne_empty.mpr hE_empty
      -- Раскладываем E на почти непересекающиеся диадические прямоугольники
      obtain ⟨B, hE_eq, hB_dyadic, hB_disj⟩ := IsOpen.eq_union_boxes hd' E hE hE_nonempty
      -- Применяем лемму eq_Jordan_inner_of_boxes (упражнение 1.2.5)
      exact Lebesgue_outer_measure.eq_Jordan_inner_of_boxes E B hE_eq hB_disj

/-- Лемма 1.2.12 (Внешняя регулярность). m\*(E) = inf\{m\*(U) : E ⊆ U, U открыто\}. -/
theorem Lebesgue_outer_measure.eq {d : ℕ} (E : Set (EuclideanSpace' d)) : Lebesgue_outer_measure E = sInf { M | ∃ U, E ⊆ U ∧ IsOpen U ∧ M = Lebesgue_outer_measure U} := by
  let S := { M | ∃ U, E ⊆ U ∧ IsOpen U ∧ M = Lebesgue_outer_measure U}
  apply le_antisymm
  · -- Направление ≤ : m*(E) ≤ sInf S (по монотонности m*(E) — нижняя грань)
    apply le_csInf
    · -- S непусто (Set.univ открыто и содержит E)
      exact ⟨Lebesgue_outer_measure Set.univ, Set.univ, Set.subset_univ E, isOpen_univ, rfl⟩
    · -- m*(E) — нижняя грань S
      intro M ⟨U, hE_sub_U, _hU_open, hM_eq⟩
      rw [hM_eq]
      exact Lebesgue_outer_measure.mono hE_sub_U
  · -- Направление ≥ : sInf S ≤ m*(E) (основная работа)
    -- Отдельно обрабатываем размерность 0
    by_cases hd : d = 0
    · -- d = 0 : в размерности 0 EuclideanSpace' 0 — одноточечный тип
      subst hd
      have h_singleton : ∀ (y z : EuclideanSpace' 0), y = z := fun y z =>
        PiLp.ext fun i => Fin.elim0 i
      by_cases hE_empty : E = ∅
      · -- E = ∅ : m*(∅) = 0, а sInf S ≥ 0 (все внешние меры ≥ 0)
        -- На самом деле нужно sInf S ≤ m*(E) = 0
        -- Поскольку ∅ открыто и содержит E = ∅, m*(∅) ∈ S
        rw [hE_empty]
        apply csInf_le_of_le
        · use 0
          intro M ⟨U, _, _, hM⟩
          rw [hM]
          exact Lebesgue_outer_measure.nonneg U
        · exact ⟨∅, Set.Subset.rfl, isOpen_empty, rfl⟩
        · exact le_refl _
      · -- E ≠ ∅ : тогда E = Set.univ (поскольку любое непустое множество в одноточечном пространстве — это univ)
        have hE_univ : E = Set.univ := by
          ext x; constructor
          · intro _; exact Set.mem_univ x
          · intro _
            have hE_nonempty : E.Nonempty := Set.nonempty_iff_ne_empty.mpr hE_empty
            obtain ⟨e, he⟩ := hE_nonempty
            rw [h_singleton x e]
            exact he
        rw [hE_univ]
        apply csInf_le_of_le
        · use 0
          intro M ⟨U, _, _, hM⟩
          rw [hM]
          exact Lebesgue_outer_measure.nonneg U
        · exact ⟨Set.univ, Set.subset_univ _, isOpen_univ, rfl⟩
        · exact le_refl _
    -- d > 0: основной аргумент
    push_neg at hd
    have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
    -- Разбор случаев по тому, равно ли m*(E) = ⊤
    by_cases h_top : Lebesgue_outer_measure E = ⊤
    · -- m*(E) = ⊤ : тривиально sInf S ≤ ⊤
      rw [h_top]
      exact le_top
    -- m*(E) конечно: используем ε-аргумент
    apply EReal.le_of_forall_pos_le_add'
    intro ε hε
    -- Используем ε/2 для покрытия и ε/2 для увеличения, чтобы получить общую оценку m*(E) + ε
    have hε2_pos : 0 < ε / 2 := by linarith
    -- Берём покрытие, близкое к m*(E): ∃ B₁, B₂,... с ∑|Bₙ| ≤ m*(E) + ε/2
    obtain ⟨B, hB_cover, hB_sum⟩ := exists_cover_close hd_pos E (ε/2) hε2_pos h_top
    -- Увеличиваем каждый прямоугольник Bₙ до открытого прямоугольника B'ₙ с
    -- |B'ₙ| ≤ |Bₙ| + (ε/2)/2^{n+1}
    have h_inflate : ∀ n, ∃ B'n : Box d, (B n).toSet ⊆ interior B'n.toSet ∧
        IsOpen (interior B'n.toSet) ∧ |B'n|ᵥ ≤ |(B n)|ᵥ + (ε/2) / 2^(n+1) := by
      intro n
      have h_eps_pos : 0 < (ε/2) / 2^(n+1) := by positivity
      exact Box.inflate (B n) ((ε/2) / 2^(n+1)) h_eps_pos
    choose B' hB'_subset hB'_open hB'_vol using h_inflate
    -- Определяем открытое множество U = ⋃ₙ interior B'ₙ
    let U := ⋃ n, interior (B' n).toSet
    -- U открыто (объединение открытых множеств)
    have hU_open : IsOpen U := isOpen_iUnion (fun n => hB'_open n)
    -- E ⊆ U (поскольку E ⊆ ⋃ₙ Bₙ.toSet ⊆ ⋃ₙ interior B'ₙ.toSet = U)
    have hE_sub_U : E ⊆ U := fun x hx => by
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hB_cover hx)
      exact Set.mem_iUnion.mpr ⟨n, hB'_subset n hn⟩
    -- m*(U) ≤ ∑ₙ m*(interior B'ₙ.toSet) ≤ ∑ₙ |B'ₙ|ᵥ (по субаддитивности + элементарной мере)
    have hU_measure : Lebesgue_outer_measure U ≤ ∑' n, (B' n).volume.toEReal := by
      -- Во-первых: m*(U) ≤ ∑' m*(interior B'ₙ) по счётной субаддитивности
      have h_subadditive := Lebesgue_outer_measure.union_le (fun n => interior (B' n).toSet)
      -- Во-вторых: ∀n, m*(interior B'ₙ) ≤ |B'ₙ|ᵥ
      have h_pointwise : ∀ n, Lebesgue_outer_measure (interior (B' n).toSet) ≤ (B' n).volume.toEReal := by
        intro n
        calc Lebesgue_outer_measure (interior (B' n).toSet)
            ≤ Lebesgue_outer_measure (B' n).toSet := Lebesgue_outer_measure.mono interior_subset
          _ = (B' n).volume.toEReal := by
              have h_elem : IsElementary (B' n).toSet := IsElementary.box (B' n)
              rw [Lebesgue_outer_measure.elementary (B' n).toSet h_elem, IsElementary.measure_of_box]
      -- В-третьих: используем сравнение tsum в EReal
      have h_nonneg_f : ∀ n, 0 ≤ Lebesgue_outer_measure (interior (B' n).toSet) :=
        fun n => Lebesgue_outer_measure.nonneg _
      have h_nonneg_g : ∀ n, 0 ≤ (B' n).volume := fun n => Box.volume_nonneg _
      have h_summable_g : Summable (fun n => (B' n).volume) := by
        -- |B'ₙ| ≤ |Bₙ| + (ε/2)/2^{n+1}. Суммируемо, потому что:
        -- 1. Геометрический ряд ∑(ε/2)/2^{n+1} суммируем
        -- 2. Сумма объёмов B ≤ m*(E) + ε/2 < ⊤, значит они суммируемы в ℝ
        -- 3. По признаку сравнения объёмы B' суммируемы
        -- Технические детали делегированы леммам о суммируемости
        have h_geom_summable : Summable (fun n : ℕ => ε / 2 / 2 ^ (n + 1)) := by
          -- Используем шаблон tsum_geometric_eps: ∑ ε/2^{n+1} = ε
          -- Значит ∑ (ε/2)/2^{n+1} = ε/2, что сходится
          have h_summable_base : Summable (fun n : ℕ => (1/2 : ℝ)^n) :=
            summable_geometric_of_lt_one (by norm_num) (by norm_num)
          have h_eq : (fun n : ℕ => ε / 2 / 2 ^ (n + 1)) = (fun n : ℕ => (ε / 4) * (1/2)^n) := by
            ext n
            have h_two_pow_pos : (0 : ℝ) < 2^(n+1) := by positivity
            have h_two_pow_ne : (2 : ℝ)^(n+1) ≠ 0 := h_two_pow_pos.ne'
            field_simp [h_two_pow_ne]
            ring_nf; simp
          rw [h_eq]
          exact h_summable_base.mul_left (ε / 4)
        have h_B_nonneg : ∀ n, 0 ≤ (B n).volume := fun n => Box.volume_nonneg _
        have h_B_summable : Summable (fun n => (B n).volume) := by
          -- Из hB_sum: ∑' (B n).volume.toEReal ≤ m*(E) + ε/2 < ⊤
          -- Извлекаем вещественную верхнюю границу из hB_sum
          have h_rhs_ne_top : Lebesgue_outer_measure E + (↑(ε / 2) : EReal) ≠ ⊤ :=
            EReal.add_ne_top h_top (EReal.coe_ne_top _)
          -- Получаем вещественную границу M такую, что tsum ≤ M
          have h_exists_M : ∃ M : ℝ, Lebesgue_outer_measure E + (↑(ε / 2) : EReal) ≤ M := by
            cases h_rhs : (Lebesgue_outer_measure E + (↑(ε / 2) : EReal)) with
            | bot => exact ⟨0, le_of_lt (EReal.bot_lt_coe _)⟩
            | coe r => exact ⟨r, le_refl _⟩
            | top => exact (h_rhs_ne_top h_rhs).elim
          obtain ⟨M, hM_ge⟩ := h_exists_M
          have h_tsum_le_M : ∑' n, (B n).volume.toEReal ≤ M := le_trans hB_sum hM_ge
          -- Используем summable_of_sum_range_le: нужно ∀ n, ∑_{i<n} f i ≤ M
          apply summable_of_sum_range_le h_B_nonneg
          intro n
          have h_partial := EReal.finset_sum_le_tsum h_B_nonneg (Finset.range n)
          have h_chain := le_trans h_partial h_tsum_le_M
          rw [← EReal.coe_finset_sum (fun i _ => h_B_nonneg i)] at h_chain
          exact EReal.coe_le_coe_iff.mp h_chain
        exact Summable.of_nonneg_of_le (fun n => Box.volume_nonneg _)
          (fun n => hB'_vol n) (h_B_summable.add h_geom_summable)
      calc Lebesgue_outer_measure U
          ≤ ∑' n, Lebesgue_outer_measure (interior (B' n).toSet) := h_subadditive
        _ ≤ ∑' n, (B' n).volume.toEReal :=
            EReal.tsum_le_coe_tsum_of_forall_le h_nonneg_f h_nonneg_g h_summable_g h_pointwise
    -- ∑ₙ |B'ₙ|ᵥ ≤ ∑ₙ (|Bₙ|ᵥ + (ε/2)/2^{n+1}) = ∑ₙ |Bₙ|ᵥ + ε/2 (поскольку ∑(ε/2)/2^{n+1} = ε/2)
    have hB'_vol_sum : (∑' n, (B' n).volume.toEReal) ≤ (∑' n, (B n).volume.toEReal) + (ε/2 : ℝ) := by
      -- Поточечно: |B'ₙ| ≤ |Bₙ| + (ε/2)/2^{n+1}
      -- Значит ∑|B'ₙ| ≤ ∑|Bₙ| + ∑(ε/2)/2^{n+1} = ∑|Bₙ| + ε/2
      have h_B_nonneg : ∀ n, 0 ≤ (B n).volume := fun n => Box.volume_nonneg _
      have h_geom_nonneg : ∀ n, 0 ≤ (ε/2) / 2^(n+1) := fun n => by positivity
      have h_pw : ∀ n, (B n).volume + (ε/2) / 2^(n+1) ≤ (B n).volume + (ε/2) / 2^(n+1) := fun n => le_refl _
      -- Используем вспомогательный факт: ∑|B'ₙ| ≤ ∑(|Bₙ| + δₙ), поскольку |B'ₙ| ≤ |Bₙ| + δₙ
      have h_B'_le_sum : ∀ n, (B' n).volume ≤ (B n).volume + (ε/2) / 2^(n+1) := hB'_vol
      have h_B'_nonneg : ∀ n, 0 ≤ (B' n).volume := fun n => Box.volume_nonneg _
      have h_B'_nonneg_EReal : ∀ n, (0 : EReal) ≤ (B' n).volume.toEReal :=
        fun n => EReal.coe_nonneg.mpr (h_B'_nonneg n)
      -- ∑|B'ₙ| ≤ ∑(|Bₙ| + δₙ) по поточечной оценке
      have h_step1 : (∑' n, (B' n).volume.toEReal) ≤ ∑' n, ((B n).volume + (ε/2) / 2^(n+1)).toEReal := by
        apply EReal.tsum_le_coe_tsum_of_forall_le h_B'_nonneg_EReal
          (fun n => add_nonneg (h_B_nonneg n) (h_geom_nonneg n))
        · -- Суммируемость |Bₙ| + δₙ
          have h_geom_summable : Summable (fun n : ℕ => (ε/2) / 2^(n+1)) := by
            have h_summable_base : Summable (fun n : ℕ => (1/2 : ℝ)^n) :=
              summable_geometric_of_lt_one (by norm_num) (by norm_num)
            have h_eq : (fun n : ℕ => (ε/2) / 2 ^ (n + 1)) = (fun n : ℕ => (ε / 4) * (1/2)^n) := by
              ext n
              have h_two_pow_ne : (2 : ℝ)^(n+1) ≠ 0 := by positivity
              field_simp [h_two_pow_ne]; ring_nf; simp
            rw [h_eq]
            exact h_summable_base.mul_left (ε / 4)
          have h_B_summable : Summable (fun n => (B n).volume) := by
            have h_rhs_ne_top : Lebesgue_outer_measure E + (↑(ε / 2) : EReal) ≠ ⊤ :=
              EReal.add_ne_top h_top (EReal.coe_ne_top _)
            have h_exists_M : ∃ M : ℝ, Lebesgue_outer_measure E + (↑(ε / 2) : EReal) ≤ M := by
              cases h_rhs : (Lebesgue_outer_measure E + (↑(ε / 2) : EReal)) with
              | bot => exact ⟨0, le_of_lt (EReal.bot_lt_coe _)⟩
              | coe r => exact ⟨r, le_refl _⟩
              | top => exact (h_rhs_ne_top h_rhs).elim
            obtain ⟨M, hM_ge⟩ := h_exists_M
            have h_tsum_le_M : ∑' n, (B n).volume.toEReal ≤ M := le_trans hB_sum hM_ge
            apply summable_of_sum_range_le h_B_nonneg
            intro n
            have h_partial := EReal.finset_sum_le_tsum h_B_nonneg (Finset.range n)
            have h_chain := le_trans h_partial h_tsum_le_M
            rw [← EReal.coe_finset_sum (fun i _ => h_B_nonneg i)] at h_chain
            exact EReal.coe_le_coe_iff.mp h_chain
          exact h_B_summable.add h_geom_summable
        · exact fun n => EReal.coe_le_coe_iff.mpr (h_B'_le_sum n)
      -- Теперь разделяем ∑(|Bₙ| + δₙ) = ∑|Bₙ| + ∑δₙ
      have h_step2 : (∑' n, ((B n).volume + (ε/2) / 2^(n+1)).toEReal) =
          (∑' n, (B n).volume.toEReal) + (∑' n, ((ε/2) / 2^(n+1)).toEReal) := by
        -- Для вещественных чисел ∑(f + g) = ∑f + ∑g, когда они суммируемы
        have h_geom_summable : Summable (fun n : ℕ => (ε/2) / 2^(n+1)) := by
          have h_summable_base : Summable (fun n : ℕ => (1/2 : ℝ)^n) :=
            summable_geometric_of_lt_one (by norm_num) (by norm_num)
          have h_eq : (fun n : ℕ => (ε/2) / 2 ^ (n + 1)) = (fun n : ℕ => (ε / 4) * (1/2)^n) := by
            ext n
            have h_two_pow_ne : (2 : ℝ)^(n+1) ≠ 0 := by positivity
            field_simp [h_two_pow_ne]; ring_nf; simp
          rw [h_eq]
          exact h_summable_base.mul_left (ε / 4)
        have h_B_summable : Summable (fun n => (B n).volume) := by
          have h_rhs_ne_top : Lebesgue_outer_measure E + (↑(ε / 2) : EReal) ≠ ⊤ :=
            EReal.add_ne_top h_top (EReal.coe_ne_top _)
          have h_exists_M : ∃ M : ℝ, Lebesgue_outer_measure E + (↑(ε / 2) : EReal) ≤ M := by
            cases h_rhs : (Lebesgue_outer_measure E + (↑(ε / 2) : EReal)) with
            | bot => exact ⟨0, le_of_lt (EReal.bot_lt_coe _)⟩
            | coe r => exact ⟨r, le_refl _⟩
            | top => exact (h_rhs_ne_top h_rhs).elim
          obtain ⟨M, hM_ge⟩ := h_exists_M
          have h_tsum_le_M : ∑' n, (B n).volume.toEReal ≤ M := le_trans hB_sum hM_ge
          apply summable_of_sum_range_le h_B_nonneg
          intro n
          have h_partial := EReal.finset_sum_le_tsum h_B_nonneg (Finset.range n)
          have h_chain := le_trans h_partial h_tsum_le_M
          rw [← EReal.coe_finset_sum (fun i _ => h_B_nonneg i)] at h_chain
          exact EReal.coe_le_coe_iff.mp h_chain
        -- Используем tsum_add для вещественных чисел
        have h_real_tsum : ∑' n, ((B n).volume + (ε/2) / 2^(n+1)) =
            (∑' n, (B n).volume) + (∑' n, (ε/2) / 2^(n+1)) :=
          h_B_summable.tsum_add h_geom_summable
        -- Приводим к EReal
        have h_sum_nonneg : ∀ n, 0 ≤ (B n).volume + (ε/2) / 2^(n+1) :=
          fun n => add_nonneg (h_B_nonneg n) (h_geom_nonneg n)
        -- Используем symm, чтобы получить: ∑' ↑(...) = ↑(∑' ...)
        rw [← EReal.coe_tsum_of_nonneg h_sum_nonneg (h_B_summable.add h_geom_summable)]
        rw [← EReal.coe_tsum_of_nonneg h_B_nonneg h_B_summable]
        rw [← EReal.coe_tsum_of_nonneg h_geom_nonneg h_geom_summable]
        rw [h_real_tsum]
        simp only [EReal.coe_add]
      -- ∑δₙ = ε/2
      have h_geom_sum : (∑' n, ((ε/2) / 2^(n+1)).toEReal) = (ε/2 : EReal) := by
        -- ∑ (ε/2)/2^{n+1} = (ε/2) * ∑ 1/2^{n+1} = (ε/2) * 1 = ε/2
        have h_geom_summable' : Summable (fun n : ℕ => (ε/2) / 2^(n+1)) := by
          have h_summable_base : Summable (fun n : ℕ => (1/2 : ℝ)^n) :=
            summable_geometric_of_lt_one (by norm_num) (by norm_num)
          have h_eq : (fun n : ℕ => (ε/2) / 2 ^ (n + 1)) = (fun n : ℕ => (ε / 4) * (1/2)^n) := by
            ext n
            have h_two_pow_ne : (2 : ℝ)^(n+1) ≠ 0 := by positivity
            field_simp [h_two_pow_ne]; ring_nf; simp
          rw [h_eq]
          exact h_summable_base.mul_left (ε / 4)
        have h_real_sum : ∑' n : ℕ, (ε/2) / 2^(n+1) = ε/2 := by
          have h_eq : (fun n : ℕ => (ε/2) / 2^(n+1)) = (fun n : ℕ => (ε/2) * (1/2)^(n+1)) := by
            ext n; field_simp; simp
          rw [h_eq, tsum_mul_left]
          have h_geom_sum_one : ∑' n : ℕ, (1/2 : ℝ)^(n+1) = 1 := by
            have h_summable : Summable (fun n : ℕ => (1/2 : ℝ)^n) :=
              summable_geometric_of_lt_one (by norm_num) (by norm_num)
            have h_formula := h_summable.sum_add_tsum_nat_add 1
            simp only [Finset.range_one, Finset.sum_singleton, pow_zero] at h_formula
            rw [tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1 : ℝ)/2 < 1)] at h_formula
            linarith
          rw [h_geom_sum_one]; ring
        -- Приводим tsum в EReal: ∑' n, (ε/2 / 2^(n+1)).toEReal = (ε/2 : EReal)
        rw [← EReal.coe_tsum_of_nonneg h_geom_nonneg h_geom_summable', h_real_sum, EReal.coe_div]
        norm_cast
      calc ∑' n, (B' n).volume.toEReal
          ≤ ∑' n, ((B n).volume + (ε/2) / 2^(n+1)).toEReal := h_step1
        _ = (∑' n, (B n).volume.toEReal) + (∑' n, ((ε/2) / 2^(n+1)).toEReal) := h_step2
        _ = (∑' n, (B n).volume.toEReal) + (ε/2 : EReal) := by rw [h_geom_sum]
    -- Объединяем: m*(U) ≤ m*(E) + ε
    have hU_bound : Lebesgue_outer_measure U ≤ Lebesgue_outer_measure E + ε := by
      calc Lebesgue_outer_measure U
          ≤ ∑' n, (B' n).volume.toEReal := hU_measure
        _ ≤ (∑' n, (B n).volume.toEReal) + (ε/2 : ℝ) := hB'_vol_sum
        _ ≤ (Lebesgue_outer_measure E + (ε/2 : ℝ)) + (ε/2 : ℝ) := by
            apply add_le_add_left hB_sum
        _ = Lebesgue_outer_measure E + ε := by
            rw [add_assoc]
            congr 1
            norm_cast
            ring
    -- sInf S ≤ m*(U), поскольку U ∈ S
    have h_U_in_S : Lebesgue_outer_measure U ∈ S :=
      ⟨U, hE_sub_U, hU_open, rfl⟩
    calc sInf S
        ≤ Lebesgue_outer_measure U := csInf_le ⟨0, fun M ⟨V, _, _, hM⟩ => hM ▸ Lebesgue_outer_measure.nonneg V⟩ h_U_in_S
      _ ≤ Lebesgue_outer_measure E + ε := hU_bound

/-- Для любого множества E и ε > 0 существует открытое U ⊇ E с m*(U) ≤ m*(E) + ε.
    Это следует из внешней регулярности (лемма 1.2.12). -/
lemma Lebesgue_outer_measure.exists_open_superset_measure_le {d : ℕ} (E : Set (EuclideanSpace' d)) (ε : EReal) (hε : 0 < ε) :
    ∃ U : Set (EuclideanSpace' d), IsOpen U ∧ E ⊆ U ∧ Lebesgue_outer_measure U ≤ Lebesgue_outer_measure E + ε := by
  -- По внешней регулярности (Lebesgue_outer_measure.eq):
  -- m*(E) = sInf { m*(U) | E ⊆ U ∧ IsOpen U }
  have h_outer_reg := Lebesgue_outer_measure.eq (d := d) E
  let S := {M | ∃ U, E ⊆ U ∧ IsOpen U ∧ M = Lebesgue_outer_measure U}
  have h_set_nonempty : S.Nonempty := by
    use Lebesgue_outer_measure (Set.univ : Set (EuclideanSpace' d))
    exact ⟨Set.univ, Set.subset_univ E, isOpen_univ, rfl⟩
  have h_inf : IsGLB S (sInf S) := isGLB_sInf S
  have h_ne_bot : sInf S ≠ ⊥ := by
    intro h_eq
    rw [h_eq] at h_inf
    have h_zero_lb : (0 : EReal) ∈ lowerBounds S := by
      intro v hv
      obtain ⟨U, _, _, rfl⟩ := hv
      exact Lebesgue_outer_measure.nonneg U
    have h_le : (0 : EReal) ≤ ⊥ := h_inf.2 h_zero_lb
    exact not_le.mpr EReal.bot_lt_zero h_le
  by_cases h_top : sInf S = ⊤
  · use Set.univ
    refine ⟨isOpen_univ, Set.subset_univ E, ?_⟩
    rw [h_outer_reg, h_top]
    cases ε with
    | bot => exact absurd hε (not_lt.mpr bot_le)
    | top => exact le_top
    | coe r => exact le_top
  · have h_lt : sInf S < sInf S + ε := by
      cases ε with
      | bot => exact absurd hε (not_lt.mpr bot_le)
      | top =>
        have h_sum_top : sInf S + ⊤ = ⊤ := by
          cases h : sInf S with
          | bot => exact absurd h h_ne_bot
          | top => exact absurd h h_top
          | coe r => rfl
        rw [h_sum_top]
        exact lt_top_iff_ne_top.mpr h_top
      | coe r =>
        have hr_pos : 0 < r := EReal.coe_pos.mp hε
        exact EReal.lt_add_of_pos_coe hr_pos h_ne_bot h_top
    have h_not_lb : sInf S + ε ∉ lowerBounds S := by
      intro h_is_lb
      have h_le : sInf S + ε ≤ sInf S := h_inf.2 h_is_lb
      exact not_lt.mpr h_le h_lt
    unfold lowerBounds at h_not_lb
    simp only [Set.mem_setOf_eq] at h_not_lb
    push_neg at h_not_lb
    obtain ⟨v, hv_in_S, hv_lt⟩ := h_not_lb
    obtain ⟨U, hE_sub_U, hU_open, hv_eq⟩ := hv_in_S
    use U
    refine ⟨hU_open, hE_sub_U, ?_⟩
    rw [h_outer_reg, ← hv_eq]
    exact le_of_lt hv_lt

/-- У компактных множеств в евклидовом пространстве конечная внешняя мера Лебега. -/
lemma Lebesgue_outer_measure.finite_of_compact {d : ℕ} {E : Set (EuclideanSpace' d)}
    (hE : IsCompact E) : Lebesgue_outer_measure E ≠ ⊤ := by
  -- Случай пустого множества тривиален
  by_cases hE_empty : E = ∅
  · rw [hE_empty, Lebesgue_outer_measure.of_empty]; exact EReal.zero_ne_top
  -- Для непустого E: E компактно → E ограничено → E ⊆ closedBall x R → E ⊆ box [-M,M]^d
  have ⟨x, hx⟩ : E.Nonempty := Set.nonempty_iff_ne_empty.mpr hE_empty
  have h_bounded : Bornology.IsBounded E := IsCompact.isBounded hE
  have ⟨r, h_sub_ball⟩ : ∃ (r : ℝ), E ⊆ Metric.closedBall x r := by
    rwa [← Metric.isBounded_iff_subset_closedBall x]
  -- Строим большой прямоугольник (box) B, содержащий замкнутый шар
  let M := ‖x‖ + |r| + 2
  let B : Box d := { side := fun _ => BoundedInterval.Icc (-M) M }
  have h_E_sub_B : E ⊆ B.toSet := by
    intro y hy
    have h_in_ball : y ∈ Metric.closedBall x r := h_sub_ball hy
    simp only [Box.mem_toSet]
    intro i
    rw [Metric.mem_closedBall] at h_in_ball
    have h_dist : ‖y - x‖ ≤ r := h_in_ball
    have h_coord_diff : |(y - x) i| ≤ ‖y - x‖ := EuclideanSpace'.coord_le_norm (y - x) i
    have h_abs : |y i - x i| ≤ r := le_trans h_coord_diff h_dist
    have h_xi : |x i| ≤ ‖x‖ := EuclideanSpace'.coord_le_norm x i
    show y i ∈ (BoundedInterval.Icc (-M) M : Set ℝ)
    rw [BoundedInterval.set_Icc, Set.mem_Icc]
    rw [abs_le] at h_abs h_xi
    have h_r_bound : r ≤ |r| := le_abs_self r
    constructor <;> linarith
  have : IsElementary B.toSet := IsElementary.box B
  have h_B_finite : Lebesgue_outer_measure B.toSet ≠ ⊤ := by
    rw [Lebesgue_outer_measure.elementary B.toSet this]
    exact EReal.coe_ne_top _
  exact ne_top_of_le_ne_top h_B_finite (Lebesgue_outer_measure.mono h_E_sub_B)

/-- Упражнение 1.2.6 -/
example : ∃ (d : ℕ) (E : Set (EuclideanSpace' d)), Lebesgue_outer_measure E ≠ sSup { M | ∃ U, U ⊆ E ∧ IsOpen U ∧ M = Lebesgue_outer_measure U} := by sorry
