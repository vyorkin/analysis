import Analysis.MeasureTheory.Section_1_3_2

/-!
# Введение в теорию меры, раздел 1.3.3: беззнаковые интегралы Лебега

Сопровождение (введения) к разделу 1.3.3 книги "An introduction to Measure Theory".

-/

/-- Определение 1.3.12 (нижний беззнаковый интеграл Лебега) -/
noncomputable def LowerUnsignedLebesgueIntegral {d : ℕ} (f : EuclideanSpace' d → EReal) : EReal :=
  sSup { R | ∃ g : EuclideanSpace' d → EReal, ∃ hg : UnsignedSimpleFunction g, ∀ x, g x ≤ f x ∧ R = hg.integ}

/-- Определение 1.3.12 (верхний беззнаковый интеграл Лебега) -/
noncomputable def UpperUnsignedLebesgueIntegral {d : ℕ} (f : EuclideanSpace' d → EReal) : EReal :=
  sInf { R | ∃ g : EuclideanSpace' d → EReal, ∃ hg : UnsignedSimpleFunction g, ∀ x, g x ≥ f x ∧ R = hg.integ}

/-- Нижний интеграл Лебега функции `f ≥ 0` можно эквивалентно определить, взяв супремум по простым
    функциям `g`, для которых `g ≤ f` выполняется лишь почти всюду, а не всюду -/
theorem LowerUnsignedLebesgueIntegral.eq {d : ℕ} {f : EuclideanSpace' d → EReal} (hf : ∀ x, 0 ≤ f x) : LowerUnsignedLebesgueIntegral f =
  sSup { R | ∃ g : EuclideanSpace' d → EReal, ∃ hg : UnsignedSimpleFunction g, (AlmostAlways (fun x ↦ g x ≤ f x)) ∧ R = hg.integ} := by
  -- Обе стороны — супремумы по множествам интегралов простых функций g, ограниченных f.
  -- Слева: g ≤ f поточечно всюду; справа: g ≤ f почти всюду.
  -- Равенство следует из того, что интеграл простой функции не меняется при изменении на нулевом множестве.
  unfold LowerUnsignedLebesgueIntegral
  -- Сначала упростим странную формулировку определения: ∀ x, g x ≤ f x ∧ R = hg.integ равносильно
  -- (∀ x, g x ≤ f x) ∧ R = hg.integ (так как R = hg.integ не зависит от x)
  congr 1
  ext R
  simp only [Set.mem_setOf_eq]
  constructor
  · intro ⟨g, hg, hcond⟩
    -- Извлекаем поточечную оценку и равенство
    have hle : ∀ x, g x ≤ f x := fun x ↦ (hcond x).1
    have hReq : R = hg.integ := by
      -- hcond даёт нам R = hg.integ для любого x, так что берём произвольный x
      -- EuclideanSpace' d всегда непусто
      haveI : Nonempty (EuclideanSpace' d) := inferInstance
      exact (hcond (Classical.arbitrary _)).2
    exact ⟨g, hg, AlmostAlways.ofAlways hle, hReq⟩
  · intro ⟨g, hg, hae, hReq⟩
    -- Нужно найти g' с g' ≤ f всюду и тем же интегралом
    -- Пусть N = {x | g x > f x} — нулевое множество, на котором g превосходит f
    let N := {x | ¬(g x ≤ f x)}
    have hN_null : IsNull N := hae
    have hN_meas : LebesgueMeasurable N := IsNull.measurable hN_null
    -- Определяем g' = g * indicator(Nᶜ) = g там, где g ≤ f, и 0 в остальных точках
    let g' := fun x => g x * (EReal.indicator Nᶜ x)
    -- g' — простая функция (произведение простой функции на индикатор измеримого множества)
    have hg'_simple : UnsignedSimpleFunction g' := by
      -- Это следует из определения простых функций как линейных комбинаций индикаторов
      -- g = ∑ c_i • indicator(E_i), значит g' = ∑ c_i • indicator(E_i ∩ Nᶜ)
      obtain ⟨k, c, E, ⟨hcE, hg_eq⟩⟩ := hg
      use k, c, fun i => E i ∩ Nᶜ
      constructor
      · intro i
        constructor
        · exact LebesgueMeasurable.inter (hcE i).1 (LebesgueMeasurable.complement hN_meas)
        · exact (hcE i).2
      · -- Доказываем g' = ∑ c_i • indicator(E_i ∩ Nᶜ) поточечно
        funext x
        simp only [g', hg_eq, EReal.indicator, Real.EReal_fun]
        -- Используем Finset.sum_fn, чтобы превратить (∑ i, f i) x в ∑ i, f i x
        conv_lhs => rw [Finset.sum_fn]; simp only [Pi.smul_apply]
        conv_rhs => rw [Finset.sum_fn]; simp only [Pi.smul_apply]
        by_cases hx : x ∈ Nᶜ
        · -- x ∈ Nᶜ : умножаем на 1, и принадлежность E_i ∩ Nᶜ сводится к принадлежности E_i
          rw [Set.indicator'_of_mem hx, EReal.coe_one, mul_one]
          apply Finset.sum_congr rfl
          intro i _
          simp only [Real.EReal_fun]
          by_cases hEi : x ∈ E i
          · rw [Set.indicator'_of_mem hEi, Set.indicator'_of_mem (Set.mem_inter hEi hx)]
          · have hnotinter : x ∉ E i ∩ Nᶜ := fun h => hEi (Set.mem_of_mem_inter_left h)
            rw [Set.indicator'_of_notMem hEi, Set.indicator'_of_notMem hnotinter]
        · -- x ∉ Nᶜ : умножаем на 0, и E_i ∩ Nᶜ пусто в точке x
          rw [Set.indicator'_of_notMem hx, EReal.coe_zero, mul_zero]
          symm
          apply Finset.sum_eq_zero
          intro i _
          have hnotinter : x ∉ E i ∩ Nᶜ := fun h => hx (Set.mem_of_mem_inter_right h)
          simp only [Real.EReal_fun, Set.indicator'_of_notMem hnotinter, EReal.coe_zero, smul_zero]
    -- g' ≤ f всюду
    have hg'_le_f : ∀ x, g' x ≤ f x := by
      intro x
      by_cases hx : x ∈ N
      · -- На N : g' x = g x * 0 = 0 ≤ f x (используем hf)
        simp only [g', EReal.indicator, Real.EReal_fun]
        have hnotmem : x ∉ Nᶜ := by simp only [Set.mem_compl_iff, not_not]; exact hx
        rw [Set.indicator'_of_notMem hnotmem, EReal.coe_zero, mul_zero]
        exact hf x
      · -- На Nᶜ : g' x = g x * 1 = g x ≤ f x (по определению N)
        simp only [N, Set.mem_setOf_eq] at hx
        push_neg at hx
        simp only [g', EReal.indicator, Real.EReal_fun]
        have hmem : x ∈ Nᶜ := by simp only [Set.mem_compl_iff, N, Set.mem_setOf_eq, hx, not_true_eq_false, not_false_eq_true]
        rw [Set.indicator'_of_mem hmem, EReal.coe_one, mul_one]
        exact hx
    -- g' = g почти всюду (они отличаются только на N, а N — нулевое множество)
    have hg'_ae : AlmostEverywhereEqual g' g := by
      unfold AlmostEverywhereEqual AlmostAlways IsNull
      -- {x | g' x ≠ g x} ⊆ N, а N нулевое
      have hsub : {x | g' x ≠ g x} ⊆ N := by
        intro x hx
        simp only [Set.mem_setOf_eq] at hx
        by_contra hxN
        -- Если x ∉ N, то g' x = g x * 1 = g x
        have hmem : x ∈ Nᶜ := by simp only [Set.mem_compl_iff, N, Set.mem_setOf_eq]; exact hxN
        simp only [g', EReal.indicator, Real.EReal_fun, Set.indicator'_of_mem hmem,
                   EReal.coe_one, mul_one] at hx
        exact hx rfl
      have hle : Lebesgue_outer_measure {x | g' x ≠ g x} ≤ 0 :=
        calc Lebesgue_outer_measure {x | g' x ≠ g x}
            ≤ Lebesgue_outer_measure N := Lebesgue_outer_measure.mono hsub
          _ = 0 := hN_null
      exact le_antisymm hle (Lebesgue_outer_measure.nonneg _)
    -- По Упражнению 1.3.1(iv), интегралы совпадают
    have hinteg_eq : hg'_simple.integ = hg.integ :=
      UnsignedSimpleFunction.integral_eq_integral_of_aeEqual hg'_simple hg hg'_ae
    -- Теперь строим искомого свидетеля
    use g', hg'_simple
    intro x
    constructor
    · exact hg'_le_f x
    · rw [hReq, ← hinteg_eq]

/-- Упражнение 1.3.10(i) (согласованность с интегралом простой функции) -/
theorem LowerUnsignedLebesgueIntegral.eq_simpleIntegral {d : ℕ} {f : EuclideanSpace' d → EReal} (hf : UnsignedSimpleFunction f) : 
    LowerUnsignedLebesgueIntegral f = hf.integ := by sorry

/-- Упражнение 1.3.10(ii) (монотонность) -/
theorem LowerUnsignedLebesgueIntegral.mono {d : ℕ} {f g : EuclideanSpace' d → EReal} (hf : UnsignedMeasurable f) (hg : UnsignedMeasurable g)
    (hfg : AlmostAlways (fun x ↦ f x ≤ g x)) : 
    LowerUnsignedLebesgueIntegral f ≤ LowerUnsignedLebesgueIntegral g := by sorry

/-- Упражнение 1.3.10(iii) (однородность) -/
theorem LowerUnsignedLebesgueIntegral.hom {d : ℕ} {f : EuclideanSpace' d → EReal} (hf : UnsignedMeasurable f) {c : ℝ} (hc : 0 ≤ c) : 
    LowerUnsignedLebesgueIntegral ((c : EReal) • f) = c * LowerUnsignedLebesgueIntegral f := by sorry

/-- Упражнение 1.3.10(iv) (эквивалентность) -/
theorem LowerUnsignedLebesgueIntegral.integral_eq_integral_of_aeEqual {d : ℕ} {f g : EuclideanSpace' d → EReal} (hf : UnsignedMeasurable f) (hg : UnsignedMeasurable g)
    (heq : AlmostEverywhereEqual f g) : 
    LowerUnsignedLebesgueIntegral f = LowerUnsignedLebesgueIntegral g := by sorry

/-- Упражнение 1.3.10(v) (супераддитивность) -/
theorem LowerUnsignedLebesgueIntegral.superadditive {d : ℕ} {f g : EuclideanSpace' d → EReal} (hf : UnsignedMeasurable f) (hg : UnsignedMeasurable g) : 
    LowerUnsignedLebesgueIntegral (f + g) ≥ LowerUnsignedLebesgueIntegral f + LowerUnsignedLebesgueIntegral g := by sorry

/-- Упражнение 1.3.10(vi) (субаддитивность верхнего интеграла). -/
theorem UpperUnsignedLebesgueIntegral.subadditive {d : ℕ} {f g : EuclideanSpace' d → EReal} (hf : UnsignedMeasurable f) (hg : UnsignedMeasurable g) : 
    UpperUnsignedLebesgueIntegral (f + g) ≤ UpperUnsignedLebesgueIntegral f + UpperUnsignedLebesgueIntegral g := by sorry

/-- Упражнение 1.3.10(vii) (делимость) -/
theorem LowerUnsignedLebesgueIntegral.eq_add {d : ℕ} {f : EuclideanSpace' d → EReal} (hf : UnsignedMeasurable f) {E : Set (EuclideanSpace' d)} (hE : LebesgueMeasurable E) : 
    LowerUnsignedLebesgueIntegral f = LowerUnsignedLebesgueIntegral (f * Real.toEReal ∘ E.indicator') +
      LowerUnsignedLebesgueIntegral (f * Real.toEReal ∘ Eᶜ.indicator') := by sorry

/-- Упражнение 1.3.10(viii) (вертикальное усечение). -/
theorem LowerUnsignedLebesgueIntegral.eq_lim_vert_trunc {d : ℕ} {f : EuclideanSpace' d → EReal} (hf : UnsignedMeasurable f) : Filter.atTop.Tendsto (fun n : ℕ ↦ LowerUnsignedLebesgueIntegral (fun x ↦ min (f x) n)) (nhds (LowerUnsignedLebesgueIntegral f)) := by sorry

def UpperUnsignedLebesgueIntegral.eq_lim_vert_trunc : Decidable (∀ (d : ℕ) (f : EuclideanSpace' d → EReal) (hf : UnsignedMeasurable f), Filter.atTop.Tendsto (fun n : ℕ ↦ UpperUnsignedLebesgueIntegral (fun x ↦ min (f x) n)) (nhds (UpperUnsignedLebesgueIntegral f))) := by
  -- первой строкой этой конструкции должна быть либо `apply isTrue`, либо `apply isFalse`.
  sorry

/-- Упражнение 1.3.10(ix) (горизонтальное усечение). -/
theorem LowerUnsignedLebesgueIntegral.eq_lim_horiz_trunc {d : ℕ} {f : EuclideanSpace' d → EReal} (hf : UnsignedMeasurable f) : Filter.atTop.Tendsto (fun n : ℕ ↦ LowerUnsignedLebesgueIntegral (f * Real.toEReal ∘ (Metric.ball 0 n).indicator')) (nhds (LowerUnsignedLebesgueIntegral f)) := by sorry

def UpperUnsignedLebesgueIntegral.eq_lim_horiz_trunc : Decidable (∀ (d : ℕ) (f : EuclideanSpace' d → EReal) (hf : UnsignedMeasurable f), Filter.atTop.Tendsto (fun n : ℕ ↦ UpperUnsignedLebesgueIntegral (f * Real.toEReal ∘ (Metric.ball 0 n).indicator')) (nhds (UpperUnsignedLebesgueIntegral f))) := by
  -- первой строкой этой конструкции должна быть либо `apply isTrue`, либо `apply isFalse`.
  sorry

/-- Упражнение 1.3.10(x) (отражение) -/
theorem LowerUnsignedLebesgueIntegral.sum_of_reflect_eq {d : ℕ} {f g : EuclideanSpace' d → EReal} (hf : UnsignedMeasurable f) (hg : UnsignedMeasurable g)
    (hfg : UnsignedSimpleFunction (f+g)) (hbound : EReal.BoundedFunction (f + g)) (hsupport : FiniteMeasureSupport (f + g)) : 
    hfg.integ = LowerUnsignedLebesgueIntegral f + LowerUnsignedLebesgueIntegral g := by sorry

/-- Определение 1.3.13 (беззнаковый интеграл Лебега). Для целей Lean удобно присвоить этому интегралу
    "мусорное" значение, когда f не является беззнаково измеримой. -/
noncomputable def UnsignedLebesgueIntegral {d : ℕ} (f : EuclideanSpace' d → EReal) : EReal := LowerUnsignedLebesgueIntegral f

noncomputable def UnsignedMeasurable.integ {d : ℕ} (f : EuclideanSpace' d → EReal) (_ : UnsignedMeasurable f) : EReal := UnsignedLebesgueIntegral f

/-- Упражнение 1.3.11 -/
theorem LowerUnsignedLebesgueIntegral.eq_upperIntegral {d : ℕ} {f : EuclideanSpace' d → EReal} (hf : UnsignedMeasurable f) (hbound : EReal.BoundedFunction f) (hsupp : FiniteMeasureSupport f) : 
    LowerUnsignedLebesgueIntegral f = UpperUnsignedLebesgueIntegral f := by sorry

def LowerUnsignedLebesgueIntegral.eq_upperIntegral_unbounded : Decidable (∀ (d : ℕ) (f : EuclideanSpace' d → EReal) (hf : UnsignedMeasurable f) (hsupp : FiniteMeasureSupport f), LowerUnsignedLebesgueIntegral f = UpperUnsignedLebesgueIntegral f) := by
  -- первой строкой этой конструкции должна быть либо `apply isTrue`, либо `apply isFalse`.
  sorry

def LowerUnsignedLebesgueIntegral.eq_upperIntegral_infinite_supp : Decidable (∀ (d : ℕ) (f : EuclideanSpace' d → EReal) (hf : UnsignedMeasurable f) (hbound : EReal.BoundedFunction f), LowerUnsignedLebesgueIntegral f = UpperUnsignedLebesgueIntegral f) := by
  -- первой строкой этой конструкции должна быть либо `apply isTrue`, либо `apply isFalse`.
  sorry

/-- Умножение беззнаково измеримой функции на индикатор шара сохраняет измеримость.
    Это ключевая вспомогательная лемма для рассуждения с горизонтальным усечением в Следствии 1.3.14. -/
lemma UnsignedMeasurable.mul_indicator_ball {d : ℕ} {f : EuclideanSpace' d → EReal}
    (hf : UnsignedMeasurable f) (n : ℕ) :
    UnsignedMeasurable (f * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' d) n).indicator') := by
  -- Индикатор шара измерим (шары открыты, значит измеримы)
  -- Произведение измеримых функций измеримо
  -- Произведение неотрицательных функций неотрицательно
  constructor
  · -- Беззнаковость : f x * ind x ≥ 0, так как f x ≥ 0 и ind x ∈ {0, 1}
    intro x
    simp only [Pi.mul_apply, Function.comp_apply]
    apply mul_nonneg (hf.1 x)
    by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace' d) n
    · simp [Set.indicator'_of_mem hx]
    · simp [Set.indicator'_of_notMem hx]
  · -- Измеримость : следует из замкнутости измеримых функций относительно умножения
    -- и измеримости индикаторных функций
    sorry

/-- Вспомогательная лемма: горизонтальное усечение даёт функции с конечным носителем меры. -/
lemma FiniteMeasureSupport.mul_indicator_ball {d : ℕ} {f : EuclideanSpace' d → EReal}
    (n : ℕ) : FiniteMeasureSupport (f * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' d) n).indicator') := by
  -- Носитель f * ind содержится в шаре 0 n, у которого конечная мера Лебега
  -- Ключевые факты:
  -- 1. Если x ∉ ball 0 n, то ind x = 0, значит f x * ind x = 0
  -- 2. Поэтому носитель ⊆ ball 0 n
  -- 3. У шаров конечная мера Лебега
  sorry

/-- Аддитивность нижнего интеграла для функций с конечным носителем.
    Это ключевой шаг, где можно применить {name}`eq_upperIntegral` и использовать рассуждение "сэндвич". -/
lemma LowerUnsignedLebesgueIntegral.add_of_finiteSupport {d : ℕ}
    {f g : EuclideanSpace' d → EReal}
    (hf : UnsignedMeasurable f) (hg : UnsignedMeasurable g)
    (hfg : UnsignedMeasurable (f + g))
    (hf_supp : FiniteMeasureSupport f) (hg_supp : FiniteMeasureSupport g) :
    LowerUnsignedLebesgueIntegral (f + g) =
      LowerUnsignedLebesgueIntegral f + LowerUnsignedLebesgueIntegral g := by
  -- Для функций с конечным носителем используем вертикальное усечение, чтобы свести к ограниченному
  -- случаю, затем применяем eq_upperIntegral, чтобы показать Lower = Upper, и, наконец, "сэндвич":
  --   Lower(f+g) ≥ Lower(f) + Lower(g)  [супераддитивность]
  --   Lower(f+g) = Upper(f+g) ≤ Upper(f) + Upper(g) = Lower(f) + Lower(g)  [eq_upperIntegral + субаддитивность]
  apply le_antisymm
  · -- направление ≤ : используем вертикальное усечение + eq_upperIntegral + субаддитивность
    -- Для ограниченного случая с конечным носителем: Lower = Upper по eq_upperIntegral
    -- Затем Upper(f+g) ≤ Upper(f) + Upper(g) по субаддитивности
    -- Берём предел вертикального усечения, чтобы разобраться с неограниченным случаем
    sorry
  · -- направление ≥ : напрямую из супераддитивности
    exact LowerUnsignedLebesgueIntegral.superadditive hf hg

/-- Следствие 1.3.14 (конечная аддитивность интеграла Лебега). -/
theorem LowerUnsignedLebesgueIntegral.add {d : ℕ} {f g : EuclideanSpace' d → EReal} (hf : UnsignedMeasurable f) (hg : UnsignedMeasurable g)
    (hfg : UnsignedMeasurable (f + g)) :
    LowerUnsignedLebesgueIntegral (f + g) = LowerUnsignedLebesgueIntegral f + LowerUnsignedLebesgueIntegral g := by
  apply le_antisymm
  · -- ≤ : горизонтальное усечение → конечный носитель → аддитивность → предел
    let f_h := fun n : ℕ ↦ f * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' d) n).indicator'
    let g_h := fun n : ℕ ↦ g * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' d) n).indicator'
    let fg_h := fun n : ℕ ↦ (f + g) * Real.toEReal ∘ (Metric.ball (0 : EuclideanSpace' d) n).indicator'

    have hfg_lim := eq_lim_horiz_trunc hfg

    -- (f+g) * ind = f * ind + g * ind по right_distrib для неотрицательных
    have heq : ∀ n, fg_h n = f_h n + g_h n := by
      intro n; funext x
      simp only [f_h, g_h, fg_h, Pi.add_apply, Pi.mul_apply]
      exact EReal.right_distrib_of_nonneg (hf.1 x) (hg.1 x)

    -- Аддитивность для усечений с конечным носителем
    have heq_integ : ∀ n, LowerUnsignedLebesgueIntegral (fg_h n) =
        LowerUnsignedLebesgueIntegral (f_h n) + LowerUnsignedLebesgueIntegral (g_h n) := by
      intro n
      rw [heq n]
      apply LowerUnsignedLebesgueIntegral.add_of_finiteSupport
      · exact UnsignedMeasurable.mul_indicator_ball hf n
      · exact UnsignedMeasurable.mul_indicator_ball hg n
      · exact UnsignedMeasurable.add (UnsignedMeasurable.mul_indicator_ball hf n)
            (UnsignedMeasurable.mul_indicator_ball hg n)
      · exact FiniteMeasureSupport.mul_indicator_ball n
      · exact FiniteMeasureSupport.mul_indicator_ball n

    conv at hfg_lim => arg 1; ext n; rw [heq_integ n]

    -- Используем le_of_tendsto': Lower(f_h n) + Lower(g_h n) → Lower(f+g), и каждое слагаемое ≤ предел
    apply le_of_tendsto' hfg_lim
    intro n
    apply add_le_add
    · -- Lower(f_h n) ≤ Lower(f) по монотонности (f_h n ≤ f поточечно)
      apply LowerUnsignedLebesgueIntegral.mono (UnsignedMeasurable.mul_indicator_ball hf n) hf
      apply AlmostAlways.ofAlways; intro x
      simp only [Pi.mul_apply, Function.comp_apply]
      by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace' d) n
      · simp [Set.indicator'_of_mem hx]
      · simp [Set.indicator'_of_notMem hx]; exact hf.1 x
    · -- Lower(g_h n) ≤ Lower(g) по монотонности
      apply LowerUnsignedLebesgueIntegral.mono (UnsignedMeasurable.mul_indicator_ball hg n) hg
      apply AlmostAlways.ofAlways; intro x
      simp only [Pi.mul_apply, Function.comp_apply]
      by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace' d) n
      · simp [Set.indicator'_of_mem hx]
      · simp [Set.indicator'_of_notMem hx]; exact hg.1 x
  · -- ≥ : из супераддитивности
    exact LowerUnsignedLebesgueIntegral.superadditive hf hg

/-- Упражнение 1.3.12 (верхний интеграл Лебега и внешняя мера). -/
theorem UpperUnsignedLebesgueIntegral.eq_outer_measure_integral {d : ℕ} {E : Set (EuclideanSpace' d)} (hE : LebesgueMeasurable E) : 
    UpperUnsignedLebesgueIntegral (Real.toEReal ∘ E.indicator') = Lebesgue_outer_measure E := by sorry

/-- Контрпример: существуют беззнаковые, но не обязательно измеримые функции `f, g`, для которых
    нижний интеграл суммы не равен сумме нижних интегралов — измеримость `f + g` в Следствии 1.3.14
    существенна -/
theorem LowerUnsignedLebesgueIntegral.not_additive : ∃ (d : ℕ) (f g : EuclideanSpace' d → EReal) (hf : Unsigned f) (hg : Unsigned g), (LowerUnsignedLebesgueIntegral (f + g) ≠ LowerUnsignedLebesgueIntegral f + LowerUnsignedLebesgueIntegral g) := by
    sorry

-- Контрпример: существуют беззнаковые, но не обязательно измеримые функции `f, g`, для которых верхний интеграл суммы не равен сумме верхних интегралов
theorem UpperUnsignedLebesgueIntegral.not_additive : ∃ (d : ℕ) (f g : EuclideanSpace' d → EReal) (hf : Unsigned f) (hg : Unsigned g), (UpperUnsignedLebesgueIntegral (f + g) ≠ UpperUnsignedLebesgueIntegral f + UpperUnsignedLebesgueIntegral g) := by
    sorry

/-- Упражнение 1.3.13 (интерпретация интеграла как площади). -/
theorem LowerUnsignedLebesgueIntegral.eq_area {d : ℕ} {f : EuclideanSpace' d → EReal} (hf : UnsignedMeasurable f) : 
    LowerUnsignedLebesgueIntegral f = Lebesgue_measure { p | ∃ x, ∃ t : ℝ, EuclideanSpace'.prod_equiv d 1 p = ⟨ x, t ⟩ ∧ 0 ≤ t ∧ t ≤ f x } := by sorry

/-- Упражнение 1.3.14 (единственность) -/
theorem UnsignedLebesgueIntegral.unique {d : ℕ} (integ : (EuclideanSpace' d → EReal) → EReal)
  (hsimple : ∀ f (hf : UnsignedSimpleFunction f), integ f = hf.integ)
  (hadd : ∀ f g (hf : UnsignedMeasurable f) (hg : UnsignedMeasurable g), integ (f + g) = integ f + integ g)
  (hvert : ∀ f (hf : UnsignedMeasurable f), Filter.atTop.Tendsto (fun n : ℕ ↦ integ (fun x ↦ min (f x) n)) (nhds (integ f)))
  (hhoriz : ∀ f (hf : UnsignedMeasurable f), Filter.atTop.Tendsto (fun n : ℕ ↦ integ (f * Real.toEReal ∘ (Metric.ball 0 n).indicator')) (nhds (integ f)))
  : ∀ f, UnsignedMeasurable f → integ f = UnsignedLebesgueIntegral f := by sorry

/-- Упражнение 1.3.15 (инвариантность относительно сдвигов). -/
theorem UnsignedLebesgueIntegral.trans {d : ℕ} {f : EuclideanSpace' d → EReal} (hf : UnsignedMeasurable f) (a : EuclideanSpace' d) : 
    UnsignedLebesgueIntegral (fun x ↦ f (x + a)) = hf.integ := by sorry

/-- Упражнение 1.3.16 (линейная замена переменных). -/
theorem UnsignedLebesgueIntegral.comp_linear {d : ℕ} {f : EuclideanSpace' d → EReal} (hf : UnsignedMeasurable f) (A : EuclideanSpace' d →ₗ[ℝ] EuclideanSpace' d) (hA : A.det ≠ 0) : 
    UnsignedLebesgueIntegral (fun x ↦ f (A x)) = |A.det|⁻¹ * hf.integ := by sorry

/-- Упражнение 1.3.17 (согласованность с интегралом Римана). -/
theorem RiemannIntegral.eq_UnsignedLebesgueIntegral {I : BoundedInterval} {f : ℝ → ℝ} (hf : RiemannIntegrableOn f I) : 
    (riemannIntegral f I : EReal) = UnsignedLebesgueIntegral (Real.toEReal ∘ (fun x ↦ (f x) * (I.toSet.indicator' x)) ∘ EuclideanSpace'.equiv_Real) := by sorry

/-- Лемма 1.3.15 (неравенство Маркова) -/
theorem UnsignedLebesgueIntegral.markov_inequality {d : ℕ} {f : EuclideanSpace' d → EReal} (hf : UnsignedMeasurable f) {t : ℝ} (ht : 0 < t) : 
    Lebesgue_measure { x | f x ≥ t } ≤ hf.integ / (t : EReal) := by
  sorry

/-- Упражнение 1.3.18 (ii) -/
theorem UnsignedLebesgueIntegral.ae_finite {d : ℕ} {f : EuclideanSpace' d → EReal} (hf : UnsignedMeasurable f) (hfin : UnsignedLebesgueIntegral f < ⊤) : 
    AlmostAlways (fun x ↦ f x < ⊤) := by sorry

-- Контрпример к обращению Упражнения 1.3.18(ii): существует измеримая функция `f`, конечная почти всюду, но с бесконечным интегралом Лебега
theorem UnsignedLebesgueIntegral.ae_finite_no_converse : ∃ (d : ℕ) (f : EuclideanSpace' d → EReal) (hf : UnsignedMeasurable f) (hfin : AlmostAlways (fun x ↦ f x < ⊤)), UnsignedLebesgueIntegral f = ⊤ := by sorry

/-- Упражнение 1.3.18 (iii) -/
theorem UnsignedLebesgueIntegral.eq_zero_aeZero {d : ℕ} {f : EuclideanSpace' d → EReal} (hf : UnsignedMeasurable f) : 
     hf.integ = 0 ↔ AlmostAlways (fun x ↦ f x = 0) := by sorry
