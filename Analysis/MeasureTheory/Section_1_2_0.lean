import Analysis.MeasureTheory.Section_1_1_3
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Topology.Instances.Irrational
/-!
# Введение в теорию меры, раздел 1.2: мера Лебега

Сопровождение (введения) к разделу 1.2 книги "An introduction to Measure Theory".

-/

open BoundedInterval

/-- Exercise 1.2.1 (счётное объединение) -/
lemma exercise_1_2_1_union :
    ∃ E : ℕ → Set ℝ, (∀ n, Bornology.IsBounded (E n)) ∧
      (∀ n, JordanMeasurable (Real.equiv_EuclideanSpace' '' (E n))) ∧
      (∀ n, E n ⊆ Set.Icc 0 1) ∧
      ¬ JordanMeasurable (⋃ n, Real.equiv_EuclideanSpace' '' (E n)) := by
  -- Стратегия: пусть E_n = {q_n}, где q_n — n-е рациональное число из [0,1].
  -- Каждое одноэлементное множество измеримо по Жордану с мерой 0,
  -- но объединение — это все рациональные числа из [0,1], которое НЕ измеримо по Жордану

  -- Получаем перечисление рациональных чисел из [0,1]
  have h_countable : (Set.Icc (0 : ℚ) 1).Countable := Set.countable_coe_iff.mp inferInstance
  have h_nonempty : (Set.Icc (0 : ℚ) 1).Nonempty := ⟨0, by simp⟩
  obtain ⟨q, hq_surj⟩ := h_countable.exists_surjective h_nonempty

  -- Определяем E_n = {q_n} (одноэлементное множество, содержащее n-е рациональное число)
  let E : ℕ → Set ℝ := fun n => {((q n).val : ℝ)}

  use E

  constructor
  -- Часть 1: каждое E_n ограничено (одноэлементные множества тривиально ограничены)
  · intro n
    apply Set.Finite.isBounded
    exact Set.finite_singleton _

  constructor
  -- Часть 2: каждое E_n измеримо по Жордану (одноэлементные множества имеют меру 0)
  · intro n
    -- Одноэлементное множество {x} в ℝ отображается в вырожденный прямоугольник в EuclideanSpace' 1.
    -- А именно, Real.equiv_EuclideanSpace' '' {x} = Icc x x (как одномерный прямоугольник)
    -- Прямоугольники элементарны, а элементарные множества измеримы по Жордану
    let x := ((q n).val : ℝ)
    have h_singleton_eq : Real.equiv_EuclideanSpace' '' {x} = (BoundedInterval.Icc x x : Box 1).toSet := by
      rw [BoundedInterval.coe_of_box]
      simp [BoundedInterval.set_Icc]
    rw [h_singleton_eq]
    exact IsElementary.jordanMeasurable (IsElementary.box _)

  constructor
  -- Часть 3: каждое E_n содержится в [0,1]
  · intro n x hx
    simp [E] at hx
    rcases hx with rfl
    rcases (q n).property with ⟨hq0, hq1⟩
    exact ⟨by exact_mod_cast hq0, by exact_mod_cast hq1⟩

  -- Часть 4: объединение ⋃_n E_n = рациональные числа из [0,1], которое НЕ измеримо по Жордану
  · intro hJM
    -- Объединение равно множеству всех рациональных чисел из [0,1]
    have h_union_eq_rats : (⋃ n, E n) = Set.range (fun r : Set.Icc (0 : ℚ) 1 => (r.val : ℝ)) := by
      ext x
      simp only [E, Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_range]
      constructor
      · intro ⟨n, hn⟩
        use q n
        exact hn.symm
      · intro ⟨r, hr⟩
        obtain ⟨n, hn⟩ := hq_surj r
        use n
        rw [hn]
        exact hr.symm

    -- Образ объединения при отображении Real.equiv_EuclideanSpace' — это образ рациональных чисел
    have hJM' : JordanMeasurable (Real.equiv_EuclideanSpace' '' (⋃ n, E n)) := by
      have : (⋃ n, Real.equiv_EuclideanSpace' '' E n) = Real.equiv_EuclideanSpace' '' (⋃ n, E n) := by
        exact Set.image_iUnion.symm
      rw [← this]
      exact hJM

    -- Пусть Q = рациональные числа из [0,1]
    let Q := Set.range (fun r : Set.Icc (0 : ℚ) 1 => (r.val : ℝ))

    -- Показываем, что Q ограничено
    have hQ_bounded : Bornology.IsBounded Q := by
      apply Bornology.IsBounded.subset (Metric.isBounded_Icc (a := 0) (b := 1))
      intro x hx
      obtain ⟨r, hr⟩ := hx
      rw [← hr]
      simp
      have : r.val ∈ Set.Icc (0 : ℚ) 1 := r.property
      constructor
      · exact_mod_cast this.1
      · exact_mod_cast this.2

    -- Переписываем hJM' через Q
    rw [h_union_eq_rats] at hJM'

    -- Используем упражнение 1.1.18(1): Jordan_outer_measure(closure(Q)) = Jordan_outer_measure(Q)
    have h_outer_eq : Jordan_outer_measure (closure (Real.equiv_EuclideanSpace' '' Q)) =
                      Jordan_outer_measure (Real.equiv_EuclideanSpace' '' Q) := by
      apply JordanMeasurable.outer_measure_of_closure
      have : Bornology.IsBounded (Real.equiv_EuclideanSpace' '' Q) := by
        -- Q ⊆ [0,1] ограничено, значит его образ при гомеоморфизме тоже ограничен.
        -- Используем, что Q ограничено: ∃ M, ∀ x y ∈ Q, dist x y ≤ M
        obtain ⟨c, hc⟩ := Metric.isBounded_iff_subset_ball 0 |>.mp hQ_bounded
        -- Показываем ограниченность образа, показав, что он лежит в шаре
        rw [Metric.isBounded_iff_subset_ball 0]
        use c
        intro v hv
        obtain ⟨x, hx, rfl⟩ := hv
        -- Показываем, что Real.equiv_EuclideanSpace' x ∈ Metric.ball 0 c.
        -- Так как ‖Real.equiv_EuclideanSpace' x‖ = |x| и x ∈ Metric.ball 0 c
        have hx_ball : x ∈ Metric.ball 0 c := hc hx
        rw [Metric.mem_ball, dist_zero_right] at hx_ball
        rw [Metric.mem_ball, dist_zero_right]
        -- ‖Real.equiv_EuclideanSpace' x‖ = |x|
        have h_norm_eq : ‖Real.equiv_EuclideanSpace' x‖ = |x| := by
          simp [Real.equiv_EuclideanSpace', EuclideanSpace'.equiv_Real]
          rw [PiLp.norm_eq_of_L2]
          simp
          exact Real.sqrt_sq_eq_abs x
        rw [h_norm_eq]
        exact hx_ball
      exact this

    -- Замыкание рациональных чисел из [0,1] — это [0,1] (рациональные числа плотны)
    have h_closure_Q : closure Q = Set.Icc 0 1 := by
      -- Рациональные числа плотны в [0,1]
      -- Сначала показываем Q ⊆ [0,1]
      have hQ_subset : Q ⊆ Set.Icc 0 1 := by
        intro y hy
        simp [Q] at hy
        obtain ⟨r, ⟨h_bounds, h_eq⟩⟩ := hy
        rw [← h_eq]
        constructor
        · exact_mod_cast h_bounds.1
        · exact_mod_cast h_bounds.2
      -- Показываем closure Q ⊆ [0,1] (так как [0,1] замкнуто)
      have h_closure_subset : closure Q ⊆ Set.Icc 0 1 :=
        closure_minimal hQ_subset isClosed_Icc
      -- Показываем [0,1] ⊆ closure Q (используя плотность рациональных чисел)
      have h_subset_closure : Set.Icc 0 1 ⊆ closure Q := by
        -- Q — это множество рациональных чисел из [0,1].
        -- Так как рациональные числа плотны в ℝ, Q плотно в [0,1].
        -- Следовательно closure Q ⊇ [0,1]
        intro x hx
        -- Используем DenseRange для рациональных чисел
        have h_dense : ∀ ε > 0, ∃ q : ℚ, |(q : ℝ) - x| < ε ∧ (q : ℝ) ∈ Set.Icc 0 1 := by
          intro ε hε
          -- Находим рациональное число в пределах ε от x, используя плотность
          have := Rat.denseRange_cast.exists_dist_lt x hε
          obtain ⟨q, hq⟩ := this
          -- Проверяем, что q ∈ [0,1]
          by_cases hq_in : (q : ℝ) ∈ Set.Icc 0 1
          · use q
            have : |(q : ℝ) - x| < ε := by
              rw [← Real.dist_eq, dist_comm]
              exact hq
            exact ⟨this, hq_in⟩
          · -- Если q ∉ [0,1], нужно найти рациональное число из [0,1], близкое к x.
            -- Рекурсивно используем плотность в меньшей окрестности, остающейся внутри [0,1].
            -- Определяем интервал [a, b] = [max(0, x-ε/2), min(1, x+ε/2)] ⊆ [0,1]
            let a := max (0 : ℝ) (x - ε / 2)
            let b := min (1 : ℝ) (x + ε / 2)
            have ha : 0 ≤ a := le_max_left _ _
            have hb : b ≤ 1 := min_le_left _ _
            have hax : a ≤ x := by
              simp only [a]
              exact max_le (hx.1) (by linarith)
            have hxb : x ≤ b := by
              simp only [b]
              exact le_min (hx.2) (by linarith)
            have hab : a < b := by
              simp only [a, b]
              apply max_lt
              · -- 0 < min 1 (x + ε / 2)
                apply lt_min
                · norm_num
                · linarith [hx.1, hε]
              · apply lt_min
                · linarith [hx.2]
                · linarith
            -- Находим рациональное число в открытом интервале (a, b), используя плотность
            have : ∃ r : ℚ, a < (r : ℝ) ∧ (r : ℝ) < b := by
              apply exists_rat_btwn
              exact hab
            obtain ⟨r, har, hrb⟩ := this
            use r
            constructor
            · -- |r - x| < ε
              have : (r : ℝ) ∈ Set.Ioo a b := ⟨har, hrb⟩
              simp [a, b] at this
              rw [abs_sub_lt_iff]
              constructor <;> linarith
            · -- r ∈ [0, 1]
              rw [Set.mem_Icc]
              constructor <;> linarith [har, ha, hrb, hb]
        -- Используем h_dense, чтобы показать x ∈ closure Q
        apply Metric.mem_closure_iff.mpr
        intro ε hε
        obtain ⟨q, hq_dist, hq_in⟩ := h_dense ε hε
        use (q : ℝ)
        constructor
        · -- Показываем (q : ℝ) ∈ Q (первая подцель от "use")
          simp only [Q, Set.mem_range]
          have hq_bounds : q ∈ Set.Icc (0 : ℚ) 1 := by
            rw [Set.mem_Icc] at hq_in ⊢
            exact ⟨by exact_mod_cast hq_in.1, by exact_mod_cast hq_in.2⟩
          use ⟨q, hq_bounds⟩
        · -- Показываем dist (q : ℝ) x < ε (вторая подцель от "use")
          rw [Real.dist_eq]
          rw [abs_sub_comm] at hq_dist
          exact hq_dist
      exact Set.Subset.antisymm h_closure_subset h_subset_closure

    -- Используем то, что Real.equiv_EuclideanSpace' коммутирует с замыканием
    have h_image_closure : Real.equiv_EuclideanSpace' '' closure Q =
                           closure (Real.equiv_EuclideanSpace' '' Q) := by
      -- Real.equiv_EuclideanSpace' — гомеоморфизм (непрерывная биекция с непрерывным обратным).
      -- Гомеоморфизмы сохраняют замыкание: f(closure A) = closure(f(A)).
      -- Чтобы доказать это формально, нужно:
      -- 1. Показать, что Real.equiv_EuclideanSpace' непрерывно (это координатное вложение x ↦ (fun _ => x))
      -- 2. Показать, что его обратное непрерывно (это проекция (f : Fin 1 → ℝ) ↦ f 0)
      -- 3. Применить image_closure_subset_closure_image в обе стороны
      -- Всё это верно, но требует детальной работы с API топологии
      classical
      -- Непрерывность прямого и обратного отображений
      have hf_cont : Continuous (fun x : ℝ => Real.equiv_EuclideanSpace' x) := by
        show Continuous (fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x))
        exact continuous_induced_rng.mpr (continuous_pi (fun _ => continuous_id))
      have hg_cont : Continuous (fun x : EuclideanSpace' 1 => EuclideanSpace'.equiv_Real x) := by
        exact PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) ⟨0, by decide⟩
      -- Упаковываем эквивалентность как гомеоморфизм, чтобы применить лемму из библиотеки
      let e : ℝ ≃ₜ EuclideanSpace' 1 :=
        { toEquiv := Real.equiv_EuclideanSpace'
          continuous_toFun := hf_cont
          continuous_invFun := hg_cont }
      simpa using e.image_closure Q

    rw [← h_image_closure] at h_outer_eq
    rw [h_closure_Q] at h_outer_eq

    -- [0,1] — это одномерный прямоугольник с жордановой внешней мерой 1
    have h_Icc_outer : Jordan_outer_measure (Real.equiv_EuclideanSpace' '' Set.Icc 0 1) = 1 := by
      -- [0,1] отображается в одномерный прямоугольник [0,1], который элементарен и имеет меру 1.
      -- Сначала показываем, что образ — прямоугольник
      have h_eq_box : Real.equiv_EuclideanSpace' '' Set.Icc 0 1 = (BoundedInterval.Icc 0 1 : Box 1).toSet := by
        rw [BoundedInterval.coe_of_box]
        simp [BoundedInterval.set_Icc]
      rw [h_eq_box]
      -- Это элементарное множество (прямоугольник)
      let B := (BoundedInterval.Icc 0 1 : Box 1)
      have hB_elem : IsElementary B.toSet := IsElementary.box B
      -- Для элементарного множества Jordan_outer_measure совпадает с его мерой
      have h_outer_eq_measure : Jordan_outer_measure B.toSet = hB_elem.measure := by
        -- Jordan_outer_measure B = sInf { m | ∃ A элементарно, B ⊆ A ∧ m = hA.measure }.
        -- Так как B элементарно и B ⊆ B, hB_elem.measure входит в это множество.
        -- Нужно показать: sInf этого множества = hB_elem.measure
        apply le_antisymm
        · -- Jordan_outer_measure B ≤ hB_elem.measure
          exact Jordan_outer_le hB_elem (Set.Subset.refl B.toSet)
        · -- hB_elem.measure ≤ Jordan_outer_measure B.
          -- Для любого элементарного A ⊇ B верно hB_elem.measure ≤ hA.measure
          unfold Jordan_outer_measure
          apply le_csInf
          · -- Показываем, что множество непусто
            use hB_elem.measure, B.toSet, hB_elem, Set.Subset.refl B.toSet
          · -- Показываем, что hB_elem.measure — нижняя грань
            intro m hm
            obtain ⟨A, hA, hB_subset_A, rfl⟩ := hm
            exact IsElementary.measure_mono hB_elem hA hB_subset_A
      rw [h_outer_eq_measure]
      -- Мера прямоугольника [0,1] равна 1
      have h_measure_eq_volume : hB_elem.measure = |B|ᵥ := IsElementary.measure_of_box B
      rw [h_measure_eq_volume]
      -- Объём одномерного прямоугольника — это длина его стороны
      simp [Box.volume, B, BoundedInterval.length]

    -- Значит, внешняя мера Q равна 1
    rw [h_Icc_outer] at h_outer_eq
    have h_Q_outer : Jordan_outer_measure (Real.equiv_EuclideanSpace' '' Q) = 1 := h_outer_eq.symm

    -- Используем упражнение 1.1.18(2): Jordan_inner_measure(interior(Q)) = Jordan_inner_measure(Q)
    have h_inner_eq : Jordan_inner_measure (interior (Real.equiv_EuclideanSpace' '' Q)) =
                      Jordan_inner_measure (Real.equiv_EuclideanSpace' '' Q) := by
      apply JordanMeasurable.inner_measure_of_interior
      have : Bornology.IsBounded (Real.equiv_EuclideanSpace' '' Q) := by
        -- То же самое доказательство, что и для внешней меры
        obtain ⟨c, hc⟩ := Metric.isBounded_iff_subset_ball 0 |>.mp hQ_bounded
        rw [Metric.isBounded_iff_subset_ball 0]
        use c
        intro v hv
        obtain ⟨x, hx, rfl⟩ := hv
        have hx_ball : x ∈ Metric.ball 0 c := hc hx
        rw [Metric.mem_ball, dist_zero_right] at hx_ball
        rw [Metric.mem_ball, dist_zero_right]
        have h_norm_eq : ‖Real.equiv_EuclideanSpace' x‖ = |x| := by
          simp [Real.equiv_EuclideanSpace', EuclideanSpace'.equiv_Real]
          rw [PiLp.norm_eq_of_L2]
          simp
          exact Real.sqrt_sq_eq_abs x
        rw [h_norm_eq]
        exact hx_ball
      exact this

    -- Внутренность Q (рациональных чисел) пуста (у рациональных чисел нет внутренности)
    have h_interior_Q : interior Q = ∅ := by
      -- Рациональные числа имеют пустую внутренность, потому что иррациональные числа плотны
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hx
      -- x ∈ interior Q означает, что существует открытая окрестность x, содержащаяся в Q
      rw [mem_interior_iff_mem_nhds] at hx
      -- Это означает, что Q ∈ nhds x, то есть существует открытое множество U с x ∈ U ⊆ Q
      obtain ⟨U, hU_Q, hU_open, hx_U⟩ := mem_nhds_iff.mp hx
      -- Находим открытый шар вокруг x, содержащийся в U
      obtain ⟨ε, hε, hball_subset⟩ := Metric.isOpen_iff.mp hU_open x hx_U
      -- Используем плотность иррациональных чисел, чтобы найти иррациональное число в шаре
      have h_ball_nonempty : (Metric.ball x ε).Nonempty := ⟨x, Metric.mem_ball_self hε⟩
      obtain ⟨y, hy_mem⟩ := Dense.inter_open_nonempty dense_irrational (Metric.ball x ε) Metric.isOpen_ball h_ball_nonempty
      rw [Set.mem_inter_iff] at hy_mem
      -- Компоненты: первая — y ∈ {x | Irrational x}, вторая — y ∈ Metric.ball x ε,
      -- но Lean даёт их в обратном порядке
      obtain ⟨hy_ball_mem, hy_irrat_mem⟩ := hy_mem
      -- y лежит в U (так как шар ⊆ U)
      have hy_U : y ∈ U := hball_subset hy_ball_mem
      -- Значит y ∈ Q (так как U ⊆ Q)
      have hy_Q : y ∈ Q := hU_Q hy_U
      -- Но Q содержит только рациональные числа
      simp only [Q, Set.mem_range] at hy_Q
      obtain ⟨r, hr⟩ := hy_Q
      -- Значит y рационально: hr показывает, что (r.val : ℝ) = y, то есть r.val — рациональный свидетель
      have hy_rational : ∃ q : ℚ, (q : ℝ) = y := ⟨r.val, hr⟩
      -- Но y иррационально: hy_irrat_mem : y ∈ {x | Irrational x}.
      -- Это означает Irrational y, что противоречит hy_rational
      simp only [Set.mem_setOf_eq] at hy_irrat_mem
      exact hy_irrat_mem hy_rational

    -- Real.equiv_EuclideanSpace' коммутирует с внутренностью
    have h_image_interior : Real.equiv_EuclideanSpace' '' interior Q =
                             interior (Real.equiv_EuclideanSpace' '' Q) := by
      -- Это стандартный факт о гомеоморфизмах: они сохраняют внутренность.
      -- Доказательство требует показать, что Real.equiv_EuclideanSpace' и его обратное
      -- отображение — оба открытые отображения (переводят открытые множества в открытые).
      -- Это верно, поскольку Real.equiv_EuclideanSpace' — гомеоморфизм
      -- между ℝ и EuclideanSpace' 1
      classical
      -- Непрерывность прямого и обратного отображений
      have hf_cont : Continuous (fun x : ℝ => Real.equiv_EuclideanSpace' x) := by
        show Continuous (fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x))
        exact continuous_induced_rng.mpr (continuous_pi (fun _ => continuous_id))
      have hg_cont : Continuous (fun x : EuclideanSpace' 1 => EuclideanSpace'.equiv_Real x) := by
        exact PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) ⟨0, by decide⟩
      -- Упаковываем эти отображения как гомеоморфизм и применяем общую лемму о внутренностях
      let e : ℝ ≃ₜ EuclideanSpace' 1 :=
        { toEquiv := Real.equiv_EuclideanSpace'
          continuous_toFun := hf_cont
          continuous_invFun := hg_cont }
      simpa using e.image_interior Q

    rw [← h_image_interior] at h_inner_eq
    rw [h_interior_Q, Set.image_empty] at h_inner_eq

    -- Внутренняя мера пустого множества равна 0
    have h_empty_inner : Jordan_inner_measure (∅ : Set (EuclideanSpace' 1)) = 0 := by
      -- Единственное элементарное подмножество ∅ — это само ∅, с мерой 0
      unfold Jordan_inner_measure
      -- Jordan_inner_measure ∅ = sSup { m | ∃ A элементарно, A ⊆ ∅ ∧ m = hA.measure }.
      -- Единственное A с A ⊆ ∅ — это A = ∅, с мерой 0.
      -- Значит множество — это (не более чем) {0}, и sSup {0} = 0
      apply le_antisymm
      · -- sSup ≤ 0 : показываем, что каждый элемент множества ≤ 0
        apply csSup_le
        · -- Показываем, что множество непусто
          use 0, ∅, IsElementary.empty 1
          simp [IsElementary.measure_of_empty]
        · -- Показываем, что каждый элемент ≤ 0
          intro m hm
          obtain ⟨A, hA, hA_subset, rfl⟩ := hm
          -- A ⊆ ∅ означает A = ∅
          have hA_empty : A = ∅ := Set.subset_empty_iff.mp hA_subset
          -- Значит hA.measure = (IsElementary.empty 1).measure = 0
          subst hA_empty
          exact le_of_eq (IsElementary.measure_of_empty 1)
      · -- 0 ≤ sSup : 0 входит в множество
        apply le_csSup
        · -- Показываем, что множество ограничено сверху
          use 0
          intro m hm
          obtain ⟨A, hA, hA_subset, rfl⟩ := hm
          have hA_empty : A = ∅ := Set.subset_empty_iff.mp hA_subset
          subst hA_empty
          exact le_of_eq (IsElementary.measure_of_empty 1)
        · -- Показываем, что 0 входит в множество
          use ∅, IsElementary.empty 1
          simp [IsElementary.measure_of_empty]

    rw [h_empty_inner] at h_inner_eq
    have h_Q_inner : Jordan_inner_measure (Real.equiv_EuclideanSpace' '' Q) = 0 := h_inner_eq.symm

    -- Но измеримость по Жордану означает, что внутренняя мера = внешней
    have h_eq : Jordan_inner_measure (Real.equiv_EuclideanSpace' '' Q) =
                Jordan_outer_measure (Real.equiv_EuclideanSpace' '' Q) := by
      exact hJM'.2

    -- Это даёт 0 = 1, противоречие
    rw [h_Q_inner, h_Q_outer] at h_eq
    exact absurd h_eq (by norm_num)

/-- Exercise 1.2.1 (счётное объединение) -/
example :
    ∃ E : ℕ → Set ℝ, (∀ n, Bornology.IsBounded (E n)) ∧
      (∀ n, JordanMeasurable (Real.equiv_EuclideanSpace' '' (E n)))
      ∧ ¬ JordanMeasurable (⋃ n, Real.equiv_EuclideanSpace' '' (E n)) := by
  obtain ⟨E, hB, hJM, -, h_union⟩ := exercise_1_2_1_union
  exact ⟨E, hB, hJM, h_union⟩

/-- Exercise 1.2.1 (счётное пересечение) -/
example : 
    ∃ E : ℕ → Set ℝ, (∀ n, Bornology.IsBounded (E n)) ∧
      (∀ n, JordanMeasurable (Real.equiv_EuclideanSpace' '' (E n))) ∧
      ¬ JordanMeasurable (⋂ n, Real.equiv_EuclideanSpace' '' (E n)) := by
  classical
  obtain ⟨S, hS_bdd, hS_jm, hS_subset, hS_union_not⟩ := exercise_1_2_1_union
  let I : Set ℝ := Set.Icc 0 1
  let E : ℕ → Set ℝ := fun n => I \ S n
  have hI_image : 
      Real.equiv_EuclideanSpace' '' I =
        (BoundedInterval.Icc 0 1 : Box 1).toSet := by
    rw [BoundedInterval.coe_of_box]
    simp [I, BoundedInterval.set_Icc]
  have hI_JM : 
      JordanMeasurable (Real.equiv_EuclideanSpace' '' I) := by
    let B : Box 1 := BoundedInterval.Icc 0 1
    simpa [hI_image, B] using
      (IsElementary.jordanMeasurable (IsElementary.box B))
  have h_image_diff : 
      ∀ n,
        Real.equiv_EuclideanSpace' '' (E n) =
          (Real.equiv_EuclideanSpace' '' I) \
            (Real.equiv_EuclideanSpace' '' (S n)) := by
    intro n
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := hy
      refine ⟨?_, ?_⟩
      · exact Set.mem_image_of_mem _ hx.1
      · intro hyC
        obtain ⟨z, hz, hz_eq⟩ := hyC
        have : z = x := by
          apply Real.equiv_EuclideanSpace'.injective
          simpa using hz_eq
        exact hx.2 (this ▸ hz)
    · intro hy
      rcases hy with ⟨hyA, hy_not⟩
      obtain ⟨x, hxI, rfl⟩ := hyA
      refine ⟨x, ?_, rfl⟩
      constructor
      · exact hxI
      · intro hxS
        exact hy_not ⟨x, hxS, rfl⟩

  refine ⟨E, ?_, ?_, ?_⟩
  · intro n
    apply Bornology.IsBounded.subset (Metric.isBounded_Icc (a := 0) (b := 1))
    exact Set.diff_subset
  ·
    intro n
    have hJ : 
        JordanMeasurable
          ((Real.equiv_EuclideanSpace' '' I) \
            (Real.equiv_EuclideanSpace' '' (S n))) :=
      JordanMeasurable.sdiff hI_JM (hS_jm n)
    exact (h_image_diff n).symm ▸ hJ
  ·
    -- Закон де Моргана внутри прямоугольника [0,1]
    let A := Real.equiv_EuclideanSpace' '' I
    let C : ℕ → Set (EuclideanSpace' 1) :=
      fun n => Real.equiv_EuclideanSpace' '' (S n)
    let F : ℕ → Set (EuclideanSpace' 1) :=
      fun n => Real.equiv_EuclideanSpace' '' (E n)
    have hF_eq : ∀ n, F n = A \ C n := by
      intro n
      simpa [F, C, A] using h_image_diff n
    have hC_union_not : ¬ JordanMeasurable (⋃ n, C n) := by
      have h_image_union : 
          Real.equiv_EuclideanSpace' '' (⋃ n, S n) =
            ⋃ n, C n := by
        ext y
        constructor
        · intro hy
          obtain ⟨x, hx, rfl⟩ := hy
          obtain ⟨n, hxSn⟩ := Set.mem_iUnion.mp hx
          refine Set.mem_iUnion.mpr ?_
          exact ⟨n, ⟨x, hxSn, rfl⟩⟩
        · intro hy
          obtain ⟨n, hyC⟩ := Set.mem_iUnion.mp hy
          obtain ⟨x, hxSn, rfl⟩ := hyC
          exact Set.mem_image_of_mem _ (Set.mem_iUnion.mpr ⟨n, hxSn⟩)
      simpa [C, h_image_union] using hS_union_not
    have h_inter_eq : 
        (⋂ n, F n) = A \ ⋃ n, C n := by
      ext x
      constructor
      · intro hx
        have hx_all : ∀ n, x ∈ A \ C n := by
          have hx_all' := Set.mem_iInter.mp hx
          intro n
          simpa [hF_eq n] using hx_all' n
        have hxA : x ∈ A := (hx_all 0).1
        have hx_not : x ∉ ⋃ n, C n := by
          intro hx_union
          obtain ⟨n, hxC⟩ := Set.mem_iUnion.mp hx_union
          exact (hx_all n).2 hxC
        exact ⟨hxA, hx_not⟩
      · intro hx
        have hxA : x ∈ A := hx.1
        have hx_not : x ∉ ⋃ n, C n := hx.2
        refine Set.mem_iInter.mpr ?_
        intro n
        have : x ∈ A \ C n := by
          refine ⟨hxA, ?_⟩
          intro hxC
          exact hx_not (Set.mem_iUnion.mpr ⟨n, hxC⟩)
        simpa [hF_eq n] using this
    intro hJM_inter
    have hC_subset : ∀ n, C n ⊆ A := by
      intro n x hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact Set.mem_image_of_mem _ (hS_subset n hy)
    have h_union_subset : (⋃ n, C n) ⊆ A := by
      intro x hx
      obtain ⟨n, hxC⟩ := Set.mem_iUnion.mp hx
      exact hC_subset n hxC
    have h_union_JM : JordanMeasurable (⋃ n, C n) := by
      have h_diff : 
          JordanMeasurable (A \ (⋂ n, F n)) :=
        JordanMeasurable.sdiff
          (by simpa [A] using hI_JM) hJM_inter
      classical
      have h_congr := congrArg (fun s => A \ s) h_inter_eq
      have h_step : 
          A \ (A \ ⋃ n, C n) = A ∩ ⋃ n, C n := by
        ext x
        constructor
        · intro hx
          have hx_union : x ∈ ⋃ n, C n := by
            by_contra hx_not
            exact hx.2 ⟨hx.1, hx_not⟩
          exact ⟨hx.1, hx_union⟩
        · intro hx
          refine ⟨hx.1, ?_⟩
          intro hx_diff
          exact hx_diff.2 hx.2
      have h_eq : 
          (A \ (⋂ n, F n)) = A ∩ ⋃ n, C n :=
        h_congr.trans h_step
      have h_eq' : A ∩ ⋃ n, C n = ⋃ n, C n := by
        apply Set.Subset.antisymm
        · intro x hx
          exact hx.2
        · intro x hx
          exact ⟨h_union_subset hx, hx⟩
      have h_target : JordanMeasurable (A ∩ ⋃ n, C n) :=
        by simpa [h_eq] using h_diff
      simpa [h_eq'] using h_target
    exact hC_union_not h_union_JM



/-- Exercise 1.2.2 -/
-- The pointwise limit of uniformly bounded Riemann integrable functions need not be Riemann integrable.
example : ∃ f: ℕ → ℝ → ℝ, ∃ F: ℝ → ℝ,
    (∃ M, ∀ n, ∀ x ∈ Set.Icc 0 1, |f n x| ≤ M) ∧
    (∀ x ∈ Set.Icc 0 1, Filter.atTop.Tendsto (fun n ↦ f n x) (nhds (F x))) ∧
    (∀ n, RiemannIntegrableOn (f n) (Icc 0 1)) ∧
    ¬ RiemannIntegrableOn F (Icc 0 1) := by
  sorry

/-- Exercise 1.2.2' -/
-- Determine whether uniform convergence of uniformly bounded Riemann integrable functions preserves Riemann integrability (true or false).
def Ex_1_2_2b : Decidable ( ∀ f: ℕ → ℝ → ℝ, ∀ F: ℝ → ℝ,
    (∃ M, ∀ n, ∀ x ∈ Set.Icc 0 1, |f n x| ≤ M) →
    TendstoUniformlyOn f F Filter.atTop (Set.Icc 0 1) →
    (∀ n, RiemannIntegrableOn (f n) (Icc 0 1)) → RiemannIntegrableOn F (Icc 0 1) ) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`, depending on whether you believe the given statement to be true or false.
  sorry

-- Внешняя мера Жордана равна инфимуму сумм объёмов прямоугольников по всем конечным покрытиям прямоугольниками.
theorem Jordan_outer_eq {d : ℕ} {E : Set (EuclideanSpace' d)} (hE : Bornology.IsBounded E) : Jordan_outer_measure E = sInf (((fun S : Finset (Box d) ↦ ∑ B ∈ S, |B|ᵥ)) '' { S | E ⊆ ⋃ B ∈ S, B.toSet }) := by
  -- Стратегия: доказываем равенство через два неравенства (le_antisymm)
  apply le_antisymm

  -- Часть 1 (≤): Jordan_outer_measure E ≤ sInf покрытий прямоугольниками
  · -- Для любого покрытия прямоугольниками S показываем Jordan_outer_measure E ≤ сумма объёмов S, затем берём инфимум
    apply le_csInf
    -- Показываем, что множество сумм покрытий непусто
    · obtain ⟨A, hA, hE_sub_A⟩ := IsElementary.contains_bounded hE
      obtain ⟨T, hT_disj, hA_eq⟩ := hA.partition
      use ∑ B ∈ T, |B|ᵥ
      use T
      simp
      intro a ha
      have : a ∈ A := hE_sub_A ha
      rw [hA_eq] at this
      exact this
    -- Показываем, что Jordan_outer_measure E — нижняя грань для всех сумм покрытий
    · intro m hm
      obtain ⟨S, hS_cover, rfl⟩ := hm
      -- Объединение ⋃ B ∈ S элементарно
      classical
      -- Отображаем S : Finset (Box d) в конечное множество множеств
      let S_sets : Finset (Set (EuclideanSpace' d)) := S.image (fun B => B.toSet)
      have hS_elem : ∀ E ∈ S_sets, IsElementary E := by
        intro E hE
        simp [S_sets] at hE
        obtain ⟨B, _, rfl⟩ := hE
        exact IsElementary.box B
      -- Применяем IsElementary.union', чтобы показать, что объединение элементарно
      have h_union_eq : ⋃ E ∈ S_sets, E = ⋃ B ∈ S, B.toSet := by simp [S_sets]
      have hA_elem : IsElementary (⋃ B ∈ S, B.toSet) := by
        rw [←h_union_eq]
        exact IsElementary.union' hS_elem
      -- E ⊆ ⋃ B ∈ S, значит Jordan_outer_measure E ≤ hA_elem.measure
      have h_outer_le : Jordan_outer_measure E ≤ hA_elem.measure := by
        unfold Jordan_outer_measure
        apply csInf_le
        · use 0; intro m' hm'; obtain ⟨_, hB, _, rfl⟩ := hm'; exact IsElementary.measure_nonneg hB
        · use ⋃ B ∈ S, B.toSet, hA_elem, hS_cover
      -- hA_elem.measure ≤ ∑ B ∈ S, |B|ᵥ по субаддитивности (IsElementary.measure_of_union')
      have h_sub : hA_elem.measure ≤ ∑ B ∈ S, |B|ᵥ := by
        -- Применяем IsElementary.measure_of_union' для получения субаддитивности
        have h1 := IsElementary.measure_of_union' hS_elem
        -- Показываем hA_elem.measure = (IsElementary.union' hS_elem).measure
        have h_eq : hA_elem.measure = (IsElementary.union' hS_elem).measure := by
          apply IsElementary.measure_eq_of_set_eq
          exact h_union_eq.symm
        -- Переводим сумму по S_sets в сумму по S.
        -- Техническая лемма: переиндексация суммы через Finset.sum_attach и Finset.sum_image
        have h2 : ∑ E : S_sets, (hS_elem E.val E.property).measure = ∑ B ∈ S, |B|ᵥ := by
          -- Определяем вспомогательную функцию, отделяющую меру от доказательства
          let vol (E : Set (EuclideanSpace' d)) := if h : IsElementary E then h.measure else 0

          -- 1. Показываем, что правая часть равна сумме по S'
          let S' := S.filter (fun B => B.toSet.Nonempty)
          have h_rhs : ∑ B ∈ S, |B|ᵥ = ∑ B ∈ S', |B|ᵥ := by
             rw [←Finset.sum_filter_add_sum_filter_not S (fun B => B.toSet.Nonempty) (fun B => |B|ᵥ)]
             suffices ∑ B ∈ S.filter (fun B => ¬B.toSet.Nonempty), |B|ᵥ = 0 by simp [this, S']
             apply Finset.sum_eq_zero
             intro B hB
             rw [Finset.mem_filter] at hB
             exact Box.volume_eq_zero_of_empty B (Set.not_nonempty_iff_eq_empty.mp hB.2)
          rw [h_rhs]

          -- 2. Упрощаем левую часть, используя vol и сумму по множествам
          have h_lhs : ∑ E : S_sets, (hS_elem E.val E.property).measure = ∑ E ∈ S_sets, vol E := by
            -- Конгруэнтность к vol
            have h_congr : ∑ E : S_sets, (hS_elem E.val E.property).measure = ∑ E : S_sets, vol E.val := by
              apply Finset.sum_congr rfl
              intro E _
              dsimp [vol]
              rw [dif_pos (hS_elem E.val E.property)]
            rw [h_congr]
            -- Сумма по подтипу — в сумму по множеству
            change ∑ E ∈ S_sets.attach, vol E.val = ∑ E ∈ S_sets, vol E
            rw [Finset.sum_attach S_sets]
          rw [h_lhs]

          -- 3. Ограничиваем сумму по множеству непустыми множествами
          let S_sets' := S'.image Box.toSet
          have h_subset : S_sets' ⊆ S_sets := Finset.image_subset_image (Finset.filter_subset _ _)

          have h_sets_eq : ∑ E ∈ S_sets, vol E = ∑ E ∈ S_sets', vol E := by
             rw [←Finset.sum_sdiff h_subset]
             suffices ∑ E ∈ S_sets \ S_sets', vol E = 0 by simp [this]
             apply Finset.sum_eq_zero
             intro E hE
             rw [Finset.mem_sdiff] at hE
             have hE_empty : E = ∅ := by
               obtain ⟨h_in, h_notin⟩ := hE
               rw [Finset.mem_image] at h_in
               obtain ⟨B, hB, rfl⟩ := h_in
               by_contra h_non
               apply h_notin
               simp [S_sets', S']
               use B
               simp [hB]
               rw [Set.nonempty_iff_ne_empty]
               exact h_non
             dsimp [vol]
             rw [hE_empty]
             rw [dif_pos (IsElementary.empty d)]
             exact IsElementary.measure_of_empty d
          rw [h_sets_eq]

          -- 4. Используем sum_image
          rw [Finset.sum_image]
          · -- Сопоставляем слагаемые
            apply Finset.sum_congr rfl
            intro B hB
            dsimp [vol]
            rw [dif_pos (IsElementary.box B)]
            exact IsElementary.measure_of_box B
          · -- Инъективность
            intro B₁ hB₁ B₂ hB₂ h_eq
            simp [S'] at hB₁ hB₂
            -- Используем вспомогательную лемму: Box.toSet инъективно для непустых прямоугольников
            exact Box.toSet_injective_of_nonempty hB₁.2 hB₂.2 h_eq
        calc hA_elem.measure
          _ = (IsElementary.union' hS_elem).measure := h_eq
          _ ≤ ∑ E : S_sets, (hS_elem E.val E.property).measure := h1
          _ = ∑ B ∈ S, |B|ᵥ := h2
      linarith

  -- Часть 2 (≥): sInf покрытий прямоугольниками ≤ Jordan_outer_measure E
  · -- Для любого элементарного A ⊇ E показываем sInf(покрытия) ≤ hA.measure
    unfold Jordan_outer_measure
    apply le_csInf
    -- Показываем, что множество мер элементарных покрытий непусто
    · obtain ⟨A, hA, hE_sub_A⟩ := IsElementary.contains_bounded hE
      use hA.measure
      use A, hA, hE_sub_A
    -- Показываем, что sInf(покрытия прямоугольниками) — нижняя грань для всех мер элементарных покрытий
    · intro m hm
      obtain ⟨A, hA, hE_sub_A, rfl⟩ := hm
      -- Получаем разбиение T множества A
      obtain ⟨T, hT_disj, hA_eq⟩ := hA.partition
      -- T — покрытие прямоугольниками: E ⊆ A = ⋃ B ∈ T
      have hT_cover : E ⊆ ⋃ B ∈ T, B.toSet := hA_eq ▸ hE_sub_A
      -- сумма объёмов T = hA.measure
      have hT_sum : ∑ B ∈ T, |B|ᵥ = hA.measure := by
        symm; exact hA.measure_eq hT_disj hA_eq
      -- sInf(покрытия прямоугольниками) ≤ ∑ B ∈ T, |B|ᵥ (так как T — покрытие прямоугольниками)
      have h_inf_le : sInf (((fun S : Finset (Box d) ↦ ∑ B ∈ S, |B|ᵥ)) '' { S | E ⊆ ⋃ B ∈ S, B.toSet }) ≤ ∑ B ∈ T, |B|ᵥ := by
        apply csInf_le
        -- Показываем, что множество покрытий прямоугольниками ограничено снизу
        · use 0
          intro m' hm'
          obtain ⟨S, _, rfl⟩ := hm'
          apply Finset.sum_nonneg
          intro B _
          rw [Box.volume]
          apply Finset.prod_nonneg
          intro i _
          rw [BoundedInterval.length]
          exact le_max_right _ _
        -- ∑ B ∈ T, |B|ᵥ входит в множество покрытий прямоугольниками
        · show ∑ B ∈ T, |B|ᵥ ∈ (fun S ↦ ∑ B ∈ S, |B|ᵥ) '' {S | E ⊆ ⋃ B ∈ S, B.toSet}
          simp
          exact ⟨T, hT_cover, rfl⟩
      -- Объединяем: sInf(покрытия прямоугольниками) ≤ ∑ B ∈ T, |B|ᵥ = hA.measure
      rw [←hT_sum]; exact h_inf_le

/-- Это определение отличается от текста тем, что работает со счётными семействами прямоугольников,
    а не с прямоугольниками, индексированными натуральными числами. Это становится важным в
    размерности ноль, когда все прямоугольники непусты. -/
noncomputable def Lebesgue_outer_measure {d : ℕ} (E : Set (EuclideanSpace' d)) : EReal :=
  sInf { V | ∃ (X : Set ℕ) (S : X → Box d), E ⊆ ⋃ n, (S n).toSet ∧ V = ∑' n, (S n).volume.toEReal }

/-- При d > 0 внешнюю меру Лебега можно вычислить, используя последовательности прямоугольников,
    индексированные ℕ, что эквивалентно определению через счётные семейства. Это возможно, так как
    любое счётное семейство можно дополнить прямоугольниками нулевого объёма
    (которые существуют при d > 0). -/
lemma Lebesgue_outer_measure_eq_nat_indexed {d : ℕ} (hd : 0 < d) (E : Set (EuclideanSpace' d)) :
    Lebesgue_outer_measure E =
    sInf (((fun S : ℕ → Box d ↦ ∑' n, (S n).volume.toEReal)) '' { S | E ⊆ ⋃ n, (S n).toSet }) := by
  unfold Lebesgue_outer_measure
  -- Стратегия: доказываем оба направления ≤
  -- (≤): любое покрытие, индексированное ℕ, — это счётное покрытие с X = Set.univ
  -- (≥): для любого счётного покрытия (X, S) строим индексированное ℕ покрытие S':
  --      - используем эквивалентность Set.univ ≃ ℕ для переиндексации
  --      - показываем равенство сумм через Equiv.tsum_eq
  apply le_antisymm

  -- Часть 1 (≤): покрытия, индексированные ℕ, ≥ счётные покрытия
  · apply le_sInf
    intro b hb
    obtain ⟨S, hS_cover, rfl⟩ := hb
    -- Показываем, что ∑' n, (S n).volume.toEReal входит в множество счётных покрытий
    apply sInf_le
    show ∑' n, (S n).volume.toEReal ∈ { V | ∃ (X : Set ℕ) (S : X → Box d), E ⊆ ⋃ n, (S n).toSet ∧ V = ∑' n, (S n).volume.toEReal }
    -- Переводим S : ℕ → Box d в S' : Set.univ → Box d
    let S' : Set.univ → Box d := fun n => S n.val
    use Set.univ, S'
    constructor
    · -- Свойство покрытия: E ⊆ ⋃ n : Set.univ, (S' n).toSet
      have : (⋃ n : Set.univ, (S' n).toSet) = (⋃ n, (S n).toSet) := by
        ext x
        simp [S']
      rw [this]
      exact hS_cover
    · -- Равенство сумм: ∑' (n : Set.univ), (S' n).volume.toEReal = ∑' n, (S n).volume.toEReal.
      -- Стратегия: используем Equiv.tsum_eq для переиндексации из Set.univ в ℕ
      simp only [S']
      -- Эквивалентность Equiv.Set.univ : Set.univ ≃ ℕ позволяет переиндексировать сумму.
      -- Мы хотим: ∑' (n : Set.univ), f(n.val) = ∑' (n : ℕ), f(n).
      -- Equiv.tsum_eq даёт: ∑' (c : Set.univ), f(e c) = ∑' (b : ℕ), f b.
      -- Нужно применить это в обратную сторону (используя symm)
      exact ((Equiv.Set.univ ℕ).tsum_eq (fun n => (S n).volume.toEReal)).symm

  -- Часть 2 (≥): счётные покрытия ≥ покрытия, индексированные ℕ
  · apply le_sInf
    intro b hb
    simp only [Set.mem_setOf_eq] at hb
    obtain ⟨X, S, hS_cover, hb_eq⟩ := hb
    open Classical in

    -- Строим прямоугольник нулевого объёма (существует при d > 0)
    have ⟨B₀, hB₀⟩ : ∃ B : Box d, B.volume = 0 := by
      -- При d > 0 можно построить прямоугольник с пустым интервалом в первом измерении
      use ⟨fun i => BoundedInterval.Ioc 0 0⟩
      simp only [Box.volume, BoundedInterval.length]
      -- Произведение ∏ i : Fin d, max (0 - 0) 0 = ∏ i : Fin d, 0
      conv_lhs => arg 2; ext i; rw [sub_self, max_eq_right (le_refl 0)]
      -- Теперь имеем ∏ i : Fin d, 0 = 0^d (так как d > 0, это 0)
      rw [Finset.prod_const]
      rw [show Finset.univ.card = d from Fintype.card_fin d]
      exact zero_pow (Nat.pos_iff_ne_zero.mp hd)

    -- Расширяем S : X → Box d до S' : ℕ → Box d, используя B₀ для индексов вне X
    let S' : ℕ → Box d := fun n => if h : n ∈ X then S ⟨n, h⟩ else B₀

    -- Показываем, что S' — корректное покрытие
    have hS'_cover : E ⊆ ⋃ n, (S' n).toSet := by
      intro x hx
      have := hS_cover hx
      simp only [Set.mem_iUnion] at this ⊢
      obtain ⟨⟨n, hn⟩, hxn⟩ := this
      use n
      -- В индексе n имеем n ∈ X, значит S' n = S ⟨n, hn⟩
      have : S' n = S ⟨n, hn⟩ := by simp [S', hn]
      rw [this]
      exact hxn

    -- Показываем равенство сумм
    have h_sum : ∑' n, (S' n).volume.toEReal = ∑' (n : X), (S n).volume.toEReal := by
      -- Стратегия: переписываем S' через if-then-else, затем показываем, что члены вне X дают 0.
      -- Используем tsum_congr, чтобы сопоставить члены внутри X с суммой по подтипу

      -- Шаг 1: явно выражаем левую часть, показывая if-then-else
      have h_S'_eq : ∀ n, (S' n).volume.toEReal =
          if h : n ∈ X then (S ⟨n, h⟩).volume.toEReal else (B₀.volume : EReal) := by
        intro n
        simp only [S']
        split_ifs <;> rfl

      simp_rw [h_S'_eq, hB₀]
      simp only [EReal.coe_zero]

      -- Шаг 2: сумма ∑' n, (if n ∈ X then f n else 0) = ∑' (n : X), f n.
      -- Это ключевое равенство, связывающее полную сумму с суммой по подтипу.
      -- Стратегия: показываем, что обе суммы перечисляют одни и те же члены через приведение подтипа.

      -- Обе части суммируют по одним и тем же элементам: для каждого n ∈ X добавляется (S n).volume.
      -- Левая часть использует характеристическую функцию; правая — индексацию по подтипу.
      -- Это стандартная переиндексация через вложение подтипа coe : X → ℕ

      -- Показываем, что функции совпадают при правильном сопоставлении
      have h_fn_eq : ∀ (x : X), (if h : ↑x ∈ X then (S ⟨↑x, h⟩).volume.toEReal else (0 : EReal)) =
                                 (S x).volume.toEReal := by
        intro ⟨n, hn⟩
        simp only [hn, dite_true]

      -- Теперь нужно: ∑' n : ℕ, (if h : n ∈ X then ... else 0) = ∑' x : X, f x.
      -- Это стандартный факт теории меры: суммирование с характеристической функцией
      -- равно суммированию по подтипу. Обе суммы перечисляют ровно одни и те же члены

      -- Определяем g, чтобы члены были яснее
      let g : ℕ → EReal := fun n => if h : n ∈ X then (S ⟨n, h⟩).volume.toEReal else 0

      -- 1. Показываем, что левая часть равна сумме g
      have h1 : (∑' n, if h : n ∈ X then (S ⟨n, h⟩).volume.toEReal else 0) = ∑' n, g n := rfl

      -- 2. Используем tsum_subtype, чтобы связать сумму по ℕ с суммой по X
      have h2 : ∑' n, g n = ∑' (x : X), g x := by
        -- Используем классическую логику для if-then-else
        classical
        -- tsum_subtype даёт: ∑' x:X, f x = ∑' n, if n ∈ X then f n else 0.
        -- Переписываем правую часть (сумму по X) в сумму по ℕ с if-then-else
        rw [tsum_subtype (f := g)]
        -- Теперь сопоставляем суммы почленно
        apply tsum_congr
        intro n
        -- g n по определению равно 0 вне X, что соответствует if-then-else
        rw [Set.indicator_apply]
        split_ifs with h
        · rfl
        · simp [g, h]

      -- 3. Показываем, что g, ограниченная на X, равна члену правой части
      have h3 : ∑' (x : X), g x = ∑' (x : X), (S x).volume.toEReal := by
        apply tsum_congr
        intro x
        -- Для x ∈ X, g x упрощается до S x.volume
        simp [g, x.property]

      -- Объединяем шаги
      rw [h1, h2, h3]

    -- Применяем sInf_le
    calc sInf (((fun S : ℕ → Box d ↦ ∑' n, (S n).volume.toEReal)) '' { S | E ⊆ ⋃ n, (S n).toSet })
        ≤ ∑' n, (S' n).volume.toEReal := by
            apply sInf_le
            use S', hS'_cover
        _ = ∑' (n : X), (S n).volume.toEReal := h_sum
        _ = b := hb_eq.symm

open Classical in
/-- Вспомогательная лемма: если X — бесконечное подмножество ℕ, то сумма его индикаторной функции
    (переводящей элементы X в 1, а остальные — в 0) расходится к ⊤ в {name}`EReal`. -/
lemma hasSum_indicator_top_of_infinite (X : Set ℕ) (hX : ¬X.Finite) :
    HasSum (fun n => if n ∈ X then (1 : EReal) else 0) ⊤ := by
  -- Стратегия: показываем, что конечные суммы растут неограниченно.
  -- Для любого n можно найти n элементов в X (так как X бесконечно),
  -- значит существует конечная сумма ≥ n. Это доказывает сходимость к ⊤.

  unfold HasSum
  rw [EReal.tendsto_nhds_top_iff_real]
  intro r

  -- Для любой вещественной границы r нужно показать, что в конце концов суммы превысят r.
  -- Выбираем n > r (используя округление вверх), затем находим n элементов в X
  obtain ⟨n, hn⟩ := exists_nat_gt r

  -- Так как X бесконечно, можно извлечь конечное подмножество ровно из n элементов
  have hX_inf : X.Infinite := hX
  obtain ⟨F, hF_sub, hF_card⟩ := Set.Infinite.exists_subset_card_eq hX_inf n

  -- Показываем, что в конце концов (в фильтре atTop) конечные суммы ≥ n
  apply Filter.eventually_atTop.mpr
  use F
  intro s hFs

  -- Для любого конечного множества s, содержащего F, имеем ∑ i ∈ s, (индикатор) ≥ n
  calc (r : EReal) < (n : EReal) := EReal.coe_lt_coe_iff.mpr hn
       _ = ↑F.card := by rw [hF_card]
       _ = ∑ i ∈ F, (1 : EReal) := by
           rw [Finset.sum_const, nsmul_one]
       _ = ∑ i ∈ F, if i ∈ X then (1 : EReal) else 0 := by
           apply Finset.sum_congr rfl
           intro i hi
           rw [if_pos]
           exact hF_sub (Finset.mem_coe.mpr hi)
       _ ≤ ∑ i ∈ s, if i ∈ X then (1 : EReal) else 0 := by
           apply Finset.sum_le_sum_of_subset_of_nonneg hFs
           intro i _ _
           split_ifs <;> norm_num

open Classical in
/-- В размерности 0 внешняя мера Лебега равна 1 для непустых множеств и 0 для пустого множества.
    Это происходит потому, что все прямоугольники в размерности 0 — это одноточечные множества с объёмом 1
    (пустое произведение). -/
lemma Lebesgue_outer_measure_of_dim_zero {E : Set (EuclideanSpace' 0)} :
    Lebesgue_outer_measure E = if E.Nonempty then 1 else 0 := by
  unfold Lebesgue_outer_measure

  -- Сначала доказываем: все прямоугольники в размерности 0 имеют объём 1 (пустое произведение)
  have h_box_vol : ∀ B : Box 0, B.volume = 1 := by
    intro B
    unfold Box.volume
    -- Fin 0 пусто, значит Finset.univ пусто, и пустое произведение = 1
    have : Finset.univ = (∅ : Finset (Fin 0)) := by
      ext i
      exact Fin.elim0 i
    rw [this]
    rfl

  by_cases hE : E.Nonempty

  -- Случай 1: E непусто → мера = 1
  · simp only [hE, ↓reduceIte]
    apply le_antisymm

    -- Верхняя граница: показываем sInf ≤ 1, предъявив покрытие с суммой = 1
    · apply sInf_le
      -- Строим покрытие, используя одноэлементное множество {0}
      let X : Set ℕ := {0}
      let B₀ : Box 0 := ⟨fun i => Fin.elim0 i⟩
      let S : X → Box 0 := fun _ => B₀
      use X, S
      constructor
      · -- Показываем E ⊆ ⋃ n, (S n).toSet
        intro x _
        simp only [Set.mem_iUnion]
        use ⟨0, Set.mem_singleton 0⟩
        -- Все точки в EuclideanSpace' 0 входят в любой прямоугольник
        unfold Box.toSet
        intro i
        exact Fin.elim0 i
      · -- Показываем V = ∑' n, (S n).volume.toEReal = 1.
        -- S отображает каждый элемент X = {0} в B₀, у которого объём 1
        have h_vol_eq : ∀ (n : X), (S n).volume.toEReal = (1 : EReal) := by
          intro n
          simp only [S, h_box_vol, EReal.coe_one]
        simp_rw [h_vol_eq]
        -- ∑' (_ : {0}), (1 : EReal) = 1, используя tsum по конечному типу
        rw [tsum_fintype]
        -- Теперь имеем ∑ x ∈ Finset.univ, (1 : EReal), где Finset.univ имеет мощность 1
        simp only [Finset.sum_const]
        -- Показываем Finset.univ.card • 1 = 1, показав, что мощность = 1
        have h_card : Fintype.card X = 1 := Set.card_singleton 0
        simp only [Fintype.card] at h_card
        rw [h_card]
        norm_num

    -- Нижняя граница: показываем 1 ≤ sInf (у каждого покрытия сумма ≥ 1)
    · apply le_sInf
      intro b hb
      simp only [Set.mem_setOf_eq] at hb
      obtain ⟨X, S, hcover, hb_eq⟩ := hb
      -- E непусто, значит покрытие тоже должно быть непустым
      have hX_nonempty : X.Nonempty := by
        obtain ⟨x, hx⟩ := hE
        have := hcover hx
        simp only [Set.mem_iUnion] at this
        obtain ⟨⟨n, hn⟩, _⟩ := this
        exact ⟨n, hn⟩
      rw [hb_eq]
      -- Сумма объёмов (каждый = 1) по непустому множеству X
      have : ∀ (n : X), (S n).volume.toEReal = (1 : EReal) := by
        intro n
        simp [h_box_vol]
      simp_rw [this]
      -- Нужно: ∑' (_ : X), (1 : EReal) ≥ 1, когда X.Nonempty.
      -- Выбираем элемент n₀ из X и показываем, что сумма включает как минимум этот член
      obtain ⟨n₀, hn₀⟩ := hX_nonempty
      -- Переводим сумму по подтипу в сумму по ℕ с индикатором
      classical
      let g : ℕ → EReal := fun n => if h : n ∈ X then (1 : EReal) else (0 : EReal)
      have h1 : ∑' (n : ↑X), (1 : EReal) = ∑' n : ℕ, g n := by
        -- Используем tsum_subtype: ∑' (x : X), f x = ∑' n, X.indicator f n
        rw [tsum_subtype (f := fun n => (1 : EReal))]
        apply tsum_congr
        intro n
        -- Показываем X.indicator (fun n => 1) n = g n
        simp [g, Set.indicator_apply]
      rw [h1]
      -- Сначала показываем, что все члены неотрицательны
      have h_nonneg : ∀ n, (0 : EReal) ≤ g n := by
        intro n
        simp [g]
        split_ifs
        · exact EReal.coe_nonneg.mpr (by norm_num)
        · exact EReal.coe_nonneg.mpr (by norm_num)
      -- Показываем, что g n₀ = 1
      have h_gn0 : g n₀ = (1 : EReal) := by
        simp [g, hn₀]
      -- Ключевая идея: для суммируемых неотрицательных функций любой член ≤ сумме.
      -- Так как g неотрицательна и суммируема (это индикаторная функция со значениями 0 или 1),
      -- имеем g n₀ ≤ ∑' n, g n.
      -- Для EReal строим это через свойства HasSum
      have h_le : g n₀ ≤ ∑' n : ℕ, g n := by
        -- Используем, что tsum — супремум конечных сумм.
        -- Так как {n₀} — конечное подмножество, ∑ n ∈ {n₀}, g n ≤ ∑' n, g n.
        -- И ∑ n ∈ {n₀}, g n = g n₀ = 1
        have h_single : ∑ n ∈ ({n₀} : Finset ℕ), g n = g n₀ := by
          simp [Finset.sum_singleton]
        have : HasSum g (∑' n : ℕ, g n) := by
          by_cases hX : X.Finite
          · -- Случай 1: X конечно
            have h_supp : g.support.Finite := by
              dsimp [g, Function.support]
              apply Set.Finite.subset hX
              intro n h
              simp at h
              exact h
            exact (summable_of_hasFiniteSupport h_supp).hasSum
          · -- Случай 2: X бесконечно.
            -- Сумма равна Top. Доказываем HasSum g Top
            have h_top : HasSum g ⊤ := by
              -- Применяем вспомогательную лемму: бесконечная индикаторная сумма расходится к ⊤.
              -- g и функция из леммы определённо равны под classical
              convert hasSum_indicator_top_of_infinite X hX using 2
            exact h_top.tsum_eq.symm ▸ h_top
        -- Если HasSum g s, то для любого конечного множества F, ∑ n ∈ F, g n ≤ s.
        -- Применяем это с F = {n₀}
        have h_fin_le : ∑ n ∈ ({n₀} : Finset ℕ), g n ≤ ∑' n : ℕ, g n := by
          rw [Finset.sum_singleton]
          -- Так как g неотрицательна, g n₀ ≤ сумме по любому надмножеству, содержащему n₀.
          -- В частности, g n₀ ≤ ∑' n, g n
          trans (∑ n ∈ Finset.range (n₀ + 1), g n)
          · apply Finset.single_le_sum (fun i _ => h_nonneg i)
            simp
          · -- Теперь показываем ∑ n ∈ range (n₀+1), g n ≤ tsum
            exact sum_le_hasSum (L := .unconditional ℕ) _ (fun i _ => h_nonneg i) this
        rw [h_single] at h_fin_le
        exact h_fin_le
      rw [h_gn0] at h_le
      exact h_le

  -- Случай 2: E пусто → мера = 0
  · simp only [hE, ↓reduceIte]
    apply le_antisymm

    -- Верхняя граница: показываем sInf ≤ 0, предъявив покрытие с суммой = 0
    · apply sInf_le
      -- Пустое покрытие: X = ∅
      let X : Set ℕ := ∅
      use X
      -- Нужно предоставить S : X → Box 0, но X пусто, поэтому используем elim
      refine ⟨fun x => absurd x.2 (Set.notMem_empty x.1), ?_, ?_⟩
      · -- Пустое множество покрывается пустым покрытием
        intro x hx
        simp only [Set.not_nonempty_iff_eq_empty] at hE
        exact absurd hx (hE ▸ Set.notMem_empty x)
      · -- Сумма по пустому множеству = 0
        simp

    -- Нижняя граница: 0 ≤ sInf (все суммы EReal ≥ 0 при суммировании объёмов)
    · apply le_sInf
      intro b hb
      simp only [Set.mem_setOf_eq] at hb
      obtain ⟨X, S, _, hb_eq⟩ := hb
      rw [hb_eq]
      -- Сумма неотрицательных объёмов ≥ 0
      apply tsum_nonneg
      intro n
      apply EReal.coe_nonneg.mpr
      -- Объём прямоугольника — это произведение неотрицательных длин
      unfold Box.volume
      apply Finset.prod_nonneg
      intro i _
      unfold BoundedInterval.length
      exact le_max_right _ _

/-- Приведение {lean}`ℝ → EReal` сохраняет инфимумы для непустых ограниченных снизу множеств -/
lemma EReal.sInf_image_coe {s : Set ℝ} (hs : s.Nonempty) (h_bdd : BddBelow s) :
    sInf ((fun x : ℝ => (x : EReal)) '' s) = ↑(sInf s) := by
  -- Стратегия: доказываем оба направления ≤, используя свойства sInf
  apply le_antisymm

  -- Часть 1: sInf(↑''s) ≤ ↑(sInf s)
  · -- Ключевая идея: sInf(↑''s) — нижняя грань для ↑''s, значит sInf(↑''s) ≤ ↑x для всех x ∈ s.
    -- Хотим показать, что отсюда следует sInf(↑''s) ≤ ↑(sInf s).
    -- Разбираем случаи: является ли sInf(↑''s) значением ⊥ или вещественным числом
    by_cases h_bot : sInf ((fun y : ℝ => (y : EReal)) '' s) = ⊥
    · rw [h_bot]; exact bot_le
    · -- sInf(↑''s) ограничена снизу (так как s ограничено), значит она не ⊥ и не ⊤.
      -- Имеем: ∀ x ∈ s, sInf(↑''s) ≤ ↑x
      have h_le_all : ∀ x ∈ s, sInf ((fun y : ℝ => (y : EReal)) '' s) ≤ ↑x := by
        intro x hx; apply sInf_le; exact ⟨x, hx, rfl⟩
      -- Так как s ограничено снизу, существует m такое, что m ≤ x для всех x ∈ s.
      -- Это означает, что ↑m — нижняя грань для ↑''s, значит ↑m ≤ sInf(↑''s).
      -- В сочетании с sInf(↑''s) ≤ ↑x для всех x получаем, что sInf(↑''s) лежит в [↑m, ↑x₀],
      -- где x₀ ∈ s, следовательно sInf(↑''s) должно быть приведённым вещественным числом.
      -- Затем можно извлечь r := (sInf(↑''s)).toReal и показать r ≤ sInf s
      obtain ⟨m, hm⟩ := h_bdd
      have h_bdd_below : (m : EReal) ≤ sInf ((fun y : ℝ => (y : EReal)) '' s) := by
        apply le_sInf
        intro b hb
        obtain ⟨x, hx, rfl⟩ := hb
        exact EReal.coe_le_coe_iff.mpr (hm hx)
      -- Теперь sInf(↑''s) ∈ [↑m, ↑x₀], значит это приведённое вещественное число.
      -- Хотим: sInf(↑''s) ≤ ↑(sInf s).
      -- Стратегия: показываем sInf(↑''s) ≤ ↑x для всех x ∈ s, затем берём инф по x.
      -- Применяем le_csInf: чтобы показать a ≤ sInf s, доказываем, что a — нижняя грань для s
      obtain ⟨x₀, hx₀⟩ := hs
      have h_le_x0 : sInf ((fun y : ℝ => (y : EReal)) '' s) ≤ ↑x₀ := h_le_all x₀ hx₀
      -- sInf(↑''s) лежит в [↑m, ↑x₀], значит это должно быть приведённое вещественное число
      have h_exists_r : ∃ r : ℝ, sInf ((fun y : ℝ => (y : EReal)) '' s) = ↑r := by
        -- Используем, что sInf(↑''s) ограничена: ↑m ≤ sInf(↑''s) ≤ ↑x₀.
        -- Если sInf(↑''s) = ⊤, то ↑x₀ ≥ ⊤, что противоречит тому, что x₀ вещественно
        by_cases h_top : sInf ((fun y : ℝ => (y : EReal)) '' s) = ⊤
        · -- Получаем противоречие: ↑x₀ ≥ ⊤
          have : (x₀ : EReal) ≥ ⊤ := by rw [←h_top]; exact h_le_x0
          simp [not_le.mpr] at this
        · -- sInf(↑''s) не равно ⊥ (из h_bot) и не равно ⊤ (из h_top).
          -- Значит это должно быть приведённое вещественное число.
          -- Используем трихотомию EReal: либо ⊥, либо ⊤, либо приведённое вещественное число
          have h_cases := EReal.def (sInf ((fun y : ℝ => (y : EReal)) '' s))
          cases h_cases with
          | inl h => obtain ⟨r, hr⟩ := h; exact ⟨r, hr.symm⟩
          | inr h => cases h with
            | inl h_eq_top => exact absurd h_eq_top h_top
            | inr h_eq_bot => exact absurd h_eq_bot h_bot
      obtain ⟨r, hr⟩ := h_exists_r
      rw [hr]
      -- Теперь показываем: ↑r ≤ ↑(sInf s), то есть r ≤ sInf s
      apply EReal.coe_le_coe_iff.mpr
      -- Показываем r ≤ sInf s, показав, что r — нижняя грань для s
      have hs' : s.Nonempty := ⟨x₀, hx₀⟩
      apply le_csInf hs'
      intro x hx
      -- Показываем r ≤ x для всех x ∈ s.
      -- У нас есть ↑r = sInf(↑''s) ≤ ↑x
      have : (r : EReal) ≤ ↑x := by rw [←hr]; exact h_le_all x hx
      exact EReal.coe_le_coe_iff.mp this

  -- Часть 2: ↑(sInf s) ≤ sInf(↑''s).
  -- Показываем, что ↑(sInf s) — нижняя грань для ↑''s
  · apply le_sInf
    intro b hb
    obtain ⟨x, hx_in_s, rfl⟩ := hb
    -- Показываем: ↑(sInf s) ≤ ↑x
    apply EReal.coe_le_coe_iff.mpr
    -- Показываем: sInf s ≤ x (верно, так как x ∈ s, а sInf s — нижняя грань)
    exact csInf_le h_bdd hx_in_s

/-- При перечислении конечного множества в последовательность, дополненную пустыми
    прямоугольниками, бесконечная сумма объёмов равна конечной сумме -/
lemma tsum_volume_finset_eq {d : ℕ} (hd : 0 < d) (S : Finset (Box d)) :
    let S_list := S.toList
    let zero_box : Box d := ⟨fun i => if i.val = 0 then ∅ else BoundedInterval.Icc 0 0⟩
    let S_seq : ℕ → Box d := fun n =>
      if h : n < S_list.length then S_list.get ⟨n, h⟩ else zero_box
    ∑' n, (S_seq n).volume.toEReal = (∑ B ∈ S, |B|ᵥ).toEReal := by
  -- Стратегия: у zero_box объём 0 (первая сторона пуста), поэтому tsum = сумма по конечному диапазону.
  -- Затем связываем сумму по конечному диапазону с суммой по конечному множеству через перечисление списком
  intro S_list zero_box S_seq

  -- Шаг 1: показываем, что у zero_box объём 0
  have h_zero_vol : |zero_box|ᵥ = 0 := by
    unfold Box.volume zero_box
    simp only
    -- Первая сторона (индекс 0) пуста, значит произведение равно 0
    apply Finset.prod_eq_zero (Finset.mem_univ (⟨0, hd⟩ : Fin d))
    simp only [ite_true]
    simp [BoundedInterval.length]

  -- Шаг 2: используем tsum_eq_sum, чтобы перевести бесконечную сумму в конечную
  have h_tsum_eq : ∑' n, (S_seq n).volume.toEReal = ∑ n ∈ Finset.range S_list.length, (S_seq n).volume.toEReal := by
    apply tsum_eq_sum
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    unfold S_seq
    rw [dif_neg (not_lt_of_ge hn)]
    simp [h_zero_vol]

  -- Шаг 3: связываем сумму по finset.range с суммой по конечному множеству S
  rw [h_tsum_eq]
  suffices h : (∑ n ∈ Finset.range S_list.length, (S_seq n).volume) = (∑ B ∈ S, |B|ᵥ) by
    calc ∑ n ∈ Finset.range S_list.length, (S_seq n).volume.toEReal
        = ∑ n ∈ Finset.range S_list.length, ((S_seq n).volume : EReal) := rfl
      _ = (∑ n ∈ Finset.range S_list.length, (S_seq n).volume : ℝ).toEReal := by
        -- Приведение ℝ → EReal коммутирует с Finset.sum.
        -- Это следует из EReal.coe_add: (x + y : EReal) = (x : EReal) + (y : EReal).
        -- Доказываем индукцией: пустая сумма равна 0, а для cons используем EReal.coe_add и предположение индукции
        refine Finset.cons_induction (by simp) ?_ (Finset.range S_list.length)
        intro a s ha ih
        rw [Finset.sum_cons ha]
        conv_rhs => rw [Finset.sum_cons ha, EReal.coe_add]
        -- Теперь: ↑(S_seq a).volume + ∑ x ∈ s, ↑(S_seq x).volume = ↑(S_seq a).volume + ↑(∑ x ∈ s, (S_seq x).volume).
        -- Используем ih: ∑ x ∈ s, ↑(S_seq x).volume = ↑(∑ x ∈ s, (S_seq x).volume)
        rw [ih]
      _ = (∑ B ∈ S, |B|ᵥ).toEReal := by rw [h]

  -- Доказываем: ∑ n ∈ Finset.range S_list.length, (S_seq n).volume = ∑ B ∈ S, |B|ᵥ.
  -- Используем Finset.sum_bij, чтобы установить биекцию между индексами и элементами конечного множества.
  -- sum_bij: (i : α → β) (hi : ∀ a ∈ s, i a ∈ t) (h : ∀ a ∈ s, g (i a) = f a)
  --          (hg : ∀ b ∈ t, ∃ a ∈ s, i a = b) (hh : ∀ a₁ a₂ ∈ s, i a₁ = i a₂ → a₁ = a₂)
  refine Finset.sum_bij (fun n hn => S_list.get ⟨n, Finset.mem_range.mp hn⟩) ?_ ?_ ?_ ?_
  · -- hi : образ лежит в S
    intro n hn
    have hn_lt := Finset.mem_range.mp hn
    have : S_list.get ⟨n, hn_lt⟩ ∈ S_list := List.get_mem S_list ⟨n, hn_lt⟩
    exact Finset.mem_toList.mp this
  · -- i_inj : инъективность
    intro n₁ hn₁ n₂ hn₂ heq
    have hn₁_lt := Finset.mem_range.mp hn₁
    have hn₂_lt := Finset.mem_range.mp hn₂
    -- List.get инъективно, когда в списке нет повторов (что верно для Finset.toList).
    -- Из heq: S_list[n₁] = S_list[n₂], и S_list.Nodup, выводим n₁ = n₂
    have h_nodup : S_list.Nodup := Finset.nodup_toList S
    -- Упрощаем heq, чтобы получить S_list.get ⟨n₁, hn₁_lt⟩ = S_list.get ⟨n₂, hn₂_lt⟩
    have h_get_eq : S_list.get ⟨n₁, hn₁_lt⟩ = S_list.get ⟨n₂, hn₂_lt⟩ := by
      simp at heq
      exact heq
    -- Используем nodup, чтобы показать равенство индексов.
    -- List.nodup_iff_injective_get: Nodup l ↔ Function.Injective l.get
    have h_inj : Function.Injective S_list.get := List.nodup_iff_injective_get.mp h_nodup
    -- Применяем инъективность: S_list.get ⟨n₁, hn₁_lt⟩ = S_list.get ⟨n₂, hn₂_lt⟩ влечёт ⟨n₁, hn₁_lt⟩ = ⟨n₂, hn₂_lt⟩
    have h_idx_eq : (⟨n₁, hn₁_lt⟩ : Fin S_list.length) = ⟨n₂, hn₂_lt⟩ := h_inj h_get_eq
    exact congrArg Fin.val h_idx_eq
  · -- i_surj : сюръективность
    intro b hb
    obtain ⟨i, hi⟩ := List.get_of_mem (Finset.mem_toList.mpr hb)
    -- hi : S.toList.get i = b, и S_list = S.toList, значит S_list.get i = b.
    -- Нужно показать (fun n hn ↦ S_list.get ⟨n, ⋯⟩) i.val ... = b.
    -- Так как i : Fin S_list.length, имеем S_list.get ⟨i.val, i.isLt⟩ = S_list.get i = b
    have h_eq : (fun n hn => S_list.get ⟨n, Finset.mem_range.mp hn⟩) i.val (Finset.mem_range.mpr i.isLt) = b := by
      simp
      -- S_list = S.toList, значит S_list.get i = S.toList.get i = b
      rw [←hi]
      rfl
    exact ⟨i.val, Finset.mem_range.mpr i.isLt, h_eq⟩
  · -- h : функция сохраняет слагаемое
    intro n hn
    have hn_lt := Finset.mem_range.mp hn
    simp only [S_seq, dif_pos hn_lt]


-- Для любого ограниченного множества внешняя мера Лебега не превосходит внешнюю меру Жордана.
theorem Lebesgue_outer_measure_le_Jordan {d : ℕ} {E : Set (EuclideanSpace' d)} (hE : Bornology.IsBounded E) : Lebesgue_outer_measure E ≤ Jordan_outer_measure E := by
  -- Стратегия: разбираем d = 0 отдельно, используя Lebesgue_outer_measure_of_dim_zero. При d > 0:
  -- выражаем внешнюю меру Жордана как инфимум по конечным покрытиям через Jordan_outer_eq.
  -- Показываем, что внешняя мера Лебега (инфимум по счётным покрытиям) ≤ Жордана, доказывая, что
  -- Лебег ≤ каждой сумме конечного покрытия: переводим конечное покрытие S в счётную
  -- последовательность S_seq (перечисляя через toList, дополняя нулями), показываем, что S_seq —
  -- счётное покрытие с той же суммой, затем применяем свойства инфимума, чтобы заключить Лебег ≤ Жордана.

  by_cases hd : d = 0
  · subst hd
    -- Используем характеризацию Lebesgue_outer_measure для d = 0
    rw [Lebesgue_outer_measure_of_dim_zero]
    by_cases hE_ne : E.Nonempty
    · -- Случай: E непусто, значит Lebesgue_outer_measure E = 1.
      simp only [hE_ne, ↓reduceIte]
      -- Нужно показать (1 : EReal) ≤ ↑(Jordan_outer_measure E).
      -- Любое элементарное множество, содержащее непустое E, должно быть непустым, значит имеет меру ≥ 1
      have h : (1 : ℝ) ≤ Jordan_outer_measure E := by
        unfold Jordan_outer_measure
        apply le_csInf
        · -- Показываем, что множество непусто
          obtain ⟨A, hA, hE_sub_A⟩ := IsElementary.contains_bounded hE
          exact ⟨hA.measure, A, hA, hE_sub_A, rfl⟩
        · -- Показываем, что 1 — нижняя грань для всех мер в множестве
          intro m hm
          obtain ⟨A, hA, hE_sub_A, rfl⟩ := hm
          -- A содержит E, которое непусто, значит A непусто
          have hA_ne : A.Nonempty := hE_ne.mono hE_sub_A
          -- В размерности 0 любое непустое элементарное множество имеет меру ≥ 1.
          -- Это потому, что элементарные множества — конечные объединения прямоугольников,
          -- а у каждого прямоугольника объём 1
          obtain ⟨S, hS_disj, hA_eq⟩ := hA.partition
          -- Находим непустой прямоугольник в разбиении
          have : ∃ B ∈ S, B.toSet.Nonempty := by
            by_contra h
            push_neg at h
            -- h говорит: ∀ B, B ∈ S → B.toSet = ∅
            have hA_empty : A = ∅ := by
              rw [hA_eq]
              ext x
              simp only [Set.mem_iUnion, Set.mem_empty_iff_false, iff_false]
              intro ⟨B, hB, hx⟩
              rw [h B hB] at hx
              exact hx
            exact Set.Nonempty.ne_empty hA_ne hA_empty
          obtain ⟨B, hB_in_S, hB_ne⟩ := this
          -- Все прямоугольники в размерности 0 имеют объём 1
          have h_vol : |B|ᵥ = 1 := by
            unfold Box.volume
            have : Finset.univ = (∅ : Finset (Fin 0)) := by ext i; exact Fin.elim0 i
            rw [this]
            rfl
          -- Мера — это сумма объёмов, включающая как минимум один прямоугольник с объёмом 1
          have h_measure : hA.measure = ∑ B' ∈ S, |B'|ᵥ := hA.measure_eq hS_disj hA_eq
          -- У каждого прямоугольника объём ≥ 0 (как произведение неотрицательных длин)
          have h_vol_nonneg : ∀ B' : Box 0, 0 ≤ |B'|ᵥ := by
            intro B'
            unfold Box.volume
            apply Finset.prod_nonneg
            intro i _
            unfold BoundedInterval.length
            exact le_max_right _ _
          -- Сумма включает B с объёмом 1, значит итог ≥ 1
          calc hA.measure
            = ∑ B' ∈ S, |B'|ᵥ := h_measure
            _ ≥ |B|ᵥ := by
                classical
                rw [←Finset.sum_erase_add _ _ hB_in_S]
                simp only [le_add_iff_nonneg_left]
                apply Finset.sum_nonneg
                intro B' _
                exact h_vol_nonneg B'
            _ = 1 := h_vol
      exact EReal.coe_le_coe_iff.mpr h
    · -- Случай: E пусто, значит Lebesgue_outer_measure E = 0.
      simp only [hE_ne, ↓reduceIte]
      -- Нужно показать (0 : EReal) ≤ ↑(Jordan_outer_measure E), что следует из неотрицательности
      exact EReal.coe_nonneg.mpr (Jordan_outer_measure_nonneg E)

  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd

  -- Переписываем внешнюю меру Жордана через Jordan_outer_eq
  rw [Jordan_outer_eq hE]
  unfold Lebesgue_outer_measure

  -- Показываем sInf (счётные покрытия) ≤ (сумма конечного покрытия : EReal) для всех конечных покрытий.
  -- Это влечёт sInf (счётные) ≤ sInf (конечные)
  have h_le : ∀ m ∈ (fun S ↦ (∑ B ∈ S, |B|ᵥ : ℝ)) '' {S | E ⊆ ⋃ B ∈ S, B.toSet},
      sInf { V | ∃ (X : Set ℕ) (S : X → Box d), E ⊆ ⋃ n, (S n).toSet ∧ V = ∑' n, (S n).volume.toEReal } ≤ (m : EReal) := by
    intro m hm
    obtain ⟨S, hS_cover, rfl⟩ := hm

    -- Переводим конечное покрытие S в счётную последовательность S_seq
    classical
    let S_list := S.toList
    let zero_box : Box d := ⟨fun i => if i.val = 0 then ∅ else BoundedInterval.Icc 0 0⟩
    have h_card_eq : S_list.length = S.card := Finset.length_toList S
    let S_seq : ℕ → Box d := fun n =>
      if h : n < S_list.length then S_list.get ⟨n, h⟩ else zero_box

    -- Шаг 1: свойство покрытия сохраняется
    have h_cover : E ⊆ ⋃ n, (S_seq n).toSet := by
      intro x hx
      -- Нужно показать: x ∈ ⋃ n, (S_seq n).toSet, то есть ∃ n, x ∈ (S_seq n).toSet
      simp only [Set.mem_iUnion]
      -- hS_cover : E ⊆ ⋃ B ∈ S, B.toSet, значит x лежит в некотором прямоугольнике B ∈ S
      have : x ∈ ⋃ B ∈ S, B.toSet := hS_cover hx
      simp only [Set.mem_iUnion] at this
      obtain ⟨B, hB_in_S, hx_in_B⟩ := this
      -- Так как B ∈ S, он встречается в S_list по некоторому индексу
      have hB_in_list : B ∈ S_list := Finset.mem_toList.mpr hB_in_S
      -- Получаем индекс i, по которому S_list содержит B
      obtain ⟨i, hi_eq⟩ := List.get_of_mem hB_in_list
      -- Предоставляем i.val в качестве свидетеля
      use i.val
      -- S_seq i.val = S_list.get ⟨i.val, i.isLt⟩ = B по hi_eq
      simp only [S_seq]
      have hi_val_lt : i.val < S_list.length := i.isLt
      rw [dif_pos hi_val_lt]
      -- Показываем ⟨i.val, hi_val_lt⟩ = i, чтобы можно было использовать hi_eq
      have : (⟨i.val, hi_val_lt⟩ : Fin S_list.length) = i := Fin.ext rfl
      rw [this, hi_eq]
      exact hx_in_B

    -- Шаг 2: равенство сумм через tsum_eq_sum
    have h_sum_eq : ∑' n, (S_seq n).volume.toEReal = (∑ B ∈ S, |B|ᵥ).toEReal := by
      exact tsum_volume_finset_eq hd_pos S

    -- Шаг 3: применяем свойство инфимума
    calc sInf { V | ∃ (X : Set ℕ) (S : X → Box d), E ⊆ ⋃ n, (S n).toSet ∧ V = ∑' n, (S n).volume.toEReal }
        ≤ ∑' n, (S_seq n).volume.toEReal := by
            apply sInf_le
            show ∑' n, (S_seq n).volume.toEReal ∈ { V | ∃ (X : Set ℕ) (S : X → Box d), E ⊆ ⋃ n, (S n).toSet ∧ V = ∑' n, (S n).volume.toEReal }
            use Set.univ, fun (n : Set.univ) => S_seq n.val
            constructor
            · -- Показываем E ⊆ ⋃ n, (S n).toSet
              convert h_cover using 2
              ext x
              simp
            · -- Показываем V = ∑' n, (S n).volume.toEReal
              exact ((Equiv.Set.univ ℕ).tsum_eq (fun n => (S_seq n).volume.toEReal)).symm
        _ = (∑ B ∈ S, |B|ᵥ).toEReal := h_sum_eq

  -- Используем h_le, чтобы показать sInf (счётные) ≤ sInf (конечные).
  -- Имеем: ∀ m ∈ finite_set, Lebesgue_sInf ≤ ↑m.
  -- Нужно показать: Lebesgue_sInf ≤ ↑(sInf finite_set).
  -- Так как finite_set непусто, а sInf finite_set — наибольшая нижняя грань,
  -- достаточно показать Lebesgue_sInf ≤ ↑m для всех m из finite_set
  have h_nonempty : ((fun S ↦ (∑ B ∈ S, |B|ᵥ : ℝ)) '' {S | E ⊆ ⋃ B ∈ S, B.toSet}).Nonempty := by
    obtain ⟨A, hA, hE_sub_A⟩ := IsElementary.contains_bounded hE
    obtain ⟨T, hT_disj, hA_eq⟩ := hA.partition
    use (∑ B ∈ T, |B|ᵥ : ℝ)
    use T
    simp
    intro a ha
    have : a ∈ A := hE_sub_A ha
    rw [hA_eq] at this
    exact this
  -- Цель — показать: Lebesgue_sInf ≤ ↑(sInf(finite)).
  -- У нас есть h_le, показывающее: ∀ m ∈ finite_set, Lebesgue_sInf ≤ ↑m.
  -- Ключевая идея: ↑(sInf finite_set) = sInf (↑ '' finite_set) (монотонное приведение сохраняет sInf).
  -- Затем используем le_sInf: если a ≤ b для всех b ∈ s, то a ≤ sInf s

  -- Сначала показываем, что sInf(счётные) ≤ sInf(↑ '' finite_set)
  have h_le_coe : sInf { V | ∃ (X : Set ℕ) (S : X → Box d), E ⊆ ⋃ n, (S n).toSet ∧ V = ∑' n, (S n).volume.toEReal }
      ≤ sInf ((fun m : ℝ => (m : EReal)) '' ((fun S ↦ ∑ B ∈ S, |B|ᵥ) '' {S | E ⊆ ⋃ B ∈ S, B.toSet})) := by
    apply le_sInf
    intro b hb
    obtain ⟨m, hm_in, rfl⟩ := hb
    exact h_le m hm_in

  -- Теперь показываем, что sInf(↑ '' finite_set) = ↑(sInf finite_set), и применяем h_le_coe.
  -- Множество объёмов ограничено снизу нулём
  have h_bdd : BddBelow ((fun S ↦ ∑ B ∈ S, |B|ᵥ) '' {S | E ⊆ ⋃ B ∈ S, B.toSet}) := by
    use 0
    intro m hm
    obtain ⟨S, _, rfl⟩ := hm
    apply Finset.sum_nonneg
    intro B _
    -- Объём прямоугольника — это произведение длин интервалов, которые неотрицательны по определению
    simp only [Box.volume]
    apply Finset.prod_nonneg
    intro i _
    simp [BoundedInterval.length]

  -- Применяем транзитивность: Lebesgue_sInf ≤ sInf(↑ '' finite) = ↑(sInf finite)
  calc sInf { V | ∃ (X : Set ℕ) (S : X → Box d), E ⊆ ⋃ n, (S n).toSet ∧ V = ∑' n, (S n).volume.toEReal }
      ≤ sInf ((fun m : ℝ => (m : EReal)) '' ((fun S ↦ ∑ B ∈ S, |B|ᵥ) '' {S | E ⊆ ⋃ B ∈ S, B.toSet})) := h_le_coe
      _ = ↑(sInf ((fun S ↦ ∑ B ∈ S, |B|ᵥ) '' {S | E ⊆ ⋃ B ∈ S, B.toSet})) := by
          -- Используем вспомогательную лемму: EReal.sInf_image_coe
          exact EReal.sInf_image_coe h_nonempty h_bdd

/-- Пример 1.2.1. С соглашениями о мусорных значениях этого сопровождения, внешняя мера Жордана
    рациональных чисел равна нулю, а не бесконечности (кажется). -/
-- Внешняя мера Жордана рациональных чисел в ограниченном интервале равна длине интервала.
example {R : ℝ} (hR : 0 < R) : Jordan_outer_measure (Real.equiv_EuclideanSpace' '' (Set.Icc (-R) R ∩ Set.range (fun q : ℚ ↦ (q : ℝ)))) = 2*R := by
  sorry

-- У любого счётного множества (в положительной размерности) внешняя мера Лебега равна нулю.
theorem Countable.Lebesgue_measure {d : ℕ} (hd : 0 < d) {E : Set (EuclideanSpace' d)} (hE : E.Countable) : Lebesgue_outer_measure E = 0 := by
  unfold Lebesgue_outer_measure
  -- Стратегия: покрываем E одноточечными прямоугольниками, у каждого из которых объём 0

  -- Получаем перечисление: E ⊆ range f для некоторого f : ℕ → EuclideanSpace' d
  haveI : Nonempty (EuclideanSpace' d) := inferInstance
  obtain ⟨f, hf⟩ := Set.countable_iff_exists_subset_range.mp hE

  -- Строим одноточечный прямоугольник для каждого f(n)
  let singleton_box : ℕ → Box d := fun n => ⟨fun i => BoundedInterval.Icc (f n i) (f n i)⟩

  -- Показываем, что E покрыто этими прямоугольниками
  have h_cover : E ⊆ ⋃ n, (singleton_box n).toSet := by
    calc E ⊆ Set.range f := hf
       _ ⊆ ⋃ n, (singleton_box n).toSet := by
         intro x hx
         obtain ⟨n, rfl⟩ := hx
         simp [Set.mem_iUnion]
         use n
         intro i
         simp [BoundedInterval.toSet]
         exact ⟨le_refl _, le_refl _⟩

  -- У каждого одноточечного прямоугольника объём 0
  have h_vol : ∀ n, (singleton_box n).volume = 0 := by
    intro n
    exact Box.volume_singleton hd (f n)

  -- Сумма объёмов равна 0
  have h_sum : ∑' n, (singleton_box n).volume.toEReal = 0 := by
    simp only [h_vol]
    simp [EReal.coe_zero, tsum_zero]

  -- Применяем это покрытие, чтобы показать, что инфимум не превосходит 0
  have h_le : sInf { V | ∃ (X : Set ℕ) (S : X → Box d), E ⊆ ⋃ n, (S n).toSet ∧ V = ∑' n, (S n).volume.toEReal } ≤ 0 := by
    apply csInf_le
    · -- Показываем, что множество ограничено снизу нулём
      use 0
      intro V ⟨X, S, _, hV⟩
      rw [hV]
      -- Объёмы прямоугольников неотрицательны, значит их сумма неотрицательна
      apply tsum_nonneg
      intro n
      exact EReal.coe_nonneg.mpr (by
        unfold Box.volume
        apply Finset.prod_nonneg
        intro i _
        unfold BoundedInterval.length
        exact le_max_right _ _)
    · -- Показываем, что 0 входит в множество (через наше одноточечное покрытие)
      use Set.univ
      use fun (n : Set.univ) => singleton_box n.val
      refine ⟨?_, ?_⟩
      · -- E ⊆ ⋃ n : Set.univ, (singleton_box n.val).toSet
        intro x hx
        simp only [Set.mem_iUnion]
        have : x ∈ ⋃ n, (singleton_box n).toSet := h_cover hx
        simp only [Set.mem_iUnion] at this
        obtain ⟨n, hn⟩ := this
        exact ⟨⟨n, Set.mem_univ n⟩, hn⟩
      · -- ∑' n : Set.univ, (singleton_box n.val).volume.toEReal = 0
        simp only [h_vol, EReal.coe_zero, tsum_zero]

  -- Показываем, что инфимум не меньше 0
  have h_ge : 0 ≤ sInf { V | ∃ (X : Set ℕ) (S : X → Box d), E ⊆ ⋃ n, (S n).toSet ∧ V = ∑' n, (S n).volume.toEReal } := by
    apply le_csInf
    · -- Показываем, что множество непусто (у нас есть одноточечное покрытие)
      use 0
      use Set.univ
      use fun (n : Set.univ) => singleton_box n.val
      exact ⟨h_cover.trans (by intro x; simp only [Set.mem_iUnion]; intro ⟨n, hn⟩; exact ⟨⟨n, Set.mem_univ n⟩, hn⟩), by simp only [h_vol, EReal.coe_zero, tsum_zero]⟩
    · -- Показываем, что все элементы ≥ 0
      intro V ⟨X, S, _, hV⟩
      rw [hV]
      apply tsum_nonneg
      intro n
      exact EReal.coe_nonneg.mpr (by
        unfold Box.volume
        apply Finset.prod_nonneg
        intro i _
        unfold BoundedInterval.length
        exact le_max_right _ _)

  exact le_antisymm h_le h_ge

-- Внешняя мера Лебега рациональных чисел в ограниченном интервале равна нулю.
example {R : ℝ} : Lebesgue_outer_measure (Real.equiv_EuclideanSpace' '' (Set.Icc (-R) R ∩ Set.range (fun q : ℚ ↦ (q : ℝ)))) = 0 := by
  apply Countable.Lebesgue_measure (by omega : 0 < 1)
  apply Set.Countable.image
  -- Пересечение счётно, потому что правая часть счётна
  have : (Set.Icc (-R) R ∩ Set.range (fun q : ℚ ↦ (q : ℝ))).Countable := by
    apply Set.Countable.mono (Set.inter_subset_right)
    exact Set.countable_range (fun q : ℚ => (q : ℝ))
  exact this

-- Внешняя мера Лебега всех рациональных чисел равна нулю.
example : Lebesgue_outer_measure (Real.equiv_EuclideanSpace' '' (Set.range (fun q : ℚ ↦ (q : ℝ)))) = 0 := by
  apply Countable.Lebesgue_measure (by omega : 0 < 1)
  apply Set.Countable.image
  exact Set.countable_range (fun q : ℚ => (q : ℝ))

-- Множество измеримо по Лебегу, если его можно сколь угодно точно приблизить снаружи открытыми множествами.
def LebesgueMeasurable {d : ℕ} (E : Set (EuclideanSpace' d)) : Prop :=
  ∀ ε > 0, ∃ U : Set (EuclideanSpace' d), IsOpen U ∧ E ⊆ U ∧ Lebesgue_outer_measure (U \ E) ≤ ε

-- Мера Лебега множества (равна его внешней мере Лебега).
noncomputable def Lebesgue_measure {d : ℕ} (E : Set (EuclideanSpace' d)) : EReal := Lebesgue_outer_measure E
