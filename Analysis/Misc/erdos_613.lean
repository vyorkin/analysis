import Mathlib

open Classical
open scoped BigOperators


-- 1. Формулировка основного утверждения

/-- «Монохроматическая звезда цвета {name}`col` размера {name}`k`»: существует центр {given}`x` и
    множество {given (type := "Finset V")}`S` из {name}`k` различных соседей {given}`x`, таких что
    каждое ребро {given -show}`y` {lean}`s(x, y)` с {lean}`y ∈ S` присутствует в {lean}`G` и
    покрашено в цвет {name}`col`.  (Никаких ограничений на рёбра внутри {name}`S` не накладывается.) -/
def hasMonoStar {V : Type*} (G : SimpleGraph V) (color : Sym2 V → Fin 2)
    (col : Fin 2) (k : ℕ) : Prop :=
  ∃ (x : V) (S : Finset V),
    S.card = k ∧
    x ∉ S ∧
    ∀ ⦃y : V⦄, y ∈ S → G.Adj x y ∧ color (s(x, y)) = col

/--
{given -show}`a, b, c : V`
«Монохроматический треугольник цвета {name}`col`»: существуют {name}`a`, {name}`b`, {name}`c`, такие
что все три ребра присутствуют в {lean}`G` и покрашены в цвет {name}`col`.  (Отношение смежности уже
гарантирует их попарную различность.)
-/
def hasMonoTriangle {V : Type*} (G : SimpleGraph V) (color : Sym2 V → Fin 2)
    (col : Fin 2) : Prop :=
  ∃ a b c : V,
    G.Adj a b ∧ G.Adj b c ∧ G.Adj a c ∧
    color (s(a, b)) = col ∧
    color (s(b, c)) = col ∧
    color (s(a, c)) = col

/-- **Утверждение (случай n = 5 контрпримера Пихурко).**
Существует простой граф на {lean}`16` вершинах ровно с {lean}`44` рёбрами, такой что для *любой*
2-раскраски неупорядоченных пар либо цвет {lean (type := "Fin 2")}`0` содержит $`K_{1,5}`
(звезду с 5 рёбрами), либо цвет {lean (type := "Fin 2")}`1` содержит $`K₃` (треугольник).

Здесь утверждение только *формулируется* (как {lean}`Prop`). Доказать его можно позже из явной
конструкции, либо пока принять как аксиому, продолжая разработку остального. -/
def Pikhurko_n5_statement : Prop :=
  ∃ (V : Type) (G : SimpleGraph V),
    G.edgeSet.ncard = 44 ∧
    ∀ (color : Sym2 V → Fin 2),
      hasMonoStar G color 0 5 ∨ hasMonoTriangle G color 1


-- 2. Построение графа

namespace PikhurkoN5

/-- Тип вершин с 2 + 5 + 3 + 5 + 1 = 16 вершинами. -/
inductive V
| A1 (i : Fin 2)  -- часть K₂ графа P_{2,5}
| B1 (j : Fin 5)  -- независимая часть P_{2,5}
| A2 (i : Fin 3)  -- часть K₃ графа P_{3,5}
| B2 (j : Fin 5)  -- независимая часть P_{3,5}
| apex            -- универсальная вершина
deriving DecidableEq, Repr

open V

/-- Отношение смежности для контрпримера Пихурко при n=5.

* Внутри {name}`A1` и внутри {name}`A2`: клики.
* Между {name}`A1`–{name}`B1` и {name}`A2`–{name}`B2`: полный двудольный граф.
* Внутри {name}`B1` и {name}`B2`: рёбер нет.
* Между двумя блоками {name}`A1`/{name}`B1` и {name}`A2`/{name}`B2` рёбер нет.
* {name}`apex` соединена рёбрами со всеми вершинами, кроме {name}`apex`. -/
def GAdj : V → V → Prop
| apex, apex => False
| apex, _    => True
| _,    apex => True
| A1 i, A1 j => i ≠ j
| A2 i, A2 j => i ≠ j
| A1 _, B1 _ => True
| B1 _, A1 _ => True
| A2 _, B2 _ => True
| B2 _, A2 _ => True
| _,    _    => False

/-- Граф {name}`G` на 16 вершинах, используемый для контрпримера при n=5. -/
def G : SimpleGraph V where
  Adj := GAdj
  symm := by
    intro u v h
    cases u <;> cases v <;> grind [GAdj]
  loopless := ⟨by intro v; cases v <;> simp [GAdj]⟩

/-!
Вспомогательные simp-леммы. Они не обязательны, но пригодятся позже при доказательстве
свойств раскрасок.
-/
@[simp] lemma adj_apex_left {v : V} : G.Adj V.apex v ↔ v ≠ V.apex := by
  cases v <;> simp [G, GAdj]

@[simp] lemma adj_apex_right {v : V} : G.Adj v V.apex ↔ v ≠ V.apex := by
  cases v <;> simp [G, GAdj]

@[simp] lemma adj_A1A1 {i j} : G.Adj (A1 i) (A1 j) ↔ i ≠ j := by
  simp [G, GAdj]

@[simp] lemma adj_A2A2 {i j} : G.Adj (A2 i) (A2 j) ↔ i ≠ j := by
  simp [G, GAdj]

@[simp] lemma adj_A1B1 {i j} : G.Adj (A1 i) (B1 j) := by
  simp [G, GAdj]

@[simp] lemma adj_B1A1 {i j} : G.Adj (B1 i) (A1 j) := by
  simp [G, GAdj]

@[simp] lemma adj_A2B2 {i j} : G.Adj (A2 i) (B2 j) := by
  simp [G, GAdj]

@[simp] lemma adj_B2A2 {i j} : G.Adj (B2 j) (A2 i)  := by
  simp [G, GAdj]

@[simp] lemma no_adj_B1B1 {j j'} : ¬ G.Adj (B1 j) (B1 j') := by
  simp [G, GAdj]

@[simp] lemma no_adj_B2B2 {j j'} : ¬ G.Adj (B2 j) (B2 j') := by
  simp [G, GAdj]

@[simp] lemma no_cross_blocks_A1B2 {i j} : ¬ G.Adj (A1 i) (B2 j) := by
  simp [G, GAdj]

@[simp] lemma no_cross_blocks_A2B1 {i j} : ¬ G.Adj (A2 i) (B1 j) := by
  simp [G, GAdj]

@[simp] lemma no_cross_blocks_B1A2 {i j} : ¬ G.Adj (B1 j) (A2 i)  := by
  simp [G, GAdj]

@[simp] lemma no_cross_blocks_B1B2 {i j} : ¬ G.Adj (B1 j) (B2 i)  := by
  simp [G, GAdj]

@[simp] lemma no_cross_blocks_A2A1 {i j} : ¬ G.Adj (A2 j) (A1 i)  := by
  simp [G, GAdj]

end PikhurkoN5


-- 3. Подсчёт рёбер

namespace PikhurkoN5

open V

/- Нам понадобится `Fintype` на `V` для `univ`, сумм и т.д. -/
deriving instance Fintype for V

/-- Явная эквивалентность, показывающая, что {name}`V` состоит из 2+5+3+5+1 = 16 элементов. -/
def VEquiv : 
    V ≃ ((((Fin 2 ⊕ Fin 5) ⊕ Fin 3) ⊕ Fin 5) ⊕ Unit) where
  toFun
  | A1 i  => Sum.inl (Sum.inl (Sum.inl (Sum.inl i)))
  | B1 j  => Sum.inl (Sum.inl (Sum.inl (Sum.inr j)))
  | A2 i  => Sum.inl (Sum.inl (Sum.inr i))
  | B2 j  => Sum.inl (Sum.inr j)
  | apex  => Sum.inr ()
  invFun
  | Sum.inl (Sum.inl (Sum.inl (Sum.inl i))) => A1 i
  | Sum.inl (Sum.inl (Sum.inl (Sum.inr j))) => B1 j
  | Sum.inl (Sum.inl (Sum.inr i))            => A2 i
  | Sum.inl (Sum.inr j)                      => B2 j
  | Sum.inr ()                               => apex
  left_inv v := by cases v <;> grind
  right_inv w := by cases w <;> grind

/-- $`|V| = 16`. Полезно для быстрой арифметики с мощностями. -/
lemma card_V : Fintype.card V = 16 := by
  -- Сводим к мощности вложенной суммы и вычисляем арифметически.
  simpa using
    (Fintype.card_congr VEquiv).trans <|
      by
        -- `simp` превращает мощности сумм в суммы мощностей; остальное делает `norm_num`.
        simp [Fintype.card_sum, Fintype.card_fin]

/-! # Вычисление степеней

Вычисляем степень каждого *вида* вершины. Используем {attr}`@[simp]`-леммы о смежности
из подхода A:
- {name}`adj_apex_left`, {name}`adj_A1A1`, {name}`adj_A2A2`, {name}`adj_A1B1`, {name}`adj_A2B2`,
  а также соответствующие леммы «нет ребра» между блоками.
-/

/-- `deg(apex) = 15`. -/
lemma degree_apex : G.degree apex = 15 := by
  classical
  -- Соседи `apex` — это в точности все вершины ≠ `apex`.
  have hN : 
      G.neighborFinset apex = (Finset.univ.erase apex) := by
    ext v; constructor
    · intro hv
      have : G.Adj apex v := by simpa using hv
      have hvne : v ≠ apex := by simpa [adj_apex_left] using this
      simpa [Finset.mem_erase] using And.intro hvne (by simp : v ∈ (Finset.univ : Finset V))
    · intro hv
      have hvne : v ≠ apex := (Finset.mem_erase.mp hv).1
      have : G.Adj apex v := by simpa [adj_apex_left] using hvne
      simpa using this
  -- Считаем `univ.erase apex`.
  have : (G.neighborFinset apex).card = 15 := by
    -- `card (erase univ apex) = |V| - 1 = 16 - 1 = 15`
    have : (Finset.univ.erase apex).card = Fintype.card V - 1 := by
      have : apex ∈ (Finset.univ : Finset V) := by simp
      simp [Finset.card_erase_of_mem, this]
    simp [hN, card_V]
  -- `degree` — это мощность множества соседей.
  simp at this
  assumption

/-- `deg(A1 i) = 7` для каждого {name}`i`. -/
lemma degree_A1 (i : Fin 2) : G.degree (A1 i) = 7 := by
  rw [←G.card_neighborFinset_eq_degree, ←Finset.card_image_of_injective _ VEquiv.injective]
  simp_rw [←Finset.card_toLeft_add_card_toRight]
  calc
    _ = 1 + 5 + 0 + 0 + 1 := by
      congr
      . calc
        _ = Finset.card {j | j ≠ i} := by
          congr; ext; simp
          simp_rw [←Equiv.eq_symm_apply VEquiv]
          simp [VEquiv]
          grind
        _ = 1 := by
          fin_cases i <;> simp
          . convert Finset.card_singleton 1
          convert Finset.card_singleton 0
      . calc
        _ = Finset.card (Finset.univ : Finset (Fin 5)) := by
          congr; ext; simp
          simp_rw [←Equiv.eq_symm_apply VEquiv]
          simp [VEquiv]
        _ = 5 := by simp [Fintype.card_fin]
      . calc
        _ = Finset.card (∅ : Finset (Fin 3)) := by
          congr; ext; simp [-iff_false]
          simp_rw [←Equiv.eq_symm_apply VEquiv]
          simp [VEquiv]
          aesop
        _ = 0 := by simp
      . calc
        _ = Finset.card (∅ : Finset (Fin 5)) := by
          congr; ext; simp [-iff_false]
          simp_rw [←Equiv.eq_symm_apply VEquiv]
          simp [VEquiv]
        _ = 0 := by simp
      calc
        _ = Finset.card (Finset.univ : Finset Unit) := by
          congr; ext; simp
          simp_rw [←Equiv.eq_symm_apply VEquiv]
          simp [VEquiv]
        _ = 1 := by simp
    _ = _ := by norm_num

/-- $`deg(B1 j) = 3` для каждого $`j`. (Два соседа в {name}`A1` + apex.) -/
lemma degree_B1 (j : Fin 5) : G.degree (B1 j) = 3 := by
  rw [←G.card_neighborFinset_eq_degree, ←Finset.card_image_of_injective _ VEquiv.injective]
  simp_rw [←Finset.card_toLeft_add_card_toRight]
  calc
    _ = 2 + 0 + 0 + 0 + 1 := by
      congr
      . calc
          _ = Finset.card (Finset.univ : Finset (Fin 2)) := by
            congr; ext; simp
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv]
          _ = _ := by simp
      . calc
          _ = Finset.card (∅ : Finset (Fin 5)) := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv]
          _ = _ := by simp
      . calc
          _ = Finset.card (∅ : Finset (Fin 3)) := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv]
          _ = _ := by simp
      . calc
          _ = Finset.card (∅ : Finset (Fin 5)) := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv]
          _ = _ := by simp
      calc
        _ = Finset.card (Finset.univ : Finset Unit) := by
          congr; ext; simp
          simp_rw [←Equiv.eq_symm_apply VEquiv]
          simp [VEquiv]
        _ = 1 := by simp
    _ = _ := by norm_num



/-- $`deg(A2 i) = 8` для каждого $`i`. (Два внутри {name}`A2` + пять в {name}`B2` + apex.) -/
lemma degree_A2 (i : Fin 3) : G.degree (A2 i) = 8 := by
  rw [←G.card_neighborFinset_eq_degree, ←Finset.card_image_of_injective _ VEquiv.injective]
  simp_rw [←Finset.card_toLeft_add_card_toRight]
  calc
    _ = 0 + 0 + 2 + 5 + 1 := by
      congr
      . calc
          _ = Finset.card (∅ : Finset (Fin 2)) := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv]
          _ = _ := by simp
      . calc
          _ = Finset.card (∅ : Finset (Fin 5)) := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv]
          _ = _ := by simp
      . calc
          _ = Finset.card {j | j ≠ i} := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv]
            grind
          _ = _ := by
            convert Finset.card_erase_of_mem (show i ∈ Finset.univ by simp)
            grind
      . calc
          _ = Finset.card (Finset.univ : Finset (Fin 5)) := by
            congr; ext; simp
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv]
          _ = _ := by simp
      calc
        _ = Finset.card (Finset.univ : Finset Unit) := by
          congr; ext; simp
          simp_rw [←Equiv.eq_symm_apply VEquiv]
          simp [VEquiv]
        _ = 1 := by simp
    _ = _ := by norm_num


/-- $`deg(B2 j) = 4` для каждого $`j`. (Три соседа в {name}`A2` + apex.) -/
lemma degree_B2 (j : Fin 5) : G.degree (B2 j) = 4 := by
  rw [←G.card_neighborFinset_eq_degree, ←Finset.card_image_of_injective _ VEquiv.injective]
  simp_rw [←Finset.card_toLeft_add_card_toRight]
  calc
    _ = 0 + 0 + 3 + 0 + 1 := by
      congr
      . calc
          _ = Finset.card (∅ : Finset (Fin 2)) := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv, G, GAdj]
          _ = _ := by simp
      . calc
          _ = Finset.card (∅ : Finset (Fin 5)) := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv, G, GAdj]
          _ = _ := by simp
      . calc
          _ = Finset.card (Finset.univ : Finset (Fin 3)) := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv, G, GAdj]
          _ = _ := by simp
      . calc
          _ = Finset.card (∅ : Finset (Fin 5)) := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv, G, GAdj]
          _ = _ := by simp
      calc
        _ = Finset.card (Finset.univ : Finset Unit) := by
          congr; ext; simp
          simp_rw [←Equiv.eq_symm_apply VEquiv]
          simp [VEquiv, G, GAdj]
        _ = 1 := by simp
    _ = _ := by norm_num

/-!
# Подсчёт рёбер через лемму о рукопожатиях
Теперь суммируем степени и делим на 2.
-/
theorem edge_count_44 : G.edgeSet.ncard = 44 := by
  classical
  -- Лемма о рукопожатиях для мощности *множества* рёбер.
  -- В текущей версии mathlib она формулируется так:
  --   `G.sum_degrees_eq_twice_card_edgeSet : (∑ v, G.degree v) = 2 * G.edgeSet.ncard`.
  have hand := G.sum_degrees_eq_twice_card_edges
  rw [←SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  rw [←Equiv.sum_comp VEquiv.symm _] at hand
  simp_rw [Fintype.sum_sum_type] at hand
  have : ∀ i, G.degree (VEquiv.symm (.inl (.inl (.inl (.inl i))))) = G.degree (A1 i) := fun _ => rfl
  have : ∀ j, G.degree (VEquiv.symm (.inl (.inl (.inl (.inr j))))) = G.degree (B1 j) := fun _ => rfl
  have : ∀ i, G.degree (VEquiv.symm (.inl (.inl (.inr i)))) = G.degree (A2 i) := fun _ => rfl
  have : ∀ j, G.degree (VEquiv.symm (.inl (.inr j))) = G.degree (B2 j) := fun _ => rfl
  have : ∀ u, G.degree (VEquiv.symm (.inr u)) = G.degree apex := fun _ => rfl
  simp_all [degree_A1, degree_B1, degree_A2, degree_B2, degree_apex]; omega

end PikhurkoN5


-- 4. Показываем, что красных соседей apex ≥ 11, если нет синей K_{1,5}

namespace PikhurkoN5
open V

/-! # Небольшие вспомогательные утверждения -/

/- Выбираем `k`-элементное подмножество finset `s`, когда `k ≤ s.card`. -/
namespace Finset
variable {α : Type*}

lemma exists_subset_card_eq (s : Finset α) {k : ℕ} (hk : k ≤ s.card) : 
  ∃ t ⊆ s, t.card = k := by
  exact Finset.le_card_iff_exists_subset_card.mp hk

end Finset

/-- В {lean}`Fin 2` условие «равно {lean (type := "Fin 2")}`1`» равносильно условию «не равно {lean (type := "Fin 2")}`0`». -/
lemma fin2_eq_one_iff_ne_zero (a : Fin 2) : (a = 1) ↔ a ≠ 0 := by
  fin_cases a <;> simp

/-! # Красных соседей apex ≥ 11, если нет синей звезды `K_{1,5}` -/

/-- Множество синих соседей {name}`apex` в цветовом классе {lean (type := "Fin 2")}`0`. -/
noncomputable def blueNeighbors (color : Sym2 V → Fin 2) : Finset V :=
  (G.neighborFinset apex).filter (fun v => color (s(apex, v)) = 0)

/-- Множество красных соседей {name}`apex` в цветовом классе {lean (type := "Fin 2")}`1`. -/
noncomputable def redNeighbors (color : Sym2 V → Fin 2) : Finset V :=
  (G.neighborFinset apex).filter (fun v => color (s(apex, v)) = 1)

/-- Если нет синей `K_{1,5}`, то у apex не более 4 синих соседей. -/
lemma blueNeighbors_card_le_4
    (color : Sym2 V → Fin 2)
    (hNoBlueStar : ¬ hasMonoStar G color 0 5) : 
    (blueNeighbors color).card ≤ 4 := by
  classical
  -- Предположим, что синих соседей ≥5; извлекаем 5-элементное подмножество и получаем синюю звезду.
  by_contra hle
  have hge : 5 ≤ (blueNeighbors color).card :=
    Nat.succ_le_of_lt (lt_of_not_ge hle)
  obtain ⟨S, hSsubset, hScard⟩ :=
    Finset.exists_subset_card_eq (blueNeighbors color) hge

  -- `apex ∉ S`, так как `apex` не является соседом самого себя.
  have hapex_notin : apex ∉ S := by
    have : apex ∉ G.neighborFinset apex := by
      -- Отсутствие петель ⇒ apex не смежна сама с собой ⇒ не входит в множество соседей.
      simp [SimpleGraph.neighborFinset]
    exact fun hx => this <| (by
      have hx' : apex ∈ blueNeighbors color := hSsubset hx
      -- Синие соседи — подмножество всех соседей.
      have : blueNeighbors color ⊆ G.neighborFinset apex :=
        by
          intro v hv
          exact Finset.mem_of_mem_filter _ hv
      exact this hx')

  -- Все рёбра от `apex` до `S` присутствуют и синие, значит, у нас есть синяя K_{1,5}.
  have hstar : hasMonoStar G color 0 5 := by
    refine ⟨apex, S, hScard, hapex_notin, ?_⟩
    intro y hy
    have hy' : y ∈ blueNeighbors color := hSsubset hy
    have hy_in : y ∈ G.neighborFinset apex ∧ color (s(apex, y)) = 0 := by
      simpa [blueNeighbors] using hy'
    exact ⟨by simpa using hy_in.1, hy_in.2⟩

  exact hNoBlueStar hstar

/-- Если нет синей `K_{1,5}`, то как минимум {lean}`11` соседей {name}`apex` красные. -/
lemma red_from_apex_at_least_11
    (color : Sym2 V → Fin 2)
    (hNoBlueStar : ¬ hasMonoStar G color 0 5) : 
    (redNeighbors color).card ≥ 11 := by
  classical
  -- Разбиваем соседей apex на синих и несиних; отождествляем несиних с красными.
  have hsplit : 
      (blueNeighbors color).card
      + ((G.neighborFinset apex).filter (fun v => ¬ (color (s(apex, v)) = 0))).card
      = (G.neighborFinset apex).card := by
    simpa [blueNeighbors] using
      (Finset.card_filter_add_card_filter_not
        (s := G.neighborFinset apex)
        (p := fun v => color (s(apex, v)) = 0))

  have hred_is_notblue : 
      (G.neighborFinset apex).filter (fun v => ¬ (color (s(apex, v)) = 0))
      =
      redNeighbors color := by
    ext v; by_cases hv : v ∈ G.neighborFinset apex
    · -- Среди соседей «не синий» означает «красный».
      simp [redNeighbors, hv, fin2_eq_one_iff_ne_zero]
    · simp [redNeighbors, hv]

  -- Итак, синих + красных = всех соседей = 15 (по `degree_apex`).
  have hsum : (blueNeighbors color).card + (redNeighbors color).card
              = (G.neighborFinset apex).card := by
    convert Finset.card_sdiff_add_card_eq_card _
    . simp only [←hred_is_notblue, blueNeighbors]
      ext v; grind
    . infer_instance
    simp [redNeighbors]


  have hdeg : (G.neighborFinset apex).card = 15 := by
    simp [degree_apex]

  have hblue_le_4 := blueNeighbors_card_le_4 color hNoBlueStar

  -- Преобразуем `blue + red = 15` в `red = 15 - blue`.
  have hred_eq : (redNeighbors color).card
      = 15 - (blueNeighbors color).card := by
    have hsum' : (redNeighbors color).card + (blueNeighbors color).card = 15 := by
      simpa [Nat.add_comm, hdeg] using hsum
    have := congrArg (fun t => t - (blueNeighbors color).card) hsum'
    -- `(red + blue) - blue = 15 - blue` ⇒ `red = 15 - blue`.
    simpa [Nat.add_sub_cancel] using this

  -- Наконец: `blue ≤ 4` ⇒ `15 - blue ≥ 11`.
  have : 11 ≤ 15 - (blueNeighbors color).card :=
    by grind

  -- Объединяем с `red = 15 - blue`.
  simpa [hred_eq] using this

end PikhurkoN5


-- 5. Принцип Дирихле: один из блоков получает ≥ 6 красных рёбер от apex
namespace PikhurkoN5
open V

/-- Принадлежность первому блоку {name}`A1`/{name}`B1`. -/
def inBlock1 : V → Prop
| A1 _ => True
| B1 _ => True
| _    => False

noncomputable instance : DecidablePred inBlock1 := by
  intro v; cases v <;> infer_instance

/-- Красные соседи {name}`apex`, лежащие в первом блоке {name}`A1`/{name}`B1`. -/
noncomputable def redBlock1 (color : Sym2 V → Fin 2) : Finset V :=
  (redNeighbors color).filter (fun v => inBlock1 v)

/-- Красные соседи {name}`apex`, лежащие во втором блоке {name}`A2`/{name}`B2`.

Реализуем это как *дополнение* {name}`inBlock1` внутри {name}`redNeighbors`.
Поскольку {name}`apex` не входит в {name}`redNeighbors`, это в точности часть {name}`A2`/{name}`B2`. -/
noncomputable def redBlock2 (color : Sym2 V → Fin 2) : Finset V :=
  (redNeighbors color).filter (fun v => ¬ inBlock1 v)

/-- Разбиение красных соседей {name}`apex` на два блока. -/
lemma redBlocks_partition_card (color : Sym2 V → Fin 2) : 
  (redBlock1 color).card + (redBlock2 color).card = (redNeighbors color).card := by
  classical
  -- Стандартное тождество разбиения `filter` + `filter (¬p)`.
  simpa [redBlock1, redBlock2] using
    (Finset.card_filter_add_card_filter_not
      (s := redNeighbors color) (p := fun v => inBlock1 v))

/-- **Шаг с принципом Дирихле.** Если нет синей `K_{1,5}`, то
один из двух блоков получает от {name}`apex` не менее шести красных рёбер. -/
lemma exists_block_receives_at_least_6_red
    (color : Sym2 V → Fin 2)
    (hNoBlueStar : ¬ hasMonoStar G color 0 5) : 
    (redBlock1 color).card ≥ 6 ∨ (redBlock2 color).card ≥ 6 := by
  classical
  -- Всего красных рёбер от `apex` не менее 11 (доказано ранее).
  have h11 : 11 ≤ (redNeighbors color).card :=
    red_from_apex_at_least_11 color hNoBlueStar
  -- Разбиваем красных соседей по двум блокам.
  have hsum := redBlocks_partition_card color
  -- Если бы в обоих блоках было ≤ 5, то суммарно было бы ≤ 10 — противоречие.
  by_contra h
  push_neg at h   -- h : (redBlock1 color).card ≤ 5 ∧ (redBlock2 color).card ≤ 5
  have hle10 : (redNeighbors color).card ≤ 10 := by
    have : (redBlock1 color).card + (redBlock2 color).card ≤ 5 + 5 := by
      grind
    simpa [hsum] using this
  exact (Nat.not_succ_le_self 10) (le_trans h11 hle10)

end PikhurkoN5


-- 6. Демонстрируем красного соседа на стороне клики

namespace PikhurkoN5
open V

/-! # Предикаты частей / блоков -/

/-- Распознаёт сторону клики {name}`A1`. -/
def isA1 : V → Prop
| A1 _ => True | _ => False

/-- Распознаёт независимую сторону {name}`B1`. -/
def isB1 : V → Prop
| B1 _ => True | _ => False

/-- Распознаёт сторону клики {name}`A2`. -/
def isA2 : V → Prop
| A2 _ => True | _ => False

/-- Распознаёт независимую сторону {name}`B2`. -/
def isB2 : V → Prop
| B2 _ => True | _ => False

/-- Второй блок {name}`A2`/{name}`B2`. -/
def inBlock2 : V → Prop
| A2 _ => True | B2 _ => True | _ => False

noncomputable instance : DecidablePred isA1 := by intro v; cases v <;> infer_instance
noncomputable instance : DecidablePred isB1 := by intro v; cases v <;> infer_instance
noncomputable instance : DecidablePred isA2 := by intro v; cases v <;> infer_instance
noncomputable instance : DecidablePred isB2 := by intro v; cases v <;> infer_instance
noncomputable instance : DecidablePred inBlock1 := by intro v; cases v <;> infer_instance
noncomputable instance : DecidablePred inBlock2 := by intro v; cases v <;> infer_instance

@[simp] lemma inBlock1_iff (v : V) : inBlock1 v ↔ (isA1 v ∨ isB1 v) := by
  cases v <;> simp [inBlock1, isA1, isB1]

@[simp] lemma inBlock2_iff (v : V) : inBlock2 v ↔ (isA2 v ∨ isB2 v) := by
  cases v <;> simp [inBlock2, isA2, isB2]

@[simp] lemma not_isA1_and_isB1 (v : V) : ¬ (isA1 v ∧ isB1 v) := by
  cases v <;> simp [isA1, isB1]

@[simp] lemma not_isA2_and_isB2 (v : V) : ¬ (isA2 v ∧ isB2 v) := by
  cases v <;> simp [isA2, isB2]

/-! # Разбиение красных соседей {name}`apex` по частям -/

-- Это было получено на предыдущем шаге:
-- def redNeighbors (color : Sym2 V → Fin 2) : Finset V := ...


/-- Уточняем {name}`redBlock1`, разбивая его на части {name}`A1` и {name}`B1`. -/
noncomputable def redBlock1A1 (color : Sym2 V → Fin 2) : Finset V :=
  (redNeighbors color).filter (fun v => isA1 v)

noncomputable def redBlock1B1 (color : Sym2 V → Fin 2) : Finset V :=
  (redNeighbors color).filter (fun v => isB1 v)

/-- Уточняем {name}`redBlock2`, разбивая его на части {name}`A2` и {name}`B2`. -/
noncomputable def redBlock2A2 (color : Sym2 V → Fin 2) : Finset V :=
  (redNeighbors color).filter (fun v => isA2 v)

noncomputable def redBlock2B2 (color : Sym2 V → Fin 2) : Finset V :=
  (redNeighbors color).filter (fun v => isB2 v)

/-- {name}`redBlock1` — это в точности непересекающееся объединение его частей {name}`A1` и {name}`B1`. -/
lemma redBlock1_eq_union (color : Sym2 V → Fin 2) : 
  redBlock1 color =
    redBlock1A1 color ∪ redBlock1B1 color := by
  ext v; constructor
  · intro hv
    rcases Finset.mem_filter.1 hv with ⟨hRN, hB⟩
    have : isA1 v ∨ isB1 v := (inBlock1_iff v).1 hB
    cases this with
    | inl hA1 => exact Finset.mem_union.2 (Or.inl (Finset.mem_filter.2 ⟨hRN, hA1⟩))
    | inr hB1 => exact Finset.mem_union.2 (Or.inr (Finset.mem_filter.2 ⟨hRN, hB1⟩))
  · intro hv
    rcases Finset.mem_union.1 hv with hA1 | hB1
    · rcases Finset.mem_filter.1 hA1 with ⟨hRN, hA1⟩
      exact Finset.mem_filter.2 ⟨hRN, (inBlock1_iff v).2 (Or.inl hA1)⟩
    · rcases Finset.mem_filter.1 hB1 with ⟨hRN, hB1⟩
      exact Finset.mem_filter.2 ⟨hRN, (inBlock1_iff v).2 (Or.inr hB1)⟩

/-- {name}`redBlock2` — это в точности непересекающееся объединение его частей {name}`A2` и {name}`B2`. -/
lemma redBlock2_eq_union (color : Sym2 V → Fin 2) : 
  redBlock2 color =
    redBlock2A2 color ∪ redBlock2B2 color := by
  ext v; constructor
  · intro hv
    rcases Finset.mem_filter.1 hv with ⟨hRN, hB⟩
    have : isA2 v ∨ isB2 v := by
      apply (inBlock2_iff v).1
      cases v <;> simp_all [inBlock1, inBlock2, redNeighbors]

    cases this with
    | inl hA2 => exact Finset.mem_union.2 (Or.inl (Finset.mem_filter.2 ⟨hRN, hA2⟩))
    | inr hB2 => exact Finset.mem_union.2 (Or.inr (Finset.mem_filter.2 ⟨hRN, hB2⟩))
  · intro hv
    rcases Finset.mem_union.1 hv with hA2 | hB2
    · rcases Finset.mem_filter.1 hA2 with ⟨hRN, hA2⟩
      exact Finset.mem_filter.2 ⟨hRN, by
        cases v <;> simp_all [inBlock1, isA2]
        ⟩
    · rcases Finset.mem_filter.1 hB2 with ⟨hRN, hB2⟩
      exact Finset.mem_filter.2 ⟨hRN, by
        cases v <;> simp_all [inBlock1, isB2]⟩

/-- Две части {name}`redBlock1` не пересекаются. -/
lemma redA1_redB1_disjoint (color : Sym2 V → Fin 2) : 
  Disjoint (redBlock1A1 color) (redBlock1B1 color) := by
  classical
  refine Finset.disjoint_left.2 ?_
  intro v hvA hvB
  rcases Finset.mem_filter.1 hvA with ⟨_, hA1⟩
  rcases Finset.mem_filter.1 hvB with ⟨_, hB1⟩
  exact (not_isA1_and_isB1 v) ⟨hA1, hB1⟩

/-- Две части {name}`redBlock2` не пересекаются. -/
lemma redA2_redB2_disjoint (color : Sym2 V → Fin 2) : 
  Disjoint (redBlock2A2 color) (redBlock2B2 color) := by
  classical
  refine Finset.disjoint_left.2 ?_
  intro v hvA hvB
  rcases Finset.mem_filter.1 hvA with ⟨_, hA2⟩
  rcases Finset.mem_filter.1 hvB with ⟨_, hB2⟩
  exact (not_isA2_and_isB2 v) ⟨hA2, hB2⟩

/-- Разложения мощностей блоков. -/
lemma redBlock1_card_eq_sum (color : Sym2 V → Fin 2) : 
  (redBlock1 color).card
    = (redBlock1A1 color).card + (redBlock1B1 color).card := by
  classical
  have := Finset.card_union_add_card_inter
            (s := redBlock1A1 color) (t := redBlock1B1 color)
  -- переписываем объединение как `redBlock1` и показываем, что пересечение пусто
  have hU : redBlock1A1 color ∪ redBlock1B1 color = redBlock1 color := by
    rw [redBlock1_eq_union]
  have hI : (redBlock1A1 color ∩ redBlock1B1 color).card = 0 := by
    have hdis := redA1_redB1_disjoint color
    -- `disjoint` означает, что пересечение пусто
    have : redBlock1A1 color ∩ redBlock1B1 color = (∅ : Finset V) := by
      simp [Disjoint] at hdis
      aesop
    aesop
  -- собираем всё вместе
  have := by simpa [hU, hI, add_comm] using this
  exact this

lemma redBlock2_card_eq_sum (color : Sym2 V → Fin 2) : 
  (redBlock2 color).card
    = (redBlock2A2 color).card + (redBlock2B2 color).card := by
  classical
  have := Finset.card_union_add_card_inter
            (s := redBlock2A2 color) (t := redBlock2B2 color)
  have hU : redBlock2A2 color ∪ redBlock2B2 color = redBlock2 color := by
    rw [redBlock2_eq_union]
  have hdis := redA2_redB2_disjoint color
  have hI : (redBlock2A2 color ∩ redBlock2B2 color).card = 0 := by
    have : redBlock2A2 color ∩ redBlock2B2 color = (∅ : Finset V) := by
      simp [Disjoint] at hdis
      aesop
    simp [this]
  have := by simpa [hU, hI, add_comm] using this
  exact this

/-! # Оценка частей {lit}`B` сверху числом {lean}`5` -/

/-- Все вершины {name}`B1` как finset (образ {lean}`Fin 5`). -/
def B1Set : Finset V := (Finset.univ.image fun j : Fin 5 => B1 j)

/-- Все вершины {name}`B2` как finset (образ {lean}`Fin 5`). -/
def B2Set : Finset V := (Finset.univ.image fun j : Fin 5 => B2 j)

lemma redBlock1B1_subset_B1Set (color : Sym2 V → Fin 2) : 
  redBlock1B1 color ⊆ B1Set := by
  classical
  intro v hv
  rcases Finset.mem_filter.1 hv with ⟨_, hB1⟩
  -- Из `isB1 v` следует `v = B1 j` для некоторого `j`, значит, `v` входит в образ.
  cases v with
  | B1 j =>
      simp [B1Set]    -- `v` в точности равно `B1 j`, значит, входит в образ `j`.
  | A1 _ => cases hB1
  | A2 _ => cases hB1
  | B2 _ => cases hB1
  | apex => cases hB1

lemma redBlock2B2_subset_B2Set (color : Sym2 V → Fin 2) : 
  redBlock2B2 color ⊆ B2Set := by
  classical
  intro v hv
  rcases Finset.mem_filter.1 hv with ⟨_, hB2⟩
  cases v with
  | B2 j =>
      simp [B2Set]
  | A1 _ => cases hB2
  | B1 _ => cases hB2
  | A2 _ => cases hB2
  | apex => cases hB2

lemma card_B1Set_le_5 : (B1Set).card ≤ 5 := by
  classical
  -- мощность образа ≤ мощности области определения
  simpa [B1Set, Fintype.card_fin] using
    (Finset.card_image_le : (Finset.univ.image (fun j : Fin 5 => B1 j)).card ≤ (Finset.univ : Finset (Fin 5)).card)

lemma card_B2Set_le_5 : (B2Set).card ≤ 5 := by
  classical
  simpa [B2Set, Fintype.card_fin] using
    (Finset.card_image_le : (Finset.univ.image (fun j : Fin 5 => B2 j)).card ≤ (Finset.univ : Finset (Fin 5)).card)

lemma redBlock1B1_card_le_5 (color : Sym2 V → Fin 2) : 
  (redBlock1B1 color).card ≤ 5 :=
  (Finset.card_le_card (redBlock1B1_subset_B1Set color)).trans card_B1Set_le_5

lemma redBlock2B2_card_le_5 (color : Sym2 V → Fin 2) : 
  (redBlock2B2 color).card ≤ 5 :=
  (Finset.card_le_card (redBlock2B2_subset_B2Set color)).trans card_B2Set_le_5

/-! # Существование красного соседа в частях клики {name}`A1` / {name}`A2` -/

/-- Если блок 1 получает от {name}`apex` не менее 6 красных соседей, то один из них лежит в {name}`A1`. -/
lemma exists_red_A1_of_block1_ge6
    (color : Sym2 V → Fin 2)
    (h6 : 6 ≤ (redBlock1 color).card) : 
    ∃ i : Fin 2, G.Adj apex (A1 i) ∧ color (s(apex, A1 i)) = 1 := by
  classical
  -- Из разложения `|redBlock1| = |A1-part| + |B1-part|`
  -- и `|B1-part| ≤ 5` получаем `|A1-part| ≥ 1`.
  have hdecomp := redBlock1_card_eq_sum color
  have hB1le := redBlock1B1_card_le_5 color
  have hposA1 : 0 < (redBlock1A1 color).card := by
    -- Если бы `A1-part` была пуста, то `|redBlock1| = |B1-part| ≤ 5`, что противоречит `≥ 6`.
    by_contra hzero
    have hz : (redBlock1A1 color).card = 0 := Nat.eq_zero_of_not_pos hzero
    have : (redBlock1 color).card = (redBlock1B1 color).card := by
      simp [hdecomp, hz, zero_add]
    have : (redBlock1 color).card ≤ 5 := by simpa [this] using hB1le
    grind
  -- Выбираем вершину `v` в части `A1`.
  rcases Finset.card_pos.1 hposA1 with ⟨v, hv⟩
  -- Из принадлежности извлекаем смежность и красноту.
  rcases Finset.mem_filter.1 hv with ⟨hRN, hA1⟩
  rcases Finset.mem_filter.1 hRN with ⟨hNei, hRed⟩
  -- Теперь `v` обязана иметь вид `A1 i`.
  cases v with
  | A1 i =>
      exact ⟨i, by aesop, by simpa using hRed⟩
  | B1 _ => cases hA1
  | A2 _ => cases hA1
  | B2 _ => cases hA1
  | apex  => cases hA1

/-- Если блок 2 получает от {name}`apex` не менее 6 красных соседей, то один из них лежит в {name}`A2`. -/
lemma exists_red_A2_of_block2_ge6
    (color : Sym2 V → Fin 2)
    (h6 : 6 ≤ (redBlock2 color).card) : 
    ∃ i : Fin 3, G.Adj apex (A2 i) ∧ color (s(apex, A2 i)) = 1 := by
  classical
  have hdecomp := redBlock2_card_eq_sum color
  have hB2le := redBlock2B2_card_le_5 color
  have hposA2 : 0 < (redBlock2A2 color).card := by
    by_contra hzero
    have hz : (redBlock2A2 color).card = 0 := Nat.eq_zero_of_not_pos hzero
    have : (redBlock2 color).card = (redBlock2B2 color).card := by
      simp [hdecomp, hz, zero_add]
    have : (redBlock2 color).card ≤ 5 := by simpa [this] using hB2le
    grind
  rcases Finset.card_pos.1 hposA2 with ⟨v, hv⟩
  rcases Finset.mem_filter.1 hv with ⟨hRN, hA2⟩
  rcases Finset.mem_filter.1 hRN with ⟨hNei, hRed⟩
  cases v with
  | A2 i =>
      exact ⟨i, by aesop, by simpa using hRed⟩
  | A1 _ => cases hA2
  | B1 _ => cases hA2
  | B2 _ => cases hA2
  | apex  => cases hA2

/-- Следствие: при гипотезе «нет синей звезды» найдётся красный сосед {name}`apex`
в соответствующей клике {name}`A1` или {name}`A2`. -/
lemma exists_red_clique_neighbor
    (color : Sym2 V → Fin 2)
    (hNoBlueStar : ¬ hasMonoStar G color 0 5) : 
    (∃ i : Fin 2, G.Adj apex (A1 i) ∧ color (s(apex, A1 i)) = 1) ∨
    (∃ i : Fin 3, G.Adj apex (A2 i) ∧ color (s(apex, A2 i)) = 1) := by
  classical
  -- Ранее доказанная лемма:
  have h := exists_block_receives_at_least_6_red color hNoBlueStar
  rcases h with h1 | h2
  · exact Or.inl (exists_red_A1_of_block1_ge6 color h1)
  · exact Or.inr (exists_red_A2_of_block2_ge6 color h2)

end PikhurkoN5


-- 7. Треугольник или звезда от вершины клики

namespace PikhurkoN5
open V

/-! # Вспомогательные утверждения: выбранная вершина клики лежит в соответствующем красном блоке -/

lemma A1_mem_redBlock1_of_red
    (color : Sym2 V → Fin 2) (i : Fin 2)
    (_hAdj : G.Adj apex (A1 i))
    (hRed : color (s(apex, A1 i)) = 1) : 
    A1 i ∈ redBlock1 color := by
  classical
  -- Во-первых: `A1 i` — красный сосед `apex`.
  have hRN : A1 i ∈ redNeighbors color := by
    -- принадлежность `neighborFinset` + color=1
    have : A1 i ∈ G.neighborFinset apex := by simp
    exact Finset.mem_filter.mpr ⟨this, by simpa⟩
  -- Во-вторых: она лежит в блоке 1.
  have hB : inBlock1 (A1 i) := by simp [inBlock1]
  -- Ещё раз фильтруем.
  simpa [redBlock1] using Finset.mem_filter.mpr ⟨hRN, hB⟩

lemma A2_mem_redBlock2_of_red
    (color : Sym2 V → Fin 2) (i : Fin 3)
    (_hAdj : G.Adj apex (A2 i))
    (hRed : color (s(apex, A2 i)) = 1) : 
    A2 i ∈ redBlock2 color := by
  classical
  have hRN : A2 i ∈ redNeighbors color := by
    have : A2 i ∈ G.neighborFinset apex := by simp
    exact Finset.mem_filter.mpr ⟨this, by simpa⟩
  have hB : inBlock2 (A2 i) := by simp [inBlock2]
  simp [redBlock2, hRN, isA1, isB1]

/-! # Треугольник или звезда из блока 1 -/

/-- Если у блока 1 не менее 6 красных соседей apex, и один из них {lean}`A1 i` с красным ребром
от {name}`apex`, то либо у нас есть красный треугольник, либо синяя `K_{1,5}` с центром в {lean}`A1 i`. -/
lemma triangle_or_blueStar_from_block1
    (color : Sym2 V → Fin 2)
    (h6 : 6 ≤ (redBlock1 color).card)
    (i : Fin 2)
    (hAdj : G.Adj apex (A1 i))
    (hRedApexA1 : color (s(apex, A1 i)) = 1) : 
    hasMonoTriangle G color 1 ∨ hasMonoStar G color 0 5 := by
  classical
  -- Помещаем `y0 := A1 i` в `redBlock1`.
  have hy0_in : A1 i ∈ redBlock1 color := A1_mem_redBlock1_of_red color i hAdj hRedApexA1
  -- Нам нужно 5 вершин в `redBlock1 \ {A1 i}`.
  have h5 : 
    5 ≤ ((redBlock1 color).erase (A1 i)).card := by
    -- `card (erase y0) + 1 = card`  ⇒  `card (erase y0) ≥ 5` из `card ≥ 6`
    have hcard : 
        ((redBlock1 color).erase (A1 i)).card + 1 = (redBlock1 color).card :=
      Finset.card_erase_add_one hy0_in
    -- преобразуем `6 ≤ RHS` в `5 ≤ LHS`
    have : 6 ≤ ((redBlock1 color).erase (A1 i)).card + 1 := by simpa [hcard] using h6
    exact (Nat.succ_le_succ_iff.mp this)
  -- Берём любое 5-элементное подмножество `T` среди них.
  obtain ⟨T, hTsub, hTcard⟩ :=
    Finset.exists_subset_card_eq ((redBlock1 color).erase (A1 i)) h5

  -- Либо какой-то `y ∈ T` делает ребро `(A1 i,y)` красным (→ треугольник), либо все синие (→ звезда).
  classical
  by_cases hTri : ∃ y ∈ T, color (s(A1 i, y)) = 1
  · rcases hTri with ⟨y, hyT, hyRedA1y⟩
    -- Факты из принадлежности: `y ≠ A1 i`, `y ∈ redBlock1`.
    have hy_erase : y ∈ (redBlock1 color).erase (A1 i) := hTsub hyT
    have hy_ne : y ≠ A1 i := (Finset.mem_erase.mp hy_erase).1
    have hy_in : y ∈ redBlock1 color := (Finset.mem_erase.mp hy_erase).2
    -- Раскрываем принадлежность `redBlock1`, чтобы получить, что `y` — красный сосед `apex` в блоке 1.
    rcases Finset.mem_filter.1 hy_in with ⟨hy_RN, hy_block1⟩
    rcases Finset.mem_filter.1 hy_RN with ⟨hyAdjApex, hyRedApexY⟩
    -- `A1 i` смежна со всеми остальными вершинами блока 1 (клика-к-A1, клика-к-B1).
    have hyAdjA1Y : G.Adj (A1 i) y := by
      cases y with
      | A1 j =>
          -- `j ≠ i`, потому что `y ≠ A1 i`
          have hij : j ≠ i := by
            intro h; exact hy_ne (by simp [h])
          -- используем `adj_A1A1 : Adj (A1 i) (A1 j) ↔ i ≠ j`
          have : i ≠ j := by simpa [ne_comm] using hij
          simp [adj_A1A1, this]
      | B1 _  => simp [adj_A1B1]
      | A2 _  => cases hy_block1       -- невозможно
      | B2 _  => cases hy_block1       -- невозможно
      | apex  => cases hy_block1       -- невозможно
    -- Строим красный треугольник: apex — A1 i — y — apex.
    refine Or.inl ?triangle
    refine ⟨apex, A1 i, y, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hAdj]
    · exact hyAdjA1Y
    · simpa using hyAdjApex
    · simpa using hRedApexA1
    · exact hyRedA1y
    · simpa using hyRedApexY
  · -- Нет красного `(A1 i,y)` с `y ∈ T` ⇒ все `(A1 i,y)` синие.
    have hAllBlue : ∀ {y}, y ∈ T → color (s(A1 i, y)) = 0 := by
      intro y hy
      have h1 : color (s(A1 i, y)) ≠ 1 := by
        intro contra; exact hTri ⟨y, hy, contra⟩
      -- В `Fin 2` «не равно `1`» означает «равно `0`».
      -- (При желании можно переиспользовать ранее доказанную лемму `fin2_eq_one_iff_ne_zero`.)
      have : color (s(A1 i, y)) = 0 ∨ color (s(A1 i, y)) = 1 := by
        grind
      exact this.resolve_right h1
    -- Показываем `A1 i ∉ T`.
    have hnotin : A1 i ∉ T := by
      intro hx
      have : A1 i ∈ (redBlock1 color).erase (A1 i) := hTsub hx
      simp at this
    -- Смежность `(A1 i,y)` для `y ∈ T`:
    have hAdjAll : ∀ {y}, y ∈ T → G.Adj (A1 i) y := by
      intro y hy
      have hy_erase : y ∈ (redBlock1 color).erase (A1 i) := hTsub hy
      have hy_ne : y ≠ A1 i := (Finset.mem_erase.mp hy_erase).1
      have hy_in : y ∈ redBlock1 color := (Finset.mem_erase.mp hy_erase).2
      rcases Finset.mem_filter.1 hy_in with ⟨_, hy_block1⟩
      -- тот же разбор случаев, что и выше
      cases y with
      | A1 j =>
          have hij : j ≠ i := by intro h; exact hy_ne (by simp [h])
          have : i ≠ j := by simpa [ne_comm] using hij
          simp [adj_A1A1, this]
      | B1 _  => simp [adj_A1B1]
      | A2 _  => simp [isA1, isB1] at hy_block1
      | B2 _  => simp [isA1, isB1] at hy_block1
      | apex  => simp [G, GAdj]
    -- У нас есть синяя звезда размера 5 с центром в `A1 i` и множеством листьев `T`.
    refine Or.inr ?star
    refine ⟨A1 i, T, by simp [hTcard], hnotin, ?_⟩
    intro y hy
    exact ⟨hAdjAll hy, hAllBlue hy⟩

/-! # Треугольник или звезда из блока 2 (тот же шаблон доказательства) -/

lemma triangle_or_blueStar_from_block2
    (color : Sym2 V → Fin 2)
    (h6 : 6 ≤ (redBlock2 color).card)
    (i : Fin 3)
    (hAdj : G.Adj apex (A2 i))
    (hRedApexA2 : color (s(apex, A2 i)) = 1) : 
    hasMonoTriangle G color 1 ∨ hasMonoStar G color 0 5 := by
  classical
  have hy0_in : A2 i ∈ redBlock2 color := A2_mem_redBlock2_of_red color i hAdj hRedApexA2
  have h5 : 
    5 ≤ ((redBlock2 color).erase (A2 i)).card := by
    have hcard : 
        ((redBlock2 color).erase (A2 i)).card + 1 = (redBlock2 color).card :=
      Finset.card_erase_add_one hy0_in
    have : 6 ≤ ((redBlock2 color).erase (A2 i)).card + 1 := by simpa [hcard] using h6
    exact (Nat.succ_le_succ_iff.mp this)
  obtain ⟨T, hTsub, hTcard⟩ :=
    Finset.exists_subset_card_eq ((redBlock2 color).erase (A2 i)) h5

  by_cases hTri : ∃ y ∈ T, color (s(A2 i, y)) = 1
  · rcases hTri with ⟨y, hyT, hyRedA2y⟩
    have hy_erase : y ∈ (redBlock2 color).erase (A2 i) := hTsub hyT
    have hy_ne : y ≠ A2 i := (Finset.mem_erase.mp hy_erase).1
    have hy_in : y ∈ redBlock2 color := (Finset.mem_erase.mp hy_erase).2
    rcases Finset.mem_filter.1 hy_in with ⟨hy_RN, hy_block2⟩
    rcases Finset.mem_filter.1 hy_RN with ⟨hyAdjApex, hyRedApexY⟩
    have hyAdjA2Y : G.Adj (A2 i) y := by
      cases y with
      | A2 j =>
          have hij : j ≠ i := by intro h; exact hy_ne (by simp [h])
          have : i ≠ j := by simpa [ne_comm] using hij
          simp [adj_A2A2, this]
      | B2 _  => simp [adj_A2B2]
      | A1 _  => simp [isA1] at hy_block2
      | B1 _  => simp [isB1] at hy_block2
      | apex  => simp [G,GAdj]
    refine Or.inl ?triangle
    refine ⟨apex, A2 i, y, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hAdj]
    · exact hyAdjA2Y
    · aesop
    · simpa using hRedApexA2
    · exact hyRedA2y
    · simpa using hyRedApexY
  ·
    have hAllBlue : ∀ {y}, y ∈ T → color (s(A2 i, y)) = 0 := by
      intro y hy
      have h1 : color (s(A2 i, y)) ≠ 1 := by
        intro contra; exact hTri ⟨y, hy, contra⟩
      have : color (s(A2 i, y)) = 0 ∨ color (s(A2 i, y)) = 1 := by grind
      exact this.resolve_right h1
    have hnotin : A2 i ∉ T := by
      intro hx
      have : A2 i ∈ (redBlock2 color).erase (A2 i) := hTsub hx
      simp at this
    have hAdjAll : ∀ {y}, y ∈ T → G.Adj (A2 i) y := by
      intro y hy
      have hy_erase : y ∈ (redBlock2 color).erase (A2 i) := hTsub hy
      have hy_ne : y ≠ A2 i := (Finset.mem_erase.mp hy_erase).1
      have hy_in : y ∈ redBlock2 color := (Finset.mem_erase.mp hy_erase).2
      rcases Finset.mem_filter.1 hy_in with ⟨_, hy_block2⟩
      cases y with
      | A2 j =>
          have hij : j ≠ i := by intro h; exact hy_ne (by simp [h])
          have : i ≠ j := by simpa [ne_comm] using hij
          simp [adj_A2A2, this]
      | B2 _  => simp [adj_A2B2]
      | A1 _  => simp [isA1] at hy_block2
      | B1 _  => simp [isB1] at hy_block2
      | apex  => simp [G, GAdj]
    refine Or.inr ?star
    refine ⟨A2 i, T, by simp [hTcard], hnotin, ?_⟩
    intro y hy
    exact ⟨hAdjAll hy, hAllBlue hy⟩

/-! # Финальный шаг: нет синей `K_{1,5}` ⇒ есть красный треугольник -/

/-- **Основной шаг (n=5):** Если нет синей `K_{1,5}`, то красный цветовой класс содержит треугольник. -/
theorem red_triangle_of_no_blue_star
    (color : Sym2 V → Fin 2)
    (hNoBlueStar : ¬ hasMonoStar G color 0 5) : 
    hasMonoTriangle G color 1 := by
  classical
  -- Один из двух блоков имеет ≥6 красных соседей от `apex`.
  have h6 := exists_block_receives_at_least_6_red color hNoBlueStar
  -- Из этого блока извлекаем вершину клики с красным ребром от `apex`.
  rcases h6 with hB1 | hB2
  · -- Случай блока 1
    rcases exists_red_A1_of_block1_ge6 color hB1 with ⟨i, hAdj, hRed⟩
    -- Либо получаем треугольник, либо (если звезда) противоречие с `hNoBlueStar`.
    rcases triangle_or_blueStar_from_block1 color hB1 i hAdj hRed with hTri | hStar
    · exact hTri
    · exact (hNoBlueStar hStar).elim
  · -- Случай блока 2
    rcases exists_red_A2_of_block2_ge6 color hB2 with ⟨i, hAdj, hRed⟩
    rcases triangle_or_blueStar_from_block2 color hB2 i hAdj hRed with hTri | hStar
    · exact hTri
    · exact (hNoBlueStar hStar).elim

end PikhurkoN5

-- Финальное утверждение

namespace PikhurkoN5

theorem main : Pikhurko_n5_statement := by
  use V, G
  split_ands
  . exact edge_count_44
  intro color
  have := red_triangle_of_no_blue_star color
  grind
