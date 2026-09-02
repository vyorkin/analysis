import Mathlib.Tactic
import Mathlib.SetTheory.ZFC.PSet
import Mathlib.SetTheory.ZFC.Basic
import Analysis.Tools.ExistsUnique
import Analysis.Section_3_1

set_option doc.verso.suggestions false

/-!
# Analysis I, эпилог главы 3: связь с ZFSet

В этом эпилоге мы показываем, что тип {name}`ZFSet` из Mathlib
(полученный как факторизация типа {name}`PSet`)
можно использовать для построения моделей класса `SetTheory`, изучаемого в этой главе,
при условии, что мы работаем во вселенной уровня не ниже 1.
Приведённые здесь конструкции принадлежат Эдварду ван де Менту (Edward van de Meent);
см. https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/Can.20this.20proof.20related.20to.20Set.20replacement.20be.20shorter.3F/near/527305173

## Ориентир: `PSet` против `ZFSet`

`PSet` («пре-множество») определён индуктивно: `⟨α, A⟩`, где `α : Type u` — произвольный
индексирующий тип, а `A : α → PSet` сопоставляет каждому индексу элемент. Например,
`{1, 2}` можно закодировать индексирующим типом `Fin 2` и функцией `A 0 = 1`, `A 1 = 2`.

Проблема в том, что один и тот же математический набор можно закодировать разными `PSet`
(скажем, `{1, 1, 2}` через `Fin 3` — с повторением индекса — и `{1, 2}` через `Fin 2`).
Чтобы отождествить такие "разные коды одного и того же множества", на `PSet` вводится
отношение экстенсиональной эквивалентности `Equiv` (рекурсивное: два `PSet` эквивалентны,
если у каждого элемента одного находится эквивалентный элемент другого, и наоборот).

`ZFSet` — это фактор-тип `PSet` по `Equiv`. Именно `ZFSet`, а не `PSet`, ведёт себя как
"настоящее" множество (два его элемента с одинаковым содержимым — это буквально один и тот же
элемент типа, а не просто эквивалентные). Ниже мы часто переходим между `PSet` (где легко
считать индукцией/рекурсией) и `ZFSet` (где формулируются сами аксиомы) через конструктор
`ZFSet.mk : PSet → ZFSet` (фактически `Quotient.mk`).
-/

universe u

/-- Предварительная лемма о `PSet`: их натуральные числа упорядочены по отношению принадлежности. -/
lemma PSet.ofNat_mem_ofNat_of_lt (m n : ℕ) : n < m → ofNat n ∈ ofNat m := by
  intro h
  -- `n < m` в Lean по определению — это `n.succ ≤ m`, поэтому индукция по `h` идёт по
  -- построению `Nat.le`: случай `refl` — это `m = n + 1`, случай `step` — переход от `m` к `m + 1`.
  --
  -- Напомним, `ofNat : ℕ → PSet` кодирует натуральные числа фон-неймановскими ординалами:
  -- `ofNat 0 = ∅`, `ofNat (n+1) = insert (ofNat n) (ofNat n)` — то есть `n ∪ {n}`.
  induction h with
  | refl =>
    -- Цель: `ofNat n ∈ ofNat (n + 1)`. Разворачиваем `ofNat (n + 1)` до `insert (ofNat n) (ofNat n)`
    -- — а `ofNat n`, разумеется, лежит в множестве, куда его же и вставили.
    rw [ofNat]
    apply mem_insert
  | step _ ih =>
    -- ih : `ofNat n ∈ ofNat m✝`. Хотим `ofNat n ∈ ofNat (m✝ + 1) = insert (ofNat m✝) (ofNat m✝)`.
    -- Раз `ofNat n` уже лежал в `ofNat m✝`, он лежит и после добавления в него ещё одного элемента.
    rw [ofNat]
    exact mem_insert_of_mem _ ih

-- Отношение принадлежности между `PSet`-натуральными числами `ofNat n` и `ofNat m`
-- в точности соответствует порядку: `ofNat n ∈ ofNat m ↔ n < m`.
lemma PSet.mem_ofNat_iff (n m : ℕ) : ofNat n ∈ ofNat m ↔ n < m := by
  refine ⟨?_, ofNat_mem_ofNat_of_lt m n⟩
  -- Прямую импликацию докажем контрапозицией: из `¬ (n < m)`, то есть `m ≤ n`,
  -- выведем `ofNat n ∉ ofNat m`.
  contrapose!
  rw [le_iff_lt_or_eq]
  rintro (h | rfl)
  · -- Случай `m < n`: тогда (по уже доказанной лемме выше) `ofNat m ∈ ofNat n`,
    -- а `mem_asymm` запрещает принадлежность сразу в обе стороны.
    exact mem_asymm (ofNat_mem_ofNat_of_lt _ _ h)
  · -- Случай `m = n`: `ofNat m ∉ ofNat m` — множество не может содержать само себя.
    apply mem_irrefl

/-- Ещё одна предварительная лемма: натуральные числа в {name}`PSet` могут быть эквивалентны
только тогда, когда они равны. -/
lemma PSet.eq_of_ofNat_equiv_ofNat (n m : ℕ) : (ofNat.{u} n).Equiv (ofNat.{u} m) → n = m := by
  -- `wlog` позволяет доказывать лемму только для случая `m ≤ n`: если на самом деле `n < m`,
  -- мы применим этот же (уже доказанный для `m ≤ n`) результат к переставленным `n` и `m`.
  wlog hmn : m ≤ n generalizing n m
  · -- Здесь `hmn : ¬ m ≤ n`, то есть `n < m`. Имя `this` — это сама лемма, но уже
    -- ограниченная условием `m ≤ n` (тем самым случаем, который мы сейчас и доказываем).
    intro heq
    have hnm : n ≤ m := by omega
    exact (this m n hnm heq.symm).symm
  intro h
  -- `Equiv.eq` переводит `PSet`-эквивалентность в равенство множеств образов (`toSet`),
  -- а `Set.ext_iff` разворачивает это равенство в поэлементное условие:
  -- "x лежит в одном образе тогда и только тогда, когда лежит в другом".
  rw [Equiv.eq, Set.ext_iff] at h
  -- Подставим x := ofNat m. Слева получаем `ofNat m ∈ ofNat n`, справа — `ofNat m ∈ ofNat m`,
  -- а последнее всегда ложно (`mem_irrefl`). Значит `ofNat m ∉ ofNat n`,
  -- а по `mem_ofNat_iff` это равносильно `n ≤ m`.
  have hnm : n ≤ m := by
    specialize h (ofNat m)
    simpa [mem_irrefl, mem_ofNat_iff] using h
  -- Вместе с `hmn : m ≤ n` это даёт `n = m` по антисимметричности `≤`.
  omega

open PSet in
/-- Используя приведённые выше леммы, мы можем построить биекцию между {name}`ZFSet.omega`
и натуральными числами. -/
noncomputable def ZFSet.nat_equiv : ℕ ≃ omega.{u} :=
  -- Кандидат в биекцию: `n ↦ mk (ofNat n)` — n-е натуральное число, "поднятое" из `PSet`-кодировки
  -- в `ZFSet`. Второй компонент пары — доказательство, что `mk (ofNat n)` действительно лежит
  -- в `omega`: `Mem.mk` даёт членство на уровне `PSet`, а `mk_mem_iff` переносит его в `ZFSet`.
  Equiv.ofBijective (fun n => ⟨mk (ofNat.{u} n), mk_mem_iff.mpr (Mem.mk _ (ULift.up n))⟩) (by
    constructor
    · -- Инъективность: если `mk (ofNat n₁) = mk (ofNat n₂)` (как элементы подтипа `omega`),
      -- то по `eq` (`mk x = mk y ↔ Equiv x y`) `ofNat n₁` и `ofNat n₂` эквивалентны как `PSet`,
      -- а значит по лемме выше `n₁ = n₂`.
      intro n₁ n₂
      simp [eq]
      apply eq_of_ofNat_equiv_ofNat
    · -- Сюръективность: берём произвольный элемент `omega` — пару из `x : ZFSet` и
      -- доказательства `hx : x ∈ omega` — и подбираем для него натуральное число-прообраз.
      intro ⟨x, hx⟩
      -- `mk_out x : mk (Quotient.out x) = x`, поэтому заменяем `x` на `mk (Quotient.out x)`
      -- (`← mk_out x`) и разворачиваем определение `omega := mk PSet.omega`.
      rw [← mk_out x, omega] at hx
      -- Используем `erw`, а не `rw`: `mk_mem_iff` не сходится с `hx` по чистому синтаксису —
      -- мешает частичное разворачивание через `Quotient.out`, а `erw` пробивает такие defeq-барьеры.
      erw [mk_mem_iff] at hx
      -- `hx : Quotient.out x ∈ PSet.omega` по определению принадлежности `PSet` разворачивается
      -- в `∃ n : ULift ℕ, Equiv (Quotient.out x) (PSet.omega.Func n)`.
      obtain ⟨n, hn⟩ := hx
      -- `mk_func`/`PSet.omega` сводят `PSet.omega.Func n` к явному `ofNat n.down`.
      simp [mk_func, PSet.omega] at hn ⊢
      use n.down
      rw [← mk_out x, eq]
      exact hn.symm)

open Classical in
/-- Показывает, что {name}`ZFSet` подчиняется аксиомам {name}`Chapter3.SetTheory`. Большинство
этих аксиом по сути уже были установлены в Mathlib, и их перенос — дело сравнительно рутинное;
эквивалентность `ZF.omega` и {name}`Nat` по содержанию оказывается самой хитрой (аксиома
степенного множества тоже требует некоторых технических манипуляций). -/
noncomputable instance ZFSet.inst_SetTheory : Chapter3.SetTheory.{u + 1,u + 1} where
  -- В этой модели `Object` и `Set` совпадают: каждый объект — это множество, атомов нет.
  Set := ZFSet
  Object := ZFSet
  -- Раз `Set = Object`, вложение множеств в объекты — это просто тождественная функция
  -- (инъективность тривиальна: `h : a₁ = a₂` уже и есть нужное доказательство).
  set_to_object := { toFun a₁ := a₁, inj' _ _ h := h}
  -- Переиспользуем готовое отношение принадлежности `ZFSet`.
  mem o s := o ∈ s
  -- Экстенсиональность у `ZFSet` уже доказана в Mathlib как `ZFSet.ext`.
  extensionality _ _ := ext
  emptyset := ∅
  emptyset_mem := notMem_empty
  singleton x := {x}
  singleton_axiom _ _ := mem_singleton
  union_pair x y := x ∪ y
  union_pair_axiom _ _ _ := mem_union
  -- `specify A P` берёт подмножество `A`, "просеянное" по предикату `P`.
  -- `ZFSet.sep pred A` в Mathlib требует тотального предиката `pred : ZFSet → Prop`,
  -- а наш `P` определён только на подтипе `{x // x ∈ A}` — поэтому оборачиваем его
  -- в `fun s ↦ (h : s ∈ A) → P ⟨s,h⟩`: вне `A` условие пусто (истинно на пустом основании),
  -- но это неважно, ведь `sep` и так оставит только элементы `A`.
  specify A P := ZFSet.sep (fun s ↦ (h : s ∈ A) → P ⟨s,h⟩) A
  -- Аксиома выделения полностью сводится к уже известным Mathlib-фактам про `mem_sep`;
  -- `+contextual` позволяет `simp` использовать во время упрощения гипотезы,
  -- которые он сам только что ввёл в контекст (здесь — `s ∈ A`).
  specification_axiom := by simp +contextual
  -- `replace A P hp` — множество образов `P` на `A`. Строим его в два шага:
  -- 1) сузим `A` до "домена определённости" `P` — тех `s ∈ A`, для которых хоть какой-то
  --    образ `z` действительно существует (P не обязана быть определена на всём `A` —
  --    условие `hp` требует только однозначности там, где она определена);
  -- 2) отобразим этот домен через `image`, беря для каждого элемента (классическим выбором,
  --    отсюда `open Classical`) тот самый единственный образ. Вне домена подставляем ∅ —
  --    "мусорное" значение, до которого дело не доходит.
  -- `allZFSetDefinable` и явные `@`/instance-аргументы нужны потому, что построенная функция
  -- использует `Classical.choice` и не может быть найдена автоматическим поиском инстансов —
  -- инстанс `Definable₁` приходится предъявлять вручную.
  replace A P hp := @(A.sep (fun s ↦ (hs : s ∈ A) → ∃ z, P ⟨s,hs⟩ z)).image (fun s ↦
    if h : ∃ (hs : s ∈ A), ∃ z, P ⟨s,hs⟩ z then h.choose_spec.choose else ∅) (allZFSetDefinable _)
  replacement_axiom A P hp s := by
    -- Цель: `s ∈ replace A P hp ↔ ∃ x, P x s`. Разворачиваем `replace` (через `mem_image`
    -- и `mem_sep`), чтобы увидеть это утверждение уже в терминах `ZFSet`.
    simp
    constructor
    · -- (→) Если `s` — образ какого-то `z` из "домена" (`z ∈ A`, и у `z` есть P-образ),
      -- нужно предъявить `x := ⟨z, hzA⟩` с `P x s`.
      intro ⟨z, ⟨hzA, hz⟩, hz'⟩
      use z, hzA
      -- Условие `∃ …` внутри `if` истинно (его подтверждают `hzA` и `hz hzA`),
      -- поэтому `dite` сводится к своей "then"-ветке: `hz'` превращается в
      -- "choice-образ z (для z ∈ A) равен s".
      simp [hzA, hz hzA] at hz'
      -- Осталось показать `P ⟨z,hzA⟩ s`. Подставляем `s = choice-образ` (`← hz'`)
      -- и применяем `Exists.choose_spec` — свойство самого выбора: он всегда удовлетворяет
      -- тому предикату, из существования которого был построен.
      simp [←hz', Exists.choose_spec]
    · -- (←) Если `∃ x, P x s`, то `s` — образ `x.val`, а `x.val` лежит в "домене" сепарации.
      intro ⟨z, hzA, hz'⟩
      -- `z` действительно попадает в домен: он лежит в `A`, и P-образ у него есть — сам `s`.
      use z, ⟨hzA, by aesop⟩
      -- Осталось показать, что choice-образ `z` — это и есть `s`. По однозначности `hp`:
      -- если одновременно верны `P ⟨z,hzA⟩ (choice-образ)` и `P ⟨z,hzA⟩ s`, то они равны.
      apply hp ⟨_, hzA⟩
      rw [dif_pos ⟨hzA, ⟨_, hz'⟩⟩]
      use Exists.choose_spec _
  nat := omega
  nat_equiv := nat_equiv
  regularity_axiom A := by
    -- В этой модели `Object = Set`, а `set_to_object` — тождество, поэтому `simp` сразу
    -- убирает "обёртку" `∀ S, x = set_to_object S → …` и оставляет чистое утверждение
    -- о фундированности: у непустого `A` найдётся элемент `x`, минимальный по `∈` внутри `A`.
    simp
    intro x hx
    -- `ZFSet.regularity` из Mathlib: у любого непустого множества найдётся элемент,
    -- не пересекающийся с самим этим множеством по принадлежности.
    have ⟨y, hy, _⟩ := regularity A (by aesop)
    use y, hy
    intro z _ _
    -- Если бы нашёлся `z`, лежащий и в `A`, и в `y`, он лежал бы в пересечении `A ∩ y`.
    have hzAy : z ∈ A ∩ y := by
      simp
      tauto
    -- Но по выбору `y` пересечение `A ∩ y` пусто — противоречие.
    aesop
  -- `pow X Y` — множество `X^Y` из книги Тао, то есть множество функций `Y → X`.
  -- В API Mathlib это ровно `funs Y X` (функции из `Y` в `X`).
  pow X Y := funs Y X
  function_to_object X Y := {
    -- Кодируем функцию `f : {x // x ∈ X} → {x // x ∈ Y}` как её график —
    -- множество пар `(s, f s)` для `s ∈ X`. Внутри `X` честно берём `f ⟨s,h⟩`,
    -- вне `X` (куда `map` формально всё равно заглядывает) подставляем "мусорное" значение `∅`.
    toFun f := @map (fun s ↦ if h : s ∈ X then f ⟨s,h⟩ else ∅) (allZFSetDefinable _) X
    -- Инъективность кодирования: если графики двух функций совпадают как множества,
    -- то и сами функции совпадают поточечно.
    inj' x _ h := by
      ext ⟨s, hs⟩
      -- Переводим равенство множеств-графиков `h` в поэлементное условие принадлежности графику.
      simp_rw [ZFSet.ext_iff, mem_map] at h
      -- Подставляем конкретный элемент графика первой функции — пару `(s, x ⟨s,hs⟩)` —
      -- и по `h` он должен лежать (тогда и только тогда) в графике второй функции тоже.
      specialize h (s.pair (x ⟨_,hs⟩))
      -- Дальше — механическая возня с инъективностью `pair` и разбором `if`-ветки: `aesop` справляется сам.
      aesop}
  powerset_axiom X Y F := by
    -- `F ∈ pow X Y` (через `mem_funs`/`IsFunc`) означает: `F` — подмножество `Y × X`,
    -- и каждому `z ∈ Y` отвечает ровно один `w` с `(z,w) ∈ F` — то есть `F` действительно
    -- является графиком некоторой функции `Y → X`.
    simp [IsFunc]
    constructor
    · -- (→) Из "F — график функции" реально строим саму функцию `f : {x // x ∈ Y} → {x // x ∈ X}`.
      intro ⟨hsub,huniq⟩
      -- Для каждого `x ∈ Y` лемма `huniq` даёт единственный `w` с `(x,w) ∈ F`.
      -- `.choose` достаёт этот `w`, а `pair_mem_prod`/`hsub` доказывают, что он лежит в `X`.
      use (fun x ↦ ⟨(huniq _ x.property).choose,(pair_mem_prod.mp (hsub (huniq _ x.property).choose_spec)).2⟩)
      -- Осталось проверить, что график построенной `f` — это в точности `F`.
      ext
      simp
      constructor
      · -- Если `(y, g y)` — пара из графика `f`, то она лежит в `F`: это ровно `choose_spec`.
        rintro ⟨y,hy,rfl⟩
        simp_all [(huniq _ hy).choose_spec]
      · -- Если `(y,x) ∈ F`, то `y ∈ Y`, `x ∈ X`, и по однозначности `huniq` выбранный
        -- choice-образ для `y` обязан совпасть с `x` — значит `(y,x)` лежит и в графике `f`.
        intro hf
        specialize hsub hf
        rw [mem_prod] at hsub
        obtain ⟨y,hy,x,_,rfl⟩ := hsub
        use y,hy
        simp_all [←(huniq _ hy).choose_eq hf]
    · -- (←) Обратное направление проще: график ЛЮБОЙ функции `f : {x // x ∈ Y} → {x // x ∈ X}`
      -- по построению лежит в `Y × X` и даёт ровно один `w` на каждый `z ∈ Y` — это и есть `IsFunc`.
      rintro ⟨f,rfl⟩
      simp
      constructor <;> intro _ _ <;> aesop (add safe [SetLike.coe_mem])
  union := sUnion
  -- `⋃₀` — уже готовая в Mathlib операция "большого" объединения (`mem_sUnion`).
  -- `And.comm` лишь меняет местами два конъюнкта: у `mem_sUnion` условие звучит как
  -- "`S ∈ x ∧ y ∈ S`", а в аксиоме класса — в обратном порядке.
  union_axiom _ _ := by simp [And.comm]
