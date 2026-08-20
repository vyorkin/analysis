import Mathlib.Tactic

/-
Ниже приведено неформальное доказательство теоремы `singleton_law`, любезно предоставленное Bruno
Le Floch: https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Alternative.20proofs.20of.20E1689.E2.8A.A2E2/near/517189582.
Для формализации этого доказательства использовался Claude Code, работавший по следующим шагам:

Шаг 0: Формализовать нотацию `S` и `f`.

Шаг 1: Сначала сформулировать в Lean *утверждения* Леммы 1, Леммы 2 и Леммы 3, оставив
доказательства в виде sorry. Реструктурировать имеющееся неформальное доказательство так, чтобы
формулировка и доказательство каждой леммы были перенесены ближе к формальной формулировке этой
леммы, выраженной в виде комментария. Использовать нотацию `S` и `f` там, где это нужно, чтобы
формальные формулировки как можно ближе соответствовали неформальным.

Шаг 2a: Создать высокоуровневый скелет доказательства Леммы 1, выразив каждый шаг неформального
доказательства как соответствующее утверждение Lean с обоснованием в виде sorry (например, шаг
может стать утверждением `have`, обоснованным через sorry). На этом этапе *не* пытаться обосновать
всё доказательство целиком — считать каждый шаг неформального доказательства верным (за исключением
исправления мелких опечаток и неточностей). Если какой-то шаг непонятен, заменить его подходящим
sorry и сообщить о возникшей проблеме, вместо того чтобы тратить много времени на его понимание.
И снова использовать нотацию `S` и `f` там, где это нужно, чтобы формализация как можно ближе
соответствовала неформальному доказательству.

Шаг 2b: Если на шаге 2a не возникло серьёзных проблем, заполнить все sorry в доказательстве Леммы 1.

Шаг 3a: Повторить шаг 2a для доказательства Леммы 2.

Шаг 3b: Повторить шаг 2b для доказательства Леммы 2.

Шаг 4a: Повторить шаг 2a для доказательства Леммы 3.

Шаг 4b: Повторить шаг 2b для доказательства Леммы 3.

Шаг 5a: Повторить шаг 2a для заключительной части доказательства `singleton_law` после Леммы 3.

Шаг 5b: Повторить шаг 2b для заключительной части доказательства `singleton_law` после Леммы 3.

После этого была проведена небольшая ручная доработка (golfing).
-/


class Magma (α : Type _) where
  op : α → α → α

infix:65 " ◇ " => Magma.op

abbrev Equation1689 (M : Type _) [Magma M] := ∀ x y z : M, x = (y ◇ x) ◇ ((x ◇ z) ◇ z)

abbrev Equation2 (M : Type _) [Magma M] := ∀ x y : M, x = y

variable {M : Type _} [Magma M]

-- Шаг 0: нотация S и f
-- S z x = (x ◇ z) ◇ z  (в неформальном доказательстве обозначено как S_z(x))
abbrev S (z x : M) : M := (x ◇ z) ◇ z

-- f x y = x ◇ S y x = x ◇ ((x ◇ y) ◇ y)  (в неформальном доказательстве обозначено как f(x,y))
abbrev f (x y : M) : M := x ◇ S y x

/-
Основное уравнение (Equation1689): x = (y ◇ x) ◇ S z x, то есть x = (y ◇ x) ◇ S z x.
Обозначаем S_z(x) = S z x = (x ◇ z) ◇ z и f(x,y) = f x y = x ◇ S y x = x ◇ ((x ◇ y) ◇ y).
-/

-- Вспомогательная лемма, используемая в Лемме 1 и Лемме 2:
-- S b a лежит в левом идеале a, то есть S b a = a ◇ S z (S b a) для любого z.
lemma S_left_ideal (h : Equation1689 M) (a b z : M) : S b a = a ◇ S z (S b a) := by
  have step := h ((a ◇ b) ◇ b) (a ◇ a) z
  grind

/-
**Лемма 1:** Для любых a, b, c верно S_b(a) = a ◇ f(b,c), то есть S b a = a ◇ f b c.

*Доказательство:* Для x = S b a и y ∈ Ma имеем y ◇ x = a. Применяя основное уравнение к этим
значениям x, y, получаем
  S b a = a ◇ S z (S b a).
Затем полагаем z = S c b и замечаем, что (S b a) ◇ z = ((a ◇ b) ◇ b) ◇ ((b ◇ c) ◇ c) = b, чтобы
упростить правую часть выше и получить, как и было анонсировано,
  S b a = a ◇ ((S b a ◇ z) ◇ z) = a ◇ (b ◇ z) = a ◇ f b c.
-/
lemma lemma1 (h : Equation1689 M) (a b c : M) : S b a = a ◇ f b c := by
  have h1 : ∀ z : M, S b a = a ◇ S z (S b a) := S_left_ideal h a b
  -- Основное уравнение при x = b, y = a ◇ b, z = c даёт b = ((a◇b)◇b) ◇ ((b◇c)◇c) = S b a ◇ S c b.
  have h2 : S b a ◇ S c b = b := (h b (a ◇ b) c).symm
  -- Следовательно, S (S c b) (S b a) = (S b a ◇ S c b) ◇ S c b = b ◇ S c b = f b c.
  have h3 : S (S c b) (S b a) = f b c := by grind
  -- Объединяя: S b a = a ◇ S (S c b) (S b a) = a ◇ f b c.
  calc S b a = a ◇ S (S c b) (S b a) := h1 (S c b)
    _ = a ◇ f b c := by rw [h3]

/-
**Лемма 2:** Для любого a существуют b, c, d, такие что f(b,c) = S_d(a), то есть f b c = S d a.

*Доказательство:* По определению f имеем f b c = b ◇ S c b. Взяв b = S x a для некоторого x
и переписав b = a ◇ S c b с помощью первого уравнения из доказательства Леммы 1, находим
  f b c = (a ◇ S c b) ◇ S c b,
что имеет нужный вид при d = S c b.  (Таким образом, утверждение на самом деле верно для всех a, c.)
-/
lemma lemma2 (h : Equation1689 M) (a : M) : ∃ b c d : M, f b c = S d a := by
  -- Берём b := S a a (= S_a(a)), c := a, d := S a (S a a) (= S c b).
  -- Доказательство работает для всех a, c; для b = S x a подходит любой x.
  use S a a, a, S a (S a a)
  -- По тому же рассуждению, что и первое уравнение в доказательстве Леммы 1 (с b := a, z := a):
  --   b = S a a = a ◇ S a (S a a) = a ◇ S c b.
  have hb : S a a = a ◇ S a (S a a) := S_left_ideal h a a a
  -- f b c = b ◇ S c b = (a ◇ S c b) ◇ S c b = S (S c b) a = S d a.
  calc f (S a a) a
      = S a a ◇ S a (S a a)              := rfl
    _ = (a ◇ S a (S a a)) ◇ S a (S a a) := by congr
    _ = S (S a (S a a)) a                := rfl

/-
**Лемма 3:** Для любого a существует e, такое что S_e(a) = a, то есть S e a = a.

*Доказательство:* Домножим уравнение из Леммы 1 слева на a³ = (a ◇ a) ◇ a, чтобы получить
(первое равенство ниже следует из основного уравнения)
  a = ((a ◇ a) ◇ a) ◇ S b a = a³ ◇ (a ◇ f b c).
Возьмём b, c, d, как в Лемме 2, чтобы переписать a ◇ f b c = a ◇ S d a = f a d. С другой стороны,
Лемма 1 при a = b и c, заменённом на d, даёт a³ = a ◇ f a d, так что в итоге получаем
  a = (a ◇ f a d) ◇ f a d,
что и требовалось при e = f a d.
-/
lemma lemma3 (h : Equation1689 M) (a : M) : ∃ e : M, S e a = a := by
  -- Берём b, c, d из Леммы 2, так что f b c = S d a.
  obtain ⟨b, c, d, hd⟩ := lemma2 h a
  -- Берём e := f a d.
  use f a d
  -- Основное уравнение при x = a, y = a ◇ a, z = b даёт a = ((a ◇ a) ◇ a) ◇ S b a.
  have h_main : a = ((a ◇ a) ◇ a) ◇ S b a := by grind
  -- Лемма 1 даёт S b a = a ◇ f b c, так что a = ((a ◇ a) ◇ a) ◇ (a ◇ f b c).
  have h_step2 : a = ((a ◇ a) ◇ a) ◇ (a ◇ f b c) :=
    h_main.trans (by rw [lemma1 h a b c])
  -- Поскольку f b c = S d a по hd, то a ◇ f b c = a ◇ S d a = f a d.
  have h_step3 : a ◇ f b c = f a d := by grind
  -- Лемма 1 при b←a, c←d даёт S a a = a ◇ f a d, то есть (a ◇ a) ◇ a = a ◇ f a d.
  have h_step4 : (a ◇ a) ◇ a = a ◇ f a d := by
    simpa using lemma1 h a a d
  -- Объединяя: S(f a d) a = (a ◇ f a d) ◇ f a d = ((a ◇ a) ◇ a) ◇ f a d
  --        = ((a ◇ a) ◇ a) ◇ (a ◇ f b c) = ((a ◇ a) ◇ a) ◇ S b a = a.
  calc S (f a d) a
      = (a ◇ f a d) ◇ f a d          := rfl
    _ = ((a ◇ a) ◇ a) ◇ f a d       := by rw [← h_step4]
    _ = ((a ◇ a) ◇ a) ◇ (a ◇ f b c) := by rw [← h_step3]
    _ = ((a ◇ a) ◇ a) ◇ S b a       := by rw [← lemma1 h a b c]
    _ = a                            := h_main.symm

/-
*Завершение доказательства:* Для любых a, y, используя e из Леммы 3, основное уравнение даёт
  a = (y ◇ a) ◇ S e a = (y ◇ a) ◇ a = S a y.
Подставляя это обратно в основное уравнение, получаем (z ◇ y) ◇ a = y для любых a, y, z.
Значит, a ◇ b = ((d ◇ a) ◇ c) ◇ b = c для любых a, b, c, d, а тогда a = b ◇ c = d для любых a, b, c, d.
-/
theorem singleton_law (h : Equation1689 M) : Equation2 M := by
  -- Шаг 1: S a b = a для всех a, b.
  -- Лемма 3 даёт e с S e a = a; основное уравнение (x=a, z=e) даёт a = (y ◇ a) ◇ S e a = (y ◇ a) ◇ a = S a y.
  have hS : ∀ a b : M, S a b = a := by
    intro a b
    obtain ⟨e, he⟩ := lemma3 h a
    grind
  -- Шаг 2: (a ◇ b) ◇ c = b для всех a, b, c.
  -- Основное уравнение (x=b, y=a, z=c) даёт b = (a ◇ b) ◇ S c b = (a ◇ b) ◇ c по hS.
  have hrel : ∀ a b c : M, (a ◇ b) ◇ c = b := by
    intro a b c
    have step := h b a c
    grind
  -- Шаг 3: a ◇ b = c для всех a, b, c.
  -- Из hrel: (d ◇ a) ◇ c = a, поэтому a ◇ b = ((d ◇ a) ◇ c) ◇ b = c по hrel.
  have hconst : ∀ a b c : M, a ◇ b = c := by
    intro a b c
    have h1 : (a ◇ a) ◇ c = a := hrel a a c
    have h2 : ((a ◇ a) ◇ c) ◇ b = c := hrel (a ◇ a) c b
    grind
  -- Заключаем: x = x ◇ x = y.
  intro x y
  exact (hconst x x x).symm.trans (hconst x x y)
