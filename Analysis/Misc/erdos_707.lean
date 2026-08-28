import Mathlib

/-! Формализация доказательства (случая простого числа) проблемы Эрдёша \#707, недавно доказанной
Alexeev, ChatGPT, Lean и Mixon по адресу https://borisalexeev.com/papers/erdos707.html, следуя
Теореме 8, доказанной на странице 5 -/

/-- Совершенное разностное множество — это множество, в котором каждый ненулевой элемент однозначно
представим как разность двух элементов этого множества. -/
def IsPerfectDifferenceSet {N : ℕ} (B : Finset (ZMod N)) := ∀ d : ZMod N, d ≠ 0 → ∃! b : B × B, b.1.val - b.2.val = d

def IsPerfectDifferenceSet.map {N : ℕ} (B : Finset (ZMod N)) (p : (B × B) ⊕ Unit) : ZMod N ⊕ B := match p with
| Sum.inl p => if p.1 = p.2 then Sum.inr p.1 else Sum.inl (p.1.val - p.2.val)
| Sum.inr _ => Sum.inl 0

/-- Основное числовое тождество для совершенного разностного множества: `|B|² + 1 = N + |B|`
(эквивалентно `|B|·(|B|-1) = N-1`). -/
lemma IsPerfectDifferenceSet.card {N : ℕ} [NeZero N] {B : Finset (ZMod N)} (hdiff : IsPerfectDifferenceSet B) : B.card * B.card + 1 = N + B.card := by
  have he : Function.Bijective (IsPerfectDifferenceSet.map B) := by
    constructor
    . intro p p' hpp'
      rcases p with ⟨ x,y ⟩ | _ <;> rcases p' with ⟨ x',y' ⟩ | _ <;> simp_all [IsPerfectDifferenceSet.map]
      . by_cases hxy : x = y <;> by_cases hx'y' : x' = y' <;> simp_all
        have := (hdiff (x.val - y.val) (by grind)).unique (y₁ := ⟨ x,y ⟩) (y₂ := ⟨ x',y' ⟩)
        grind
      . by_cases hxy : x = y <;> grind
      by_cases hxy' : x' = y' <;> grind
    rintro (x | b)
    . by_cases h : x = 0
      . use Sum.inr Unit.unit
        simp [IsPerfectDifferenceSet.map, h]
      have := (hdiff x h).exists.choose_spec
      set b := (hdiff x h).exists.choose
      use Sum.inl b
      have hb : b.1 ≠ b.2 := by grind
      simp [IsPerfectDifferenceSet.map, hb, this]
    use Sum.inl ⟨ b, b ⟩
    simp [IsPerfectDifferenceSet.map]
  replace he := Fintype.card_of_bijective he
  simp [Fintype.card_sum] at he
  convert he

namespace Mainstep

/-- Мы покажем, что следующие гипотезы противоречивы; это и составляет основную часть доказательства
Теоремы 8. -/
class Hypotheses where
  p : ℕ
  hp : Nat.Prime p
  N : ℕ
  hN : N = p^2 + p + 1
  B : Finset (ZMod N)
  hdiff : IsPerfectDifferenceSet B
  embed : ({1,2,4,8} : Finset ℕ) → B
  h_embed : ∀ n, (embed n).val = n
  h_inj : Function.Injective embed

export Hypotheses (p hp N  hN B hdiff embed h_embed h_inj)

variable [Hypotheses]

-- Элемент `1` лежит в `B`, так как он входит в образ вложения `{1,2,4,8} → B`
lemma h1 : 1 ∈ B := by
  convert (embed ⟨ 1, by grind ⟩).property
  simp [h_embed]

-- Элемент `2` лежит в `B`, так как он входит в образ вложения `{1,2,4,8} → B`
lemma h2 : 2 ∈ B := by
  convert (embed ⟨ 2, by grind ⟩).property
  simp [h_embed]

-- Элемент `4` лежит в `B`, так как он входит в образ вложения `{1,2,4,8} → B`
lemma h4 : 4 ∈ B := by
  convert (embed ⟨ 4, by grind ⟩).property
  simp [h_embed]

-- Элемент `8` лежит в `B`, так как он входит в образ вложения `{1,2,4,8} → B`
lemma h8 : 8 ∈ B := by
  convert (embed ⟨ 8, by grind ⟩).property
  simp [h_embed]

-- `2` и `1` различны в `ZMod N`, так как вложение `{1,2,4,8} → B` инъективно
lemma h2_ne_1 : (2 : ZMod N) ≠ (1 : ZMod N) := by
  have : (embed ⟨ 2, by grind ⟩).val ≠ (embed ⟨ 1, by grind ⟩).val := by
    rw [Subtype.coe_ne_coe]
    by_contra!
    replace := h_inj this
    grind
  convert this <;> simp [h_embed]

-- `4` и `1` различны в `ZMod N`, так как вложение `{1,2,4,8} → B` инъективно
lemma h4_ne_1 : (4 : ZMod N) ≠ (1 : ZMod N) := by
  have : (embed ⟨ 4, by grind ⟩).val ≠ (embed ⟨ 1, by grind ⟩).val := by
    rw [Subtype.coe_ne_coe]
    by_contra!
    replace := h_inj this
    grind
  convert this <;> simp [h_embed]

-- `4` и `8` различны в `ZMod N`, так как вложение `{1,2,4,8} → B` инъективно
lemma h4_ne_8 : (4 : ZMod N) ≠ (8 : ZMod N) := by
  have : (embed ⟨ 4, by grind ⟩).val ≠ (embed ⟨ 8, by grind ⟩).val := by
    rw [Subtype.coe_ne_coe]
    by_contra!
    replace := h_inj this
    grind
  convert this <;> simp [h_embed]

-- `N = p² + p + 1` всегда нечётно, так как `p² + p = p·(p+1)` чётно
lemma hodd : Odd N := by
  rw [hN]
  grind

-- Размер `B` в точности равен `p + 1` — следует из тождества `IsPerfectDifferenceSet.card` при `N = p²+p+1`
lemma card_B : B.card = p + 1 := by
  have hnon : NeZero N := by rw [neZero_iff, hN]; grind
  have := hdiff.card
  have h1 := Finset.card_le_card_of_injective h_inj
  simp at h1
  replace : B.card * B.card = p^2 + p + B.card := by grind [hN]
  replace : (B.card : ℤ) * B.card = p^2 + p + B.card := by grind
  replace : ((B.card : ℤ) - (p + 1)) * (B.card + p) = 0 := by grind
  rw [mul_eq_zero] at this
  grind

-- Простое число `p` из гипотез нечётно (случай `p = 2` невозможен)
lemma odd_P : Odd p := by
  apply Nat.Prime.odd_of_ne_two hp
  by_contra!
  replace := this ▸ card_B
  have h1 := Finset.card_le_card_of_injective h_inj
  simp at h1
  grind

-- `|B| = p+1` чётно, так как `p` нечётно
lemma heven : Even B.card := by
  rw [card_B]
  grind [odd_P]

-- Умножение на `2` в `ZMod N` инъективно, так как `N` нечётно и потому `2` обратимо по модулю `N`
lemma mul_two_inj {x y : ZMod N} (h : 2 * x = 2 * y) : x = y := by
  apply IsUnit.mul_left_cancel _ h
  convert (ZMod.isUnit_prime_iff_not_dvd (n := N) Nat.prime_two).mpr _
  exact Odd.not_two_dvd_nat hodd

-- Единственность представления разности в `B`: если `a ≠ b` и `a - b = c - d`, то `a = c` и `b = d`
lemma diff_uniq {a b c d : B} (ha : a ≠ b) (hsub : a.val-b.val = c.val-d.val) : a=c ∧ b=d := by
  have := hdiff (a-b) (by grind)
  replace : (⟨ a, b ⟩ : B × B) = ⟨ c, d ⟩ := by apply this.unique <;> grind
  grind

/--
{given -show}`b, c, d`
Для совершенного разностного множества {name}`B` и элемента {name}`a`, не входящего в {name}`B`,
функция {lean}`f (a := a)` отображает каждый {lean}`b ∈ B` в единственный {lean}`c ∈ B`, такой что
{lean}`a - b = c - d` для некоторого {lean}`d ∈ B`.
-/
noncomputable def f {a : ZMod N} (ha : a ∉ B) (b : B) : B :=
    (hdiff (a-b.val) (by grind)).choose.1

/--
{given -show}`d`
Хотя в Теореме 8 она и не определена, удобно также ввести сопутствующую функцию {lean}`g (a := a)`,
определённую как элемент {name}`d`, такой что {lean}`a - b = f (a := a) ha b - d`.
-/
noncomputable def g {a : ZMod N} (ha : a ∉ B) (b : B) : B :=
    (hdiff (a-b.val) (by grind)).choose.2

-- Определяющее свойство `f` и `g`: `a - b = f a b - g a b`
lemma f_def {a : ZMod N} (ha : a ∉ B) (b : B) : a - b = f ha b - g ha b := by
  convert (hdiff (a - b.val) (by grind)).choose_spec.1.symm

-- Обращение `f_def`: `a - b = c - d` тогда и только тогда, когда `c = f a b` и `d = g a b`
lemma f_def' {a : ZMod N} (ha : a ∉ B) (b c d : B) : a - b = c - d ↔ c = f ha b ∧ d = g ha b := by
  constructor
  . intro h
    rw [f_def ha b] at h; symm at h
    apply diff_uniq _ h
    rw [←f_def ha b] at h
    grind
  rintro ⟨ rfl, rfl ⟩
  exact f_def ha b

/-- {lean}`f (a := a)` — это инволюция. -/
lemma f_inv {a : ZMod N} (ha : a ∉ B) : Function.Involutive (f ha) := by
  intro b
  have h1 := f_def ha b
  replace h1 : a - (f ha b) = b - (g ha b) := by grind
  rw [f_def' ha] at h1
  rw [←h1.1]

/-- Неподвижные точки {lean}`f (a := a)` удовлетворяют {lean}`2 * f ha b = a + g ha b`. -/
lemma f_fixed {a : ZMod N} {ha : a ∉ B} {b : B} (hb : f ha b = b) : 2 * b.val = a + (g ha b).val := by
  have := f_def ha b
  grind


@[implicit_reducible] noncomputable def z2_vact {a : ZMod N} (ha : a ∉ B) : AddAction (ZMod 2) B :=
{
  vadd i b := if i=1 then f ha b else b
  zero_vadd b := by
    change (if (0 : ZMod 2) = 1 then f ha b else b) = b
    simp
  add_vadd i j b := by
    change (if i + j = 1 then f ha b else b) = if i = 1 then f ha (if j = 1 then f ha b else b) else (if j = 1 then f ha b else b)
    fin_cases i <;> fin_cases j <;> dsimp only <;> first | rfl | exact (f_inv ha b).symm
}

/-- Если есть одна неподвижная точка, то есть и другая. -/
lemma f_second_fixed {a : ZMod N} {ha : a ∉ B} {b : B} (hb : f ha b = b) : ∃ c : B, c ≠ b ∧ f ha c = c := by
  let action := z2_vact ha
  classical
  have := action.sum_card_fixedBy_eq_card_orbits_mul_card_addGroup _ _
  simp only [ZMod.card] at this
  set N :=  Fintype.card (Quotient (action.orbitRel (ZMod 2) { x // x ∈ B }))
  set S := action.fixedBy { x // x ∈ B } 1
  replace := calc
    N * 2 = ∑ a, Fintype.card (action.fixedBy { x // x ∈ B } a) := this.symm
    _ = Fintype.card (action.fixedBy { x // x ∈ B } 0) + Fintype.card S := by
      exact Fin.sum_univ_two _
    _ = B.card + Fintype.card S := by simp
  replace : Even (Fintype.card S) := by
    apply (Nat.even_add.mp ?_).mp heven
    rw [←this]
    grind
  have hs : b ∈ S := by
    change (if (1 : ZMod 2) = 1 then f ha b else b) = b
    simp [hb]
  have c1 : Fintype.card S ≥ 1 := by
    haveI : Nonempty ↑S := ⟨⟨b, hs⟩⟩
    exact Fintype.card_pos
  replace c1 : Fintype.card S ≥ 2 := by grind
  have c2 : S ≠ {b} := by
    contrapose! c1
    simp [c1]
  have c3 : ∃ c : B, c ∈ S ∧ c ≠ b := by
    simp at c2
    grind
  obtain ⟨ c, hc ⟩ := c3
  use c; simp [hc]
  simp [S] at hc
  replace hc := hc.1
  change (if (1 : ZMod 2) = 1 then f ha c else c) = c at hc
  simp_all

-- Для `x ∈ B` с `x ≠ 2` элемент `2*(x-1)` не лежит в `B` — это позволяет применить `f`, `g` при `a := 2*(x-1)`
lemma two_mul_sub_one_notin {x : B} (hx : x.val ≠ 2) : 2 * (x.val - 1) ∉ B := by
  by_contra! this
  replace := diff_uniq (a:= x) (b := ⟨ 2,h2 ⟩) (c := ⟨_,this⟩) (d:=x) (by grind) (by grind)
  grind

-- При `a := 2*(x-1)` элемент `x` — неподвижная точка `f`
lemma first_fixed {x : B} (hx : x.val ≠ 2) : f (two_mul_sub_one_notin hx) x = x := by
  convert ((f_def' (two_mul_sub_one_notin hx) x x ⟨ 2, h2⟩).mp ?_).1.symm
  grind

-- Помимо `x`, у `f` при `a := 2*(x-1)` есть ещё одна неподвижная точка
lemma second_fixed {x : B} (hx : x.val ≠ 2) : ∃ b, b ≠ x ∧ f (two_mul_sub_one_notin hx) b = b :=  f_second_fixed (first_fixed hx)

noncomputable def b (x : B) := if hx : x.val = 2 then ⟨ 2, h2 ⟩ else (second_fixed hx).choose

noncomputable def d (x : B) := if hx : x.val = 2 then ⟨ 2, h2 ⟩ else g (two_mul_sub_one_notin hx) (second_fixed hx).choose

-- Выбранная вторая неподвижная точка `b x` отличается от самого `x`
lemma b_neq {x : B} (hx : x.val ≠ 2) : b x ≠ x := by
  simp [b, hx]
  convert (second_fixed hx).choose_spec.1

-- Ключевое тождество, связывающее `b x` и `d x`: `2*(b x) = 2*(x-1) + d x`
lemma bd_ident (x : B) : 2 * (b x).val = 2 * (x.val - 1) + (d x).val := by
  by_cases hx : x.val = 2
  · simp [b,d,hx]; ring
  · simp [b, d, hx]
    convert f_fixed _ using 2
    convert (second_fixed hx).choose_spec.2

-- Функция `d` инъективна
lemma d_injective : Function.Injective d := by
  intro x x' h
  have h1 := bd_ident x
  have h2 := bd_ident x'
  have h3 : 2 * ((b x).val - b x') = 2 * (x - x') := by grind
  replace h3 := (mul_two_inj h3).symm
  by_contra! this
  replace h3 := diff_uniq this h3
  have h4 := b_neq (x := x)
  have h5 := b_neq (x := x')
  grind

-- `d` инъективна на конечном множестве `B`, значит и сюръективна
lemma d_surjective : Function.Surjective d := Finite.surjective_of_injective d_injective

-- Значение `d` в точке `1` равно `4`
lemma d1_eq_4 : d ⟨ 1, h1 ⟩ = ⟨ 4, h4 ⟩ := by
  obtain ⟨ x, hx ⟩ := d_surjective ⟨ 4, h4 ⟩
  have := bd_ident x
  simp [hx] at this
  replace : 2 * (b x).val = 2 * (x.val + 1) := by grind
  replace := mul_two_inj this
  convert hx
  convert congrArg Subtype.val (diff_uniq ?_ ?_ (a := ⟨ 2, h2 ⟩) (b := ⟨ 1, h1 ⟩) (c := b x) (d := x)).2
  . simp; convert h2_ne_1
  grind

-- Значение `d` в точке `1` равно `8`
lemma d1_eq_8 : d ⟨ 1, h1 ⟩ = ⟨ 8, h8 ⟩ := by
  obtain ⟨ x, hx ⟩ := d_surjective ⟨ 8, h8 ⟩
  have := bd_ident x
  simp [hx] at this
  replace : 2 * (b x).val = 2 * (x.val + 3) := by grind
  replace := mul_two_inj this
  convert hx
  convert congrArg Subtype.val (diff_uniq ?_ ?_ (a := ⟨ 4, h4 ⟩) (b := ⟨ 1, h1 ⟩) (c := b x) (d := x)).2
  . simp; convert h4_ne_1
  grind

-- Итоговое противоречие: `d1_eq_4` и `d1_eq_8` дают `4 = 8` в `ZMod N`, что противоречит `h4_ne_8`;
-- значит, гипотезы `Hypotheses` несовместны
lemma contradiction : False := by
  have := d1_eq_8
  rw [d1_eq_4] at this
  simp at this
  exact h4_ne_8 this

end Mainstep
