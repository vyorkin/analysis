import Mathlib.Tactic
import Analysis.Section_3_3
import Analysis.Section_3_5

/-!
# Analysis I, раздел 3.6: Мощность множеств

Я старался сделать перевод максимально точным перефразированием оригинального текста. Когда
приходилось выбирать между более идиоматичным Lean-решением и более точным переводом, я, как
правило, выбирал второе. В частности, местами Lean-код можно было бы "заголфить", сделав его более
элегантным и идиоматичным, но я сознательно этого избегал.


Основные конструкции и результаты этого раздела:

- Мощность множества
- Конечные и бесконечные множества
- Связи с соответствующими понятиями из Mathlib

После этого раздела данные понятия будут вытеснены их аналогами из Mathlib.

## Советы от прошлых пользователей

Пользователи, прошедшие упражнения этого раздела, могут присылать свои советы для будущих
пользователей в виде PR.

- (Добавьте совет сюда)

-/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

/-- Определение 3.6.1 (Равная мощность) -/
abbrev SetTheory.Set.EqualCard (X Y : Set) : Prop := ∃ f : X → Y, Function.Bijective f

/-- Пример 3.6.2 -/
theorem SetTheory.Set.Example_3_6_2 : EqualCard {0,1,2} {3,4,5} := by
  use open Classical in fun x ↦
    ⟨if x.val = 0 then 3 else if x.val = 1 then 4 else 5, by aesop⟩
  constructor
  · intro; aesop
  intro y
  have : y = (3 : Object) ∨ y = (4 : Object) ∨ y = (5 : Object) := by
    have := y.property
    aesop
  rcases this with (_ | _ | _)
  · use ⟨0, by simp⟩; aesop
  · use ⟨1, by simp⟩; aesop
  · use ⟨2, by simp⟩; aesop

/-- Пример 3.6.3 -/
theorem SetTheory.Set.Example_3_6_3 : EqualCard nat (nat.specify (fun x ↦ Even (x : ℕ))) := by sorry

-- рефлексивность равномощности: `X` равномощно самому себе
@[refl]
theorem SetTheory.Set.EqualCard.refl (X : Set) : EqualCard X X := by
  sorry

-- симметричность равномощности: из `X` равномощно `Y` следует, что и `Y` равномощно `X`
@[symm]
theorem SetTheory.Set.EqualCard.symm {X Y : Set} (h : EqualCard X Y) : EqualCard Y X := by
  sorry

-- транзитивность равномощности: из `X` равномощно `Y` и `Y` равномощно `Z` следует `X` равномощно `Z`
@[trans]
theorem SetTheory.Set.EqualCard.trans {X Y Z : Set} (h1 : EqualCard X Y) (h2 : EqualCard Y Z) : EqualCard X Z := by
  sorry

/-- Утверждение 3.6.4 / Упражнение 3.6.1 -/
instance SetTheory.Set.EqualCard.inst_setoid : Setoid SetTheory.Set := ⟨ EqualCard, {refl, symm, trans} ⟩

/-- Определение 3.6.5 -/
abbrev SetTheory.Set.has_card (X : Set) (n : ℕ) : Prop := X ≈ Fin n

-- разворачивает `has_card`: `X` имеет мощность `n` тогда и только тогда, когда существует биекция `X → Fin n`
theorem SetTheory.Set.has_card_iff (X : Set) (n : ℕ) : 
    X.has_card n ↔ ∃ f : X → Fin n, Function.Bijective f := by
  simp [has_card, HasEquiv.Equiv, instHasEquivOfSetoid, Setoid.r, EqualCard]

/-- Замечание 3.6.6 -/
theorem SetTheory.Set.Remark_3_6_6 (n : ℕ) : 
    (nat.specify (fun x ↦ 1 ≤ (x : ℕ) ∧ (x : ℕ) ≤ n)).has_card n := by sorry

/-- Пример 3.6.7 -/
theorem SetTheory.Set.Example_3_6_7a (a : Object) : ({a} : Set).has_card 1 := by
  rw [has_card_iff]
  use fun _ ↦ Fin_mk _ 0 (by simp)
  constructor
  · intro x1 x2 hf; aesop
  intro y
  use ⟨a, by simp⟩
  have := Fin.toNat_lt y
  simp_all

-- пример: множество из четырёх попарно различных элементов `{a,b,c,d}` имеет мощность `4`
theorem SetTheory.Set.Example_3_6_7b {a b c d : Object} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : ({a,b,c,d} : Set).has_card 4 := by
  rw [has_card_iff]
  use open Classical in fun x ↦ Fin_mk _ (
    if x.val = a then 0 else if x.val = b then 1 else if x.val = c then 2 else 3
  ) (by aesop)
  constructor
  · intro x1 x2 hf; aesop
  intro y
  have : y = (0 : ℕ) ∨ y = (1 : ℕ) ∨ y = (2 : ℕ) ∨ y = (3 : ℕ) := by
    have := Fin.toNat_lt y
    omega
  rcases this with (_ | _ | _ | _)
  · use ⟨a, by aesop⟩; aesop
  · use ⟨b, by aesop⟩; aesop
  · use ⟨c, by aesop⟩; aesop
  · use ⟨d, by aesop⟩; aesop

/-- Лемма 3.6.9 -/
theorem SetTheory.Set.pos_card_nonempty {n : ℕ} (h : n ≥ 1) {X : Set} (hX : X.has_card n) : X ≠ ∅ := by
  -- Это доказательство написано так, чтобы следовать структуре оригинального текста.
  by_contra! this
  have hnon : Fin n ≠ ∅ := by
    apply nonempty_of_inhabited (x := 0); rw [mem_Fin]; use 0, (by omega); rfl
  rw [has_card_iff] at hX
  choose f hf using hX
  sorry
  -- получить противоречие из того факта, что `f` — биекция из пустого множества в
  -- непустое множество.

/-- Упражнение 3.6.2a -/
theorem SetTheory.Set.has_card_zero {X : Set} : X.has_card 0 ↔ X = ∅ := by sorry

/-- Лемма 3.6.9 -/
theorem SetTheory.Set.card_erase {n : ℕ} (h : n ≥ 1) {X : Set} (hX : X.has_card n) (x : X) :
    (X \ {x.val}).has_card (n-1) := by
  -- Это доказательство переписано относительно оригинального текста в попытке сделать его
  -- более удобным для формализации в Lean.
  rw [has_card_iff] at hX; choose f hf using hX
  set X' : Set := X \ {x.val}
  set ι : X' → X := fun ⟨y, hy⟩ ↦ ⟨ y, by aesop ⟩
  observe hι : ∀ x : X', (ι x : Object) = x
  choose m₀ hm₀ hm₀f using (mem_Fin _ _).mp (f x).property
  set g : X' → Fin (n-1) := fun x' ↦
    let := Fin.toNat_lt (f (ι x'))
    let : (f (ι x') : ℕ) ≠ m₀ := by
      by_contra!; simp [←this, Subtype.val_inj, hf.1.eq_iff, ι] at hm₀f
      have := x'.property; aesop
    if h' : f (ι x') < m₀ then Fin_mk _ (f (ι x')) (by omega)
    else Fin_mk _ (f (ι x') - 1) (by omega)
  have hg_def (x' : X') : if (f (ι x') : ℕ) < m₀ then (g x' : ℕ) = f (ι x') else (g x' : ℕ) = f (ι x') - 1 := by
    split_ifs with h' <;> simp [g,h']
  have hg : Function.Bijective g := by sorry
  use g

/-- Утверждение 3.6.8 (Единственность мощности) -/
theorem SetTheory.Set.card_uniq {X : Set} {n m : ℕ} (h1 : X.has_card n) (h2 : X.has_card m) : n = m := by
  -- Это доказательство написано так, чтобы следовать структуре оригинального текста.
  revert X m; induction' n with n hn
  . intro _ _ h1 h2; rw [has_card_zero] at h1; contrapose! h1
    apply pos_card_nonempty _ h2; omega
  intro X m h1 h2
  have : X ≠ ∅ := pos_card_nonempty (by omega) h1
  choose x hx using nonempty_def this
  have : m ≠ 0 := by contrapose! this; simpa [has_card_zero, this] using h2
  specialize hn (card_erase ?_ h1 ⟨ _, hx ⟩) (card_erase ?_ h2 ⟨ _, hx ⟩) <;> omega

-- пример: множество `{0,1,2}` имеет мощность `3`
lemma SetTheory.Set.Example_3_6_8_a : ({0,1,2} : Set).has_card 3 := by
  rw [has_card_iff]
  have : ({0, 1, 2} : Set) = SetTheory.Set.Fin 3 := by
    ext x
    simp only [mem_insert, mem_singleton, mem_Fin]
    constructor
    · aesop
    rintro ⟨x, ⟨_, rfl⟩⟩
    simp only [nat_coe_eq_iff]
    omega
  rw [this]
  use id
  exact Function.bijective_id

-- пример: множество `{3,4}` имеет мощность `2`
lemma SetTheory.Set.Example_3_6_8_b : ({3,4} : Set).has_card 2 := by
  rw [has_card_iff]
  use open Classical in fun x ↦ Fin_mk _ (if x = (3 : Object) then 0 else 1) (by aesop)
  constructor
  · intro x1 x2
    aesop
  intro y
  have := Fin.toNat_lt y
  have : y = (0 : ℕ) ∨ y = (1 : ℕ) := by omega
  aesop

-- пример: множества `{0,1,2}` и `{3,4}` не равномощны, поскольку имеют разную мощность (3 и 2)
lemma SetTheory.Set.Example_3_6_8_c : ¬({0,1,2} : Set) ≈ ({3,4} : Set) := by
  by_contra h
  have h1 : Fin 3 ≈ Fin 2 := (Example_3_6_8_a.symm.trans h).trans Example_3_6_8_b
  have h2 : Fin 3 ≈ Fin 3 := by rfl
  have := card_uniq h1 h2
  contradiction

abbrev SetTheory.Set.finite (X : Set) : Prop := ∃ n : ℕ, X.has_card n

abbrev SetTheory.Set.infinite (X : Set) : Prop := ¬ finite X

/-- Упражнение 3.6.3, сформулированное с использованием натуральных чисел Mathlib -/
theorem SetTheory.Set.bounded_on_finite {n : ℕ} (f : Fin n → nat) : ∃ M, ∀ i, (f i : ℕ) ≤ M := by sorry

/-- Теорема 3.6.12 -/
theorem SetTheory.Set.nat_infinite : infinite nat := by
  -- Это доказательство написано так, чтобы следовать структуре оригинального текста.
  by_contra this; choose n hn using this
  simp [has_card] at hn; symm at hn; simp [HasEquiv.Equiv] at hn
  choose f hf using hn; choose M hM using bounded_on_finite f
  replace hf := hf.surjective ↑(M+1); contrapose! hf
  peel hM with hi; contrapose! hi
  apply_fun nat_equiv.symm at hi; simp_all

open Classical in
/-- Для удобства в Lean бесконечным множествам присваивается "мусорная" мощность, равная нулю. -/
noncomputable def SetTheory.Set.card (X : Set) : ℕ := if h : X.finite then h.choose else 0

-- для конечного `X` число `X.card` действительно является его мощностью в смысле `has_card`
theorem SetTheory.Set.has_card_card {X : Set} (hX : X.finite) : X.has_card (SetTheory.Set.card X) := by
  simp [card, hX, hX.choose_spec]

-- если `X` имеет мощность `n`, то функция `card` вычисляет именно `n`
theorem SetTheory.Set.has_card_to_card {X : Set} {n : ℕ} : X.has_card n → X.card = n := by
  intro h; simp [card, card_uniq (⟨ n, h ⟩ : X.finite).choose_spec h]; aesop

-- обратное направление: при ненулевом `n` равенство `X.card = n` влечёт `X.has_card n`
theorem SetTheory.Set.card_to_has_card {X : Set} {n : ℕ} (hn : n ≠ 0) : X.card = n → X.has_card n
  := by grind [card, has_card_card]

-- множество `Fin n` имеет мощность `n`, как и ожидается
theorem SetTheory.Set.card_fin_eq (n : ℕ) : (Fin n).has_card n := (has_card_iff _ _).mp ⟨ id, Function.bijective_id ⟩

-- значение `card` на `Fin n` равно `n`
theorem SetTheory.Set.Fin_card (n : ℕ) : (Fin n).card = n := has_card_to_card (card_fin_eq n)

-- множество `Fin n` конечно
theorem SetTheory.Set.Fin_finite (n : ℕ) : (Fin n).finite := ⟨n, card_fin_eq n⟩

-- равномощные множества имеют одну и ту же мощность `n` (для любого `n`)
theorem SetTheory.Set.EquivCard_to_has_card_eq {X Y : Set} {n : ℕ} (h : X ≈ Y) : X.has_card n ↔ Y.has_card n := by
  choose f hf using h; let e := Equiv.ofBijective f hf
  constructor <;> (intro h'; rw [has_card_iff] at *; choose g hg using h')
  . use e.symm.trans (.ofBijective _ hg); apply Equiv.bijective
  . use e.trans (.ofBijective _ hg); apply Equiv.bijective

-- равномощные множества имеют равные значения `card`
theorem SetTheory.Set.EquivCard_to_card_eq {X Y : Set} (h : X ≈ Y) : X.card = Y.card := by
  by_cases hX : X.finite <;> by_cases hY : Y.finite <;> try rw [finite] at hX hY
  . choose nX hXn using hX; choose nY hYn using hY
    simp [has_card_to_card hXn, has_card_to_card hYn, EquivCard_to_has_card_eq h] at *
    solve_by_elim [card_uniq]
  . choose nX hXn using hX; rw [EquivCard_to_has_card_eq h] at hXn; tauto
  . choose nY hYn using hY; rw [←EquivCard_to_has_card_eq h] at hYn; tauto
  simp [card, hX, hY]

/-- Упражнение 3.6.2 -/
theorem SetTheory.Set.empty_iff_card_eq_zero {X : Set} : X = ∅ ↔ X.finite ∧ X.card = 0 := by
  sorry

-- конечное множество нулевой мощности пусто
lemma SetTheory.Set.empty_of_card_eq_zero {X : Set} (hX : X.finite) : X.card = 0 → X = ∅ := by
  intro h
  rw [empty_iff_card_eq_zero]
  exact ⟨hX, h⟩

-- пустое множество конечно
lemma SetTheory.Set.finite_of_empty {X : Set} : X = ∅ → X.finite := by
  intro h
  rw [empty_iff_card_eq_zero] at h
  exact h.1

-- мощность пустого множества равна нулю
lemma SetTheory.Set.card_eq_zero_of_empty {X : Set} : X = ∅ → X.card = 0 := by
  intro h
  rw [empty_iff_card_eq_zero] at h
  exact h.2

-- пустое множество конечно (частный случай `finite_of_empty`)
@[simp]
lemma SetTheory.Set.empty_finite : (∅ : Set).finite := finite_of_empty rfl

-- мощность пустого множества равна нулю (частный случай `card_eq_zero_of_empty`)
@[simp]
lemma SetTheory.Set.empty_card_eq_zero : (∅ : Set).card = 0 := card_eq_zero_of_empty rfl

/-- Утверждение 3.6.14 (a) / Упражнение 3.6.4 -/
theorem SetTheory.Set.card_insert {X : Set} (hX : X.finite) {x : Object} (hx : x ∉ X) : 
    (X ∪ {x}).finite ∧ (X ∪ {x}).card = X.card + 1 := by sorry

/-- Утверждение 3.6.14 (b) / Упражнение 3.6.4 -/
theorem SetTheory.Set.card_union {X Y : Set} (hX : X.finite) (hY : Y.finite) : 
    (X ∪ Y).finite ∧ (X ∪ Y).card ≤ X.card + Y.card := by sorry

/-- Утверждение 3.6.14 (b') / Упражнение 3.6.4 -/
theorem SetTheory.Set.card_union_disjoint {X Y : Set} (hX : X.finite) (hY : Y.finite)
  (hdisj : Disjoint X Y) : (X ∪ Y).card = X.card + Y.card := by sorry

/-- Утверждение 3.6.14 (c) / Упражнение 3.6.4 -/
theorem SetTheory.Set.card_subset {X Y : Set} (hX : X.finite) (hY : Y ⊆ X) : 
    Y.finite ∧ Y.card ≤ X.card := by sorry

/-- Утверждение 3.6.14 (c') / Упражнение 3.6.4 -/
theorem SetTheory.Set.card_ssubset {X Y : Set} (hX : X.finite) (hY : Y ⊂ X) : 
    Y.card < X.card := by sorry

/-- Утверждение 3.6.14 (d) / Упражнение 3.6.4 -/
theorem SetTheory.Set.card_image {X Y : Set} (hX : X.finite) (f : X → Y) : 
    (image f X).finite ∧ (image f X).card ≤ X.card := by sorry

/-- Утверждение 3.6.14 (d') / Упражнение 3.6.4 -/
theorem SetTheory.Set.card_image_inj {X Y : Set} (hX : X.finite) {f : X → Y}
  (hf : Function.Injective f) : (image f X).card = X.card := by sorry

/-- Утверждение 3.6.14 (e) / Упражнение 3.6.4 -/
theorem SetTheory.Set.card_prod {X Y : Set} (hX : X.finite) (hY : Y.finite) : 
    (X ×ˢ Y).finite ∧ (X ×ˢ Y).card = X.card * Y.card := by sorry

noncomputable def SetTheory.Set.pow_fun_equiv {A B : Set} : ↑(A ^ B) ≃ (B → A) where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

-- элементы `A ^ B` равны тогда и только тогда, когда равны их образы под `pow_fun_equiv`
lemma SetTheory.Set.pow_fun_eq_iff {A B : Set} (x y : ↑(A ^ B)) : x = y ↔ pow_fun_equiv x = pow_fun_equiv y := by
  rw [←pow_fun_equiv.apply_eq_iff_eq]

/-- Утверждение 3.6.14 (f) / Упражнение 3.6.4 -/
theorem SetTheory.Set.card_pow {X Y : Set} (hY : Y.finite) (hX : X.finite) : 
    (Y ^ X).finite ∧ (Y ^ X).card = Y.card ^ X.card := by sorry

/-- Упражнение 3.6.5. Вам может пригодиться {name}`SetTheory.Set.prod_commutator`. -/
theorem SetTheory.Set.prod_EqualCard_prod (A B : Set) : 
    EqualCard (A ×ˢ B) (B ×ˢ A) := by sorry

noncomputable abbrev SetTheory.Set.pow_fun_equiv' (A B : Set) : ↑(A ^ B) ≃ (B → A) :=
  pow_fun_equiv (A:=A) (B:=B)

/-- Упражнение 3.6.6. Вам может пригодиться {name}`SetTheory.Set.curry_equiv`. -/
theorem SetTheory.Set.pow_pow_EqualCard_pow_prod (A B C : Set) : 
    EqualCard ((A ^ B) ^ C) (A ^ (B ×ˢ C)) := by sorry

-- закон степеней для натуральных чисел: `(a^b)^c = a^(b*c)`
theorem SetTheory.Set.pow_pow_eq_pow_mul (a b c : ℕ) : (a^b)^c = a^(b*c) := by sorry

-- для непересекающихся `B` и `C` произведение `(A^B) ×ˢ (A^C)` равномощно `A^(B ∪ C)`
theorem SetTheory.Set.pow_prod_pow_EqualCard_pow_union (A B C : Set) (hd : Disjoint B C) : 
    EqualCard ((A ^ B) ×ˢ (A ^ C)) (A ^ (B ∪ C)) := by sorry

-- закон степеней для натуральных чисел: `a^b * a^c = a^(b+c)`
theorem SetTheory.Set.pow_mul_pow_eq_pow_add (a b c : ℕ) : (a^b) * a^c = a^(b+c) := by sorry

/-- Упражнение 3.6.7 -/
theorem SetTheory.Set.injection_iff_card_le {A B : Set} (hA : A.finite) (hB : B.finite) : 
    (∃ f : A → B, Function.Injective f) ↔ A.card ≤ B.card := sorry

/-- Упражнение 3.6.8 -/
theorem SetTheory.Set.surjection_from_injection {A B : Set} (hA : A ≠ ∅) (f : A → B)
  (hf : Function.Injective f) : ∃ g : B → A, Function.Surjective g := by sorry

/-- Упражнение 3.6.9 -/
theorem SetTheory.Set.card_union_add_card_inter {A B : Set} (hA : A.finite) (hB : B.finite) : 
    A.card + B.card = (A ∪ B).card + (A ∩ B).card := by  sorry

/-- Упражнение 3.6.10 -/
theorem SetTheory.Set.pigeonhole_principle {n : ℕ} {A : Fin n → Set}
  (hA : ∀ i, (A i).finite) (hAcard : (iUnion _ A).card > n) : ∃ i, (A i).card ≥ 2 := by sorry

/-- Упражнение 3.6.11 -/
theorem SetTheory.Set.two_to_two_iff {X Y : Set} (f : X → Y) : Function.Injective f ↔
    ∀ S ⊆ X, S.card = 2 → (image f S).card = 2 := by sorry

/-- Упражнение 3.6.12 -/
def SetTheory.Set.Permutations (n : ℕ) : Set := (Fin n ^ Fin n).specify (fun F ↦
    Function.Bijective (pow_fun_equiv F))

/-- Упражнение 3.6.12 (i), first part -/
theorem SetTheory.Set.Permutations_finite (n : ℕ) : (Permutations n).finite := by sorry

/- Чтобы продолжить Упражнение 3.6.12 (i), сначала разовьём немного теории о `Permutations` и `Fin`. -/

noncomputable def SetTheory.Set.Permutations_toFun {n : ℕ} (p : Permutations n) : (Fin n) → (Fin n) := by
  have := p.property
  simp only [Permutations, specification_axiom'', powerset_axiom] at this
  exact this.choose.choose

-- функция `Permutations_toFun p`, отвечающая перестановке `p`, действительно биективна
theorem SetTheory.Set.Permutations_bijective {n : ℕ} (p : Permutations n) : 
    Function.Bijective (Permutations_toFun p) := by sorry

-- `Permutations_toFun` инъективна: разные перестановки задают разные функции `Fin n → Fin n`
theorem SetTheory.Set.Permutations_inj {n : ℕ} (p1 p2 : Permutations n) : 
    Permutations_toFun p1 = Permutations_toFun p2 ↔ p1 = p2 := by sorry

/-- Это связывает наше понятие перестановки с {name}`Equiv` из Mathlib между {lean}`Fin n` и {lean}`Fin n`. -/
noncomputable def SetTheory.Set.perm_equiv_equiv {n : ℕ} : Permutations n ≃ (Fin n ≃ Fin n) := {
  toFun := fun p => Equiv.ofBijective (Permutations_toFun p) (Permutations_bijective p)
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
}

/- Упражнение 3.6.12 включает много перемещений между `Fin n` и `Fin (n + 1)`, поэтому добавим
несколько удобств. -/

/-- Любой {lean}`Fin n` можно привести к {lean}`Fin (n + 1)`. Сравните с {name}`Fin.castSucc` из Mathlib. -/
def SetTheory.Set.Fin.castSucc {n} (x : Fin n) : Fin (n + 1) :=
  Fin_embed _ _ (by omega) x

-- вложение `castSucc : Fin n → Fin (n+1)` инъективно
@[simp]
lemma SetTheory.Set.Fin.castSucc_inj {n} {x y : Fin n} : castSucc x = castSucc y ↔ x = y := by sorry

-- `castSucc` не отображает ни один элемент `Fin n` в `n`
@[simp]
theorem SetTheory.Set.Fin.castSucc_ne {n} (x : Fin n) : castSucc x ≠ n := by sorry

/-- Любой {lean}`Fin (n + 1)`, кроме {lean}`n`, можно привести к {lean}`Fin n`. Сравните с {name}`Fin.castPred` из Mathlib. -/
noncomputable def SetTheory.Set.Fin.castPred {n} (x : Fin (n + 1)) (h : (x : ℕ) ≠ n) : Fin n :=
  Fin_mk _ (x : ℕ) (by have := Fin.toNat_lt x; omega)

-- `castSucc` восстанавливает `x`, применённый после `castPred` (когда `x ≠ n`)
@[simp]
theorem SetTheory.Set.Fin.castSucc_castPred {n} (x : Fin (n + 1)) (h : (x : ℕ) ≠ n) : 
    castSucc (castPred x h) = x := by sorry

-- `castPred` восстанавливает `x` после применения `castSucc` — обратное направление к `castSucc_castPred`
@[simp]
theorem SetTheory.Set.Fin.castPred_castSucc {n} (x : Fin n) (h : ((castSucc x : Fin (n + 1)) : ℕ) ≠ n) : 
    castPred (castSucc x) h = x := by sorry

/-- Любое натуральное {lean}`n` можно привести к {lean}`Fin (n + 1)`. Сравните с {name}`Fin.last` из Mathlib. -/
def SetTheory.Set.Fin.last (n : ℕ) : Fin (n + 1) := Fin_mk _ n (by omega)

/-- Сейчас удобный момент доказать этот результат, который пригодится для завершения Упражнения 3.6.12 (i). -/
theorem SetTheory.Set.card_iUnion_card_disjoint {n m : ℕ} {S : Fin n → Set}
    (hSc : ∀ i, (S i).has_card m)
    (hSd : Pairwise fun i j => Disjoint (S i) (S j)) : 
    ((Fin n).iUnion S).finite ∧ ((Fin n).iUnion S).card = n * m := by sorry

/- Наконец, настроим способ сжимать `Fin (n + 1)` в `Fin n` (или расширять обратно), проделывая
"дыру". -/

/--
  Если некоторый {lean}`x : Fin (n+1)` никогда не равен {name}`i`, мы можем сжать его в
  {lean}`Fin n`, сдвинув все {lean}`(x : ℕ) > i` на единицу вниз.
  Сравните с {name}`Fin.predAbove` из Mathlib.
-/
noncomputable def SetTheory.Set.Fin.predAbove {n} (i : Fin (n + 1)) (x : Fin (n + 1)) (h : x ≠ i) : Fin n :=
  if hx : (x : ℕ) < i then
    Fin_mk _ (x : ℕ) (by sorry)
  else
    Fin_mk _ ((x : ℕ) - 1) (by sorry)

/--
  Мы можем расширить {lean}`x : Fin n` до {lean}`Fin (n + 1)`, сдвинув все {lean}`(x : ℕ) ≥ i`
  на единицу вверх. Результат никогда не равен {name}`i`, поэтому он образует обратную операцию
  к сжатию, выполняемому {name}`predAbove`.
  Сравните с {name}`Fin.succAbove` из Mathlib.
-/
noncomputable def SetTheory.Set.Fin.succAbove {n} (i : Fin (n + 1)) (x : Fin n) : Fin (n + 1) :=
  if (x : ℕ) < i then
    Fin_embed _ _ (by sorry) x
  else
    Fin_mk _ ((x : ℕ) + 1) (by sorry)

-- расширение `succAbove i x` никогда не попадает в "дыру" `i`
@[simp]
theorem SetTheory.Set.Fin.succAbove_ne {n} (i : Fin (n + 1)) (x : Fin n) : succAbove i x ≠ i := by sorry

-- `succAbove` восстанавливает `x` после `predAbove` — эти операции взаимно обратны
@[simp]
theorem SetTheory.Set.Fin.succAbove_predAbove {n} (i : Fin (n + 1)) (x : Fin (n + 1)) (h : x ≠ i) : 
    (succAbove i) (predAbove i x h) = x := by sorry

-- `predAbove` восстанавливает `x` после `succAbove` — обратное направление к `succAbove_predAbove`
@[simp]
theorem SetTheory.Set.Fin.predAbove_succAbove {n} (i : Fin (n + 1)) (x : Fin n) : 
    (predAbove i) (succAbove i x) (succAbove_ne i x) = x := by sorry

/-- Упражнение 3.6.12 (i), second part -/
theorem SetTheory.Set.Permutations_ih (n : ℕ) : 
    (Permutations (n + 1)).card = (n + 1) * (Permutations n).card := by
  let S i := (Permutations (n + 1)).specify (fun p ↦ perm_equiv_equiv p (Fin.last n) = i)

  have hSe : ∀ i, S i ≈ Permutations n := by
    intro i
    -- Подсказка: вам могут пригодиться `perm_equiv_equiv`, `Fin.succAbove` и `Fin.predAbove`.
    have equiv : S i ≃ Permutations n := sorry
    use equiv, equiv.injective, equiv.surjective

  -- Подсказка: вам могут пригодиться `card_iUnion_card_disjoint` и `Permutations_finite`.
  sorry

/-- Упражнение 3.6.12 (ii) -/
theorem SetTheory.Set.Permutations_card (n : ℕ) : 
    (Permutations n).card = n.factorial := by sorry

/-- Связи с {name}`Finite` из Mathlib -/
theorem SetTheory.Set.finite_iff_finite {X : Set} : X.finite ↔ Finite X := by
  rw [finite_iff_exists_equiv_fin, finite]
  constructor
  · rintro ⟨n, hn⟩
    use n
    obtain ⟨f, hf⟩ := hn
    have eq := (Equiv.ofBijective f hf).trans (Fin.Fin_equiv_Fin n)
    exact ⟨eq⟩
  rintro ⟨n, hn⟩
  use n
  have eq := hn.some.trans (Fin.Fin_equiv_Fin n).symm
  exact ⟨eq, eq.bijective⟩

/-- Связи с {name}`Set.Finite` из Mathlib -/
theorem SetTheory.Set.finite_iff_set_finite {X : Set} : 
    X.finite ↔ (X : _root_.Set Object).Finite := by
  rw [finite_iff_finite]
  rfl

/-- Связи с {name}`Nat.card` из Mathlib -/
theorem SetTheory.Set.card_eq_nat_card {X : Set} : X.card = Nat.card X := by
  by_cases hf : X.finite
  · by_cases hz : X.card = 0
    · rw [hz]; symm
      have : X = ∅ := empty_of_card_eq_zero hf hz
      rw [this, Nat.card_eq_zero, isEmpty_iff]
      aesop
    symm
    have hc := has_card_card hf
    obtain ⟨f, hf⟩ := hc
    apply Nat.card_eq_of_equiv_fin
    exact (Equiv.ofBijective f hf).trans (Fin.Fin_equiv_Fin X.card)
  simp only [card, hf, ↓reduceDIte]; symm
  rw [Nat.card_eq_zero, ←not_finite_iff_infinite]
  right
  rwa [finite_iff_set_finite] at hf

/-- Связи с {name}`Set.ncard` из Mathlib -/
theorem SetTheory.Set.card_eq_ncard {X : Set} : X.card = (X : _root_.Set Object).ncard := by
  rw [card_eq_nat_card]
  rfl

end Chapter3
