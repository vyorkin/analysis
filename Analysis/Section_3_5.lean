import Mathlib.Tactic
import Analysis.Section_3_1
import Analysis.Section_3_2
import Analysis.Section_3_4

/-!
# Analysis I, раздел 3.5: Декартовы произведения

Я старался сделать перевод максимально точным перефразированием оригинального текста. Когда
приходилось выбирать между более идиоматичным Lean-решением и более точным переводом, я, как
правило, выбирал второе. В частности, местами Lean-код можно было бы "заголфить", сделав его более
элегантным и идиоматичным, но я сознательно этого избегал.

Основные конструкции и результаты этого раздела:

- Упорядоченные пары и n-ки (кортежи).
- Декартовы произведения и n-кратные произведения.
- Конечный выбор.
- Связи с соответствующими понятиями из Mathlib, такими как {name}`Set.pi` и {name}`Set.prod`.

## Советы от прошлых пользователей

Пользователи, прошедшие упражнения этого раздела, могут присылать свои советы для будущих
пользователей в виде PR.

- (Добавьте совет сюда)

-/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

open SetTheory.Set

/-- Определение 3.5.1 (Упорядоченная пара). Здесь для определения {name}`OrderedPair` можно
было бы также использовать {lean}`Object × Object`. -/
@[ext]
structure OrderedPair where
  fst : Object
  snd : Object

#check OrderedPair.ext

/-- Определение 3.5.1 (Упорядоченная пара) -/
@[simp]
theorem OrderedPair.eq (x y x' y' : Object) :
    (⟨ x, y ⟩ : OrderedPair) = (⟨ x', y' ⟩ : OrderedPair) ↔ x = x' ∧ y = y' := by aesop

/-- Вспомогательная лемма для Упражнения 3.5.1 -/
lemma SetTheory.Set.pair_eq_singleton_iff {a b c : Object} : {a, b} = ({c} : Set) ↔
    a = c ∧ b = c := by
  sorry

/-- Упражнение 3.5.1, first part -/
def OrderedPair.toObject : OrderedPair ↪ Object where
  toFun p := ({ (({p.fst} : Set) : Object), (({p.fst, p.snd} : Set) : Object) } : Set)
  inj' := by sorry

instance OrderedPair.inst_coeObject : Coe OrderedPair Object where
  coe := toObject

/--
  Техническая операция, превращающая объект $`x` и множество $`Y` в множество $`{x} × Y`,
  нужная для определения полного декартова произведения
-/
abbrev SetTheory.Set.slice (x : Object) (Y : Set) : Set :=
  Y.replace (P := fun y z ↦ z = (⟨x, y⟩ : OrderedPair)) (by grind)

/-- `z ∈ slice x Y` тогда и только тогда, когда `z = ⟨x, y⟩` для некоторого `y ∈ Y`. -/
@[simp]
theorem SetTheory.Set.mem_slice (x z : Object) (Y : Set) :
    z ∈ (SetTheory.Set.slice x Y) ↔ ∃ y : Y, z = (⟨x, y⟩ : OrderedPair) := replacement_axiom _ _

/-- Определение 3.5.4 (Декартово произведение) -/
abbrev SetTheory.Set.cartesian (X Y : Set) : Set :=
  union (X.replace (P := fun x z ↦ z = slice x Y) (by intro _ _ _ ⟨h1, h2⟩; exact h1.trans h2.symm))

/-- Этот инстанс включает нотацию ×ˢ для декартова произведения. -/
instance SetTheory.Set.inst_SProd : SProd Set Set Set where
  sprod := cartesian

example (X Y : Set) : X ×ˢ Y = SetTheory.Set.cartesian X Y := rfl

/-- Элемент декартова произведения `X ×ˢ Y` — это в точности упорядоченная пара `⟨x, y⟩` с `x ∈ X`, `y ∈ Y`. -/
@[simp]
theorem SetTheory.Set.mem_cartesian (z : Object) (X Y : Set) :
    z ∈ X ×ˢ Y ↔ ∃ x : X, ∃ y : Y, z = (⟨x, y⟩ : OrderedPair) := by
  simp only [SProd.sprod, union_axiom]; constructor
  . intro ⟨ S, hz, hS ⟩; rw [replacement_axiom] at hS; obtain ⟨ x, hx ⟩ := hS
    use x; simp_all
  rintro ⟨ x, y, rfl ⟩; use slice x Y; refine ⟨ by simp, ?_ ⟩
  rw [replacement_axiom]; use x

noncomputable abbrev SetTheory.Set.fst {X Y : Set} (z : X ×ˢ Y) : X :=
  ((mem_cartesian _ _ _).mp z.property).choose

noncomputable abbrev SetTheory.Set.snd {X Y : Set} (z : X ×ˢ Y) : Y :=
  (exists_comm.mp ((mem_cartesian _ _ _).mp z.property)).choose

/-- Любой элемент `z ∈ X ×ˢ Y` восстанавливается из своих проекций: `z = ⟨fst z, snd z⟩`. -/
theorem SetTheory.Set.pair_eq_fst_snd {X Y : Set} (z : X ×ˢ Y) :
    z.val = (⟨ fst z, snd z ⟩ : OrderedPair) := by
  have := (mem_cartesian _ _ _).mp z.property
  obtain ⟨ y, hy : z.val = (⟨ fst z, y ⟩ : OrderedPair)⟩ := this.choose_spec
  obtain ⟨ x, hx : z.val = (⟨ x, snd z ⟩ : OrderedPair)⟩ := (exists_comm.mp this).choose_spec
  simp_all [EmbeddingLike.apply_eq_iff_eq]

/-- Это снабжает {name}`OrderedPair` доказательствами того, что $`x ∈ X` и $`y ∈ Y`. -/
def SetTheory.Set.mk_cartesian {X Y : Set} (x : X) (y : Y) : X ×ˢ Y :=
  ⟨(⟨ x, y ⟩ : OrderedPair), by simp⟩

/-- Первая проекция пары, построенной из `x` и `y`, возвращает `x`. -/
@[simp]
theorem SetTheory.Set.fst_of_mk_cartesian {X Y : Set} (x : X) (y : Y) :
    fst (mk_cartesian x y) = x := by
  let z := mk_cartesian x y; have := (mem_cartesian _ _ _).mp z.property
  obtain ⟨ y', hy : z.val = (⟨ fst z, y' ⟩ : OrderedPair) ⟩ := this.choose_spec
  simp [z, mk_cartesian, Subtype.val_inj] at *; rw [←hy.1]

/-- Вторая проекция пары, построенной из `x` и `y`, возвращает `y`. -/
@[simp]
theorem SetTheory.Set.snd_of_mk_cartesian {X Y : Set} (x : X) (y : Y) :
    snd (mk_cartesian x y) = y := by
  let z := mk_cartesian x y; have := (mem_cartesian _ _ _).mp z.property
  obtain ⟨ x', hx : z.val = (⟨ x', snd z ⟩ : OrderedPair) ⟩ := (exists_comm.mp this).choose_spec
  simp [z, mk_cartesian, Subtype.val_inj] at *; rw [←hx.2]

/-- Сборка пары из её же проекций возвращает исходный элемент: `mk_cartesian (fst z) (snd z) = z`. -/
@[simp]
theorem SetTheory.Set.mk_cartesian_fst_snd_eq {X Y : Set} (z : X ×ˢ Y) :
    (mk_cartesian (fst z) (snd z)) = z := by
  rw [mk_cartesian, Subtype.mk.injEq, pair_eq_fst_snd]

/--
  {given -show}`x : X, y : Y`
  Связи с произведением множеств из Mathlib, которое состоит из Lean-пар вида {lean}`(x, y)`,
  снабжённых доказательством того, что {name}`x` лежит в левом множестве, а {name}`y` — в правом.
  Lean-пары вида {lean}`(x, y)` похожи на наш {name}`OrderedPair`, но более общие.
-/
noncomputable abbrev SetTheory.Set.prod_equiv_prod (X Y : Set) :
    ((X ×ˢ Y) : _root_.Set Object) ≃ (X : _root_.Set Object) ×ˢ (Y : _root_.Set Object) where
  toFun z := ⟨(fst z, snd z), by simp⟩
  invFun z := mk_cartesian ⟨z.val.1, z.prop.1⟩ ⟨z.val.2, z.prop.2⟩
  left_inv _ := by simp
  right_inv _ := by simp

/-- Пример 3.5.5 -/
example : ({1, 2} : Set) ×ˢ ({3, 4, 5} : Set) = ({
  ((mk_cartesian (1 : Nat) (3 : Nat)) : Object),
  ((mk_cartesian (1 : Nat) (4 : Nat)) : Object),
  ((mk_cartesian (1 : Nat) (5 : Nat)) : Object),
  ((mk_cartesian (2 : Nat) (3 : Nat)) : Object),
  ((mk_cartesian (2 : Nat) (4 : Nat)) : Object),
  ((mk_cartesian (2 : Nat) (5 : Nat)) : Object)
} : Set) := by ext; aesop

/-- Пример 3.5.5 / Упражнение 3.6.5. Между {lean}`X ×ˢ Y` и {lean}`Y ×ˢ X` существует биекция. -/
noncomputable abbrev SetTheory.Set.prod_commutator (X Y : Set) : X ×ˢ Y ≃ Y ×ˢ X where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

/-- Пример 3.5.5. Функцию от двух переменных можно рассматривать как функцию от пары. -/
noncomputable abbrev SetTheory.Set.curry_equiv {X Y Z : Set} : (X → Y → Z) ≃ (X ×ˢ Y → Z) where
  toFun f z := f (fst z) (snd z)
  invFun f x y := f (mk_cartesian x y)
  left_inv _ := by ext; simp
  right_inv _ := by simp

/-- Определение 3.5.6. Индексирующее множество {name}`I` играет роль $`{ i : 1 ≤ i ≤ n }` в тексте
    учебника. Некоторые связи между этим понятием и предыдущими понятиями декартова произведения
    и упорядоченной пары см. в Упражнении 3.5.10 ниже. -/
abbrev SetTheory.Set.tuple {I : Set} {X : I → Set} (x : ∀ i, X i) : Object :=
  ((fun i ↦ ⟨ x i, by rw [mem_iUnion]; use i; exact (x i).property ⟩) : I → iUnion I X)

/-- Определение 3.5.6 (indexed product) -/
abbrev SetTheory.Set.iProd {I : Set} (X : I → Set) : Set :=
  ((iUnion I X)^I).specify (fun t ↦ ∃ x : ∀ i, X i, t = tuple x)

/-- Определение 3.5.6 (membership in an indexed product) -/
theorem SetTheory.Set.mem_iProd {I : Set} {X : I → Set} (t : Object) :
    t ∈ iProd X ↔ ∃ x : ∀ i, X i, t = tuple x := by
  simp only [iProd, specification_axiom'']; constructor
  . intro ⟨ ht, x, h ⟩; use x
  intro ⟨ x, hx ⟩
  have h : t ∈ (I.iUnion X)^I := by simp [hx]
  use h, x

/-- Любой кортеж `tuple x`, построенный из значений `x i ∈ X i`, лежит в индексированном произведении `iProd X`. -/
theorem SetTheory.Set.tuple_mem_iProd {I : Set} {X : I → Set} (x : ∀ i, X i) :
    tuple x ∈ iProd X := by rw [mem_iProd]; use x

/-- Построение кортежа инъективно: `tuple x = tuple y` тогда и только тогда, когда `x = y` покомпонентно. -/
@[simp]
theorem SetTheory.Set.tuple_inj {I : Set} {X : I → Set} (x y : ∀ i, X i) :
    tuple x = tuple y ↔ x = y := by sorry

/-- Пример 3.5.8. Между {lean}`(X ×ˢ Y) ×ˢ Z` и {lean}`X ×ˢ (Y ×ˢ Z)` существует биекция. -/
noncomputable abbrev SetTheory.Set.prod_associator (X Y Z : Set) : (X ×ˢ Y) ×ˢ Z ≃ X ×ˢ (Y ×ˢ Z) where
  toFun p := mk_cartesian (fst (fst p)) (mk_cartesian (snd (fst p)) (snd p))
  invFun p := mk_cartesian (mk_cartesian (fst p) (fst (snd p))) (snd (snd p))
  left_inv _ := by simp
  right_inv _ := by simp

/--
  Пример 3.5.10 (a). Подозреваю, что большинству эквивалентностей понадобятся классические
  рассуждения, и они смогут быть определены только неконструктивно, но был бы рад
  контрпримерам.
-/
noncomputable abbrev SetTheory.Set.singleton_iProd_equiv (i : Object) (X : Set) :
    iProd (fun _ : ({i} : Set) ↦ X) ≃ X where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

/-- Пример 3.5.10 (b) -/
abbrev SetTheory.Set.empty_iProd_equiv (X : (∅ : Set) → Set) : iProd X ≃ Unit where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

/-- Пример 3.5.10 (c) -/
noncomputable abbrev SetTheory.Set.iProd_of_const_equiv (I : Set) (X : Set) :
    iProd (fun _ : I ↦ X) ≃ (I → X) where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

/-- Пример 3.5.10 (d) -/
noncomputable abbrev SetTheory.Set.iProd_equiv_prod (X : ({0,1} : Set) → Set) :
    iProd X ≃ (X ⟨ 0, by simp ⟩) ×ˢ (X ⟨ 1, by simp ⟩) where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

/-- Пример 3.5.10 (e) -/
noncomputable abbrev SetTheory.Set.iProd_equiv_prod_triple (X : ({0,1,2} : Set) → Set) :
    iProd X ≃ (X ⟨ 0, by simp ⟩) ×ˢ (X ⟨ 1, by simp ⟩) ×ˢ (X ⟨ 2, by simp ⟩) where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

/-- Связи с {name}`Set.pi` из Mathlib -/
noncomputable abbrev SetTheory.Set.iProd_equiv_pi (I : Set) (X : I → Set) :
    iProd X ≃ Set.pi .univ (fun i : I ↦ ((X i) : _root_.Set Object)) where
  toFun t := ⟨fun i ↦ ((mem_iProd _).mp t.property).choose i, by simp⟩
  invFun x :=
    ⟨tuple fun i ↦ ⟨x.val i, by have := x.property i; simpa⟩, by apply tuple_mem_iProd⟩
  left_inv t := by ext; rw [((mem_iProd _).mp t.property).choose_spec, tuple_inj]
  right_inv x := by
    ext; dsimp
    generalize_proofs _ h
    rw [←(tuple_inj _ _).mp h.choose_spec]


/-
замечание: между этими эквивалентностями существуют и дополнительные соотношения, но это уже
уводит в область теории категорий высшего порядка, которую мы здесь развивать не будем.
-/

/--
  Здесь мы строим аналог типов {lean}`Fin n` из Mathlib в рамках теории множеств Главы 3,
  с базовым API.
-/
abbrev SetTheory.Set.Fin (n : ℕ) : Set := nat.specify (fun m ↦ (m : ℕ) < n)

/-- `x ∈ Fin n` тогда и только тогда, когда `x` — это некоторое натуральное `m < n`. -/
theorem SetTheory.Set.mem_Fin (n : ℕ) (x : Object) : x ∈ Fin n ↔ ∃ m, m < n ∧ x = m := by
  rw [specification_axiom'']; constructor
  . intro ⟨ h1, h2 ⟩; use ↑(⟨ x, h1 ⟩ : nat); simp [h2]
  intro ⟨ m, hm, h ⟩
  use (by rw [h, ←Object.ofnat_eq]; exact (m : nat).property)
  grind [Object.ofnat_eq''']

abbrev SetTheory.Set.Fin_mk (n m : ℕ) (h : m < n) : Fin n := ⟨ m, by rw [mem_Fin]; use m ⟩

/-- Любой элемент `x : Fin n` представим как `Fin_mk n m h` для некоторого `m < n`. -/
theorem SetTheory.Set.mem_Fin' {n : ℕ} (x : Fin n) : ∃ m, ∃ h : m < n, x = Fin_mk n m h := by
  choose m hm this using (mem_Fin _ _).mp x.property; use m, hm
  simp [Fin_mk, ←Subtype.val_inj, this]

@[coe]
noncomputable abbrev SetTheory.Set.Fin.toNat {n : ℕ} (i : Fin n) : ℕ := (mem_Fin' i).choose

noncomputable instance SetTheory.Set.Fin.inst_coeNat {n : ℕ} : CoeOut (Fin n) ℕ where
  coe := toNat

/-- `toNat` даёт то самое `m < n`, для которого `i = Fin_mk n m h` — обоснование корректности приведения `Fin n → ℕ`. -/
theorem SetTheory.Set.Fin.toNat_spec {n : ℕ} (i : Fin n) :
    ∃ h : i < n, i = Fin_mk n i h := (mem_Fin' i).choose_spec

/-- Приведение `i : Fin n` к `ℕ` действительно даёт число, меньшее `n`. -/
theorem SetTheory.Set.Fin.toNat_lt {n : ℕ} (i : Fin n) : i < n := (toNat_spec i).choose

/-- Приведение `i : Fin n` сначала к `ℕ`, а затем к `Object`, совпадает с прямым приведением `i` к `Object`. -/
@[simp]
theorem SetTheory.Set.Fin.coe_toNat {n : ℕ} (i : Fin n) : ((i : ℕ) : Object) = (i : Object) := by
  set j := (i : ℕ); obtain ⟨ h, h' : i = Fin_mk n j h ⟩ := toNat_spec i; rw [h']

/-- Приведение `Fin n → ℕ` инъективно: элементы `Fin n` равны тогда и только тогда, когда равны их числовые значения. -/
@[simp low]
lemma SetTheory.Set.Fin.coe_inj {n : ℕ} {i j : Fin n} : i = j ↔ (i : ℕ) = (j : ℕ) := by
  constructor
  · simp_all
  obtain ⟨_, hi⟩ := toNat_spec i
  obtain ⟨_, hj⟩ := toNat_spec j
  grind

/-- `i : Fin n` совпадает как `Object` с числом `j : ℕ` тогда и только тогда, когда `i = j` в `Fin n`. -/
@[simp]
theorem SetTheory.Set.Fin.coe_eq_iff {n : ℕ} (i : Fin n) {j : ℕ} : (i : Object) = (j : Object) ↔ i = j := by
  constructor
  · intro h
    rw [Subtype.coe_eq_iff] at h
    obtain ⟨_, rfl⟩ := h
    simp [←Object.natCast_inj]
  aesop

/-- Если `i : Fin n` также лежит в `Fin m`, то его числовое значение не меняется при этом повторном вложении. -/
@[simp]
theorem SetTheory.Set.Fin.coe_eq_iff' {n m : ℕ} (i : Fin n) (hi : ↑i ∈ Fin m) : ((⟨i, hi⟩ : Fin m) : ℕ) = (i : ℕ) := by
  obtain ⟨val, property⟩ := i
  simp only [toNat, Subtype.mk.injEq, exists_prop]
  generalize_proofs h1 h2
  suffices : (h1.choose : Object) = h2.choose
  · aesop
  have := h1.choose_spec
  have := h2.choose_spec
  grind

/-- Числовое значение `Fin_mk n m h` — это как раз `m`. -/
@[simp]
theorem SetTheory.Set.Fin.toNat_mk {n : ℕ} (m : ℕ) (h : m < n) : (Fin_mk n m h : ℕ) = m := by
  have := coe_toNat (Fin_mk n m h)
  rwa [Object.natCast_inj] at this

abbrev SetTheory.Set.Fin_embed (n N : ℕ) (h : n ≤ N) (i : Fin n) : Fin N := ⟨ i.val, by
  have := i.property; rw [mem_Fin] at *; grind
⟩

/-- Связи с {lean}`Fin n` из Mathlib -/
noncomputable abbrev SetTheory.Set.Fin.Fin_equiv_Fin (n : ℕ) : Fin n ≃ _root_.Fin n where
  toFun m := _root_.Fin.mk m (toNat_lt m)
  invFun m := Fin_mk n m.val m.isLt
  left_inv m := (toNat_spec m).2.symm
  right_inv m := by simp

/-- Лемма 3.5.11 (конечный выбор) -/
theorem SetTheory.Set.finite_choice {n : ℕ} {X : Fin n → Set} (h : ∀ i, X i ≠ ∅) : iProd X ≠ ∅ := by
  -- Это доказательство в целом следует тексту учебника
  -- (хотя удобнее вести индукцию от 0, а не от 1)
  induction' n with n hn
  . have : Fin 0 = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      grind [specification_axiom'']
    have empty (i : Fin 0) : X i := False.elim (by rw [this] at i; exact not_mem_empty i i.property)
    apply nonempty_of_inhabited (x := tuple empty); rw [mem_iProd]; use empty
  set X' : Fin n → Set := fun i ↦ X (Fin_embed n (n+1) (by linarith) i)
  have hX' (i : Fin n) : X' i ≠ ∅ := h _
  choose x'_obj hx' using nonempty_def (hn hX')
  rw [mem_iProd] at hx'; obtain ⟨ x', rfl ⟩ := hx'
  set last : Fin (n+1) := Fin_mk (n+1) n (by linarith)
  choose a ha using nonempty_def (h last)
  have x : ∀ i, X i := fun i =>
    if h : i = n then
      have : i = last := by ext; simpa [←Fin.coe_toNat, last]
      ⟨a, by grind⟩
    else
      have : i < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Fin.toNat_lt i)) h
      let i' := Fin_mk n i this
      have : X i = X' i' := by simp [X', i', Fin_embed]
      ⟨x' i', by grind⟩
  exact nonempty_of_inhabited (tuple_mem_iProd x)

/-- Упражнение 3.5.1, вторая часть (требует аксиому регулярности) -/
abbrev OrderedPair.toObject' : OrderedPair ↪ Object where
  toFun p := ({ p.fst, (({p.fst, p.snd} : Set) : Object) } : Set)
  inj' := by sorry

/-- Альтернативное определение кортежа, используемое в Упражнении 3.5.2 -/
structure SetTheory.Set.Tuple (n : ℕ) where
  X : Set
  x : Fin n → X
  surj : Function.Surjective x

/--
  Пользовательская лемма экстенсиональности для Упражнения 3.5.2.
  Если разместить {attr}`@[ext]` прямо на структуре, это сгенерировало бы лемму, требующую
  доказательства {lit}`t.x = t'.x`, но эти функции имеют разные типы, когда {lean}`t.X ≠ t'.X`.
  Данная лемма как раз и решает эту часть.
-/
@[ext]
lemma SetTheory.Set.Tuple.ext {n : ℕ} {t t' : Tuple n}
    (hX : t.X = t'.X)
    (hx : ∀ n : Fin n, ((t.x n) : Object) = ((t'.x n) : Object)) :
    t = t' := by
  have ⟨_, _, _⟩ := t
  have ⟨_, _, _⟩ := t'
  subst hX
  congr
  ext
  grind

/-- Упражнение 3.5.2 -/
theorem SetTheory.Set.Tuple.eq {n : ℕ} (t t' : Tuple n) :
    t = t' ↔ ∀ n : Fin n, ((t.x n) : Object) = ((t'.x n) : Object) := by sorry

noncomputable abbrev SetTheory.Set.iProd_equiv_tuples (n : ℕ) (X : Fin n → Set) :
    iProd X ≃ { t : Tuple n // ∀ i, (t.x i : Object) ∈ X i } where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

/--
  Упражнение 3.5.3.

  Суть здесь в том, чтобы избегать прямых переписываний
  (которые делают все эти утверждения тривиальными),
  а вместо этого использовать {name}`OrderedPair.eq` или {name}`SetTheory.Set.tuple_inj`
-/
theorem OrderedPair.refl (p : OrderedPair) : p = p := by sorry

/-- Равенство упорядоченных пар симметрично: `p = q` тогда и только тогда, когда `q = p`. -/
theorem OrderedPair.symm (p q : OrderedPair) : p = q ↔ q = p := by sorry

/-- Равенство упорядоченных пар транзитивно. -/
theorem OrderedPair.trans {p q r : OrderedPair} (hpq : p=q) (hqr : q=r) : p=r := by sorry

/-- Равенство кортежей рефлексивно. -/
theorem SetTheory.Set.tuple_refl {I : Set} {X : I → Set} (a : ∀ i, X i) :
    tuple a = tuple a := by sorry

/-- Равенство кортежей симметрично: `tuple a = tuple b` тогда и только тогда, когда `tuple b = tuple a`. -/
theorem SetTheory.Set.tuple_symm {I : Set} {X : I → Set} (a b : ∀ i, X i) :
    tuple a = tuple b ↔ tuple b = tuple a := by sorry

/-- Равенство кортежей транзитивно. -/
theorem SetTheory.Set.tuple_trans {I : Set} {X : I → Set} {a b c : ∀ i, X i}
  (hab : tuple a = tuple b) (hbc : tuple b = tuple c) :
    tuple a = tuple c := by sorry

/-- Упражнение 3.5.4 (a) -/
theorem SetTheory.Set.prod_union (A B C : Set) : A ×ˢ (B ∪ C) = (A ×ˢ B) ∪ (A ×ˢ C) := by sorry

/-- Упражнение 3.5.4 (b) -/
theorem SetTheory.Set.prod_inter (A B C : Set) : A ×ˢ (B ∩ C) = (A ×ˢ B) ∩ (A ×ˢ C) := by sorry

/-- Упражнение 3.5.4 (c) -/
theorem SetTheory.Set.prod_diff (A B C : Set) : A ×ˢ (B \ C) = (A ×ˢ B) \ (A ×ˢ C) := by sorry

/-- Упражнение 3.5.4 (d) -/
theorem SetTheory.Set.union_prod (A B C : Set) : (A ∪ B) ×ˢ C = (A ×ˢ C) ∪ (B ×ˢ C) := by sorry

/-- Упражнение 3.5.4 (e) -/
theorem SetTheory.Set.inter_prod (A B C : Set) : (A ∩ B) ×ˢ C = (A ×ˢ C) ∩ (B ×ˢ C) := by sorry

/-- Упражнение 3.5.4 (f) -/
theorem SetTheory.Set.diff_prod (A B C : Set) : (A \ B) ×ˢ C = (A ×ˢ C) \ (B ×ˢ C) := by sorry

/-- Упражнение 3.5.5 (a) -/
theorem SetTheory.Set.inter_of_prod (A B C D : Set) :
    (A ×ˢ B) ∩ (C ×ˢ D) = (A ∩ C) ×ˢ (B ∩ D) := by sorry

/-- Упражнение 3.5.5 (b) -/
def SetTheory.Set.union_of_prod :
  Decidable (∀ (A B C D : Set), (A ×ˢ B) ∪ (C ×ˢ D) = (A ∪ C) ×ˢ (B ∪ D)) := by
  -- первой строкой этой конструкции должно быть `apply isTrue` или `apply isFalse`.
  sorry

/-- Упражнение 3.5.5 (c) -/
def SetTheory.Set.diff_of_prod :
  Decidable (∀ (A B C D : Set), (A ×ˢ B) \ (C ×ˢ D) = (A \ C) ×ˢ (B \ D)) := by
  -- первой строкой этой конструкции должно быть `apply isTrue` или `apply isFalse`.
  sorry

/--
  Упражнение 3.5.6.
-/
theorem SetTheory.Set.prod_subset_prod {A B C D : Set}
  (hA : A ≠ ∅) (hB : B ≠ ∅) (hC : C ≠ ∅) (hD : D ≠ ∅) :
    A ×ˢ B ⊆ C ×ˢ D ↔ A ⊆ C ∧ B ⊆ D := by sorry

def SetTheory.Set.prod_subset_prod' :
  Decidable (∀ (A B C D : Set), A ×ˢ B ⊆ C ×ˢ D ↔ A ⊆ C ∧ B ⊆ D) := by
  -- первой строкой этой конструкции должно быть `apply isTrue` или `apply isFalse`.
  sorry

/-- Упражнение 3.5.7 -/
theorem SetTheory.Set.direct_sum {X Y Z : Set} (f : Z → X) (g : Z → Y) :
    ∃! h : Z → X ×ˢ Y, fst ∘ h = f ∧ snd ∘ h = g := by sorry

/-- Упражнение 3.5.8 -/
@[simp]
theorem SetTheory.Set.iProd_empty_iff {n : ℕ} {X : Fin n → Set} :
    iProd X = ∅ ↔ ∃ i, X i = ∅ := by sorry

/-- Упражнение 3.5.9 -/
theorem SetTheory.Set.iUnion_inter_iUnion {I J : Set} (A : I → Set) (B : J → Set) :
    (iUnion I A) ∩ (iUnion J B) = iUnion (I ×ˢ J) (fun p ↦ (A (fst p)) ∩ (B (snd p))) := by sorry

abbrev SetTheory.Set.graph {X Y : Set} (f : X → Y) : Set :=
  (X ×ˢ Y).specify (fun p ↦ (f (fst p) = snd p))

/-- Упражнение 3.5.10 -/
theorem SetTheory.Set.graph_inj {X Y : Set} (f f' : X → Y) :
    graph f = graph f' ↔ f = f' := by sorry

/-- Множество `G ⊆ X ×ˢ Y`, для каждого `x` содержащее ровно одну пару `⟨x, y⟩`, — это в точности
    график `graph f` некоторой единственной функции `f : X → Y`. -/
theorem SetTheory.Set.is_graph {X Y G : Set} (hG : G ⊆ X ×ˢ Y)
  (hvert : ∀ x : X, ∃! y : Y, ((⟨x,y⟩ : OrderedPair) : Object) ∈ G) :
    ∃! f : X → Y, G = graph f := by sorry

/--
  Упражнение 3.5.11. Это тривиально следует из {name}`SetTheory.Set.powerset_axiom`, но суть
  упражнения в том, чтобы вывести это вместо этого из {name}`SetTheory.Set.exists_powerset`.
-/
theorem SetTheory.Set.powerset_axiom' (X Y : Set) :
    ∃! S : Set, ∀(F : Object), F ∈ S ↔ ∃ f : Y → X, f = F := sorry

/-- Упражнение 3.5.12, с учётом опечаток с сайта -/
theorem SetTheory.Set.recursion (X : Set) (f : nat → X → X) (c : X) :
    ∃! a : nat → X, a 0 = c ∧ ∀ n, a (n + 1 : ℕ) = f n (a n) := by sorry

/-- Упражнение 3.5.13 -/
theorem SetTheory.Set.nat_unique (nat' : Set) (zero : nat') (succ : nat' → nat')
  (succ_ne : ∀ n : nat', succ n ≠ zero) (succ_of_ne : ∀ n m : nat', n ≠ m → succ n ≠ succ m)
  (ind : ∀ P : nat' → Prop, P zero → (∀ n, P n → P (succ n)) → ∀ n, P n) :
    ∃! f : nat → nat', Function.Bijective f ∧ f 0 = zero
    ∧ ∀ (n : nat) (n' : nat'), f n = n' ↔ f (n+1 : ℕ) = succ n' := by
  have nat_coe_eq {m : nat} {n} : (m : ℕ) = n → m = n := by aesop
  have nat_coe_eq_zero {m : nat} : (m : ℕ) = 0 → m = 0 := nat_coe_eq
  obtain ⟨f, hf⟩ := recursion nat' sorry sorry
  apply existsUnique_of_exists_of_unique
  · use f
    constructor
    · constructor
      · intro x1 x2 heq
        induction' hx1 : (x1 : ℕ) with i ih generalizing x1 x2
        · sorry
        sorry
      sorry
    sorry
  sorry


end Chapter3
