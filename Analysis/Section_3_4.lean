import Mathlib.Tactic
import Analysis.Section_3_1

/-!
# Analysis I, раздел 3.4: Образы и прообразы

Я старался сделать перевод максимально точным перефразированием оригинального текста. Когда
приходилось выбирать между более идиоматичным Lean-решением и более точным переводом, я, как
правило, выбирал второе. В частности, местами Lean-код можно было бы "заголфить", сделав его более
элегантным и идиоматичным, но я сознательно этого избегал.

Основные конструкции и результаты этого раздела:

- Образы и прообразы функций (из Mathlib) в рамках теории множеств из раздела 3.1.
  (Функции из раздела 3.3 теперь устарели и далее использоваться не будут.)
- Связь с понятиями образа {syntax term}`f '' S` и прообраза {syntax term}`f ⁻¹' S` из Mathlib.

## Советы от прошлых пользователей

Пользователи, прошедшие упражнения этого раздела, могут присылать свои советы для будущих
пользователей в виде PR.

- (Добавьте совет сюда)

-/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

/-- Definition 3.4.1. Интересно, что определение не требует, чтобы {lean}`S` было подмножеством {lean}`X`. -/
abbrev SetTheory.Set.image {X Y : Set} (f : X → Y) (S : Set) : Set :=
  X.replace (P := fun x y ↦ f x = y ∧ x.val ∈ S) (by simp_all)

/-- Definition 3.4.1 -/
theorem SetTheory.Set.mem_image {X Y : Set} (f : X → Y) (S : Set) (y : Object) :
  y ∈ image f S ↔ ∃ x : X, x.val ∈ S ∧ f x = y := by
    grind [replacement_axiom]

/-- Альтернативное определение образа через аксиому спецификации -/
theorem SetTheory.Set.image_eq_specify {X Y : Set} (f : X → Y) (S : Set) :
  image f S = Y.specify (fun y ↦ ∃ x : X, x.val ∈ S ∧ f x = y) := by sorry

/--
  Связь с понятием образа из Mathlib. Обратите внимание на необходимость приведения
  {name}`Subtype.val`, чтобы согласовать типы.
-/
theorem SetTheory.Set.image_eq_image {X Y : Set} (f : X → Y) (S : Set) :
  (image f S : _root_.Set Object) = Subtype.val '' (f '' {x | x.val ∈ S}) := by
    ext
    simp
    grind

theorem SetTheory.Set.image_in_codomain {X Y : Set} (f : X → Y) (S : Set) :
  image f S ⊆ Y := by
    intro _ h
    rw [mem_image] at h
    grind

/-- Example 3.4.2 -/
abbrev f_3_4_2 : nat → nat := fun n ↦ (2*n : ℕ)

theorem SetTheory.Set.image_f_3_4_2 : image f_3_4_2 {1,2,3} = {2,4,6} := by
  ext; simp only [mem_image, mem_triple, f_3_4_2]
  constructor
  · rintro ⟨_, (_ | _ | _), rfl⟩ <;> simp_all
  · rintro (_ | _ | _)
    map_tacs [use 1; use 2; use 3]
    all_goals simp_all

/-- Example 3.4.3 записан с использованием понятия образа из Mathlib. -/
example : (fun n : ℤ ↦ n^2) '' {-1,0,1,2} = {0,1,4} := by aesop

theorem SetTheory.Set.mem_image_of_eval {X Y : Set} (f : X → Y) (S : Set) (x : X) :
    x.val ∈ S → (f x).val ∈ image f S := by sorry

theorem SetTheory.Set.mem_image_of_eval_counter :
    ∃ (X Y : Set) (f : X → Y) (S : Set) (x : X), ¬((f x).val ∈ image f S → x.val ∈ S) := by sorry

/--
  Definition 3.4.4 (прообразы).
  Здесь также не требуется, чтобы {lean}`U` было подмножеством {lean}`Y`.
-/
abbrev SetTheory.Set.preimage {X Y : Set} (f : X → Y) (U : Set) : Set := X.specify (P := fun x ↦ (f x).val ∈ U)

@[simp]
theorem SetTheory.Set.mem_preimage {X Y : Set}
  (f : X → Y) (U : Set) (x : X) :
    x.val ∈ preimage f U ↔ (f x).val ∈ U := by rw [specification_axiom']

/--
  Версия {name}`mem_preimage`, не требующая, чтобы {lean}`x` имел тип {lean}`X`.
-/
theorem SetTheory.Set.mem_preimage' {X Y : Set} (f : X → Y) (U : Set) (x : Object) :
  x ∈ preimage f U ↔ ∃ x' : X, x'.val = x ∧ (f x').val ∈ U := by
    constructor
    . intro h
      by_cases hx : x ∈ X
      . use ⟨x, hx⟩
        have := mem_preimage f U ⟨ _, hx ⟩
        simp_all
      . grind [specification_axiom]
    . rintro ⟨x', rfl, hfx'⟩
      rwa [mem_preimage]

/-- Связь с понятием прообраза из Mathlib. -/
theorem SetTheory.Set.preimage_eq {X Y : Set} (f : X → Y) (U : Set) :
  ((preimage f U) : _root_.Set Object) = Subtype.val '' (f⁻¹' {y | y.val ∈ U}) := by
    ext; simp

theorem SetTheory.Set.preimage_in_domain {X Y : Set} (f : X → Y) (U : Set) :
    (preimage f U) ⊆ X := by intro _ _; aesop

/-- Example 3.4.6 -/
theorem SetTheory.Set.preimage_f_3_4_2 : preimage f_3_4_2 {2,4,6} = {1,2,3} := by
  ext
  simp only [mem_preimage', mem_triple, f_3_4_2]
  constructor
  · rintro ⟨x, rfl, (_ | _ | _)⟩ <;> simp_all <;> omega
  · rintro (rfl | rfl | rfl)
    map_tacs [use 1; use 2; use 3]
    all_goals simp

theorem SetTheory.Set.image_preimage_f_3_4_2 :
  image f_3_4_2 (preimage f_3_4_2 {1,2,3}) ≠ {1,2,3} := by sorry

/-- Example 3.4.7 (с использованием понятия прообраза из Mathlib) -/
example : (fun n : ℤ ↦ n^2) ⁻¹' {0,1,4} = {-2,-1,0,1,2} := by
  ext; refine ⟨ ?_, by aesop ⟩; rintro (_ | _ | h)
  on_goal 3 => have : 2 ^ 2 = (4 : ℤ) := (by norm_num); rw [←h, sq_eq_sq_iff_eq_or_eq_neg] at this
  all_goals aesop

example : (fun n : ℤ ↦ n^2) ⁻¹' ((fun n : ℤ ↦ n^2) '' {-1,0,1,2}) ≠ {-1,0,1,2} := by sorry

instance SetTheory.Set.inst_pow : Pow Set Set where
  pow := pow

@[coe]
def SetTheory.Set.coe_of_fun {X Y : Set} (f : X → Y) : Object := function_to_object X Y f

/-- Это приведение должно быть {name}`CoeOut`, а не
{name}`Coe`, потому что входной тип {lean}`X → Y` содержит
параметры, отсутствующие в выходном типе {name}`Object` -/
instance SetTheory.Set.inst_coe_of_fun {X Y : Set} : CoeOut (X → Y) Object where
  coe := coe_of_fun

@[simp]
theorem SetTheory.Set.coe_of_fun_inj {X Y : Set} (f g : X → Y) : (f : Object) = (g : Object) ↔ f = g := by
  simp [coe_of_fun]

/-- Axiom 3.11 (Аксиома степенного множества) -/
@[simp]
theorem SetTheory.Set.powerset_axiom {X Y : Set} (F : Object) :
    F ∈ (X ^ Y) ↔ ∃ f : Y → X, f = F := SetTheory.powerset_axiom X Y F

/-- Example 3.4.9 -/
abbrev f_3_4_9_a : ({4,7} : Set) → ({0,1} : Set) := fun x ↦ ⟨ 0, by simp ⟩

open Classical in
noncomputable abbrev f_3_4_9_b : ({4,7} : Set) → ({0,1} : Set) :=
  fun x ↦ if x.val = 4 then ⟨ 0, by simp ⟩ else ⟨ 1, by simp ⟩

open Classical in
noncomputable abbrev f_3_4_9_c : ({4,7} : Set) → ({0,1} : Set) :=
  fun x ↦ if x.val = 4 then ⟨ 1, by simp ⟩ else ⟨ 0, by simp ⟩

abbrev f_3_4_9_d : ({4,7} : Set) → ({0,1} : Set) := fun x ↦ ⟨ 1, by simp ⟩

theorem SetTheory.Set.example_3_4_9 (F : Object) :
    F ∈ ({0,1} : Set) ^ ({4,7} : Set) ↔ F = f_3_4_9_a
    ∨ F = f_3_4_9_b ∨ F = f_3_4_9_c ∨ F = f_3_4_9_d := by
  rw [powerset_axiom]
  refine ⟨?_, by aesop ⟩
  rintro ⟨f, rfl⟩
  have h1 := (f ⟨4, by simp⟩).property
  have h2 := (f ⟨7, by simp⟩).property
  simp [coe_of_fun_inj] at *
  obtain _ | _ := h1 <;> obtain _ | _ := h2
  map_tacs [left; (right;left); (right;right;left); (right;right;right)]
  all_goals ext ⟨_, hx⟩; simp at hx; grind

/-- Exercise 3.4.6 (i). Здесь нужно дать подходящее определение степенного множества. -/
def SetTheory.Set.powerset (X : Set) : Set :=
  (({0,1} ^ X) : Set).replace (P := sorry) (by sorry)

open Classical in
/-- Exercise 3.4.6 (i) -/
@[simp]
theorem SetTheory.Set.mem_powerset {X : Set} (x : Object) :
    x ∈ powerset X ↔ ∃ Y : Set, x = Y ∧ Y ⊆ X := by sorry

/-- Lemma 3.4.10 -/
theorem SetTheory.Set.exists_powerset (X : Set) :
   ∃ (Z : Set), ∀ x, x ∈ Z ↔ ∃ Y : Set, x = Y ∧ Y ⊆ X := by
  use powerset X; apply mem_powerset

/- Как отмечено в списке опечаток, Exercise 3.4.6 (ii) заменено на Exercise 3.5.11. -/

/-- Remark 3.4.11 -/
theorem SetTheory.Set.powerset_of_triple (a b c x : Object) :
    x ∈ powerset {a,b,c}
    ↔ x = (∅ : Set)
    ∨ x = ({a} : Set)
    ∨ x = ({b} : Set)
    ∨ x = ({c} : Set)
    ∨ x = ({a,b} : Set)
    ∨ x = ({a,c} : Set)
    ∨ x = ({b,c} : Set)
    ∨ x = ({a,b,c} : Set) := by
  simp only [mem_powerset, subset_def, mem_triple]
  refine ⟨ ?_, by aesop ⟩
  rintro ⟨Y, rfl, hY⟩; by_cases a ∈ Y <;> by_cases b ∈ Y <;> by_cases c ∈ Y
  on_goal 8 => left
  on_goal 4 => right; left
  on_goal 6 => right; right; left
  on_goal 7 => right; right; right; left
  on_goal 2 => right; right; right; right; left
  on_goal 3 => right; right; right; right; right; left
  on_goal 5 => right; right; right; right; right; right; left
  on_goal 1 => right; right; right; right; right; right; right
  all_goals congr; ext; simp; grind

/-- Axiom 3.12 (Объединение) -/
theorem SetTheory.Set.union_axiom (A : Set) (x : Object) :
    x ∈ union A ↔ ∃ (S : Set), x ∈ S ∧ (S : Object) ∈ A := SetTheory.union_axiom A x

/-- Example 3.4.12 -/
theorem SetTheory.Set.example_3_4_12 :
    union { (({2,3} : Set) : Object), (({3,4} : Set) : Object), (({4,5} : Set) : Object) } = {2,3,4,5} := by
  sorry

/-- Связь с объединением из Mathlib -/
theorem SetTheory.Set.union_eq (A : Set) :
    (union A : _root_.Set Object) =
    ⋃₀ { S : _root_.Set Object | ∃ S' : Set, S = S' ∧ (S' : Object) ∈ A } := by
  ext; simp [union_axiom, Set.mem_sUnion]; aesop

/-- Индексированное объединение -/
abbrev SetTheory.Set.iUnion (I : Set) (A : I → Set) : Set :=
  union (I.replace (P := fun α S ↦ S = A α) (by intro _ _ _ ⟨h1, h2⟩; exact h1.trans h2.symm))

theorem SetTheory.Set.mem_iUnion {I : Set} (A : I → Set) (x : Object) :
    x ∈ iUnion I A ↔ ∃ α : I, x ∈ A α := by
  rw [union_axiom]; constructor
  . simp_all [replacement_axiom]
  grind [replacement_axiom]

open Classical in
noncomputable abbrev SetTheory.Set.index_example : ({1,2,3} : Set) → Set :=
  fun i ↦ if i.val = 1 then {2,3} else if i.val = 2 then {3,4} else {4,5}

theorem SetTheory.Set.iUnion_example : iUnion {1,2,3} index_example = {2,3,4,5} := by
  apply ext; intros; simp [mem_iUnion, index_example, Insert.insert]
  refine ⟨ by aesop, ?_ ⟩; rintro (_ | _ | _); map_tacs [use 1; use 2; use 3]
  all_goals aesop

/-- Связь с индексированным объединением из Mathlib -/
theorem SetTheory.Set.iUnion_eq (I : Set) (A : I → Set) :
    (iUnion I A : _root_.Set Object) = ⋃ α, (A α : _root_.Set Object) := by
  ext; simp [mem_iUnion]

theorem SetTheory.Set.iUnion_of_empty (A : (∅ : Set) → Set) : iUnion (∅ : Set) A = ∅ := by sorry

/-- Индексированное пересечение -/
noncomputable abbrev SetTheory.Set.nonempty_choose {I : Set} (hI : I ≠ ∅) : I :=
  ⟨(nonempty_def hI).choose, (nonempty_def hI).choose_spec⟩

abbrev SetTheory.Set.iInter' (I : Set) (β : I) (A : I → Set) : Set :=
  (A β).specify (P := fun x ↦ ∀ α : I, x.val ∈ A α)

noncomputable abbrev SetTheory.Set.iInter (I : Set) (hI : I ≠ ∅) (A : I → Set) : Set :=
  iInter' I (nonempty_choose hI) A

theorem SetTheory.Set.mem_iInter {I : Set} (hI : I ≠ ∅) (A : I → Set) (x : Object) :
    x ∈ iInter I hI A ↔ ∀ α : I, x ∈ A α := by
  sorry

/-- Exercise 3.4.1 -/
theorem SetTheory.Set.preimage_eq_image_of_inv {X Y V : Set} (f : X → Y) (f_inv : Y → X)
  (hf : Function.LeftInverse f_inv f ∧ Function.RightInverse f_inv f) (hV : V ⊆ Y) :
    image f_inv V = preimage f V := by sorry

/- Exercise 3.4.2.  Сформулируйте и докажите утверждение, связывающее `preimage f (image f S)` и `S`. -/
-- theorem SetTheory.Set.preimage_of_image {X Y:Set} (f:X → Y) (S: Set) (hS: S ⊆ X) : sorry := by sorry

/- Exercise 3.4.2.  Сформулируйте и докажите утверждение, связывающее `image f (preimage f U)` и `U`.
Интересно, что здесь не требуется, чтобы U было подмножеством Y. -/
-- theorem SetTheory.Set.image_of_preimage {X Y:Set} (f:X → Y) (U: Set) : sorry := by sorry

/- Exercise 3.4.2.  Сформулируйте и докажите утверждение, связывающее `preimage f (image f (preimage f U))` и `preimage f U`.
Интересно, что здесь не требуется, чтобы U было подмножеством Y. -/
-- theorem SetTheory.Set.preimage_of_image_of_preimage {X Y:Set} (f:X → Y) (U: Set) : sorry := by sorry

/--
  Exercise 3.4.3.
-/
theorem SetTheory.Set.image_of_inter {X Y : Set} (f : X → Y) (A B : Set) :
    image f (A ∩ B) ⊆ (image f A) ∩ (image f B) := by sorry

theorem SetTheory.Set.image_of_diff {X Y : Set} (f : X → Y) (A B : Set) :
    (image f A) \ (image f B) ⊆ image f (A \ B) := by sorry

theorem SetTheory.Set.image_of_union {X Y : Set} (f : X → Y) (A B : Set) :
    image f (A ∪ B) = (image f A) ∪ (image f B) := by sorry

def SetTheory.Set.image_of_inter' : Decidable (∀ X Y : Set, ∀ f : X → Y, ∀ A B : Set, image f (A ∩ B) = (image f A) ∩ (image f B)) := by
  -- первой строкой этой конструкции должно быть либо `apply isTrue`, либо `apply isFalse`
  sorry

def SetTheory.Set.image_of_diff' : Decidable (∀ X Y : Set, ∀ f : X → Y, ∀ A B : Set, image f (A \ B) = (image f A) \ (image f B)) := by
  -- первой строкой этой конструкции должно быть либо `apply isTrue`, либо `apply isFalse`
  sorry

/-- Exercise 3.4.4 -/
theorem SetTheory.Set.preimage_of_inter {X Y : Set} (f : X → Y) (A B : Set) :
    preimage f (A ∩ B) = (preimage f A) ∩ (preimage f B) := by sorry

theorem SetTheory.Set.preimage_of_union {X Y : Set} (f : X → Y) (A B : Set) :
    preimage f (A ∪ B) = (preimage f A) ∪ (preimage f B) := by sorry

theorem SetTheory.Set.preimage_of_diff {X Y : Set} (f : X → Y) (A B : Set) :
    preimage f (A \ B) = (preimage f A) \ (preimage f B)  := by sorry

/-- Exercise 3.4.5 -/
theorem SetTheory.Set.image_preimage_of_surj {X Y : Set} (f : X → Y) :
    (∀ S, S ⊆ Y → image f (preimage f S) = S) ↔ Function.Surjective f := by sorry

/-- Exercise 3.4.5 -/
theorem SetTheory.Set.preimage_image_of_inj {X Y : Set} (f : X → Y) :
    (∀ S, S ⊆ X → preimage f (image f S) = S) ↔ Function.Injective f := by sorry

/-- Вспомогательная лемма для Exercise 3.4.7. -/
@[simp]
lemma SetTheory.Set.mem_powerset' {S S' : Set} : (S' : Object) ∈ S.powerset ↔ S' ⊆ S := by
  simp [mem_powerset]

/-- Ещё одна вспомогательная лемма для Exercise 3.4.7. -/
lemma SetTheory.Set.mem_union_powerset_replace_iff {S : Set} {P : S.powerset → Object → Prop} {hP : _} {x : Object} :
    x ∈ union (S.powerset.replace (P := P) hP) ↔
    ∃ (S' : S.powerset) (U : Set), P S' U ∧ x ∈ U := by
  grind [union_axiom, replacement_axiom]

/-- Exercise 3.4.7 -/
theorem SetTheory.Set.partial_functions {X Y : Set} :
    ∃ Z : Set, ∀ F : Object, F ∈ Z ↔ ∃ X' Y' : Set, X' ⊆ X ∧ Y' ⊆ Y ∧ ∃ f : X' → Y', F = f := by
  sorry

/--
  Exercise 3.4.8. Суть этого упражнения — доказать утверждение, не используя
  операцию попарного объединения {kw (of := «term_∪_»)}`∪`.
-/
theorem SetTheory.Set.union_pair_exists (X Y : Set) : ∃ Z : Set, ∀ x, x ∈ Z ↔ (x ∈ X ∨ x ∈ Y) := by
  sorry

/-- Exercise 3.4.9 -/
theorem SetTheory.Set.iInter'_insensitive {I : Set} (β β' : I) (A : I → Set) :
    iInter' I β A = iInter' I β' A := by sorry

/-- Exercise 3.4.10 -/
theorem SetTheory.Set.union_iUnion {I J : Set} (A : (I ∪ J : Set) → Set) :
    iUnion I (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    ∪ iUnion J (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    = iUnion (I ∪ J) A := by sorry

/-- Exercise 3.4.10 -/
theorem SetTheory.Set.union_of_nonempty {I J : Set} (hI : I ≠ ∅) (hJ : J ≠ ∅) : I ∪ J ≠ ∅ := by sorry

/-- Exercise 3.4.10 -/
theorem SetTheory.Set.inter_iInter {I J : Set} (hI : I ≠ ∅) (hJ : J ≠ ∅) (A : (I ∪ J : Set) → Set) :
    iInter I hI (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    ∩ iInter J hJ (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    = iInter (I ∪ J) (union_of_nonempty hI hJ) A := by sorry

/-- Exercise 3.4.11 -/
theorem SetTheory.Set.compl_iUnion {X I : Set} (hI : I ≠ ∅) (A : I → Set) :
    X \ iUnion I A = iInter I hI (fun α ↦ X \ A α) := by sorry

/-- Exercise 3.4.11 -/
theorem SetTheory.Set.compl_iInter {X I : Set} (hI : I ≠ ∅) (A : I → Set) :
    X \ iInter I hI A = iUnion I (fun α ↦ X \ A α) := by sorry

end Chapter3
