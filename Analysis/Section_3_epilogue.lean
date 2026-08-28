import Mathlib.Tactic
import Mathlib.SetTheory.ZFC.PSet
import Mathlib.SetTheory.ZFC.Basic
import Analysis.Tools.ExistsUnique
import Analysis.Section_3_1

set_option doc.verso.suggestions false

/-!
# Analysis I, эпилог главы 3: связь с ZFSet

В этом эпилоге мы показываем, что тип {name}`ZFSet` из Mathlib (полученный как факторизация типа
{name}`PSet`) можно использовать для построения моделей класса `SetTheory`, изучаемого в этой главе,
при условии, что мы работаем во вселенной уровня не ниже 1. Приведённые здесь конструкции
принадлежат Эдварду ван де Менту (Edward van de Meent); см.
https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/Can.20this.20proof.20related.20to.20Set.20replacement.20be.20shorter.3F/near/527305173
-/

universe u

/-- Предварительная лемма о `PSet`: их натуральные числа упорядочены по отношению принадлежности. -/
lemma PSet.ofNat_mem_ofNat_of_lt (m n : ℕ) : n < m → ofNat n ∈ ofNat m := by
  intro h
  induction h with
  | refl => rw [ofNat]; apply mem_insert
  | step _ ih => rw [ofNat]; exact mem_insert_of_mem _ ih

-- отношение принадлежности между `PSet`-натуральными числами `ofNat n` и `ofNat m`
-- в точности соответствует порядку: `ofNat n ∈ ofNat m ↔ n < m`
lemma PSet.mem_ofNat_iff (n m : ℕ) : ofNat n ∈ ofNat m ↔ n < m := by
  refine ⟨ ?_, ofNat_mem_ofNat_of_lt m n ⟩
  contrapose!; rw [le_iff_lt_or_eq]; rintro (h|rfl)
  · exact mem_asymm (ofNat_mem_ofNat_of_lt _ _ h)
  apply mem_irrefl

/-- Ещё одна предварительная лемма: натуральные числа в {name}`PSet` могут быть эквивалентны
только тогда, когда они равны. -/
lemma PSet.eq_of_ofNat_equiv_ofNat (n m : ℕ) : (ofNat.{u} n).Equiv (ofNat.{u} m) → n = m := by
  wlog hmn : m ≤ n generalizing n m
  · intro heq; rw [this _ _ _ heq.symm]; order
  intro h; rw [Equiv.eq, Set.ext_iff] at h
  have : n ≤ m := by specialize h (ofNat m); simpa [mem_irrefl, mem_ofNat_iff] using h
  order

open PSet in
/-- Используя приведённые выше леммы, мы можем построить биекцию между {name}`ZFSet.omega`
и натуральными числами. -/
noncomputable def ZFSet.nat_equiv : ℕ ≃ omega.{u} := Equiv.ofBijective (fun n => ⟨mk (ofNat.{u} n),mk_mem_iff.mpr (Mem.mk _ (ULift.up n))⟩) (by
  constructor
  · intro _ _; simp [eq]; apply eq_of_ofNat_equiv_ofNat
  · intro ⟨x,hx⟩; rw [←mk_out x, omega] at hx; erw [mk_mem_iff] at hx; obtain ⟨n,hn⟩ := hx
    simp [mk_func, PSet.omega] at *; use n.down; rw [←mk_out x, eq]; exact hn.symm
  )

open Classical in
/-- Показывает, что {name}`ZFSet` подчиняется аксиомам {name}`Chapter3.SetTheory`. Большинство
этих аксиом по сути уже были установлены в Mathlib, и их перенос — дело сравнительно рутинное;
эквивалентность `ZF.omega` и {name}`Nat` по содержанию оказывается самой хитрой (аксиома
степенного множества тоже требует некоторых технических манипуляций). -/
noncomputable instance ZFSet.inst_SetTheory : Chapter3.SetTheory.{u + 1,u + 1} where
  Set := ZFSet
  Object := ZFSet
  set_to_object := { toFun ⦃a₁⦄ := a₁, inj' _ _ h := h}
  mem o s := o ∈ s
  extensionality _ _ := ext
  emptyset := ∅
  emptyset_mem := notMem_empty
  singleton x := {x}
  singleton_axiom _ _ := mem_singleton
  union_pair x y := x ∪ y
  union_pair_axiom _ _ _ := mem_union
  specify A P := ZFSet.sep (fun s ↦ (h : s ∈ A) → P ⟨s,h⟩) A
  specification_axiom := by simp +contextual
  replace A P hp := @(A.sep (fun s ↦ (hs : s ∈ A) → ∃ z, P ⟨s,hs⟩ z)).image (fun s ↦
    if h : ∃ (hs : s ∈ A), ∃ z, P ⟨s,hs⟩ z then h.choose_spec.choose else ∅) (allZFSetDefinable _)
  replacement_axiom A P hp s := by
    simp; constructor
    · intro ⟨z, ⟨hzA, hz⟩, hz'⟩; use z, hzA; simp [hzA, hz hzA] at hz'
      simp [←hz', Exists.choose_spec]
    · intro ⟨z, hzA, hz'⟩; use z, ⟨hzA, by aesop⟩
      apply hp ⟨_, hzA⟩; rw [dif_pos ⟨hzA, ⟨_, hz'⟩⟩]; use Exists.choose_spec _
  nat := omega
  nat_equiv := nat_equiv
  regularity_axiom A := by
    simp; intro x hx; have ⟨y,hy,_⟩ := regularity A (by aesop)
    use y, hy; intro z _ _; have : z ∈ A ∩ y := by simp; tauto
    aesop
  pow X Y := funs Y X
  function_to_object X Y := {
    toFun f := @map (fun s ↦ if h : s ∈ X then f ⟨s,h⟩ else ∅) (allZFSetDefinable _) X
    inj' x _ h := by
      ext ⟨s, hs⟩; simp_rw [ZFSet.ext_iff, mem_map] at h
      specialize h (s.pair (x ⟨_,hs⟩)); aesop}
  powerset_axiom X Y F := by
    simp [IsFunc]; constructor
    · intro ⟨hsub,huniq⟩
      use (fun x ↦ ⟨(huniq _ x.property).choose,(pair_mem_prod.mp (hsub (huniq _ x.property).choose_spec)).2⟩)
      ext; simp; constructor
      · rintro ⟨y,hy,rfl⟩; simp_all [(huniq _ hy).choose_spec]
      · intro hf; specialize hsub hf; rw [mem_prod] at hsub; obtain ⟨y,hy,x,_,rfl⟩ := hsub
        use y,hy; simp_all [←(huniq _ hy).choose_eq hf]
    · rintro ⟨f,rfl⟩; simp; constructor <;> intro _ _ <;> aesop (add safe [SetLike.coe_mem])
  union := sUnion
  union_axiom _ _ := by simp [And.comm]
