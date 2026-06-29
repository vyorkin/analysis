import Mathlib.Tactic
import Analysis.Section_2_3

/-!
# Analysis I, Chapter 2 epilogue: Isomorphism with the Mathlib natural numbers

In this (technical) epilogue, we show that the "Chapter 2" natural numbers {name}`Chapter2.Nat` are
isomorphic in various senses to the standard natural numbers {lean}`ℕ`.

After this epilogue, {name}`Chapter2.Nat` will be deprecated, and we will instead use the standard
natural numbers {lean}`ℕ` throughout.  In particular, one should use the full Mathlib API for {lean}`ℕ` for
all subsequent chapters, in lieu of the {name}`Chapter2.Nat` API.

Filling the sorries here requires both the {name}`Chapter2.Nat` API and the Mathlib API for the standard
natural numbers {lean}`ℕ`.  As such, they are excellent exercises to prepare you for the aforementioned
transition.

In second half of this section we also give a fully axiomatic treatment of the natural numbers
via the Peano axioms. The treatment in the preceding three sections was only partially axiomatic,
because we used a specific construction {name}`Chapter2.Nat` of the natural numbers that was an inductive
type, and used that inductive type to construct a recursor.  Here, we give some exercises to show
how one can accomplish the same tasks directly from the Peano axioms, without knowing the specific
implementation of the natural numbers.

## Tips from past users

Users of the companion who have completed the exercises in this section are
welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

/-- Converting a Chapter 2 natural number to a Mathlib natural number. -/
abbrev Chapter2.Nat.toNat (n : Chapter2.Nat) : ℕ := match n with
  | zero => 0
  | succ n' => n'.toNat + 1

lemma Chapter2.Nat.zero_toNat : (0 : Chapter2.Nat).toNat = 0 := rfl

lemma Chapter2.Nat.succ_toNat (n : Chapter2.Nat) : (n++).toNat = n.toNat + 1 := rfl

/-- The conversion is a bijection. Here we use the existing capability (from Section 2.1) to map
the Mathlib natural numbers to the Chapter 2 natural numbers. -/
abbrev Chapter2.Nat.equivNat : Chapter2.Nat ≃ ℕ where
  toFun := toNat
  invFun n := (n : Chapter2.Nat)
  left_inv n := by
    induction' n with n hn; rfl
    simp [hn]
    rw [succ_eq_add_one]
  right_inv n := by
    induction' n with n hn; rfl
    simp [←succ_eq_add_one, hn]

/-- The conversion preserves addition. -/
abbrev Chapter2.Nat.map_add : ∀ (n m : Nat), (n + m).toNat = n.toNat + m.toNat := by
  intro n m
  induction' n with n hn
  · rw [show zero = 0 from rfl]
    rw [zero_add]
    rw [_root_.Nat.zero_add]
  · rw [succ_add]
    rw [_root_.Nat.succ_add]
    rw [← hn]

/-- The conversion preserves multiplication. -/
abbrev Chapter2.Nat.map_mul : ∀ (n m : Nat), (n * m).toNat = n.toNat * m.toNat := by
  intro n m
  induction' n with n hn
  · rw [show zero = 0 from rfl, zero_mul, _root_.Nat.zero_mul]
  · rw [succ_mul]
    rw [_root_.Nat.succ_mul]
    rw [← hn]
    rw [map_add]

/-- The conversion preserves order. -/
abbrev Chapter2.Nat.map_le_map_iff : ∀ {n m : Nat}, n.toNat ≤ m.toNat ↔ n ≤ m := by
  intro n m
  induction' n with n hn
  · rw [show zero = 0 from rfl]
    constructor
    · intro h
      exact zero_le m
    · intro h
      apply _root_.Nat.zero_le
  · constructor
    · intro h
      rw [succ_toNat] at h
      rw [Nat.le_iff]
      obtain ⟨k, hk⟩ := _root_.Nat.exists_eq_add_of_le h
      refine ⟨(k : Chapter2.Nat), equivNat.injective ?_⟩
      change m.toNat = (n++ + (k : Chapter2.Nat)).toNat
      rw [map_add, succ_toNat]
      have hk' : (↑k : Chapter2.Nat).toNat = k := equivNat.right_inv k
      omega
    · intro h
      rw [succ_toNat]
      rw [Nat.le_iff] at h
      obtain ⟨a, ha⟩ := h
      rw [ha, map_add, succ_toNat]
      omega

/-- Более простое доказательство: без индукции, через `Nat.le_iff` и `map_add`. -/
abbrev Chapter2.Nat.map_le_map_iff' : ∀ {n m : Nat}, n.toNat ≤ m.toNat ↔ n ≤ m := by
  intro n m
  rw [Nat.le_iff, le_iff_exists_add]
  constructor
  · rintro ⟨k, hk⟩
    have hk' : (↑k : Chapter2.Nat).toNat = k := equivNat.right_inv k
    have hm  : m.toNat = (n + (k : Chapter2.Nat)).toNat := by
      rw [map_add, hk']
      exact hk
    exact ⟨k, equivNat.injective hm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a.toNat, by rw [map_add]⟩

abbrev Chapter2.Nat.equivNat_ordered_ring : Chapter2.Nat ≃+*o ℕ where
  toEquiv := equivNat
  map_add' := map_add
  map_mul' := map_mul
  map_le_map_iff' := map_le_map_iff

/-- The conversion preserves exponentiation. -/
lemma Chapter2.Nat.pow_eq_pow (n m : Chapter2.Nat) :
    n.toNat ^ m.toNat = (n^m).toNat := by
  induction' m with m hm
  · rw [show zero = 0 by rfl]
    rw [_root_.pow_zero, pow_zero]
    rfl
  · rw [pow_succ]
    rw [_root_.Nat.pow_succ]
    rw [map_mul]
    rw [← hm]

/-- The Peano axioms for an abstract type {name}`Nat` -/
@[ext]
structure PeanoAxioms where
  Nat : Type
  zero : Nat -- Axiom 2.1
  succ : Nat → Nat -- Axiom 2.2
  succ_ne : ∀ n : Nat, succ n ≠ zero -- Axiom 2.3
  succ_cancel : ∀ {n m : Nat}, succ n = succ m → n = m -- Axiom 2.4
  induction : ∀ (P : Nat → Prop),
    P zero → (∀ n : Nat, P n → P (succ n)) → ∀ n : Nat, P n -- Axiom 2.5

namespace PeanoAxioms

/-- The Chapter 2 natural numbers obey the Peano axioms. -/
def Chapter2_Nat : PeanoAxioms where
  Nat := Chapter2.Nat
  zero := Chapter2.Nat.zero
  succ := Chapter2.Nat.succ
  succ_ne := Chapter2.Nat.succ_ne
  succ_cancel := Chapter2.Nat.succ_cancel
  induction := Chapter2.Nat.induction

/-- The Mathlib natural numbers obey the Peano axioms. -/
def Mathlib_Nat : PeanoAxioms where
  Nat := ℕ
  zero := 0
  succ := Nat.succ
  succ_ne := Nat.succ_ne_zero
  succ_cancel := Nat.succ_inj.mp
  induction _ := Nat.rec

/-- One can map the Mathlib natural numbers into any other structure obeying the Peano axioms. -/
abbrev natCast (P : PeanoAxioms) : ℕ → P.Nat := fun n ↦ match n with
  | Nat.zero => P.zero
  | Nat.succ n => P.succ (natCast P n)

/-- One can start the proof here with {syntax tactic}`unfold Function.Injective`, although it is not strictly necessary. -/
theorem natCast_injective (P : PeanoAxioms) : Function.Injective P.natCast := by
  intro a b hab
  induction a generalizing b with
  | zero =>
    -- P.natCast 0 = P.zero; если b = succ b', получаем P.zero = P.succ ..., противоречие
    cases b with
    | zero => rfl
    | succ b' =>
      apply absurd
      · exact hab.symm
      · apply P.succ_ne
  | succ a' ih =>
    cases b with
    | zero =>
      apply absurd
      · exact hab
      · apply P.succ_ne
    | succ b' =>
      have hcancel : P.natCast a' = P.natCast b' := P.succ_cancel hab
      rw [ih hcancel]

/-- One can start the proof here with {syntax tactic}`unfold Function.Surjective`, although it is not strictly necessary. -/
theorem natCast_surjective (P : PeanoAxioms) : Function.Surjective P.natCast := by
  -- индукция по целевому элементу: всякий x : P.Nat достижим
  apply P.induction (fun x => ∃ n : ℕ, P.natCast n = x)
  · exact ⟨0, rfl⟩
  · intro x ⟨n, hn⟩
    have hstep : P.natCast (n + 1) = P.succ x := by
      have hdef : P.natCast (n + 1) = P.succ (P.natCast n) := rfl
      rw [hdef, hn]
    exact ⟨n + 1, hstep⟩

/-- The notion of an equivalence between two structures obeying the Peano axioms.
    The symbol {kw (of := «term_≃_»)}`≃` is an alias for Mathlib's {name}`Equiv` class; for instance {lean}`P.Nat ≃ Q.Nat` is
    an alias for {lean}`_root_.Equiv P.Nat Q.Nat`. -/
class Equiv (P Q : PeanoAxioms) where
  equiv : P.Nat ≃ Q.Nat
  equiv_zero : equiv P.zero = Q.zero
  equiv_succ : ∀ n : P.Nat, equiv (P.succ n) = Q.succ (equiv n)

/-- This exercise will require application of Mathlib's API for the {name}`Equiv` class.
    Some of this API can be invoked automatically via the {tactic}`simp` tactic. -/
abbrev Equiv.symm {P Q : PeanoAxioms} (eqv : Equiv P Q) : Equiv Q P where
  equiv := eqv.equiv.symm
  equiv_zero := by
    rw [_root_.Equiv.symm_apply_eq]
    exact eqv.equiv_zero.symm
  equiv_succ n := by
    rw [_root_.Equiv.symm_apply_eq, eqv.equiv_succ, eqv.equiv.apply_symm_apply]

/-- This exercise will require application of Mathlib's API for the {name}`Equiv` class.
    Some of this API can be invoked automatically via the {tactic}`simp` tactic. -/
abbrev Equiv.trans {P Q R : PeanoAxioms} (equiv1 : Equiv P Q) (equiv2 : Equiv Q R) : Equiv P R where
  equiv := equiv1.equiv.trans equiv2.equiv
  equiv_zero := by
    rw [_root_.Equiv.trans_apply, equiv1.equiv_zero, equiv2.equiv_zero]
  equiv_succ n := by
    rw [_root_.Equiv.trans_apply, equiv1.equiv_succ, equiv2.equiv_succ]
    rfl

/-- Useful Mathlib tools for inverting bijections include {name}`Function.surjInv` and {name}`Function.invFun`. -/
noncomputable abbrev Equiv.fromNat (P : PeanoAxioms) : Equiv Mathlib_Nat P where
  equiv :=
    -- Mathlib_Nat.Nat = ℕ лишь по определению, поэтому даём Nonempty явно
    haveI : Nonempty Mathlib_Nat.Nat := ⟨(0 : ℕ)⟩
    {
      toFun := P.natCast
      invFun := Function.invFun P.natCast
      left_inv := Function.leftInverse_invFun (natCast_injective P)
      right_inv := Function.rightInverse_invFun (natCast_surjective P)
    }
  equiv_zero := rfl
  equiv_succ _ := rfl

/-- The task here is to establish that any two structures obeying the Peano axioms are equivalent. -/
noncomputable abbrev Equiv.mk' (P Q : PeanoAxioms) : Equiv P Q :=
  (Equiv.fromNat P).symm.trans (Equiv.fromNat Q)

/-- There is only one equivalence between any two structures obeying the Peano axioms. -/
theorem Equiv.uniq {P Q : PeanoAxioms} (equiv1 equiv2 : PeanoAxioms.Equiv P Q) :
    equiv1 = equiv2 := by
  obtain ⟨equiv1, equiv_zero1, equiv_succ1⟩ := equiv1
  obtain ⟨equiv2, equiv_zero2, equiv_succ2⟩ := equiv2
  congr
  ext n
  apply P.induction (fun n => equiv1 n = equiv2 n)
  · rw [equiv_zero1, equiv_zero2]
  · intro n ih
    rw [equiv_succ1, equiv_succ2, ih]

/-- A sample result: recursion is well-defined on any structure obeying the Peano axioms-/
theorem Nat.recurse_uniq {P : PeanoAxioms} (f: P.Nat → P.Nat → P.Nat) (c: P.Nat) :
    ∃! (a: P.Nat → P.Nat), a P.zero = c ∧ ∀ n, a (P.succ n) = f n (a n) := by
  -- φ — обратная к natCast, существует благодаря инъективности и сюръективности
  set φ : P.Nat → ℕ := Function.invFun P.natCast with hφ
  have hleft : ∀ n : ℕ, φ (P.natCast n) = n :=
    Function.leftInverse_invFun (natCast_injective P)
  have hright : ∀ y : P.Nat, P.natCast (φ y) = y :=
    Function.rightInverse_invFun (natCast_surjective P)
  -- значения φ на P.zero и на P.succ
  have hφ_zero : φ P.zero = 0 := hleft 0
  have hφ_succ : ∀ n : P.Nat, φ (P.succ n) = φ n + 1 := by
    intro n
    have hcast : P.natCast (φ n + 1) = P.succ n := by
      have hdef : P.natCast (φ n + 1) = P.succ (P.natCast (φ n)) := rfl
      rw [hdef, hright]
    calc φ (P.succ n) = φ (P.natCast (φ n + 1)) := by rw [hcast]
      _ = φ n + 1 := hleft (φ n + 1)
  -- рекурсия на уровне ℕ, перенесённая на P.Nat через φ
  set b : ℕ → P.Nat := fun n => Nat.rec c (fun k v => f (P.natCast k) v) n with hb
  have hb_zero : b 0 = c := rfl
  have hb_succ : ∀ k : ℕ, b (k + 1) = f (P.natCast k) (b k) := fun k => rfl
  set a : P.Nat → P.Nat := b ∘ φ with ha
  apply ExistsUnique.intro a
  · constructor
    · show b (φ P.zero) = c
      rw [hφ_zero, hb_zero]
    · intro n
      show b (φ (P.succ n)) = f n (b (φ n))
      rw [hφ_succ, hb_succ, hright]
  · intro a' ha'
    obtain ⟨ha'_zero, ha'_succ⟩ := ha'
    funext y
    apply P.induction (fun y => a' y = a y)
    · have hdef : a P.zero = b (φ P.zero) := rfl
      have haz : a P.zero = c := by rw [hdef, hφ_zero]; exact hb_zero
      exact ha'_zero.trans haz.symm
    · intro n ih
      rw [ha'_succ, ih]
      simp only [ha, Function.comp]
      rw [hφ_succ, hb_succ, hright]

end PeanoAxioms
