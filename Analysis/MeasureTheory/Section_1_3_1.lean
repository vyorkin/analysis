import Analysis.MeasureTheory.Section_1_2_3
import Analysis.Misc.NatBitwise

/-!
# Введение в теорию меры, раздел 1.3.1: Интегрирование простых функций

Сопровождение к (введению к) разделу 1.3.1 книги «An Introduction to Measure Theory».

-/

-- Некоторые вспомогательные инструменты для перехода между EReal-значными, ℝ-значными и ℂ-значными функциями

def EReal.abs_fun {X Y : Type*} [RCLike Y] (f : X → Y) : X → EReal := fun x ↦ ‖f x‖.toEReal
def Complex.re_fun {X : Type*} (f : X → ℂ) : X → ℝ := fun x ↦ Complex.re (f x)
def Complex.im_fun {X : Type*} (f : X → ℂ) : X → ℝ := fun x ↦ Complex.im (f x)
def Complex.conj_fun {X : Type*} (f : X → ℂ) : X → ℂ := fun x ↦ starRingEnd ℂ (f x)
def EReal.pos_fun {X : Type*} (f : X → ℝ) : X → EReal := fun x ↦ (max (f x) 0).toEReal
def EReal.neg_fun {X : Type*} (f : X → ℝ) : X → EReal := fun x ↦ (max (-f x) 0).toEReal
def Real.complex_fun {X : Type*} (f : X → ℝ) : X → ℂ := fun x ↦ Complex.ofReal (f x)
def Real.EReal_fun {X : Type*} (f : X → ℝ) : X → EReal := fun x ↦ Real.toEReal (f x)

noncomputable def EReal.indicator {X : Type*} (A : Set X) : X → EReal := Real.EReal_fun A.indicator'

theorem EReal.indicator_of_mem {X : Type*} {A : Set X} {x : X} (h : x ∈ A) : EReal.indicator A x = 1 := by
  simp [EReal.indicator, Real.EReal_fun, Set.indicator'_of_mem h]

theorem EReal.indicator_of_notMem {X : Type*} {A : Set X} {x : X} (h : x ∉ A) : EReal.indicator A x = 0 := by
  simp [EReal.indicator, Real.EReal_fun, Set.indicator'_of_notMem h]

noncomputable def Complex.indicator {X : Type*} (A : Set X) : X → ℂ := Real.complex_fun A.indicator'

/-- Definition 1.3.2 -/
def UnsignedSimpleFunction {d : ℕ} (f : EuclideanSpace' d → EReal) : Prop := ∃ (k : ℕ) (c : Fin k → EReal) (E : Fin k → Set (EuclideanSpace' d)),
  (∀ i, LebesgueMeasurable (E i) ∧ c i ≥ 0) ∧ f = ∑ i, (c i) • (EReal.indicator (E i))

def RealSimpleFunction {d : ℕ} (f : EuclideanSpace' d → ℝ) : Prop := ∃ (k : ℕ) (c : Fin k → ℝ) (E : Fin k → Set (EuclideanSpace' d)),
  (∀ i, LebesgueMeasurable (E i)) ∧ f = ∑ i, (c i) • (E i).indicator'

def ComplexSimpleFunction {d : ℕ} (f : EuclideanSpace' d → ℂ) : Prop := ∃ (k : ℕ) (c : Fin k → ℂ) (E : Fin k → Set (EuclideanSpace' d)),
  (∀ i, LebesgueMeasurable (E i)) ∧ f = ∑ i, (c i) • (Complex.indicator (E i))

-- TODO: приведения между этими понятиями, а также структура векторного пространства на вещественных и
-- комплексных простых функциях (и структура конуса на беззнаковых простых функциях).


@[coe]
abbrev RealSimpleFunction.toComplex {d : ℕ} (f : EuclideanSpace' d → ℝ) (df : RealSimpleFunction f) : ComplexSimpleFunction (Real.complex_fun f) := by
  obtain ⟨k, c, E, hmes, heq⟩ := df
  use k, fun i => Complex.ofReal (c i), E
  constructor
  · exact hmes
  · ext x
    simp only [Real.complex_fun, Complex.indicator, heq]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Complex.ofReal_sum]
    congr 1
    ext i
    exact Complex.ofReal_mul (c i) ((E i).indicator' x)

instance RealSimpleFunction.coe_complex {d : ℕ} (f : EuclideanSpace' d → ℝ) : Coe (RealSimpleFunction f) (ComplexSimpleFunction (Real.complex_fun f)) := {
  coe := RealSimpleFunction.toComplex f
}


lemma UnsignedSimpleFunction.add {d : ℕ} {f g : EuclideanSpace' d → EReal} (hf : UnsignedSimpleFunction f) (hg : UnsignedSimpleFunction g) : UnsignedSimpleFunction (f + g) := by
  obtain ⟨k₁, c₁, E₁, ⟨hmes₁, heq₁⟩⟩ := hf
  obtain ⟨k₂, c₂, E₂, ⟨hmes₂, heq₂⟩⟩ := hg
  use k₁ + k₂, fun i => if h : i < k₁ then c₁ ⟨i, h⟩ else c₂ ⟨i - k₁, by omega⟩,
       fun i => if h : i < k₁ then E₁ ⟨i, h⟩ else E₂ ⟨i - k₁, by omega⟩
  constructor
  · intro i
    split_ifs with h
    · exact hmes₁ ⟨i, h⟩
    · exact hmes₂ ⟨i - k₁, by omega⟩
  · ext x
    rw [heq₁, heq₂]
    simp [Fin.sum_univ_add]

private lemma EReal.indicator_nonneg' {X : Type*} (A : Set X) (x : X) : 0 ≤ EReal.indicator A x := by
  simp only [EReal.indicator, Real.EReal_fun]
  exact EReal.coe_nonneg.mpr (Set.indicator_nonneg (fun _ _ => zero_le_one) x)

lemma UnsignedSimpleFunction.smul {d : ℕ} {f : EuclideanSpace' d → EReal} (hf : UnsignedSimpleFunction f) {a : EReal} (ha : a ≥ 0) : UnsignedSimpleFunction (a • f) := by
  obtain ⟨k, c, E, ⟨hmes, heq⟩⟩ := hf
  use k, fun i => a * (c i), E
  constructor
  · intro i
    exact ⟨hmes i |>.1, mul_nonneg ha (hmes i |>.2)⟩
  · rw [heq]
    ext x
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [EReal.mul_finset_sum_of_nonneg k a (fun i => (c i) * EReal.indicator (E i) x)
        (fun i => mul_nonneg (hmes i |>.2) (EReal.indicator_nonneg' (E i) x))]
    congr 1
    ext i
    rw [mul_assoc]

lemma RealSimpleFunction.add {d : ℕ} {f g : EuclideanSpace' d → ℝ} (hf : RealSimpleFunction f) (hg : RealSimpleFunction g) : RealSimpleFunction (f + g) := by
  obtain ⟨k₁, c₁, E₁, ⟨hmes₁, heq₁⟩⟩ := hf
  obtain ⟨k₂, c₂, E₂, ⟨hmes₂, heq₂⟩⟩ := hg
  use k₁ + k₂, fun i => if h : i < k₁ then c₁ ⟨i, h⟩ else c₂ ⟨i - k₁, by omega⟩,
       fun i => if h : i < k₁ then E₁ ⟨i, h⟩ else E₂ ⟨i - k₁, by omega⟩
  constructor
  · intro i
    split_ifs with h
    · exact hmes₁ ⟨i, h⟩
    · exact hmes₂ ⟨i - k₁, by omega⟩
  · ext x
    rw [heq₁, heq₂]
    simp [Fin.sum_univ_add]

lemma ComplexSimpleFunction.add {d : ℕ} {f g : EuclideanSpace' d → ℂ} (hf : ComplexSimpleFunction f) (hg : ComplexSimpleFunction g) : ComplexSimpleFunction (f + g) := by
  obtain ⟨k₁, c₁, E₁, ⟨hmes₁, heq₁⟩⟩ := hf
  obtain ⟨k₂, c₂, E₂, ⟨hmes₂, heq₂⟩⟩ := hg
  use k₁ + k₂, fun i => if h : i < k₁ then c₁ ⟨i, h⟩ else c₂ ⟨i - k₁, by omega⟩,
       fun i => if h : i < k₁ then E₁ ⟨i, h⟩ else E₂ ⟨i - k₁, by omega⟩
  constructor
  · intro i
    split_ifs with h
    · exact hmes₁ ⟨i, h⟩
    · exact hmes₂ ⟨i - k₁, by omega⟩
  · ext x
    rw [heq₁, heq₂]
    simp [Fin.sum_univ_add]

lemma RealSimpleFunction.smul {d : ℕ} {f : EuclideanSpace' d → ℝ} (hf : RealSimpleFunction f) (a : ℝ)  : RealSimpleFunction (a • f) := by
  obtain ⟨k, c, E, ⟨hmes, heq⟩⟩ := hf
  use k, fun i => a * (c i), E
  constructor
  · intro i
    exact hmes i
  · rw [heq]
    ext x
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    congr 1
    ext i
    rw [mul_assoc]

lemma ComplexSimpleFunction.smul {d : ℕ} {f : EuclideanSpace' d → ℂ} (hf : ComplexSimpleFunction f) (a : ℂ)  : ComplexSimpleFunction (a • f) := by
  obtain ⟨k, c, E, ⟨hmes, heq⟩⟩ := hf
  use k, fun i => a * (c i), E
  constructor
  · intro i
    exact hmes i
  · rw [heq]
    ext x
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    congr 1
    ext i
    rw [mul_assoc]

private lemma Complex.indicator_conj {X : Type*} (A : Set X) (x : X) : 
    starRingEnd ℂ (Complex.indicator A x) = Complex.indicator A x := by
  simp only [Complex.indicator, Real.complex_fun]
  exact Complex.conj_ofReal _

lemma ComplexSimpleFunction.conj {d : ℕ} {f : EuclideanSpace' d → ℂ} (hf : ComplexSimpleFunction f) : ComplexSimpleFunction (Complex.conj_fun f) := by
  obtain ⟨k, c, E, ⟨hmes, heq⟩⟩ := hf
  use k, fun i => starRingEnd ℂ (c i), E
  constructor
  · intro i
    exact hmes i
  · rw [heq]
    ext x
    simp only [Complex.conj_fun, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [map_sum]
    congr 1
    ext i
    rw [map_mul, Complex.indicator_conj]

noncomputable def UnsignedSimpleFunction.integ {d : ℕ} {f : EuclideanSpace' d → EReal} (hf : UnsignedSimpleFunction f) : EReal := ∑ i, (hf.choose_spec.choose i) * Lebesgue_measure (hf.choose_spec.choose_spec.choose i)

/-! ## Вспомогательные леммы к лемме 1.3.4

Доказательство использует аргумент с диаграммой Венна: имея два представления одной и той же
простой функции, мы разбиваем R^d на атомы (пересечения всех множеств и их дополнений), выражаем
каждое исходное множество как несвязное объединение атомов и используем конечную аддитивность
меры Лебега.
-/

namespace UnsignedSimpleFunction.IntegralWellDef

open scoped Classical

/-- {given -show}`k, k'` Для семейств множеств, индексированных {lean}`Fin k` и {lean}`Fin k'`, атом определяется
    выбором «в» или «вне» для каждого множества. Мы кодируем это индексом {lean}`Fin (2^(k+k'))`. -/
def atomMembership (_k _k' : ℕ) (n : ℕ) (i : ℕ) : Bool := (n / 2^i) % 2 = 1

lemma atomMembership_eq_testBit (k k' n i : ℕ) : atomMembership k k' n i = n.testBit i := by
  simp only [atomMembership, Nat.testBit_eq_decide_div_mod_eq]

/-- Атом с индексом n — это пересечение по всем $`i` множеств ($`E_i`, если бит $`i` равен 1, иначе $`E_i^c`) -/
def atom {X : Type*} {k k' : ℕ} (E : Fin k → Set X) (E' : Fin k' → Set X) (n : Fin (2^(k+k'))) : Set X :=
  {x | (∀ i : Fin k, atomMembership k k' n i ↔ x ∈ E i) ∧
       (∀ i : Fin k', atomMembership k k' n (k + i) ↔ x ∈ E' i)}

/-- Атомы попарно не пересекаются -/
lemma atom_pairwiseDisjoint {X : Type*} {k k' : ℕ} (E : Fin k → Set X) (E' : Fin k' → Set X) :
    Set.univ.PairwiseDisjoint (atom E E') := by
  intro i _ j _ hij
  simp only [Function.onFun]
  rw [Set.disjoint_left]
  intro x hxi hxj
  simp only [atom, Set.mem_setOf_eq, atomMembership_eq_testBit] at hxi hxj
  -- Если i ≠ j, они различаются в каком-то бите
  have hne : i.val ≠ j.val := Fin.val_ne_of_ne hij
  obtain ⟨bit, hbit⟩ := Nat.exists_testBit_ne_of_ne hne
  -- Этот бит должен быть < k + k', поскольку оба i, j < 2^(k+k')
  have hi_lt : i.val < 2^(k + k') := i.isLt
  have hj_lt : j.val < 2^(k + k') := j.isLt
  have hbit_bound : bit < k + k' := by
    by_contra h
    push_neg at h
    have hi_false : i.val.testBit bit = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hi_lt (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) h))
    have hj_false : j.val.testBit bit = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hj_lt (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) h))
    exact hbit (hi_false.trans hj_false.symm)
  -- Теперь мы знаем, что bit < k + k', значит он индексирует E или E'
  by_cases hbit_k : bit < k
  · -- bit индексирует E
    have hi_iff := hxi.1 ⟨bit, hbit_k⟩
    have hj_iff := hxj.1 ⟨bit, hbit_k⟩
    -- И hxi, и hxj дают x ∈ E ⟨bit, _⟩ ↔ testBit = true
    -- Но у i и j разные биты, значит один говорит x ∈ E, а другой x ∉ E
    cases h_i : i.val.testBit bit <;> cases h_j : j.val.testBit bit
    · exact hbit (h_i.trans h_j.symm)
    · have hx_in : x ∈ E ⟨bit, hbit_k⟩ := hj_iff.mp h_j
      have hx_out : x ∉ E ⟨bit, hbit_k⟩ := fun h => by simp [hi_iff.mpr h] at h_i
      exact hx_out hx_in
    · have hx_in : x ∈ E ⟨bit, hbit_k⟩ := hi_iff.mp h_i
      have hx_out : x ∉ E ⟨bit, hbit_k⟩ := fun h => by simp [hj_iff.mpr h] at h_j
      exact hx_out hx_in
    · exact hbit (h_i.trans h_j.symm)
  · -- bit индексирует E' (bit ∈ [k, k+k'))
    have hbit_k' : bit - k < k' := by omega
    have h_add : k + (bit - k) = bit := by omega
    have hi_iff := hxi.2 ⟨bit - k, hbit_k'⟩
    have hj_iff := hxj.2 ⟨bit - k, hbit_k'⟩
    simp only [h_add] at hi_iff hj_iff
    cases h_i : i.val.testBit bit <;> cases h_j : j.val.testBit bit
    · exact hbit (h_i.trans h_j.symm)
    · have hx_in : x ∈ E' ⟨bit - k, hbit_k'⟩ := hj_iff.mp h_j
      have hx_out : x ∉ E' ⟨bit - k, hbit_k'⟩ := fun h => by simp [hi_iff.mpr h] at h_i
      exact hx_out hx_in
    · have hx_in : x ∈ E' ⟨bit - k, hbit_k'⟩ := hi_iff.mp h_i
      have hx_out : x ∉ E' ⟨bit - k, hbit_k'⟩ := fun h => by simp [hj_iff.mpr h] at h_j
      exact hx_out hx_in
    · exact hbit (h_i.trans h_j.symm)

/-- Сумма степеней двойки до n равна 2^n - 1 -/
private lemma sum_pow_two_range (n : ℕ) : ∑ i ∈ Finset.range n, (2 : ℕ)^i = 2^n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    have h : 1 ≤ 2^n := Nat.one_le_two_pow
    omega

/-- Для любого подмножества {lean}`Fin k` сумма {given -show (type := "Fin k")}`j` {lean}`2^j.val` меньше {lean}`2^k` -/
private lemma sum_pow_two_fin_lt {k : ℕ} {s : Finset (Fin k)} :
    s.sum (fun j => (2 : ℕ)^j.val) < 2^k := by
  have h1 : s.sum (fun j => (2 : ℕ)^j.val) ≤ Finset.univ.sum (fun j : Fin k => (2 : ℕ)^j.val) := by
    apply Finset.sum_le_sum_of_subset
    exact Finset.subset_univ s
  have h2 : Finset.univ.sum (fun j : Fin k => (2 : ℕ)^j.val) = ∑ i ∈ Finset.range k, 2^i := by
    rw [Fin.sum_univ_eq_sum_range]
  have h3 : ∑ i ∈ Finset.range k, (2 : ℕ)^i = 2^k - 1 := sum_pow_two_range k
  have h4 : 2^k - 1 < 2^k := Nat.sub_lt Nat.one_le_two_pow Nat.one_pos
  omega

/-- Вспомогательная лемма: строит индекс атома по шаблону принадлежности.
    Индекс атома кодирует принадлежность x каждому множеству в виде битов. -/
noncomputable def atomIndexOf {X : Type*} [DecidableEq X] {k k' : ℕ} (E : Fin k → Set X) (E' : Fin k' → Set X) (x : X) : ℕ :=
  (Finset.univ.filter fun j : Fin k => x ∈ E j).sum (fun j => 2^j.val) +
  (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => 2^(k + j'.val))

/-- Индекс атома ограничен 2^(k+k') -/
lemma atomIndexOf_lt {X : Type*} [DecidableEq X] {k k' : ℕ} (E : Fin k → Set X) (E' : Fin k' → Set X) (x : X) :
    atomIndexOf E E' x < 2^(k+k') := by
  unfold atomIndexOf
  have hpart1 : (Finset.univ.filter fun j : Fin k => x ∈ E j).sum (fun j => (2 : ℕ)^j.val) < 2^k :=
    sum_pow_two_fin_lt
  have hpart2_inner : (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2 : ℕ)^j'.val) < 2^k' :=
    sum_pow_two_fin_lt
  have hrw : (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2 : ℕ)^(k + j'.val)) =
             2^k * (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2 : ℕ)^j'.val) := by
    rw [Finset.mul_sum]
    congr 1; ext j'; rw [pow_add]
  rw [hrw]
  have h2k_pos : 0 < 2^k := Nat.two_pow_pos k
  have hpart2 : 2^k * (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2 : ℕ)^j'.val) < 2^(k+k') := by
    calc 2^k * (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2 : ℕ)^j'.val)
        < 2^k * 2^k' := (Nat.mul_lt_mul_left h2k_pos).mpr hpart2_inner
      _ = 2^(k+k') := by rw [← pow_add]
  -- Используем точные границы: sum1 ≤ 2^k - 1, sum2 ≤ 2^k * (2^k' - 1) = 2^(k+k') - 2^k
  -- Значит sum1 + sum2 ≤ (2^k - 1) + (2^(k+k') - 2^k) = 2^(k+k') - 1 < 2^(k+k')
  have hpart1_le : (Finset.univ.filter fun j : Fin k => x ∈ E j).sum (fun j => (2 : ℕ)^j.val) ≤ 2^k - 1 :=
    Nat.le_sub_one_of_lt hpart1
  have hpart2_le : 2^k * (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2 : ℕ)^j'.val) ≤ 2^(k+k') - 2^k := by
    have inner_le : (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2 : ℕ)^j'.val) ≤ 2^k' - 1 :=
      Nat.le_sub_one_of_lt hpart2_inner
    calc 2^k * (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2 : ℕ)^j'.val)
        ≤ 2^k * (2^k' - 1) := Nat.mul_le_mul_left _ inner_le
      _ = 2^k * 2^k' - 2^k := by rw [Nat.mul_sub_one]
      _ = 2^(k+k') - 2^k := by rw [pow_add]
  have h2k_le : 2^k ≤ 2^(k+k') := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right k k')
  calc (Finset.univ.filter fun j : Fin k => x ∈ E j).sum (fun j => (2 : ℕ)^j.val) +
       2^k * (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2 : ℕ)^j'.val)
      ≤ (2^k - 1) + (2^(k+k') - 2^k) := Nat.add_le_add hpart1_le hpart2_le
    _ = 2^(k+k') - 1 := by omega
    _ < 2^(k+k') := Nat.sub_lt (Nat.two_pow_pos _) (by norm_num)

/-- Индекс атома имеет бит j установленным тогда и только тогда, когда x ∈ E j -/
lemma atomIndexOf_testBit_E {X : Type*} [DecidableEq X] {k k' : ℕ} (E : Fin k → Set X) (E' : Fin k' → Set X) (x : X) (j : Fin k) :
    (atomIndexOf E E' x).testBit j.val ↔ x ∈ E j := by
  unfold atomIndexOf
  -- atomIndexOf = Part1 + Part2, где Part2 = 2^k * (внутренняя сумма)
  have hrw : (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2 : ℕ)^(k + j'.val)) =
             2^k * (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2 : ℕ)^j'.val) := by
    rw [Finset.mul_sum]; congr 1; ext j'; rw [pow_add]
  rw [hrw]
  -- Используем testBit_two_pow_mul_add: при j.val < k и Part1 < 2^k, testBit j смотрит только на Part1
  have hpart1_lt : (Finset.univ.filter fun i : Fin k => x ∈ E i).sum (fun i => (2 : ℕ)^i.val) < 2^k :=
    sum_pow_two_fin_lt
  rw [add_comm, Nat.testBit_two_pow_mul_add _ hpart1_lt, if_pos j.isLt]
  -- Теперь показываем: Part1.testBit j.val ↔ x ∈ E j
  rw [Nat.testBit_sum_pow_two_fin]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- Индекс атома имеет бит (k+j) установленным тогда и только тогда, когда x ∈ E' j -/
lemma atomIndexOf_testBit_E' {X : Type*} [DecidableEq X] {k k' : ℕ} (E : Fin k → Set X) (E' : Fin k' → Set X) (x : X) (j : Fin k') :
    (atomIndexOf E E' x).testBit (k + j.val) ↔ x ∈ E' j := by
  unfold atomIndexOf
  have hrw : (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2 : ℕ)^(k + j'.val)) =
             2^k * (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2 : ℕ)^j'.val) := by
    rw [Finset.mul_sum]; congr 1; ext j'; rw [pow_add]
  rw [hrw]
  -- Используем testBit_two_pow_mul_add: при k + j.val ≥ k и Part1 < 2^k
  have hpart1_lt : (Finset.univ.filter fun i : Fin k => x ∈ E i).sum (fun i => (2 : ℕ)^i.val) < 2^k :=
    sum_pow_two_fin_lt
  rw [add_comm, Nat.testBit_two_pow_mul_add _ hpart1_lt]
  have hge : ¬ (k + j.val < k) := by omega
  rw [if_neg hge]
  -- Теперь показываем: Part2_inner.testBit ((k + j.val) - k) ↔ x ∈ E' j
  have hsub : (k + j.val) - k = j.val := Nat.add_sub_cancel_left k j.val
  rw [hsub, Nat.testBit_sum_pow_two_fin]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- Исходное множество E\_i является объединением атомов, у которых бит i равен 1 -/
lemma set_eq_biUnion_atoms {X : Type*} {k k' : ℕ} (E : Fin k → Set X) (E' : Fin k' → Set X) (i : Fin k) :
    E i = ⋃ n ∈ {n : Fin (2^(k+k')) | atomMembership k k' n i}, atom E E' n := by
  classical
  ext x
  constructor
  · intro hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    -- Строим индекс атома по шаблону принадлежности x
    let n : Fin (2^(k+k')) := ⟨atomIndexOf E E' x, atomIndexOf_lt E E' x⟩
    refine ⟨n, ?_, ?_⟩
    · -- Показываем atomMembership k k' n i = true
      rw [atomMembership_eq_testBit]
      simp only [n, atomIndexOf_testBit_E E E' x i]
      exact hx
    · -- Показываем x ∈ atom E E' n
      simp only [atom, Set.mem_setOf_eq, n]
      refine ⟨fun j => ?_, fun j => ?_⟩
      · rw [atomMembership_eq_testBit, atomIndexOf_testBit_E E E' x j]
      · rw [atomMembership_eq_testBit, atomIndexOf_testBit_E' E E' x j]
  · intro hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx
    obtain ⟨n, hn_bit, hx_atom⟩ := hx
    exact (hx_atom.1 i).mp hn_bit

/-- Исходное множество E'\_i является объединением атомов, у которых бит (k+i) равен 1 -/
lemma set_eq_biUnion_atoms' {X : Type*} {k k' : ℕ} (E : Fin k → Set X) (E' : Fin k' → Set X) (i : Fin k') :
    E' i = ⋃ n ∈ {n : Fin (2^(k+k')) | atomMembership k k' n (k + i)}, atom E E' n := by
  classical
  ext x
  constructor
  · intro hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    let n : Fin (2^(k+k')) := ⟨atomIndexOf E E' x, atomIndexOf_lt E E' x⟩
    refine ⟨n, ?_, ?_⟩
    · rw [atomMembership_eq_testBit]
      simp only [n, atomIndexOf_testBit_E' E E' x i]
      exact hx
    · simp only [atom, Set.mem_setOf_eq, n]
      refine ⟨fun j => ?_, fun j => ?_⟩
      · rw [atomMembership_eq_testBit, atomIndexOf_testBit_E E E' x j]
      · rw [atomMembership_eq_testBit, atomIndexOf_testBit_E' E E' x j]
  · intro hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx
    obtain ⟨n, hn_bit, hx_atom⟩ := hx
    exact (hx_atom.2 i).mp hn_bit

/-- Атомы измеримы, если измеримы исходные множества -/
lemma atom_measurable {d k k' : ℕ} {E : Fin k → Set (EuclideanSpace' d)} {E' : Fin k' → Set (EuclideanSpace' d)}
    (hE : ∀ i, LebesgueMeasurable (E i)) (hE' : ∀ i, LebesgueMeasurable (E' i)) (n : Fin (2^(k+k'))) :
    LebesgueMeasurable (atom E E' n) := by
  -- Атом является пересечением множеств вида E_i или (E_i)ᶜ
  -- Переписываем атом как пересечение
  have hatom_eq : atom E E' n =
      (⋂ i : Fin k, if atomMembership k k' n i then E i else (E i)ᶜ) ∩
      (⋂ i : Fin k', if atomMembership k k' n (k + i) then E' i else (E' i)ᶜ) := by
    ext x
    simp only [atom, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · intro ⟨h1, h2⟩
      constructor
      · intro i
        by_cases hbit : atomMembership k k' n i
        · simp only [hbit, ↓reduceIte]
          exact (h1 i).mp hbit
        · simp only [hbit]
          exact fun hx => hbit ((h1 i).mpr hx)
      · intro i
        by_cases hbit : atomMembership k k' n (k + i)
        · simp only [hbit, ↓reduceIte]
          exact (h2 i).mp hbit
        · simp only [hbit]
          exact fun hx => hbit ((h2 i).mpr hx)
    · intro ⟨h1, h2⟩
      constructor
      · intro i
        specialize h1 i
        by_cases hbit : atomMembership k k' n i
        · simp only [hbit, ↓reduceIte] at h1
          exact ⟨fun _ => h1, fun _ => hbit⟩
        · simp only [hbit] at h1
          exact ⟨fun hf => (hbit hf).elim, fun hx => (h1 hx).elim⟩
      · intro i
        specialize h2 i
        by_cases hbit : atomMembership k k' n (k + i)
        · simp only [hbit, ↓reduceIte] at h2
          exact ⟨fun _ => h2, fun _ => hbit⟩
        · simp only [hbit] at h2
          exact ⟨fun hf => (hbit hf).elim, fun hx => (h2 hx).elim⟩
  rw [hatom_eq]
  -- Теперь показываем, что пересечение измеримо
  -- Каждый компонент — это E i или (E i)ᶜ, оба измеримы
  -- Конечное пересечение измеримых множеств измеримо
  apply LebesgueMeasurable.inter
  · -- Первая часть: ⋂ i : Fin k, ... (конечное пересечение измеримых множеств)
    apply LebesgueMeasurable.finite_inter
    intro i
    by_cases h : atomMembership k k' n i
    · simp only [h]; exact hE i
    · simp only [h]; exact (hE i).complement
  · -- Вторая часть: ⋂ i : Fin k', ... (конечное пересечение измеримых множеств)
    apply LebesgueMeasurable.finite_inter
    intro i
    by_cases h : atomMembership k k' n (k + i)
    · simp only [h]; exact hE' i
    · simp only [h]; exact (hE' i).complement

/-- Индикаторная функция равна c, если x ∈ E -/
lemma indicator_mul_mem {d : ℕ} (E : Set (EuclideanSpace' d)) (c : EReal) (x : EuclideanSpace' d)
    (h : x ∈ E) : c * (EReal.indicator E x) = c := by
  simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_mem h, EReal.coe_one, mul_one]

/-- Индикаторная функция равна 0, если x ∉ E -/
lemma indicator_mul_not_mem {d : ℕ} (E : Set (EuclideanSpace' d)) (c : EReal) (x : EuclideanSpace' d)
    (h : x ∉ E) : c * (EReal.indicator E x) = 0 := by
  simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_notMem h, EReal.coe_zero, mul_zero]

/-- Взвешенная сумма мер для данного представления -/
noncomputable def weightedMeasureSum {d k : ℕ} (c : Fin k → EReal) (E : Fin k → Set (EuclideanSpace' d)) : EReal :=
  ∑ i, (c i) * Lebesgue_measure (E i)

/-- Основная лемма: два представления одной и той же функции дают одну и ту же взвешенную сумму мер.
    Это ядро леммы 1.3.4 (аргумент с диаграммой Венна). -/
lemma weightedMeasureSum_eq_of_eq {d k k' : ℕ}
    {c : Fin k → EReal} {E : Fin k → Set (EuclideanSpace' d)}
    {c' : Fin k' → EReal} {E' : Fin k' → Set (EuclideanSpace' d)}
    (hmes : ∀ i, LebesgueMeasurable (E i)) (hmes' : ∀ i, LebesgueMeasurable (E' i))
    (hnonneg : ∀ i, c i ≥ 0) (hnonneg' : ∀ i, c' i ≥ 0)
    (heq : ∑ i, (c i) • (EReal.indicator (E i)) = ∑ i, (c' i) • (EReal.indicator (E' i))) :
    weightedMeasureSum c E = weightedMeasureSum c' E' := by
  -- Доказательство использует аргумент с диаграммой Венна / атомами
  -- 1. Для любого x в непустом атоме A_n вычисляем heq в точке x:
  --    sum_{i : x ∈ E_i} c_i = sum_{j : x ∈ E'_j} c'_j
  -- 2. Принадлежность x ∈ A_n множеству E_i определяется битом i числа n
  -- 3. Умножаем на m(A_n) и суммируем по всем атомам
  -- 4. Меняем порядок суммирования, чтобы получить результат

  -- Определяем меры атомов
  let atomMeas : Fin (2^(k+k')) → EReal := fun n => Lebesgue_measure (atom E E' n)

  -- Атомы измеримы
  have hatom_mes : ∀ n, LebesgueMeasurable (atom E E' n) := atom_measurable hmes hmes'

  -- Шаг 1: для любой точки в атоме поточечные суммы равны
  have hpoint : ∀ n : Fin (2^(k+k')), ∀ x ∈ atom E E' n,
      ∑ i : Fin k, (c i) * (EReal.indicator (E i) x) = ∑ i : Fin k', (c' i) * (EReal.indicator (E' i) x) := by
    intro n x hx
    have := congr_fun heq x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    exact this

  -- Шаг 2: в атоме n принадлежность E_i определяется битом i
  have hmem_E : ∀ n : Fin (2^(k+k')), ∀ x ∈ atom E E' n, ∀ i : Fin k,
      (x ∈ E i) ↔ atomMembership k k' n i := by
    intro n x hx i
    exact (hx.1 i).symm

  have hmem_E' : ∀ n : Fin (2^(k+k')), ∀ x ∈ atom E E' n, ∀ i : Fin k',
      (x ∈ E' i) ↔ atomMembership k k' n (k + i) := by
    intro n x hx i
    exact (hx.2 i).symm

  -- Шаг 3: поточечная сумма упрощается в зависимости от битового шаблона
  have hsum_simp : ∀ n : Fin (2^(k+k')), ∀ x ∈ atom E E' n,
      ∑ i : Fin k, (c i) * (EReal.indicator (E i) x) = ∑ i : Fin k, if atomMembership k k' n i then c i else 0 := by
    intro n x hx
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : atomMembership k k' n i
    · simp only [h]
      have hx_in : x ∈ E i := (hmem_E n x hx i).mpr h
      exact indicator_mul_mem (E i) (c i) x hx_in
    · simp only [h]
      have hx_out : x ∉ E i := fun hc => h ((hmem_E n x hx i).mp hc)
      exact indicator_mul_not_mem (E i) (c i) x hx_out

  have hsum_simp' : ∀ n : Fin (2^(k+k')), ∀ x ∈ atom E E' n,
      ∑ i : Fin k', (c' i) * (EReal.indicator (E' i) x) = ∑ i : Fin k', if atomMembership k k' n (k + i) then c' i else 0 := by
    intro n x hx
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : atomMembership k k' n (k + i)
    · simp only [h]
      have hx_in : x ∈ E' i := (hmem_E' n x hx i).mpr h
      exact indicator_mul_mem (E' i) (c' i) x hx_in
    · simp only [h]
      have hx_out : x ∉ E' i := fun hc => h ((hmem_E' n x hx i).mp hc)
      exact indicator_mul_not_mem (E' i) (c' i) x hx_out

  -- Шаг 4: для непустых атомов суммы по битовому шаблону равны
  have hbit_eq : ∀ n : Fin (2^(k+k')), (atom E E' n).Nonempty →
      (∑ i : Fin k, if atomMembership k k' n i = true then c i else 0 : EReal) =
      (∑ i : Fin k', if atomMembership k k' n (k + i) = true then c' i else 0 : EReal) := by
    intro n ⟨x, hx⟩
    rw [← hsum_simp n x hx, ← hsum_simp' n x hx]
    exact hpoint n x hx

  -- Шаг 5: E_i = объединение атомов, у которых бит i = 1
  have hE_decomp : ∀ i : Fin k, E i = ⋃ n ∈ {n : Fin (2^(k+k')) | atomMembership k k' n i}, atom E E' n :=
    fun i => set_eq_biUnion_atoms E E' i

  -- Шаг 6: используем конечную аддитивность (для этого нужно показать, что атомы не пересекаются и измеримы)
  -- m(E_i) = сумма по атомам с битом i = 1 значений m(atom)
  have hmes_decomp : ∀ i : Fin k, Lebesgue_measure (E i) =
      ∑ n : Fin (2^(k+k')), if atomMembership k k' n i then atomMeas n else 0 := by
    intro i
    -- Определяем модифицированное семейство атомов: atom' n = atom n, если бит i равен 1, иначе ∅
    let atom' : Fin (2^(k+k')) → Set (EuclideanSpace' d) := fun n =>
      if atomMembership k k' n i then atom E E' n else ∅
    -- E i = ⋃ n, atom' n (поскольку атомы с битом 0 не дают вклада)
    have hE_eq : E i = ⋃ n, atom' n := by
      rw [hE_decomp i]
      ext x
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · intro ⟨n, hn, hx⟩
        use n
        simp only [atom', hn, ite_true]
        exact hx
      · intro ⟨n, hx⟩
        simp only [atom'] at hx
        by_cases hn : atomMembership k k' n i
        · simp only [hn, ite_true] at hx
          exact ⟨n, hn, hx⟩
        · simp only [hn] at hx
          exact False.elim hx
    -- atom' попарно не пересекается
    have hdisj' : Set.univ.PairwiseDisjoint atom' := by
      intro i₁ _ i₂ _ hi
      simp only [Function.onFun, atom']
      by_cases h1 : atomMembership k k' i₁ i <;> by_cases h2 : atomMembership k k' i₂ i
      · simp only [h1, h2, ite_true]
        exact atom_pairwiseDisjoint E E' (by trivial : i₁ ∈ Set.univ) (by trivial) hi
      · simp only [h1, h2, ite_true]
        rw [Set.disjoint_left]; intro _ _; simp
      · simp only [h1, h2, ite_true]
        rw [Set.disjoint_left]; simp
      · simp only [h1, h2]
        rw [Set.disjoint_left]; simp
    -- atom' измеримо
    have hmes'_atom : ∀ n, LebesgueMeasurable (atom' n) := by
      intro n
      simp only [atom']
      by_cases h : atomMembership k k' n i
      · simp only [h, ite_true]; exact hatom_mes n
      · simp only [h]; exact LebesgueMeasurable.empty
    -- Применяем конечную аддитивность
    calc Lebesgue_measure (E i) = Lebesgue_measure (⋃ n, atom' n) := by rw [hE_eq]
      _ = ∑' n, Lebesgue_measure (atom' n) := Lebesgue_measure.finite_union hmes'_atom hdisj'
      _ = ∑ n : Fin (2^(k+k')), Lebesgue_measure (atom' n) := tsum_fintype _
      _ = ∑ n : Fin (2^(k+k')), if atomMembership k k' n i then atomMeas n else 0 := by
          congr 1; funext n; simp only [atom']
          by_cases h : atomMembership k k' n i
          · simp only [h, ite_true]; rfl
          · simp only [h]; exact Lebesgue_measure.empty

  have hE'_decomp : ∀ i : Fin k', E' i = ⋃ n ∈ {n : Fin (2^(k+k')) | atomMembership k k' n (k + i)}, atom E E' n :=
    fun i => set_eq_biUnion_atoms' E E' i

  have hmes_decomp' : ∀ i : Fin k', Lebesgue_measure (E' i) =
      ∑ n : Fin (2^(k+k')), if atomMembership k k' n (k + i) then atomMeas n else 0 := by
    intro i
    let atom'' : Fin (2^(k+k')) → Set (EuclideanSpace' d) := fun n =>
      if atomMembership k k' n (k + i) then atom E E' n else ∅
    have hE'_eq : E' i = ⋃ n, atom'' n := by
      rw [hE'_decomp i]
      ext x
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · intro ⟨n, hn, hx⟩
        use n
        simp only [atom'', hn, ite_true]
        exact hx
      · intro ⟨n, hx⟩
        simp only [atom''] at hx
        by_cases hn : atomMembership k k' n (k + i)
        · simp only [hn, ite_true] at hx
          exact ⟨n, hn, hx⟩
        · simp only [hn] at hx
          exact False.elim hx
    have hdisj'' : Set.univ.PairwiseDisjoint atom'' := by
      intro i₁ _ i₂ _ hi
      simp only [Function.onFun, atom'']
      by_cases h1 : atomMembership k k' i₁ (k + i) <;> by_cases h2 : atomMembership k k' i₂ (k + i)
      · simp only [h1, h2, ite_true]
        exact atom_pairwiseDisjoint E E' (by trivial : i₁ ∈ Set.univ) (by trivial) hi
      · simp only [h1, h2, ite_true]
        rw [Set.disjoint_left]; intro _ _; simp
      · simp only [h1, h2, ite_true]
        rw [Set.disjoint_left]; simp
      · simp only [h1, h2]
        rw [Set.disjoint_left]; simp
    have hmes''_atom : ∀ n, LebesgueMeasurable (atom'' n) := by
      intro n
      simp only [atom'']
      by_cases h : atomMembership k k' n (k + i)
      · simp only [h, ite_true]; exact hatom_mes n
      · simp only [h]; exact LebesgueMeasurable.empty
    calc Lebesgue_measure (E' i) = Lebesgue_measure (⋃ n, atom'' n) := by rw [hE'_eq]
      _ = ∑' n, Lebesgue_measure (atom'' n) := Lebesgue_measure.finite_union hmes''_atom hdisj''
      _ = ∑ n : Fin (2^(k+k')), Lebesgue_measure (atom'' n) := tsum_fintype _
      _ = ∑ n : Fin (2^(k+k')), if atomMembership k k' n (k + i) then atomMeas n else 0 := by
          congr 1; funext n; simp only [atom'']
          by_cases h : atomMembership k k' n (k + i)
          · simp only [h, ite_true]; rfl
          · simp only [h]; exact Lebesgue_measure.empty

  -- Шаг 7: вычисляем weightedMeasureSum, используя разложение
  calc weightedMeasureSum c E
      = ∑ i : Fin k, (c i) * Lebesgue_measure (E i) := rfl
    _ = ∑ i : Fin k, (c i) * (∑ n : Fin (2^(k+k')), if atomMembership k k' n i then atomMeas n else 0) := by
        congr 1; ext i; congr 1; exact hmes_decomp i
    _ = ∑ i : Fin k, ∑ n : Fin (2^(k+k')), (c i) * (if atomMembership k k' n i then atomMeas n else 0) := by
        congr 1; ext i
        -- c i * sum = сумма c i * каждый член
        have hf_nonneg : ∀ n : Fin (2^(k+k')), 0 ≤ (if atomMembership k k' n i then atomMeas n else 0) := by
          intro n
          split_ifs
          · exact Lebesgue_outer_measure.nonneg _
          · rfl
        exact EReal.mul_finset_sum_of_nonneg (2^(k+k')) (c i) (fun n => if atomMembership k k' n i then atomMeas n else 0) hf_nonneg
    _ = ∑ i : Fin k, ∑ n : Fin (2^(k+k')), if atomMembership k k' n i then (c i) * atomMeas n else 0 := by
        congr 1; ext i; congr 1; ext n
        split_ifs <;> simp
    _ = ∑ n : Fin (2^(k+k')), ∑ i : Fin k, if atomMembership k k' n i then (c i) * atomMeas n else 0 := by
        rw [Finset.sum_comm]
    _ = ∑ n : Fin (2^(k+k')), atomMeas n * (∑ i : Fin k, if atomMembership k k' n i then c i else 0) := by
        congr 1; ext n
        -- Вынесение множителя: ∑ i, if p then c i * m else 0 = m * ∑ i, if p then c i else 0
        have hc_nonneg : ∀ i : Fin k, 0 ≤ (if atomMembership k k' n i then c i else 0) := fun i => by
          split_ifs; exact hnonneg i; rfl
        rw [EReal.mul_finset_sum_of_nonneg k (atomMeas n) _ hc_nonneg]
        congr 1; ext i
        split_ifs with h
        · -- c i * atomMeas n = atomMeas n * c i
          exact (EReal.mul_comm (atomMeas n) (c i)).symm
        · simp
    _ = ∑ n : Fin (2^(k+k')), atomMeas n * (∑ i : Fin k', if atomMembership k k' n (k + i) then c' i else 0) := by
        congr 1; ext n
        by_cases h : (atom E E' n).Nonempty
        · congr 1; exact hbit_eq n h
        · -- Пустой атом имеет меру 0, значит этот член равен 0
          rw [Set.not_nonempty_iff_eq_empty] at h
          have hzero : atomMeas n = 0 := by
            simp only [atomMeas, h, Lebesgue_measure.empty]
          simp only [hzero, zero_mul]
    _ = ∑ n : Fin (2^(k+k')), ∑ i : Fin k', if atomMembership k k' n (k + i) then (c' i) * atomMeas n else 0 := by
        congr 1; ext n
        -- Раскрытие: m * ∑ i, if p then c i else 0 = ∑ i, if p then c i * m else 0
        have hc'_nonneg : ∀ i : Fin k', 0 ≤ (if atomMembership k k' n (k + i) then c' i else 0) := fun i => by
          split_ifs; exact hnonneg' i; rfl
        rw [EReal.mul_finset_sum_of_nonneg k' (atomMeas n) _ hc'_nonneg]
        congr 1; ext i
        split_ifs with h
        · exact EReal.mul_comm (atomMeas n) (c' i)
        · simp
    _ = ∑ i : Fin k', ∑ n : Fin (2^(k+k')), if atomMembership k k' n (k + i) then (c' i) * atomMeas n else 0 := by
        rw [Finset.sum_comm]
    _ = ∑ i : Fin k', (c' i) * (∑ n : Fin (2^(k+k')), if atomMembership k k' n (k + i) then atomMeas n else 0) := by
        congr 1; ext i
        -- c' i * sum = сумма c' i * каждый член, затем распределяем по условиям
        have hf_nonneg : ∀ n : Fin (2^(k+k')), 0 ≤ (if atomMembership k k' n (k + i) then atomMeas n else 0) := by
          intro n
          split_ifs
          · exact Lebesgue_outer_measure.nonneg _
          · rfl
        rw [EReal.mul_finset_sum_of_nonneg (2^(k+k')) (c' i) _ hf_nonneg]
        congr 1; ext n
        split_ifs <;> simp
    _ = ∑ i : Fin k', (c' i) * Lebesgue_measure (E' i) := by
        congr 1; ext i; congr 1; exact (hmes_decomp' i).symm
    _ = weightedMeasureSum c' E' := rfl

/-! ## Атомы для одного семейства (специализация k' = 0)

При работе с одним семейством множеств (без второго семейства для сравнения) мы
специализируем машинерию атомов, полагая k' = 0. -/

/-- Атом для одного семейства множеств — использует k' = 0 в общем определении атома -/
def singleAtom {X : Type*} {k : ℕ} (E : Fin k → Set X) (n : Fin (2^k)) : Set X :=
  atom E (fun _ : Fin 0 => ∅) ⟨n.val, by simp only [add_zero]; exact n.isLt⟩

/-- Одиночные атомы попарно не пересекаются -/
lemma singleAtom_pairwiseDisjoint {X : Type*} {k : ℕ} (E : Fin k → Set X) :
    Set.univ.PairwiseDisjoint (singleAtom E) := by
  intro i _ j _ hij
  simp only [Function.onFun, singleAtom]
  have hlt_i : i.val < 2^(k+0) := by simp only [add_zero]; exact i.isLt
  have hlt_j : j.val < 2^(k+0) := by simp only [add_zero]; exact j.isLt
  have hij' : (⟨i.val, hlt_i⟩ : Fin (2^(k+0))) ≠ ⟨j.val, hlt_j⟩ := by
    intro h; apply hij; ext; exact Fin.mk.inj h
  exact atom_pairwiseDisjoint E (fun _ : Fin 0 => ∅) (by simp : i ∈ Set.univ) (by simp : j ∈ Set.univ) hij'

/-- Принадлежность singleAtom определяется битовым шаблоном -/
lemma mem_singleAtom_iff {X : Type*} {k : ℕ} (E : Fin k → Set X) (n : Fin (2^k)) (x : X) :
    x ∈ singleAtom E n ↔ ∀ i : Fin k, n.val.testBit i.val ↔ x ∈ E i := by
  simp only [singleAtom, atom, Set.mem_setOf_eq]
  constructor
  · intro ⟨h1, _⟩ i
    specialize h1 i
    rw [atomMembership_eq_testBit] at h1
    convert h1 using 1
  · intro h
    constructor
    · intro i
      rw [atomMembership_eq_testBit]
      exact h i
    · intro i; exact Fin.elim0 i

/-- Каждая точка лежит ровно в одном singleAtom -/
lemma exists_unique_singleAtom {X : Type*} [DecidableEq X] {k : ℕ} (E : Fin k → Set X) (x : X) :
    ∃! n : Fin (2^k), x ∈ singleAtom E n := by
  let n : ℕ := atomIndexOf E (fun _ : Fin 0 => ∅) x
  have hn_lt : n < 2^k := by
    have := atomIndexOf_lt E (fun _ : Fin 0 => ∅) x
    simp only [add_zero] at this
    exact this
  use ⟨n, hn_lt⟩
  constructor
  · simp only
    rw [mem_singleAtom_iff]
    intro i
    exact atomIndexOf_testBit_E E (fun _ : Fin 0 => ∅) x i
  · intro m hm
    ext
    rw [mem_singleAtom_iff] at hm
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < k
    · have h1 := hm ⟨j, hj⟩
      have h2 := atomIndexOf_testBit_E E (fun _ : Fin 0 => ∅) x ⟨j, hj⟩
      by_cases hx : x ∈ E ⟨j, hj⟩
      · rw [h1.mpr hx, h2.mpr hx]
      · have hm_false : (m.val.testBit j) = false := Bool.eq_false_iff.mpr (fun ht => hx (h1.mp ht))
        have hn_false : (n.testBit j) = false := Bool.eq_false_iff.mpr (fun ht => hx (h2.mp ht))
        rw [hm_false, hn_false]
    · have hm_lt : m.val < 2^k := m.isLt
      have hn_lt' : (atomIndexOf E (fun _ : Fin 0 => ∅) x) < 2^k := hn_lt
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm_lt (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (le_of_not_gt hj)))]
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hn_lt' (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (le_of_not_gt hj)))]

/-- Значение на атоме n — это сумма коэффициентов множеств, содержащих этот атом -/
noncomputable def atomValue {k : ℕ} (c : Fin k → ℝ) (n : Fin (2^k)) : ℝ :=
  ∑ i : Fin k, if n.val.testBit i.val then c i else 0

end UnsignedSimpleFunction.IntegralWellDef

/-- Lemma 1.3.4 (корректность определения простого интеграла) -/
lemma UnsignedSimpleFunction.integral_eq {d : ℕ} {f : EuclideanSpace' d → EReal} (hf : UnsignedSimpleFunction f) {k : ℕ} {c : Fin k → EReal}
    {E : Fin k → Set (EuclideanSpace' d)} (hmes : ∀ i, LebesgueMeasurable (E i)) (hnonneg : ∀ i, c i ≥ 0)
    (heq : f = ∑ i, (c i) • (EReal.indicator (E i))) :
    hf.integ = ∑ i, (c i) * Lebesgue_measure (E i) := by
  -- Извлекаем каноническое представление из hf
  -- hf даёт: ∃ k', ∃ (c': Fin k' → EReal) (E': Fin k' → Set _), (∀ i, LebesgueMeasurable (E' i) ∧ c' i ≥ 0) ∧ f = ∑...
  -- hf.choose_spec.choose — это c', hf.choose_spec.choose_spec.choose — это E'
  let k' := hf.choose
  let c' := hf.choose_spec.choose
  let E' := hf.choose_spec.choose_spec.choose
  have hmes'_nonneg : ∀ i, LebesgueMeasurable (E' i) ∧ c' i ≥ 0 := hf.choose_spec.choose_spec.choose_spec.1
  have heq' : f = ∑ i, (c' i) • (EReal.indicator (E' i)) := hf.choose_spec.choose_spec.choose_spec.2

  -- Каноническое представление тоже равно f
  have hfunc_eq : ∑ i, (c i) • (EReal.indicator (E i)) = ∑ i, (c' i) • (EReal.indicator (E' i)) := by
    rw [← heq, ← heq']

  -- Применяем основную лемму: два представления одной и той же функции дают одну и ту же взвешенную меру
  have h := IntegralWellDef.weightedMeasureSum_eq_of_eq
    hmes (fun i => (hmes'_nonneg i).1) hnonneg (fun i => (hmes'_nonneg i).2) hfunc_eq

  -- h утверждает: weightedMeasureSum c E = weightedMeasureSum c' E'
  -- Цель: ∑ i, (c' i) * Lebesgue_measure (E' i) = ∑ i, (c i) * Lebesgue_measure (E i)
  simp only [UnsignedSimpleFunction.IntegralWellDef.weightedMeasureSum] at h
  exact h.symm

/-- Definition 1.3.5 (almost always) -/
def AlmostAlways {d:ℕ} (P: EuclideanSpace' d → Prop) : Prop :=
  IsNull { x | ¬ P x }

/-- Definition 1.3.5 (almost everywhere equal) -/
def AlmostEverywhereEqual {d:ℕ} {X: Type*} (f g: EuclideanSpace' d → X) : Prop :=
  AlmostAlways (fun x ↦ f x = g x)

/-- Definition 1.3.5 (support) -/
def Support {X Y: Type*} [Zero Y] (f: X → Y) : Set X := { x | f x ≠ 0 }

lemma UnsignedSimpleFunction.support_measurable {d : ℕ} {f : EuclideanSpace' d → EReal} (hf : UnsignedSimpleFunction f) : LebesgueMeasurable (Support f) := by
  -- Извлекаем представление: f = ∑ i, c(i) • EReal.indicator(E_i)
  obtain ⟨k, c, E, hmes_nonneg, heq⟩ := hf
  -- Определяем E' i = E i, если c i > 0, иначе ∅
  let E' : Fin k → Set (EuclideanSpace' d) := fun i => if c i > 0 then E i else ∅
  -- Каждое E' i измеримо
  have hE'_meas : ∀ i, LebesgueMeasurable (E' i) := fun i => by
    simp only [E']
    split_ifs with h
    · exact (hmes_nonneg i).1
    · exact LebesgueMeasurable.empty
  -- Ключевой момент: Support f = ⋃ i, E' i
  have h_eq : Support f = ⋃ i, E' i := by
    ext x
    simp only [Support, Set.mem_setOf_eq, Set.mem_iUnion, E']
    constructor
    · -- (⊆) Если f(x) ≠ 0, то некоторое c_i > 0 и x ∈ E_i
      intro hne
      rw [heq] at hne
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hne
      -- Сумма неотрицательных членов ненулевая, значит некоторый член ненулевой
      have h_exists := Finset.exists_ne_zero_of_sum_ne_zero hne
      obtain ⟨i, _, hi_ne⟩ := h_exists
      use i
      -- c i * indicator ≠ 0 означает c i > 0 и x ∈ E i
      by_cases hc : c i > 0
      · simp only [hc, ↓reduceIte]
        by_cases hx : x ∈ E i
        · exact hx
        · -- Если x ∉ E i, то индикатор равен 0, значит c i * 0 = 0, противоречие
          simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_notMem hx,
                     EReal.coe_zero, mul_zero] at hi_ne
          exact absurd rfl hi_ne
      · -- c i ≤ 0, но c i ≥ 0, значит c i = 0
        have hc_zero : c i = 0 := le_antisymm (le_of_not_gt hc) (hmes_nonneg i).2
        simp only [hc_zero, zero_mul] at hi_ne
        exact absurd rfl hi_ne
    · -- (⊇) Если x ∈ E' i для некоторого i, то f(x) ≠ 0
      intro ⟨i, hi⟩
      split_ifs at hi with hc
      · -- c i > 0 и x ∈ E i
        rw [heq]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        -- f(x) ≥ c i * indicator(E i)(x) = c i > 0
        have h_term_pos : c i * EReal.indicator (E i) x > 0 := by
          simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_mem hi,
                     EReal.coe_one, mul_one]
          exact hc
        -- Сумма неотрицательных членов, среди которых один положительный, положительна
        have h_sum_nonneg : ∀ j, 0 ≤ c j * EReal.indicator (E j) x := fun j =>
          mul_nonneg (hmes_nonneg j).2 (EReal.indicator_nonneg' (E j) x)
        have h_sum_pos : 0 < ∑ j : Fin k, c j * EReal.indicator (E j) x := by
          calc 0 < c i * EReal.indicator (E i) x := h_term_pos
            _ ≤ ∑ j : Fin k, c j * EReal.indicator (E j) x :=
                Finset.single_le_sum (fun j _ => h_sum_nonneg j) (Finset.mem_univ i)
        exact ne_of_gt h_sum_pos
      · -- hi : x ∈ ∅, противоречие
        exact absurd hi (Set.notMem_empty x)
  rw [h_eq]
  exact LebesgueMeasurable.finite_union hE'_meas

lemma AlmostAlways.ofAlways {d : ℕ} {P : EuclideanSpace' d → Prop} (h : ∀ x, P x) : AlmostAlways P := by
  -- AlmostAlways P означает IsNull { x | ¬ P x }, т.е. Lebesgue_outer_measure { x | ¬ P x } = 0
  -- Если ∀ x, P x, то { x | ¬ P x } = ∅
  unfold AlmostAlways IsNull
  have h_empty : { x | ¬ P x } = ∅ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    exact h x
  rw [h_empty]
  exact Lebesgue_outer_measure.of_empty d

lemma AlmostAlways.mp {d : ℕ} {P Q : EuclideanSpace' d → Prop} (hP : AlmostAlways P) (himp : ∀ x, P x → Q x) : AlmostAlways Q := by
  -- AlmostAlways P означает IsNull { x | ¬ P x }, т.е. Lebesgue_outer_measure { x | ¬ P x } = 0
  -- Если P → Q всюду, то ¬Q → ¬P (по контрапозиции), значит { x | ¬ Q x } ⊆ { x | ¬ P x }
  unfold AlmostAlways IsNull at *
  -- hP : Lebesgue_outer_measure { x | ¬ P x } = 0
  -- Цель: Lebesgue_outer_measure { x | ¬ Q x } = 0
  have h_subset : { x | ¬ Q x } ⊆ { x | ¬ P x } := by
    intro x hx
    simp only [Set.mem_setOf_eq] at *
    exact fun hp => hx (himp x hp)
  -- По монотонности: measure { x | ¬ Q x } ≤ measure { x | ¬ P x } = 0
  have h_le := Lebesgue_outer_measure.mono h_subset
  rw [hP] at h_le
  exact le_antisymm h_le (Lebesgue_outer_measure.nonneg _)

lemma AlmostAlways.countable {d : ℕ} {I : Type*} [Countable I] {P : I → EuclideanSpace' d → Prop} (hP : ∀ i, AlmostAlways (P i)) : AlmostAlways (fun x ↦ ∀ i, P i x) := by
  -- AlmostAlways (fun x ↦ ∀ i, P i x) означает IsNull { x | ¬ ∀ i, P i x }
  -- { x | ¬ ∀ i, P i x } = { x | ∃ i, ¬ P i x } = ⋃ᵢ { x | ¬ P i x }
  -- Каждое { x | ¬ P i x } нулевое по hP, а счётное объединение нулевых множеств нулевое
  unfold AlmostAlways IsNull at *
  -- Цель: Lebesgue_outer_measure { x | ¬ ∀ i, P i x } = 0
  -- hP i : Lebesgue_outer_measure { x | ¬ P i x } = 0
  have h_eq : { x | ¬ ∀ i, P i x } = ⋃ i, { x | ¬ P i x } := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, not_forall]
  rw [h_eq]
  -- Нужно: Lebesgue_outer_measure (⋃ i, { x | ¬ P i x }) = 0
  -- Используем счётность типа I через Encodable
  cases nonempty_encodable I with
  | intro enc =>
    -- Теперь есть Encodable I, можно использовать объединение, индексированное ℕ
    -- Переиндексируем через Encodable.encode
    let E' : ℕ → Set (EuclideanSpace' d) := fun n => match @Encodable.decode I enc n with
      | some i => { x | ¬ P i x }
      | none => ∅
    have h_subset : (⋃ i : I, { x | ¬ P i x }) ⊆ ⋃ n : ℕ, E' n := by
      intro x hx
      simp only [Set.mem_iUnion] at hx ⊢
      obtain ⟨i, hi⟩ := hx
      use @Encodable.encode I enc i
      simp only [E', @Encodable.encodek I enc]
      exact hi
    have h_le := Lebesgue_outer_measure.mono h_subset
    have h_E'_null : ∀ n, Lebesgue_outer_measure (E' n) = 0 := fun n => by
      simp only [E']
      cases h : @Encodable.decode I enc n with
      | none => exact Lebesgue_outer_measure.of_empty d
      | some i => exact hP i
    -- По счётной субаддитивности: m(⋃ E'_n) ≤ ∑' n, m(E'_n) = ∑' n, 0 = 0
    have h_sum_zero : ∑' n, Lebesgue_outer_measure (E' n) = 0 := by
      simp only [h_E'_null, tsum_zero]
    have h_union_le := Lebesgue_outer_measure.union_le E'
    have h_bound : Lebesgue_outer_measure (⋃ i : I, { x | ¬ P i x }) ≤ 0 :=
      calc Lebesgue_outer_measure (⋃ i : I, { x | ¬ P i x })
          ≤ Lebesgue_outer_measure (⋃ n, E' n) := h_le
        _ ≤ ∑' n, Lebesgue_outer_measure (E' n) := h_union_le
        _ = 0 := h_sum_zero
    exact le_antisymm h_bound (Lebesgue_outer_measure.nonneg _)

/-- Равенство почти всюду рефлексивно -/
lemma AlmostEverywhereEqual.refl {d : ℕ} {X : Type*} (f : EuclideanSpace' d → X) :
    AlmostEverywhereEqual f f :=
  -- {x | f x ≠ f x} = ∅, что нулевое
  AlmostAlways.ofAlways (fun _ => rfl)

/-- Равенство почти всюду симметрично -/
lemma AlmostEverywhereEqual.symm {d : ℕ} {X : Type*} {f g : EuclideanSpace' d → X}
    (h : AlmostEverywhereEqual f g) : AlmostEverywhereEqual g f := by
  -- {x | g x ≠ f x} = {x | f x ≠ g x}, то же множество
  unfold AlmostEverywhereEqual AlmostAlways IsNull at *
  convert h using 2
  ext x
  exact ne_comm

/-- Равенство почти всюду транзитивно -/
lemma AlmostEverywhereEqual.trans {d : ℕ} {X : Type*} {f g h : EuclideanSpace' d → X}
    (hfg : AlmostEverywhereEqual f g) (hgh : AlmostEverywhereEqual g h) :
    AlmostEverywhereEqual f h := by
  -- {x | f x ≠ h x} ⊆ {x | f x ≠ g x} ∪ {x | g x ≠ h x}
  -- Объединение двух нулевых множеств нулевое
  unfold AlmostEverywhereEqual AlmostAlways IsNull at *
  have h_subset : {x | f x ≠ h x} ⊆ {x | f x ≠ g x} ∪ {x | g x ≠ h x} := by
    intro x hx
    simp only [Set.mem_setOf_eq, Set.mem_union] at *
    by_contra hc
    push_neg at hc
    exact hx (hc.1.trans hc.2)
  -- Представляем объединение как ℕ-индексированное для счётной субаддитивности
  let E : ℕ → Set (EuclideanSpace' d) := fun n =>
    match n with
    | 0 => {x | f x ≠ g x}
    | 1 => {x | g x ≠ h x}
    | _ => ∅
  have h_union_eq : {x | f x ≠ g x} ∪ {x | g x ≠ h x} = ⋃ n, E n := by
    ext x
    simp only [Set.mem_union, Set.mem_iUnion, E]
    constructor
    · intro hx
      cases hx with
      | inl hl => exact ⟨0, hl⟩
      | inr hr => exact ⟨1, hr⟩
    · intro ⟨n, hn⟩
      match n with
      | 0 => exact Or.inl hn
      | 1 => exact Or.inr hn
      | n + 2 => exact absurd hn (Set.notMem_empty x)
  have h_E_null : ∀ n, Lebesgue_outer_measure (E n) = 0 := fun n => by
    match n with
    | 0 => exact hfg
    | 1 => exact hgh
    | n + 2 => exact Lebesgue_outer_measure.of_empty d
  have h_sum_zero : ∑' n, Lebesgue_outer_measure (E n) = 0 := by simp only [h_E_null, tsum_zero]
  have h_union_le := Lebesgue_outer_measure.union_le E
  have h_bound : Lebesgue_outer_measure {x | f x ≠ h x} ≤ 0 :=
    calc Lebesgue_outer_measure {x | f x ≠ h x}
        ≤ Lebesgue_outer_measure (⋃ n, E n) := by rw [← h_union_eq]; exact Lebesgue_outer_measure.mono h_subset
      _ ≤ ∑' n, Lebesgue_outer_measure (E n) := h_union_le
      _ = 0 := h_sum_zero
  exact le_antisymm h_bound (Lebesgue_outer_measure.nonneg _)

/-- Равенство почти всюду является отношением эквивалентности -/
theorem AlmostEverywhereEqual.equivalence {d : ℕ} {X : Type*} :
    Equivalence (@AlmostEverywhereEqual d X) :=
  ⟨refl, symm, trans⟩

/-- Exercise 1.3.1 (i) (Unsigned linearity, sum) -/
lemma UnsignedSimpleFunction.integral_add {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) (hg: UnsignedSimpleFunction g) :
  (hf.add hg).integ = hf.integ + hg.integ := by
  sorry

/-- Exercise 1.3.1 (i) (Unsigned linearity, scalar multiple) -/
lemma UnsignedSimpleFunction.integral_smul {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) {c:EReal} (hc: c ≥ 0) :
  (hf.smul hc).integ = c * hf.integ := by
  sorry

/-- Exercise 1.3.1 (ii) (конечность) -/
lemma UnsignedSimpleFunction.integral_finite_iff {d : ℕ} {f : EuclideanSpace' d → EReal} (hf : UnsignedSimpleFunction f) : 
  (hf.integ < ⊤) ↔ (AlmostAlways (fun x ↦ f x < ⊤)) ∧ (Lebesgue_measure (Support f)) < ⊤ := by
  sorry

/-- Exercise 1.3.1 (iii) (обращение в ноль) -/
lemma UnsignedSimpleFunction.integral_eq_zero_iff {d : ℕ} {f : EuclideanSpace' d → EReal} (hf : UnsignedSimpleFunction f) : 
  (hf.integ = 0) ↔ AlmostAlways (fun x ↦ f x = 0) := by
  sorry

/-- Exercise 1.3.1 (iv) (эквивалентность) -/
lemma UnsignedSimpleFunction.integral_eq_integral_of_aeEqual {d : ℕ} {f g : EuclideanSpace' d → EReal} (hf : UnsignedSimpleFunction f) (hg : UnsignedSimpleFunction g)
  (hae : AlmostEverywhereEqual f g) : 
  hf.integ = hg.integ := by
  sorry

/-- Exercise 1.3.1 (v) (монотонность) -/
lemma UnsignedSimpleFunction.integral_le_integral_of_aeLe {d : ℕ} {f g : EuclideanSpace' d → EReal} (hf : UnsignedSimpleFunction f) (hg : UnsignedSimpleFunction g)
  (hae : AlmostAlways (fun x ↦ f x ≤ g x)) : 
  hf.integ ≤ hg.integ := by
  sorry

/-- Exercise 1.3.1(vi) (Compatibility with Lebesgue measure, indicator) -/
lemma UnsignedSimpleFunction.indicator {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) :
  UnsignedSimpleFunction (Real.toEReal ∘ E.indicator') := by
  sorry

/-- Exercise 1.3.1(vi) (Compatibility with Lebesgue measure, integral of an indicator) -/
lemma UnsignedSimpleFunction.integral_indicator {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) :
  (UnsignedSimpleFunction.indicator hE).integ = Lebesgue_measure E := by
  sorry

lemma RealSimpleFunction.abs {d : ℕ} {f : EuclideanSpace' d → ℝ} (hf : RealSimpleFunction f) : UnsignedSimpleFunction (EReal.abs_fun f) := by
  sorry

lemma ComplexSimpleFunction.abs {d : ℕ} {f : EuclideanSpace' d → ℂ} (hf : ComplexSimpleFunction f) : UnsignedSimpleFunction (EReal.abs_fun f) := by
  sorry

/-- Definition 1.3.6 (Absolutely convergent simple integral, real) -/
def RealSimpleFunction.AbsolutelyIntegrable {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) : Prop :=
  (hf.abs).integ < ⊤

/-- Definition 1.3.6 (Absolutely convergent simple integral, complex) -/
def ComplexSimpleFunction.AbsolutelyIntegrable {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) : Prop :=
  (hf.abs).integ < ⊤

/-! ## Несвязное представление для {name}`RealSimpleFunction`

Специфичные для теории меры леммы о несвязном представлении простых функций. -/

namespace RealSimpleFunction.DisjointRepr

open UnsignedSimpleFunction.IntegralWellDef

/-- Одиночные атомы измеримы -/
lemma singleAtom_measurable {d k : ℕ} {E : Fin k → Set (EuclideanSpace' d)}
    (hE : ∀ i, LebesgueMeasurable (E i)) (n : Fin (2^k)) :
    LebesgueMeasurable (singleAtom E n) := by
  simp only [singleAtom]
  exact atom_measurable hE (fun i => Fin.elim0 i) ⟨n.val, by simp only [add_zero]; exact n.isLt⟩

/-- В точке, принадлежащей singleAtom n, исходная сумма равна atomValue n -/
lemma sum_indicator_eq_atomValue {d k : ℕ} (c : Fin k → ℝ) (E : Fin k → Set (EuclideanSpace' d))
    (n : Fin (2^k)) (x : EuclideanSpace' d) (hx : x ∈ singleAtom E n) :
    (∑ i : Fin k, (c i) * (E i).indicator' x) = atomValue c n := by
  simp only [atomValue]
  apply Finset.sum_congr rfl
  intro i _
  rw [mem_singleAtom_iff] at hx
  by_cases hbit : (n.val.testBit i.val) = true
  · simp only [hbit, ↓reduceIte]
    have hx_in : x ∈ E i := (hx i).mp hbit
    simp only [Set.indicator'_of_mem hx_in, mul_one]
  · have hbit_false : (n.val.testBit i.val) = false := Bool.eq_false_iff.mpr hbit
    have hx_out : x ∉ E i := fun h => hbit ((hx i).mpr h)
    simp only [Set.indicator'_of_notMem hx_out, mul_zero, hbit_false, Bool.false_eq_true,
      ↓reduceIte]

/-- Исходная функция равна сумме по атомам с коэффициентами atomValue -/
lemma eq_sum_atomValue_indicator {d k : ℕ} (c : Fin k → ℝ) (E : Fin k → Set (EuclideanSpace' d)) :
    (∑ i : Fin k, (c i) • (E i).indicator') = ∑ n : Fin (2^k), (atomValue c n) • (singleAtom E n).indicator' := by
  classical
  ext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have ⟨n, hn_mem, hn_unique⟩ := exists_unique_singleAtom E x
  have hrhs : (∑ m : Fin (2^k), atomValue c m * (singleAtom E m).indicator' x) = atomValue c n := by
    rw [Finset.sum_eq_single n]
    · simp only [Set.indicator'_of_mem hn_mem, mul_one]
    · intro m _ hm_ne
      have hx_notin : x ∉ singleAtom E m := fun h => hm_ne (hn_unique m h)
      simp only [Set.indicator'_of_notMem hx_notin, mul_zero]
    · intro h; exact absurd (Finset.mem_univ n) h
  rw [hrhs]
  exact sum_indicator_eq_atomValue c E n x hn_mem

end RealSimpleFunction.DisjointRepr

/-- Несвязное представление: любая {name}`RealSimpleFunction` имеет эквивалентное представление
    через попарно непересекающиеся измеримые множества. -/
lemma RealSimpleFunction.disjoint_representation {d : ℕ} {f : EuclideanSpace' d → ℝ} (hf : RealSimpleFunction f) :
    ∃ (n : ℕ) (v : Fin n → ℝ) (A : Fin n → Set (EuclideanSpace' d)),
      (∀ i, LebesgueMeasurable (A i)) ∧
      Set.univ.PairwiseDisjoint A ∧
      f = ∑ i, (v i) • (A i).indicator' := by
  open UnsignedSimpleFunction.IntegralWellDef in
  obtain ⟨k, c, E, hmes, heq⟩ := hf
  use 2^k, UnsignedSimpleFunction.IntegralWellDef.atomValue c,
      UnsignedSimpleFunction.IntegralWellDef.singleAtom E
  refine ⟨?_, ?_, ?_⟩
  · exact fun i => DisjointRepr.singleAtom_measurable hmes i
  · exact UnsignedSimpleFunction.IntegralWellDef.singleAtom_pairwiseDisjoint E
  · rw [heq]
    exact DisjointRepr.eq_sum_atomValue_indicator c E

def RealSimpleFunction.pos {d : ℕ} {f : EuclideanSpace' d → ℝ} (hf : RealSimpleFunction f) : UnsignedSimpleFunction (EReal.pos_fun f) := by
  -- Используем несвязное представление: f = ∑ i, v_i • A_i.indicator' с непересекающимися A_i
  obtain ⟨n, v, A, hA_meas, hA_disj, heq⟩ := hf.disjoint_representation
  -- Положительная часть равна ∑ i, (max(v_i, 0)).toEReal • EReal.indicator(A_i)
  use n, fun i => (max (v i) 0).toEReal, A
  constructor
  · intro i
    constructor
    · exact hA_meas i
    · exact EReal.coe_nonneg.mpr (le_max_right (v i) 0)
  · ext x
    simp only [EReal.pos_fun, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    -- Поскольку атомы не пересекаются, x лежит не более чем в одном атоме
    by_cases hx_in : ∃ j, x ∈ A j
    · -- x лежит ровно в одном атоме благодаря непересекаемости (используем версию с exists)
      obtain ⟨j, hj⟩ := hx_in
      -- В обеих суммах только один ненулевой член
      have hlhs : f x = v j := by
        rw [heq]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [Finset.sum_eq_single j]
        · simp only [Set.indicator'_of_mem hj, mul_one]
        · intro i _ hi_ne
          have hx_notin : x ∉ A i := by
            intro hx_in_i
            have := hA_disj (Set.mem_univ i) (Set.mem_univ j) hi_ne
            simp only [Function.onFun, Set.disjoint_left] at this
            exact this hx_in_i hj
          simp only [Set.indicator'_of_notMem hx_notin, mul_zero]
        · intro h; exact absurd (Finset.mem_univ j) h
      have hrhs : (∑ i : Fin n, (max (v i) 0).toEReal * EReal.indicator (A i) x) =
                  (max (v j) 0).toEReal := by
        rw [Finset.sum_eq_single j]
        · simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_mem hj, EReal.coe_one, mul_one]
        · intro i _ hi_ne
          have hx_notin : x ∉ A i := by
            intro hx_in_i
            have := hA_disj (Set.mem_univ i) (Set.mem_univ j) hi_ne
            simp only [Function.onFun, Set.disjoint_left] at this
            exact this hx_in_i hj
          simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_notMem hx_notin, EReal.coe_zero, mul_zero]
        · intro h; exact absurd (Finset.mem_univ j) h
      rw [hlhs, hrhs]
    · -- x не лежит ни в одном атоме, значит f(x) = 0
      push_neg at hx_in
      have hlhs : f x = 0 := by
        rw [heq]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        apply Finset.sum_eq_zero
        intro i _
        simp only [Set.indicator'_of_notMem (hx_in i), mul_zero]
      have hrhs : (∑ i : Fin n, (max (v i) 0).toEReal * EReal.indicator (A i) x) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_notMem (hx_in i), EReal.coe_zero, mul_zero]
      rw [hlhs, hrhs]
      simp only [max_self, EReal.coe_zero]

def RealSimpleFunction.neg {d : ℕ} {f : EuclideanSpace' d → ℝ} (hf : RealSimpleFunction f) : UnsignedSimpleFunction (EReal.neg_fun f) := by
  -- neg_fun f = pos_fun (-f), а -f = (-1) • f является простой функцией
  have h : EReal.neg_fun f = EReal.pos_fun ((-1 : ℝ) • f) := by
    ext x; simp only [EReal.neg_fun, EReal.pos_fun, Pi.smul_apply, smul_eq_mul, neg_one_mul]
  rw [h]
  exact (hf.smul (-1)).pos

noncomputable def RealSimpleFunction.integ {d : ℕ} {f : EuclideanSpace' d → ℝ} (hf : RealSimpleFunction f) : ℝ := (hf.pos).integ.toReal - (hf.neg).integ.toReal

def ComplexSimpleFunction.re {d : ℕ} {f : EuclideanSpace' d → ℂ} (hf : ComplexSimpleFunction f) : RealSimpleFunction (Complex.re_fun f) := by
  -- Если f = ∑ i, c_i • Complex.indicator(E_i), то Re(f) = ∑ i, Re(c_i) • indicator'(E_i)
  obtain ⟨k, c, E, hmes, heq⟩ := hf
  use k, fun i => (c i).re, E
  constructor
  · exact hmes
  · ext x
    simp only [Complex.re_fun, heq, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    -- Цель: (∑ i, c i * Complex.indicator (E i) x).re = ∑ i, (c i).re * (E i).indicator' x
    rw [Complex.re_sum]
    congr 1; ext i
    -- Цель: (c i * Complex.indicator (E i) x).re = (c i).re * (E i).indicator' x
    simp only [Complex.indicator, Real.complex_fun]
    rw [Complex.re_mul_ofReal]

def ComplexSimpleFunction.im {d : ℕ} {f : EuclideanSpace' d → ℂ} (hf : ComplexSimpleFunction f) : RealSimpleFunction (Complex.im_fun f) := by
  -- Если f = ∑ i, c_i • Complex.indicator(E_i), то Im(f) = ∑ i, Im(c_i) • indicator'(E_i)
  obtain ⟨k, c, E, hmes, heq⟩ := hf
  use k, fun i => (c i).im, E
  constructor
  · exact hmes
  · ext x
    simp only [Complex.im_fun, heq, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    -- Цель: (∑ i, c i * Complex.indicator (E i) x).im = ∑ i, (c i).im * (E i).indicator' x
    rw [Complex.im_sum]
    congr 1; ext i
    -- Цель: (c i * Complex.indicator (E i) x).im = (c i).im * (E i).indicator' x
    simp only [Complex.indicator, Real.complex_fun]
    rw [Complex.im_mul_ofReal]

noncomputable def ComplexSimpleFunction.integ {d : ℕ} {f : EuclideanSpace' d → ℂ} (hf : ComplexSimpleFunction f) : ℂ :=
  hf.re.integ + Complex.I * hf.im.integ

lemma RealSimpleFunction.absolutelyIntegrable_iff {d : ℕ} {f : EuclideanSpace' d → ℝ} (hf : RealSimpleFunction f) : hf.AbsolutelyIntegrable ↔ Lebesgue_measure (Support f) < ⊤ := by
  sorry

lemma ComplexSimpleFunction.absolutelyIntegrable_iff {d : ℕ} {f : EuclideanSpace' d → ℂ} (hf : ComplexSimpleFunction f) : hf.AbsolutelyIntegrable ↔ Lebesgue_measure (Support f) < ⊤ := by
  sorry

lemma RealSimpleFunction.AbsolutelyIntegrable.add {d : ℕ} {f g : EuclideanSpace' d → ℝ} {hf : RealSimpleFunction f} {hg : RealSimpleFunction g} (hf_integ : hf.AbsolutelyIntegrable) (hg_integ : hg.AbsolutelyIntegrable) : 
  (hf.add hg).AbsolutelyIntegrable := by sorry

lemma ComplexSimpleFunction.AbsolutelyIntegrable.add {d : ℕ} {f g : EuclideanSpace' d → ℂ} {hf : ComplexSimpleFunction f} {hg : ComplexSimpleFunction g} (hf_integ : hf.AbsolutelyIntegrable) (hg_integ : hg.AbsolutelyIntegrable) : 
  (hf.add hg).AbsolutelyIntegrable := by sorry

lemma RealSimpleFunction.AbsolutelyIntegrable.smul {d : ℕ} {f : EuclideanSpace' d → ℝ} {hf : RealSimpleFunction f} (hf_integ : hf.AbsolutelyIntegrable) (a : ℝ) : 
  (hf.smul a).AbsolutelyIntegrable := by sorry

lemma ComplexSimpleFunction.AbsolutelyIntegrable.smul {d : ℕ} {f : EuclideanSpace' d → ℂ} {hf : ComplexSimpleFunction f} (hf_integ : hf.AbsolutelyIntegrable) (a : ℂ) : 
  (hf.smul a).AbsolutelyIntegrable := by sorry

lemma ComplexSimpleFunction.AbsolutelyIntegrable.conj {d : ℕ} {f : EuclideanSpace' d → ℂ} {hf : ComplexSimpleFunction f} (hf_integ : hf.AbsolutelyIntegrable) : 
  (hf.conj).AbsolutelyIntegrable := by sorry

/-- Exercise 1.3.2 (i) ({lit}`*`-linearity, sum) -/
lemma RealSimpleFunction.integ_add {d:ℕ} {f g: EuclideanSpace' d → ℝ} {hf: RealSimpleFunction f} {hg: RealSimpleFunction g} (hf_integ: hf.AbsolutelyIntegrable) (hg_integ: hg.AbsolutelyIntegrable) : (hf.add hg).integ = hf.integ + hg.integ := by sorry

lemma ComplexSimpleFunction.integ_add {d : ℕ} {f g : EuclideanSpace' d → ℂ} {hf : ComplexSimpleFunction f} {hg : ComplexSimpleFunction g} (hf_integ : hf.AbsolutelyIntegrable) (hg_integ : hg.AbsolutelyIntegrable) : (hf.add hg).integ = hf.integ + hg.integ := by
  sorry

/-- Exercise 1.3.2 (i) ({lit}`*`-linearity, scalar multiple) -/
lemma RealSimpleFunction.integ_smul {d:ℕ} {f: EuclideanSpace' d → ℝ} {hf: RealSimpleFunction f} (hf_integ: hf.AbsolutelyIntegrable) (a: ℝ) : (hf.smul a).integ = a * hf.integ := by
  sorry

lemma ComplexSimpleFunction.integ_smul {d : ℕ} {f : EuclideanSpace' d → ℂ} {hf : ComplexSimpleFunction f} (hf_integ : hf.AbsolutelyIntegrable) (a : ℂ) : (hf.smul a).integ = a * hf.integ := by
  sorry

/-- Exercise 1.3.2 (i) ({lit}`*`-linearity, conjugation) -/
lemma ComplexSimpleFunction.integral_conj {d:ℕ} {f: EuclideanSpace' d → ℂ} {hf: ComplexSimpleFunction f} (hf_integ: hf.AbsolutelyIntegrable) : (hf.conj).integ = (starRingEnd ℂ) hf.integ := by
  sorry

/-- Exercise 1.3.2 (ii) (эквивалентность) -/
lemma RealSimpleFunction.integral_eq_integral_of_aeEqual {d : ℕ} {f g : EuclideanSpace' d → ℝ} {hf : RealSimpleFunction f} {hg : RealSimpleFunction g} (hf_integ : hf.AbsolutelyIntegrable) (hg_integ : hg.AbsolutelyIntegrable) (h_ae : AlmostEverywhereEqual f g) : hf.integ = hg.integ := by
  sorry

lemma ComplexSimpleFunction.integral_eq_integral_of_aeEqual {d : ℕ} {f g : EuclideanSpace' d → ℂ} {hf : ComplexSimpleFunction f} {hg : ComplexSimpleFunction g} (hf_integ : hf.AbsolutelyIntegrable) (hg_integ : hg.AbsolutelyIntegrable) (h_ae : AlmostEverywhereEqual f g) : hf.integ = hg.integ := by
  sorry

/-- Exercise 1.3.2(iii) (Compatibility with Lebesgue measure, indicator) -/
lemma RealSimpleFunction.indicator {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) :
  RealSimpleFunction (E.indicator') := by
  sorry

lemma ComplexSimpleFunction.indicator {d : ℕ} {E : Set (EuclideanSpace' d)} (hE : LebesgueMeasurable E) : 
  ComplexSimpleFunction (Complex.indicator E) := by
  sorry

/-- Exercise 1.3.2(iii) (Compatibility with Lebesgue measure, integral of an indicator) -/
lemma RealSimpleFunction.integral_indicator {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) (hfin: Lebesgue_measure E < ⊤): (RealSimpleFunction.indicator hE).integ = (Lebesgue_measure E).toReal := by
  sorry

lemma ComplexSimpleFunction.integral_indicator {d : ℕ} {E : Set (EuclideanSpace' d)} (hE : LebesgueMeasurable E) (hfin : Lebesgue_measure E < ⊤) : (ComplexSimpleFunction.indicator hE).integ = (Lebesgue_measure E).toReal := by
  sorry
