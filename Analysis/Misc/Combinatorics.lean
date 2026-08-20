import Mathlib.Tactic

/-!
# Комбинаторные вспомогательные утверждения

Общие комбинаторные леммы про Fin, Finset и булевы выборы.
-/

/-- Дистрибутивный закон: произведение сумм по Fin d равно сумме по булевым выборам произведений.
    Это ключевое тождество: ∏ᵢ (aᵢ + bᵢ) = ∑\_\{c : Fin d → Bool\} ∏ᵢ (if cᵢ then bᵢ else aᵢ) -/
lemma Fin.prod_add_eq_sum_prod_choice (d : ℕ) (a b : Fin d → ℝ) : 
    ∏ i, (a i + b i) = ∑ c : Fin d → Bool, ∏ i, (if c i then b i else a i) := by
  induction d with
  | zero =>
    -- Пустое произведение = 1, и существует ровно одна функция Fin 0 → Bool
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    have h_card : (Finset.univ : Finset (Fin 0 → Bool)).card = 1 := by simp
    rw [Finset.card_eq_one] at h_card
    obtain ⟨f, hf⟩ := h_card
    simp only [hf, Finset.sum_singleton]
  | succ d ih =>
    -- Отделяем первую координату: ∏_{i:Fin(d+1)} = (первый множитель) * ∏_{i:Fin d}
    rw [Fin.prod_univ_succ]
    -- Применяем индукционное предположение к хвосту
    let a' : Fin d → ℝ := fun i => a i.succ
    let b' : Fin d → ℝ := fun i => b i.succ
    have h_tail : ∏ i : Fin d, (a i.succ + b i.succ) = ∏ i, (a' i + b' i) := rfl
    rw [h_tail, ih a' b']
    -- Раскрываем: (a 0 + b 0) * (∑ c', ...) = b 0 * (∑ c', ...) + a 0 * (∑ c', ...)
    rw [add_comm (a 0) (b 0), add_mul, Finset.mul_sum, Finset.mul_sum]
    -- Разбиваем сумму в правой части по первому биту: ∑_c = ∑_{c 0 = true} + ∑_{c 0 = false}
    symm
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun c : Fin (d+1) → Bool => c 0)]
    -- Теперь: (∑_{c 0 = true} ...) + (∑_{c 0 = false} ...) = b 0 * (...) + a 0 * (...)
    congr 1
    · -- случай c 0 = true
      have h_factor : ∀ c ∈ Finset.filter (fun c : Fin (d+1) → Bool => c 0) Finset.univ,
          ∏ i, (if c i then b i else a i) =
          b 0 * ∏ i : Fin d, (if c i.succ then b' i else a' i) := by
        intro c hc
        rw [Fin.prod_univ_succ]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
        simp only [hc, ↓reduceIte, a', b']
      rw [Finset.sum_congr rfl h_factor, ← Finset.mul_sum]
      -- Теперь цель: b 0 * (∑ c ∈ filter, ∏...) = b 0 * (∑ c' ∈ univ, ∏...)
      -- Нужно показать равенство сумм, а затем домножить на b 0
      have h_sum_eq : ∑ c ∈ Finset.filter (fun c : Fin (d+1) → Bool => c 0) Finset.univ,
          ∏ i : Fin d, (if c i.succ then b' i else a' i) =
          ∑ c' : Fin d → Bool, ∏ i, (if c' i then b' i else a' i) := by
        symm
        refine Finset.sum_bij (fun (c' : Fin d → Bool) _ => Fin.cons true c') ?_ ?_ ?_ ?_
        · intro c' _
          simp only [Finset.mem_filter, Finset.mem_univ, Fin.cons_zero, true_and]
        · intro c₁ _ c₂ _ heq
          simp only at heq
          funext i
          have h : (Fin.cons true c₁ : Fin (d+1) → Bool) i.succ =
                   (Fin.cons true c₂ : Fin (d+1) → Bool) i.succ := by rw [heq]
          simp only [Fin.cons_succ] at h
          exact h
        · intro c hc
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
          refine ⟨fun i => c i.succ, Finset.mem_univ _, ?_⟩
          funext i; cases' i using Fin.cases with i
          · simp only [Fin.cons_zero]; exact hc.symm
          · simp only [Fin.cons_succ]
        · intro c' _
          apply Finset.prod_congr rfl; intro i _
          simp only [Fin.cons_succ]
      rw [h_sum_eq, Finset.mul_sum]
    · -- случай c 0 = false
      have h_factor : ∀ c ∈ Finset.filter (fun c : Fin (d+1) → Bool => ¬c 0) Finset.univ,
          ∏ i, (if c i then b i else a i) =
          a 0 * ∏ i : Fin d, (if c i.succ then b' i else a' i) := by
        intro c hc
        rw [Fin.prod_univ_succ]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
        simp only [Bool.eq_false_iff.mpr hc, Bool.false_eq_true, ↓reduceIte, a', b']
      rw [Finset.sum_congr rfl h_factor, ← Finset.mul_sum]
      have h_sum_eq : ∑ c ∈ Finset.filter (fun c : Fin (d+1) → Bool => ¬c 0) Finset.univ,
          ∏ i : Fin d, (if c i.succ then b' i else a' i) =
          ∑ c' : Fin d → Bool, ∏ i, (if c' i then b' i else a' i) := by
        symm
        refine Finset.sum_bij (fun (c' : Fin d → Bool) _ => Fin.cons false c') ?_ ?_ ?_ ?_
        · intro c' _
          simp only [Finset.mem_filter, Finset.mem_univ, Fin.cons_zero]
          trivial
        · intro c₁ _ c₂ _ heq
          simp only at heq
          funext i
          have h : (Fin.cons false c₁ : Fin (d+1) → Bool) i.succ =
                   (Fin.cons false c₂ : Fin (d+1) → Bool) i.succ := by rw [heq]
          simp only [Fin.cons_succ] at h
          exact h
        · intro c hc
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
          refine ⟨fun i => c i.succ, Finset.mem_univ _, ?_⟩
          funext i; cases' i using Fin.cases with i
          · simp only [Fin.cons_zero]; exact (Bool.eq_false_iff.mpr hc).symm
          · simp only [Fin.cons_succ]
        · intro c' _
          apply Finset.prod_congr rfl; intro i _
          simp only [Fin.cons_succ]
      rw [h_sum_eq, Finset.mul_sum]
