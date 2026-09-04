import Mathlib.Tactic
import Analysis.Section_6_4
import Analysis.Section_7_4
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Analysis I, раздел 7.5: Признаки Коши и Даламбера

Я старался сделать перевод максимально точным перефразированием оригинального текста. Когда приходилось выбирать между более идиоматичным Lean-решением и более точным переводом, я, как правило, выбирал второе. В частности, местами Lean-код можно было бы "заголфить", сделав его более элегантным и идиоматичным, но я сознательно этого избегал.

Основные конструкции и результаты этого раздела:

- Признаки Коши (корневой) и Даламбера (по отношению).

Момент, который в тексте лишь подразумевается: для этих признаков lim inf и lim sup следует
понимать в расширенных вещественных числах. Приведённые ниже формализации на Lean делают это
явным.

-/

namespace Chapter7

open Filter Real EReal

/-- Теорема 7.5.1(a) (признак Коши). Нужно техническое условие, гарантирующее конечность limsup. -/
theorem Series.root_test_pos {s : Series}
  (h : atTop.limsup (fun n ↦ ((|s.seq n|^(1/(n : ℝ)) : ℝ) : EReal)) < 1) : s.absConverges := by
    -- Это доказательство написано так, чтобы следовать структуре оригинального текста.
    set α' : EReal := atTop.limsup (fun n ↦ ↑(|s.seq n|^(1/(n : ℝ)) : ℝ))
    have hpos : 0 ≤ α' := by
      apply le_limsup_of_frequently_le (Frequently.of_forall _) (by isBoundedDefault)
      intros; positivity
    set α := α'.toReal
    have hαα' : α' = α := by
      symm; apply coe_toReal
      . contrapose! h; simp [h]; exact le_top
      contrapose! hpos; simp [hpos]
    rw [hαα'] at h hpos; norm_cast at h hpos
    set ε := (1-α)/2
    have hε : 0 < ε := by simp [ε]; linarith
    have hε' : α' < (α+ε : ℝ) := by rw [hαα', EReal.coe_lt_coe_iff]; linarith
    have hα : α + ε < 1 := by simp [ε]; linarith
    have hα' : 0 < α + ε := by linarith
    have := eventually_lt_of_limsup_lt hε' (by isBoundedDefault)
    rw [eventually_atTop] at this
    choose N' hN using this; set N := max N' (max s.m 1)
    have (n : ℤ) (hn : n ≥ N) : |s.seq n| ≤ (α + ε)^n := by
      have : n ≥ N' := by omega
      have npos : 0 < n := by omega
      specialize hN n this
      rw [EReal.coe_lt_coe_iff] at hN
      calc
        _ = (|s.seq n|^(1/(n : ℝ)))^n := by
          rw [←rpow_intCast, ←rpow_mul (by positivity)]
          symm; convert rpow_one _; field_simp
        _ ≤ _ := by
          convert pow_le_pow_left₀ (by positivity) (le_of_lt hN) n.toNat
          all_goals convert zpow_natCast _ _; omega
    set k := (N - s.m).toNat
    have hNk : N = s.m + k := by omega
    have hgeom : (fun n ↦ (α+ε) ^ n : Series).converges := by
      simp [converges_geom_iff, abs_of_pos hα', hα]
    rw [converges_from _ N.toNat] at hgeom
    have : (s.from N).absConverges := by
      apply (converges_of_le _ _ hgeom).1
      . simp; omega
      intro n hn; simp at hn
      have hn' : n ≥ 0 := by omega
      simp [hn.1, hn.2, hn']
      convert this n hn.2; symm; convert zpow_natCast _ _; omega
    unfold absConverges at this ⊢
    rw [converges_from _ k]; convert this; simp; refine ⟨ by omega, ?_ ⟩
    ext n
    by_cases hnm : n ≥ s.m <;> simp [hnm]
    by_cases hn : n ≥ N <;> simp [hn] <;> grind


/-- Теорема 7.5.1(b) (признак Коши) -/
theorem Series.root_test_neg {s : Series}
  (h : atTop.limsup (fun n ↦ ((|s.seq n|^(1/(n : ℝ)) : ℝ) : EReal)) > 1) : s.diverges := by
    -- Это доказательство написано так, чтобы следовать структуре оригинального текста.
    apply frequently_lt_of_lt_limsup (by isBoundedDefault) at h
    apply diverges_of_nodecay
    by_contra this; rw [LinearOrderedAddCommGroup.tendsto_nhds] at this; specialize this 1 (by positivity)
    choose n hn hs hs' using (h.and_eventually this).forall_exists_of_atTop 1
    simp at hs'; replace hs' := rpow_lt_one ?_ hs' (?_ : 0 < 1/(n : ℝ)) <;> try positivity
    rw [show (1 : EReal) = (1 : ℝ) by simp, EReal.coe_lt_coe_iff] at hs
    linarith

/-- Теорема 7.5.1(c) (признак Коши) / Упражнение 7.5.3 -/
theorem Series.root_test_inconclusive : ∃ s : Series,
  atTop.Tendsto (fun n ↦ |s.seq n|^(1/(n : ℝ))) (nhds 1) ∧ s.diverges := by
    sorry

/-- Теорема 7.5.1 (признак Коши) / Упражнение 7.5.3 -/
theorem Series.root_test_inconclusive' : ∃ s : Series,
  atTop.Tendsto (fun n ↦ |s.seq n|^(1/(n : ℝ))) (nhds 1) ∧ s.absConverges := by
    sorry

/-- Лемма 7.5.2 / Упражнение 7.5.1 -/
theorem Series.ratio_ineq {c : ℤ → ℝ} (m : ℤ) (hpos : ∀ n ≥ m, c n > 0) : 
  atTop.liminf (fun n ↦ ((c (n+1) / c n : ℝ) : EReal)) ≤
    atTop.liminf (fun n ↦ ↑((c n)^(1/(n : ℝ)) : ℝ))
  ∧ atTop.liminf (fun n ↦ (((c n)^(1/(n : ℝ)) : ℝ) : EReal)) ≤
    atTop.limsup (fun n ↦ ↑((c n)^(1/(n : ℝ)) : ℝ))
  ∧ atTop.limsup (fun n ↦ (((c n)^(1/(n : ℝ)) : ℝ) : EReal)) ≤
    atTop.limsup (fun n ↦ ↑(c (n+1) / c n : ℝ))
    := by
  -- Это доказательство написано так, чтобы следовать структуре оригинального текста.
  refine ⟨ ?_, liminf_le_limsup ?_ ?_, ?_ ⟩ <;> try isBoundedDefault
  . sorry
  set L' := limsup (fun n ↦ ((c (n+1) / c n : ℝ) : EReal)) .atTop
  by_cases hL : L' = ⊤; · rw [hL]; exact le_top
  have hL'pos : 0 ≤ L' := by
    apply le_limsup_of_frequently_le'
    rw [frequently_atTop]
    intro N; use max N m, by omega
    have hpos1 := hpos (max N m) (by omega)
    have hpos2 := hpos ((max N m)+1) (by omega)
    positivity
  have why : L' ≠ ⊥ := by sorry
  set L := L'.toReal
  have hL' : L' = L := (coe_toReal hL why).symm
  have hLpos : 0 ≤ L := by rw [hL'] at hL'pos; norm_cast at hL'pos
  apply le_of_forall_gt_imp_ge_of_dense
  intro y hy
  by_cases hy' : y = ⊤; · simp [hy']; exact le_top
  have : y = y.toReal := by symm; apply coe_toReal hy'; contrapose! hy; simp [hy]
  rw [this, hL', EReal.coe_lt_coe_iff] at hy
  set ε := y.toReal - L
  have hε : 0 < ε := by grind
  replace this : y = (L+ε : ℝ) := by convert this; simp [ε]
  rw [this]
  have hε' : L' < (L+ε : ℝ) := by rw [hL', EReal.coe_lt_coe_iff]; linarith
  have := eventually_lt_of_limsup_lt hε' (by isBoundedDefault)
  rw [eventually_atTop] at this; choose N' hN using this
  set N := max N' (max m 1)
  have (n : ℤ) (hn : n ≥ N) : c (n+1) / c n ≤ (L + ε) := by
    have : n ≥ N' := by omega
    have npos : 0 < n := by omega
    specialize hN n this; norm_cast at hN; order
  set A := c N * (L+ε)^(-N)
  have hA : 0 < A := by specialize hpos N (by omega); positivity
  have why2 (n : ℤ) (hn : n ≥ N) : c n ≤ A * (L+ε)^n := by
    sorry
  have why2_root (n : ℤ) (hn : n ≥ N) : (((c n)^(1/(n : ℝ)) : ℝ) : EReal) ≤ (A^(1/(n : ℝ)) * (L+ε) : ℝ) := by
    rw [EReal.coe_le_coe_iff]
    have hn' : n > 0 := by omega
    calc
      _ ≤ (A * (L+ε)^n)^(1/(n : ℝ)) := by
        apply_rules [rpow_le_rpow, le_of_lt (hpos n _)]; omega; positivity
      _ = A^(1/(n : ℝ)) * ((L+ε)^n)^(1/(n : ℝ)) := mul_rpow (by positivity) (by positivity)
      _ = _ := by
        congr
        rw [←rpow_intCast, ←rpow_mul (by positivity)]
        convert rpow_one _
        field_simp
  calc
    _ ≤ atTop.limsup (fun n : ℤ ↦ ((A^(1/(n : ℝ)) * (L+ε) : ℝ) : EReal)) := by
      apply limsup_le_limsup <;> try isBoundedDefault
      unfold EventuallyLE; rw [eventually_atTop]
      use N
    _ ≤ (atTop.limsup (fun n : ℤ ↦ ((A^(1/(n : ℝ)) : ℝ) : EReal))) * (atTop.limsup (fun n : ℤ ↦ ((L+ε : ℝ) : EReal))) := by
      convert EReal.limsup_mul_le _ _ _ _ with n
      . rfl
      . apply Frequently.of_forall; intros; positivity
      . apply Eventually.of_forall; simp; positivity
      . simp [-coe_add]
      simp [-coe_add]; grind
    _ = (L+ε : ℝ) := by
      simp; convert one_mul _
      apply Tendsto.limsup_eq
      convert Tendsto.comp (f := fun n : ℤ ↦ (A ^ (n : ℝ)⁻¹)) (g := fun x : ℝ ↦ (x : EReal)) (y := nhds 1) _ _
      . apply continuous_coe_real_ereal.tendsto'; norm_num
      convert Tendsto.comp (f := fun n : ℤ ↦ (n : ℝ)⁻¹) (g := fun x : ℝ ↦ A^x) (y := nhds 0) _ _
      . apply (continuous_const_rpow (by positivity)).tendsto'; simp
      exact tendsto_inv_atTop_zero.comp tendsto_intCast_atTop_atTop

/-- Следствие 7.5.3 (признак Даламбера, сходимость). -/
theorem Series.ratio_test_pos {s : Series} (hnon : ∀ n ≥ s.m, s.seq n ≠ 0)
  (h : atTop.limsup (fun n ↦ ((|s.seq (n+1)| / |s.seq n| : ℝ) : EReal)) < 1) : s.absConverges := by
    apply Series.root_test_pos (lt_of_le_of_lt _ h)
    convert (ratio_ineq s.m _).2.2
    convert hnon using 1 with n
    simp

/-- Следствие 7.5.3 (признак Даламбера, расходимость). -/
theorem Series.ratio_test_neg {s : Series} (hnon : ∀ n ≥ s.m, s.seq n ≠ 0)
  (h : atTop.liminf (fun n ↦ ((|s.seq (n+1)| / |s.seq n| : ℝ) : EReal)) > 1) : s.diverges := by
    apply Series.root_test_neg (lt_of_lt_of_le h _)
    convert (ratio_ineq s.m _).1.trans (ratio_ineq s.m _).2.1 with n; rfl
    all_goals convert hnon using 1 with n; simp

/-- Следствие 7.5.3(i) (признак Даламбера неоднозначен, расходится) / Упражнение 7.5.3 -/
theorem Series.ratio_test_inconclusive : ∃ s : Series, (∀ n ≥ s.m, s.seq n ≠ 0) ∧
  atTop.Tendsto (fun n ↦ |s.seq (n+1)| / |s.seq n|) (nhds 1) ∧ s.diverges := by
    sorry

/-- Следствие 7.5.3(ii) (признак Даламбера неоднозначен, абсолютно сходится) / Упражнение 7.5.3 -/
theorem Series.ratio_test_inconclusive' : ∃ s : Series, (∀ n ≥ s.m, s.seq n ≠ 0) ∧
  atTop.Tendsto (fun n ↦ |s.seq (n+1)| / |s.seq n|) (nhds 1) ∧ s.absConverges := by
    sorry

/-- Утверждение 7.5.4 -/
theorem Series.root_self_converges : atTop.Tendsto (fun (n : ℕ) ↦ (n : ℝ)^(1 / (n : ℝ))) (nhds 1) := by
  sorry

/-- Упражнение 7.5.2 -/
theorem Series.poly_mul_geom_converges {x : ℝ} (hx : |x|<1) (q : ℝ) : (fun n : ℕ ↦ (n : ℝ)^q * x^n : Series).converges
  ∧ atTop.Tendsto (fun n : ℕ ↦ (n : ℝ)^q * x^n) (nhds 0) := by
  sorry

end Chapter7
