import Mathlib.Logic.ExistsUnique
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.Complex.Trigonometric

import Complementi.ODE

set_option maxHeartbeats 0

open Real

postfix:max "²" => (· ^ 2)

@[simp]
noncomputable def f (x y : ℝ) := Real.arctan (x + y) + Real.sin y

lemma cont_diff_f : ContDiff ℝ 1 f.uncurry :=
  ContDiff.add (ContDiff.arctan contDiff_add) (ContDiff.sin contDiff_snd)

lemma lipschitz_f : ∀ t : ℝ, LipschitzWith 2 (f t) := by
  intro t
  have diff_arctan : Differentiable ℝ (λ x => Real.arctan (t + x)) := Differentiable.arctan (Differentiable.add (differentiable_const _) differentiable_id)
  refine lipschitzWith_of_nnnorm_deriv_le (Differentiable.add diff_arctan Real.differentiable_sin) ?_
  intro x
  have eq : (f t)´ x = 1 / (1 + (t + x)²) + Real.cos x := by
    rw [(funext (by simp) : f t = (λ x => Real.arctan (t + x)) + (λ x => Real.sin x))]
    rw [deriv_add diff_arctan.differentiableAt Real.differentiableAt_sin]
    rw [deriv_arctan (f := HAdd.hAdd t) (Differentiable.add (differentiable_const _) differentiable_id).differentiableAt]
    rw [deriv_sin differentiableAt_fun_id]
    rw [deriv_const_add]
    simp
  simp only [nnnorm, eq, one_div, Real.norm_eq_abs]
  apply Subtype.coe_le_coe.mp
  simp only [NNReal.val_eq_coe, NNReal.coe_ofNat]
  refine abs_le.mpr ⟨?_, ?_⟩
  . rw [(by ring : (-2 : ℝ) = -1 + -1)]
    gcongr
    . refine le_trans (by simp : (-1 : ℝ) ≤ 0) (inv_nonneg_of_nonneg ?_)
      rw [(by ring: (0 : ℝ) = 0 + 0)]
      gcongr
      . exact zero_le_one
      . exact sq_nonneg _
    . exact Real.neg_one_le_cos _
  . rw [(by ring : (2 : ℝ) = 1 + 1)]
    gcongr
    . refine inv_le_one_of_one_le₀ ?_
      conv_lhs => rw [(by ring : (1 : ℝ) = 1 + 0)]
      gcongr
      exact sq_nonneg (t + x)
    . exact Real.cos_le_one x

lemma bound_f (x t : ℝ) : |f x t| ≤ π / 2 + 1 := by
  rw [f, abs_le]
  constructor
  . rw [neg_add]
    gcongr
    . exact le_of_lt (Real.neg_pi_div_two_lt_arctan _)
    . exact neg_one_le_sin t
  . gcongr
    . exact le_of_lt (Real.arctan_lt_pi_div_two _)
    . exact sin_le_one t

lemma bound_ge_zero : π / 2 + 1 ≥ 0 :=
  add_nonneg (div_nonneg Real.pi_nonneg zero_le_two) zero_le_one

lemma bound_gt_zero : π / 2 + 1 > 0 :=
  add_pos (div_pos Real.pi_pos zero_lt_two) zero_lt_one

theorem global_uniqueness : ∃! y : ℝ → ℝ, (∀ x : ℝ, HasDerivAt y (f x (y x)) x) ∧ y 0 = 0 := by
  have ⟨yₘ, hyₘ⟩ := top_local_solutions f cont_diff_f ⟨2, lipschitz_f⟩ 0 0
  use yₘ.val.2
  have eq : yₘ.val.1 = Set.univ := by
    by_contra abs
    let x := sSup { x : ℝ | Set.Ioo (-x) x ⊆ yₘ.val.1 }
    have bdd : BddAbove { x : ℝ | Set.Ioo (-x) x ⊆ yₘ.val.1 } := by
      rw [←ne_eq, ←Set.nonempty_compl] at abs
      have ⟨ub, hub⟩ := abs
      use |ub|
      by_contra! abs
      simp only [upperBounds, f, Set.mem_setOf_eq] at abs
      rw [not_forall] at abs
      have ⟨x, hx⟩ := abs
      rw [Classical.not_imp, not_le] at hx
      have := hx.1 (by simp_all [abs_lt] : ub ∈ Set.Ioo _ _)
      simp_all
    have x_ge_zero : x ≥ 0 := le_csSup bdd (by simp)
    have x_gt_zero : x > 0 := (lt_csSup_iff bdd ⟨0, by simp⟩).mpr
      ((Metric.isOpen_iff.mp yₘ.prop.1.1 0 yₘ.prop.1.2.2).imp (λ r hr => by simp_all [Real.ball_eq_Ioo]))
    have range : Set.Ioo (-x) x ⊆ yₘ.val.1 := λ y hy => by
      have hy := abs_lt.mpr (Set.mem_Ioo.mp hy)
      have ⟨a, ha⟩ := exists_lt_of_lt_csSup ⟨0, by simp⟩ hy
      exact ha.left (by simp_all [abs_lt])
    have extr : x ∉ yₘ.val.1 ∨ -x ∉ yₘ.val.1 := by
      by_contra! abs
      have ⟨ε₁, hε₁⟩ := Metric.isOpen_iff.mp yₘ.prop.1.1 x abs.1
      have ⟨ε₂, hε₂⟩ := Metric.isOpen_iff.mp yₘ.prop.1.1 (-x) abs.2
      rw [Real.ball_eq_Ioo] at hε₁ hε₂
      have sup : x + min ε₁ ε₂ ∈ { x : ℝ | Set.Ioo (-x) x ⊆ yₘ.val.1 } := by
        intro y hy
        rw [Set.mem_Ioo, neg_lt, ←sub_lt_iff_lt_add', ←sub_lt_iff_lt_add', lt_inf_iff, lt_inf_iff] at hy
        apply (le_or_gt y (-x)).elim
        . exact λ h => hε₂.2 (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩)
        . intros
          apply (lt_or_ge y x).elim
          . exact λ h => range (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩)
          . exact λ h => hε₁.2 (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩)
      have cont : x + min ε₁ ε₂ ≤ x := le_csSup bdd sup
      simp only [add_le_iff_nonpos_right, inf_le_iff] at cont
      exact cont.elim (by simp_all) (by simp_all)
    have lip : LipschitzOnWith ⟨π / 2 + 1, bound_ge_zero⟩ yₘ.val.2 yₘ.val.1 := by
      refine Convex.lipschitzOnWith_of_nnnorm_deriv_le
        (λ x hx => (yₘ.prop.2.1 x hx).differentiableAt)
        (λ x hx => Subtype.coe_le_coe.mp ?_)
        (Real.convex_iff_isPreconnected.mpr yₘ.prop.1.2.1.isPreconnected)
      rw [(yₘ.prop.2.1 x hx).deriv]
      exact bound_f _ _
    have ⟨ℓ₁, ℓ₂, K, L, h⟩ := is_picard_lindelof_constant_radius_on_rectangle_of_contdiff f cont_diff_f 0 (by linarith : -x ≤ x) (mul_nonneg bound_ge_zero x_ge_zero)
    apply extr.elim
    . intro hx
      have := div_nonneg (le_of_lt h.1) zero_le_two
      have pl := h.2 (max 0 (x - ℓ₁ / 2)) (by simp_all) (yₘ.val.2 (max 0 (x - ℓ₁ / 2))) <| by
        have := (lipschitzOnWith_iff_dist_le_mul.mp lip) _ yₘ.prop.1.2.2 _ (range (by simp_all) : max 0 (x - ℓ₁ / 2) ∈ _)
        simp_all [yₘ.prop]
        refine le_trans this ((mul_le_mul_iff_of_pos_left bound_gt_zero).mpr ?_)
        simp_all [sup_le_iff, abs_le]
      have ⟨α, hα⟩ := pl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
      let sel : Fin 2 → free_local_solutions f
        | 0 => ⟨yₘ.val, ⟨⟨yₘ.prop.1.1, yₘ.prop.1.2.1⟩, yₘ.prop.2.1⟩⟩
        | 1 => ⟨
            (Set.Ioo (max 0 (x - ℓ₁ / 2) - ℓ₁) (max 0 (x - ℓ₁ / 2) + ℓ₁), α),
            ⟨
              ⟨isOpen_Ioo, isConnected_Ioo (by linarith)⟩,
              λ t ht => (hα.2 t (Set.mem_Icc_of_Ioo ht)).hasDerivAt (mem_nhds_iff.mpr ⟨
                Set.Ioo _ _, ⟨Set.Ioo_subset_Icc_self, isOpen_Ioo, ht⟩
              ⟩)
            ⟩
          ⟩
      have ⟨β', hβ'⟩ := union_of_free_solutions f ⟨2, lipschitz_f⟩ sel <| λ i j => by
        have : 0 < ℓ₁ + (x - ℓ₁ / 2) := by
          ring_nf
          exact add_pos (mul_pos h.1 (by norm_num)) x_gt_zero
        have : max 0 (x - ℓ₁ / 2) ∈ yₘ.val.1 := range (by simp_all)
        fin_cases i <;> fin_cases j
        . have mem : ∃ x, x ∈ yₘ.val.1 := ⟨0, yₘ.prop.1.2.2⟩
          simp [sel, mem]
        . have mem : ∃ x ∈ (sel 0).val.1, x ∈ (sel 1).val.1 ∧ (sel 0).val.2 x = (sel 1).val.2 x :=
            ⟨max 0 (x - ℓ₁ / 2), by simp_all [sel, sub_lt_iff_lt_add', sup_lt_iff]⟩
          simp [mem]
        . have mem : ∃ x ∈ (sel 1).val.1, x ∈ (sel 0).val.1 ∧ (sel 1).val.2 x = (sel 0).val.2 x :=
            ⟨max 0 (x - ℓ₁ / 2), by simp_all [sel, sub_lt_iff_lt_add', sup_lt_iff]⟩
          simp [mem]
        . have mem : ∃ x, x ∈ (sel 1).val.1 := ⟨max 0 (x - ℓ₁ / 2), by split_ands; repeat linarith⟩
          simp [mem]
      have : 0 ∈ β'.val.1 := (hβ' 0).1 yₘ.prop.1.2.2
      have : β'.val.2 0 = 0 := Eq.trans ((hβ' 0).2 yₘ.prop.1.2.2).symm yₘ.prop.2.2
      have := β'.prop.2
      let β : local_solutions f 0 0 := ⟨β'.val, by simp_all [β'.prop];⟩
      have : x ∈ yₘ.val.1 := (hyₘ β).1 <| (hβ' 1).1 <| by
        simp [sel]
        constructor
        . rw [sub_lt_iff_lt_add, sup_lt_iff]
          exact ⟨by linarith, by linarith⟩
        . rw [←sub_lt_iff_lt_add, lt_sup_iff]
          exact Or.inr (by linarith)
      contradiction
    . intro hx
      have := div_nonneg (le_of_lt h.1) zero_le_two
      have pl := h.2 (min 0 (-x + ℓ₁ / 2)) (by simp_all) (yₘ.val.2 (min 0 (-x + ℓ₁ / 2))) <| by
        have := (lipschitzOnWith_iff_dist_le_mul.mp lip) _ yₘ.prop.1.2.2  _ (range (by simp_all) : min 0 (-x + ℓ₁ / 2) ∈ _)
        simp_all [yₘ.prop]
        refine le_trans this ((mul_le_mul_iff_of_pos_left bound_gt_zero).mpr ?_)
        simp_all [abs_le]
      have ⟨α, hα⟩ := pl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
      let sel : Fin 2 → free_local_solutions f
        | 0 => ⟨yₘ.val, ⟨⟨yₘ.prop.1.1, yₘ.prop.1.2.1⟩, yₘ.prop.2.1⟩⟩
        | 1 => ⟨
            (Set.Ioo (min 0 (-x + ℓ₁ / 2) - ℓ₁) (min 0 (-x + ℓ₁ / 2) + ℓ₁), α),
            ⟨
              ⟨isOpen_Ioo, isConnected_Ioo (by linarith)⟩,
              λ t ht => (hα.2 t (Set.mem_Icc_of_Ioo ht)).hasDerivAt (mem_nhds_iff.mpr ⟨
                Set.Ioo _ _, ⟨Set.Ioo_subset_Icc_self, isOpen_Ioo, ht⟩
              ⟩)
            ⟩
          ⟩
      have ⟨β', hβ'⟩ := union_of_free_solutions f ⟨2, lipschitz_f⟩ sel <| λ i j => by
        have : 0 < ℓ₁ + (x - ℓ₁ / 2) := by
          ring_nf
          exact add_pos (mul_pos h.1 (by norm_num)) x_gt_zero
        have : min 0 (-x + ℓ₁ / 2) ∈ yₘ.val.1 := range (by simp_all)
        fin_cases i <;> fin_cases j
        . have mem : ∃ x, x ∈ yₘ.val.1 := ⟨0, yₘ.prop.1.2.2⟩
          simp [sel, mem]
        . have mem : ∃ x ∈ (sel 0).val.1, x ∈ (sel 1).val.1 ∧ (sel 0).val.2 x = (sel 1).val.2 x := by
            use min 0 (-x + ℓ₁ / 2)
            simp_all [sel]
            rw [←lt_tsub_iff_left, sub_lt_iff_lt_add', inf_lt_iff]
            exact Or.inr (by linarith)
          simp [mem]
        . have mem : ∃ x ∈ (sel 1).val.1, x ∈ (sel 0).val.1 ∧ (sel 1).val.2 x = (sel 0).val.2 x := by
            use min 0 (-x + ℓ₁ / 2)
            simp_all [sel]
            rw [←lt_tsub_iff_left, sub_lt_iff_lt_add', inf_lt_iff]
            exact Or.inr (by linarith)
          simp [mem]
        . have mem : ∃ x, x ∈ (sel 1).val.1 := ⟨min 0 (-x + ℓ₁ / 2), by split_ands; repeat linarith⟩
          simp [mem]
      have : 0 ∈ β'.val.1 := (hβ' 0).1 yₘ.prop.1.2.2
      have : β'.val.2 0 = 0 := Eq.trans ((hβ' 0).2 yₘ.prop.1.2.2).symm yₘ.prop.2.2
      have := β'.prop.2
      let β : local_solutions f 0 0 := ⟨β'.val, by simp_all [β'.prop];⟩
      have : -x ∈ yₘ.val.1 := (hyₘ β).1 <| (hβ' 1).1 <| by
        simp [sel]
        constructor
        . rw [sub_lt_iff_lt_add, inf_lt_iff]
          exact Or.inr (by linarith)
        . rw [←sub_lt_iff_lt_add, lt_inf_iff]
          exact ⟨by linarith, by linarith⟩
      contradiction
  constructor
  . exact ⟨λ x => yₘ.prop.2.1 x (by simp_all), yₘ.prop.2.2⟩
  . intro y hy
    have := ODE_solution_unique_of_open_interval (t₀ := 0) (s := λ _ => Set.univ)
      ⟨isOpen_univ, isConnected_univ⟩
      (λ t ht => (lipschitz_f t).lipschitzOnWith)
      trivial
      (λ t ht => ⟨(hy.1 t), trivial⟩)
      (λ t ht => ⟨yₘ.prop.2.1 t (by simp_all), trivial⟩)
      (by simp_all [yₘ.prop])
    simp_all
