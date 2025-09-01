import Mathlib.Logic.ExistsUnique
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.Complex.Trigonometric
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Taylor

import Complementi.ODE

set_option maxHeartbeats 0

open Real
open Topology

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

-- Exercise 4.A
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

-- Exercise 4.B
theorem f_gt_zero (y : ℝ → ℝ) (hy : ∀ x : ℝ, HasDerivAt y (f x (y x)) x) (hi : y 0 = 0) : ∀ x > 0, y x > 0 := by
  have deriv_pos : ∀ x > 0, ∀ y > 0, f x y > 0 := λ x hx y hy => calc
    _ > Real.arctan y + Real.sin y := by
      simp [f, arctan_strictMono (by linarith : x + y > y)]
    _ ≥ _ := by
      apply (le_or_gt y π).elim
      . intro h
        rw [←AddZeroClass.zero_add 0]
        gcongr
        . have := arctan_strictMono hy
          simp_all
          linarith
        . exact sin_nonneg_of_nonneg_of_le_pi (le_of_lt hy) h
      . intro h
        rw [ge_iff_le, ←neg_le_iff_add_nonneg]
        refine le_trans (by simp [neg_le, Real.neg_one_le_sin] : -sin y ≤ 1) (le_of_lt ?_)
        refine lt_trans (by linarith [Real.pi_gt_three] : π / 3 > 1) ?_
        have := arctan_strictMono (lt_trans (lt_trans ((sqrt_lt' zero_lt_three).mpr (by norm_num)) Real.pi_gt_three) h : y > √3)
        have := Real.arctan_tan (x := π / 3) (by linarith [pi_pos]) (by linarith [pi_pos])
        simp_all
  have eq₁ : y´ 0 = 0 := by
    have := (hy 0).deriv
    simp_all
  have eq : y´´ = (λ x => (1 + y´ x) / (1 + (x + y x)²) + cos (y x) * y´ x) := by
    have eq : y´ = λ x => f x (y x) := funext λ x => (hy x).deriv
    simp only [eq, f]
    have : (λ x => arctan (x + y x) + sin (y x))´ = (λ x => (1 + y´ x) / (1 + (x + y x)²) + cos (y x) * y´ x) := funext λ x => by
      have eq := deriv_fun_add (f := λ x => arctan (x + y x)) (g := λ x => sin (y x)) (x := x)
        (DifferentiableAt.arctan (DifferentiableAt.add differentiableAt_id (hy x).differentiableAt))
        (DifferentiableAt.sin (hy x).differentiableAt)
      rw [eq]
      congr
      . have eq₁ : (λ x => arctan (x + y x))´ x = _ :=
          _root_.deriv_arctan (DifferentiableAt.add differentiableAt_id (hy x).differentiableAt)
        have eq₂ := deriv_fun_add (f := λ x => x) (g := λ x => y x) (x := x) differentiableAt_id (hy x).differentiableAt
        rw [eq₁, eq₂]
        ring_nf
        field_simp
      . exact deriv_sin (hy x).differentiableAt
    simp_all
  have eq₂ : y´´ 0 = 1 := by simp_all
  have contdiff : ContDiff ℝ (1 + 1) y := by
    have diff : Differentiable ℝ (λ x => f x (y x)) := Differentiable.add
      (Differentiable.arctan (Differentiable.add differentiable_id (λ x => (hy x).differentiableAt)))
      (Differentiable.sin (λ x => (hy x).differentiableAt))
    refine contDiff_succ_iff_deriv.mpr ⟨λ x => (hy x).differentiableAt, by simp, ?_⟩
    refine contDiff_one_iff_deriv.mpr ⟨?_, ?_⟩
    . rwa [funext λ x => (hy x).deriv]
    . rw [eq]
      exact Continuous.add
        (Continuous.div₀
          (Continuous.add continuous_const (by rw [funext λ x => (hy x).deriv]; exact diff.continuous))
          (Continuous.add continuous_const (Continuous.pow (Continuous.add continuous_id (continuous_iff_continuousAt.mpr (λ x => (hy x).continuousAt))) _))
          (λ x => ne_of_gt (by linarith [sq_nonneg (x + y x)])))
        (Continuous.mul
          (Continuous.comp Real.continuous_cos (continuous_iff_continuousAt.mpr (λ x => (hy x).continuousAt)) : Continuous (cos ∘ y))
          (by rw [funext λ x => (hy x).deriv]; exact diff.continuous))
  rw [(by norm_cast : (1 : WithTop ℕ∞) + 1 = (2 : ℕ))] at contdiff
  have taylor := taylor_isLittleO (x₀ := 0) convex_univ trivial contdiff.contDiffOn
  simp [iteratedDerivWithin_succ] at taylor
  conv at taylor in iteratedDerivWithin _ _ _ =>
    rw [(funext (by simp) : iteratedDerivWithin 1 y Set.univ = λ x => iteratedDerivWithin 1 y Set.univ x),
        funext (λ x => iteratedDerivWithin_one (x := x))]
  simp [eq₁, eq₂, hi, Asymptotics.IsLittleO_def] at taylor
  norm_num at taylor
  have ⟨U', hU'⟩ := eventually_nhds_iff.mp (Asymptotics.isBigOWith_iff.mp (taylor (by norm_num : (0 : ℝ) < 1 / 4)))
  let U := U' ∩ Set.Ioi 0
  have gt : ∀ x ∈ U, y x > 0 := λ x hx => by
    have diseq := hU'.1 x (Set.mem_of_mem_inter_left hx)
    simp [abs_le] at diseq
    have : y x ≥ (1 / 4) * x² := by linarith
    have : x² > 0 := sq_pos_iff.mpr (ne_of_lt (Set.mem_of_mem_inter_right hx)).symm
    linarith
  by_contra! abs
  have ⟨x₀, hx₀⟩ := abs
  have ⟨ε, hε⟩ := Metric.isOpen_iff.mp hU'.2.1 0 hU'.2.2
  have closed_preimage := IsClosed.preimage (t := Set.Iic 0) (continuous_iff_continuousAt.mpr (λ x => (hy x).continuousAt)) isClosed_Iic
  have closed : IsClosed ((y ⁻¹' Set.Iic 0) ∩ (Set.Ici ε)) := IsClosed.inter closed_preimage isClosed_Ici
  have nonempty : ((y ⁻¹' Set.Iic 0) ∩ (Set.Ici ε)).Nonempty := by
    use x₀
    refine Set.mem_inter (by simp_all) ?_
    by_contra abs
    rw [Set.mem_Ici, not_le] at abs
    have ins : x₀ ∈ U := Set.mem_inter (hε.2 (by simp [abs_lt]; split_ands; repeat linarith : x₀ ∈ _)) (by simp_all)
    have := gt _ ins
    linarith
  let x₁ := sInf ((y ⁻¹' Set.Iic 0) ∩ (Set.Ici ε))
  have inf_mem : x₁ ∈ _ := IsClosed.csInf_mem closed nonempty ⟨0, λ x hx => by simp_all; linarith⟩
  have mem_gt_zero : ∀ x ∈ ((y ⁻¹' Set.Iic 0) ∩ (Set.Ici ε)), x > 0 := λ x hx => by
    have := Set.mem_of_mem_inter_right hx
    simp_all
    linarith
  have mem_nonpos_y : ∀ x ∈ ((y ⁻¹' Set.Iic 0) ∩ (Set.Ici ε)), y x ≤ 0 := λ x hx => by
    have := Set.mem_of_mem_inter_left hx
    simp_all
  have ⟨x₂, hx₂⟩ := exists_deriv_eq_slope y
    (mem_gt_zero _ inf_mem)
    (λ x hx => (hy x).continuousAt.continuousWithinAt)
    (λ x hx => (hy x).differentiableAt.differentiableWithinAt)
  simp only [Set.mem_Ioo, hi, sub_zero] at hx₂
  have : y´ x₂ ≤ 0 := by
    rw [hx₂.2]
    exact div_nonpos_iff.mpr (Or.inr ⟨mem_nonpos_y _ inf_mem, le_of_lt (mem_gt_zero _ inf_mem)⟩)
  have not_mem := notMem_of_lt_csInf hx₂.1.2 ⟨0, λ x hx => by simp_all; linarith⟩
  rw [Set.mem_inter_iff, not_and_or] at not_mem
  have y_pos : y x₂ > 0 := not_mem.elim
    (λ h => by simp_all)
    (λ h => gt _ (Set.mem_inter (hε.2 (by simp_all [abs_lt]; linarith)) (by simp_all)))
  have : y´ x₂ > 0 := by
    rw [(hy x₂).deriv]
    exact deriv_pos _ hx₂.1.1 _ y_pos
  linarith
