import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.LHopital

import Complementi.Notation

open Filter
open Topology

variable (a b : ℝ) (hab : a ≤ b)
variable (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc a b))

@[simp]
def twice_differentiable :=
  DifferentiableOn ℝ f (Set.Ioo a b) ∧ DifferentiableOn ℝ f´ (Set.Ioo a b)

@[simp]
noncomputable def expansion (f : ℝ → ℝ) (x₀ t : ℝ) :=
  (f (x₀ + t) + f (x₀ - t) - 2 * f x₀) / t²

lemma map_punctured_nhd_add (x₀ : ℝ) : (map (fun x ↦ x₀ + x) (𝓝[≠] 0)) = 𝓝[≠] x₀ := by
  simp [nhdsWithin, Filter.map_inf (add_right_injective x₀), map_add_left_nhds]

lemma map_punctured_nhd_sub (x₀ : ℝ) : (map (fun x ↦ x₀ - x) (𝓝[≠] 0)) = 𝓝[≠] x₀ := by
  rw [nhdsWithin, nhdsWithin, Filter.map_inf sub_right_injective]
  rw [(funext λ x => by simp; ring_nf : (x₀ - ·) = (x₀ + ·) ∘ Neg.neg)]
  rw [←Filter.map_compose, Function.comp_apply, Filter.map_neg]
  have symm : 𝓝 (0 : ℝ) = -(𝓝 0) := (nhds_zero_symm' ℝ).symm
  rw [←symm, map_add_left_nhds]
  simp

-- Exercise 3.A
include hf
theorem expansion_tendsto_second_deriv (hfd : twice_differentiable a b f) : ∀ x₀ ∈ Set.Ioo a b, Tendsto (expansion f x₀) (𝓝[≠] 0) (𝓝 (f´´ x₀)) := by
  intro x₀ hx₀
  have eq : expansion f x₀ = (λ t => (f (x₀ + t) + f (x₀ - t) - 2 * f x₀) / t²) := funext (by simp_all)
  let contained_nhd := Set.Ioo (max (a - x₀) (x₀ - b)) (min (b - x₀) (x₀ - a))
  have diff_f_add : ∀ y ∈ contained_nhd, DifferentiableAt ℝ (f ∘ HAdd.hAdd x₀) y := λ y ⟨hyl, hyr⟩ => by
    refine DifferentiableAt.comp y
      ((hfd.left _ ⟨?_, ?_⟩).differentiableAt (Ioo_mem_nhds ?_ ?_))
      (DifferentiableAt.const_add _ differentiableAt_id)
    all_goals simp_all [sup_lt_iff]; linarith
  have diff_f_sub : ∀ y ∈ contained_nhd, DifferentiableAt ℝ (f ∘ HSub.hSub x₀) y := λ y ⟨hyl, hyr⟩ => by
    refine DifferentiableAt.comp y
        ((hfd.left _ ⟨?_, ?_⟩).differentiableAt (Ioo_mem_nhds ?_ ?_))
        (DifferentiableAt.const_add _ differentiable_neg.differentiableAt)
    all_goals simp_all [sup_lt_iff]; linarith
  rw [eq]
  apply deriv.lhopital_zero_nhdsNE
  . refine eventually_nhdsWithin_of_eventually_nhds (eventually_nhds_iff.mpr ?_)
    refine ⟨contained_nhd, ⟨?_, ?_, ?_⟩⟩
    . exact λ y hy => DifferentiableAt.add_const _ (DifferentiableAt.add (diff_f_add _ hy) (diff_f_sub _ hy))
    . exact isOpen_Ioo
    . simp_all [sup_lt_iff, contained_nhd]
  . have eq : (λ (x : ℝ) => x²)´ = (2 * ·) := funext (by simp)
    exact eventually_nhdsWithin_of_forall (λ x hx => by simp_all)
  . have lim : Tendsto (fun x ↦ f (x₀ + x) + f (x₀ - x) - 2 * f x₀) (𝓝 0) (𝓝 (f x₀ + f x₀ - 2 * f x₀)) := by
      apply Tendsto.sub_const
      apply Tendsto.add
      . have := ContinuousAt.tendsto (f := λ x => f (x₀ + x)) (x := 0)
          (ContinuousAt.comp (hf.continuousAt (by simp_all))
          (Continuous.add continuous_const continuous_id).continuousAt)
        simp_all
      . have := ContinuousAt.tendsto (f := λ x => f (x₀ - x)) (x := 0)
          (ContinuousAt.comp (hf.continuousAt (by simp_all))
          (Continuous.sub continuous_const continuous_id).continuousAt)
        simp_all
    conv at lim in (occs := 2) 𝓝 _ => ring_nf
    exact Tendsto.mono_left lim nhdsWithin_le_nhds
  . have lim := Continuous.tendsto (f := λ (x : ℝ) => x²) (continuous_pow 2) 0
    conv at lim in (occs := 2) 𝓝 _ => ring_nf
    refine Tendsto.mono_left lim nhdsWithin_le_nhds
  . have eq₁ : (λ (x : ℝ) => x²)´ = (2 * ·) := funext (by simp)
    rw [eq₁]
    apply Tendsto.congr' (f₁ := λ x => (1 / 2) * ((f´ (x₀ + x) - f´ x₀) / x - (f´ (x₀ - x) - f´ x₀) / x))
    . apply Filter.eventually_of_mem (U := contained_nhd \ {0})
      . exact diff_mem_nhdsWithin_compl (Ioo_mem_nhds (by simp_all) (by simp_all)) {0}
      . intro x hx
        cancel_denoms
        ring_nf
        rw [mul_comm, ←mul_sub_left_distrib]
        simp_all only [twice_differentiable, Set.mem_diff, Set.mem_singleton_iff, mul_eq_mul_left_iff, inv_eq_zero, or_false]
        have ⟨hxl, hxr⟩ := hx.left
        symm
        calc
          _ = _ := deriv_add (diff_f_add _ hx.left) (diff_f_sub _ hx.left)
          _ = _ := by
            have : (f ∘ HAdd.hAdd x₀)´ x = f´ (x₀ + x) := by
              have := deriv_comp (h := HAdd.hAdd x₀) x
                (hfd.left.differentiableAt (Ioo_mem_nhds (by simp_all; linarith) (by simp_all; linarith)))
                (Differentiable.differentiableAt (Differentiable.const_add _ differentiable_id))
              have : (λ x => x₀ + id x)´ x = id´ x := by apply deriv_const_add
              simp_all
            have : (f ∘ HSub.hSub x₀)´ x = -f´ (x₀ - x) := by
              have := deriv_comp (h := HSub.hSub x₀) x
                (hfd.left.differentiableAt (Ioo_mem_nhds (by simp_all; linarith) (by simp_all; linarith)))
                (Differentiable.differentiableAt (Differentiable.const_add _ differentiable_neg))
              have : (λ x => x₀ - id x)´ x = -id´ x := by apply deriv_const_sub
              simp_all
            simp_all [sub_eq_add_neg]
    . rw [(by ring : f´´ x₀ = 1 / 2 * (f´´ x₀ + f´´ x₀))]
      apply Tendsto.const_mul
      apply Tendsto.add
      . rw [(funext (λ x => by simp [slope]; ring_nf) : (λ x => (f´ (x₀ + x) - f´ x₀) / x) = ((slope f´ x₀) ∘ (x₀ + ·)))]
        rw [←Filter.tendsto_map'_iff, map_punctured_nhd_add, ←hasDerivAt_iff_tendsto_slope]
        have := hfd.right.differentiableAt (x := x₀) (Ioo_mem_nhds (by simp_all) (by simp_all))
        simp_all
      . rw [(funext (λ x => by simp [slope]; ring_nf) : (λ x => -((f´ (x₀ - x) - f´ x₀) / x)) = ((slope f´ x₀) ∘ (x₀ - ·)))]
        rw [←Filter.tendsto_map'_iff, map_punctured_nhd_sub, ←hasDerivAt_iff_tendsto_slope]
        have := hfd.right.differentiableAt (x := x₀) (Ioo_mem_nhds (by simp_all) (by simp_all))
        simp_all

-- Exercise 3.B.1
include hab
theorem nonneg_of_neg_expansion
    (g : ℝ → ℝ)
    (hg : ∀ x ∈ Set.Ioo a b, g x < 0)
    (hgl : ∀ x ∈ Set.Ioo a b, Tendsto (expansion f x) (𝓝[≠] 0) (𝓝 (g x)))
    (hfa : f a = 0)
    (hfb : f b = 0) :
    ∀ x ∈ Set.Ioo a b, f x ≥ 0 := by
  by_contra! abs
  have ⟨xₙ, hxₙ⟩ := abs
  have ⟨xₘ, hxₘ⟩ := IsCompact.exists_isMinOn isCompact_Icc (by simp_all) hf
  rw [IsMinOn, IsMinFilter, eventually_principal] at hxₘ
  have : f xₘ < 0 := lt_of_le_of_lt (hxₘ.right _ (Set.mem_Icc_of_Ioo hxₙ.left)) hxₙ.right
  have xₘ_in_open : xₘ ∈ Set.Ioo a b := by
    refine Set.mem_Ioo.mpr ⟨lt_of_le_of_ne (by simp_all) ?_, lt_of_le_of_ne (by simp_all) ?_⟩
    . exact λ x => (by simp_all : f a ≠ f xₘ) (congr_arg f x)
    . exact λ x => (by simp_all : f b ≠ f xₘ) (congr_arg f x.symm)
  have : g xₘ ≥ 0 := by
    by_contra! abs
    have ev_lt := Filter.Tendsto.eventually_lt_const abs (hgl xₘ xₘ_in_open)
    have ev_ge : ∀ᶠ (a : ℝ) in 𝓝[≠] 0, expansion f xₘ a ≥ 0 :=
      Filter.mem_of_superset (x := Set.Ioo (max (a - xₘ) (xₘ - b)) (min (b - xₘ) (xₘ - a)) \ {0}) (by simp_all [diff_mem_nhdsWithin_compl, Ioo_mem_nhds]) <| by
        intro x ⟨⟨hxl, hxr⟩, _⟩
        simp only [expansion, Set.mem_setOf_eq]
        refine div_nonneg ?_ (sq_nonneg _)
        calc
          (0 : ℝ) = 0 + 0 := by simp
          _ ≤ (f (xₘ + x) - f xₘ) + (f (xₘ - x) - f xₘ) := by
            gcongr
            . exact sub_nonneg.mpr (hxₘ.right _ (Set.mem_Icc_of_Ioo (by simp_all; split_ands; repeat linarith)))
            . exact sub_nonneg.mpr (hxₘ.right _ (Set.mem_Icc_of_Ioo (by simp_all; split_ands; repeat linarith)))
          _ = _ := by ring

    rw [Filter.Eventually] at ev_lt ev_ge
    have ⟨x, hx⟩ := Filter.nonempty_of_mem (inter_mem ev_lt ev_ge)
    simp_all
    linarith
  have := hg xₘ xₘ_in_open
  linarith

lemma nonneg_of_zero_expansion
    (hgl : ∀ x ∈ Set.Ioo a b, Tendsto (expansion f x) (𝓝[≠] 0) (𝓝 0))
    (hfa : f a = 0)
    (hfb : f b = 0) :
    ∀ x ∈ Set.Ioo a b, f x ≥ 0 := by
  by_contra! abs
  have ⟨xₙ, hxₙ⟩ := abs
  have ⟨xₘ, hxₘ⟩ := IsCompact.exists_isMinOn isCompact_Icc (by simp_all) hf
  let ε := (1 / 2) * (f xₘ) / (max (xₘ - a)² (xₘ - b)²)
  let fₑ := λ x => f x + ε * (x - xₘ)²
  have add_cont : Continuous (λ x => ε * (x - xₘ)²) := Continuous.mul
    continuous_const
    (Continuous.pow (Continuous.add continuous_id continuous_const) _)
  have ⟨xₚ, hxₚ⟩ := IsCompact.exists_isMinOn (f := fₑ) isCompact_Icc (by simp_all) (ContinuousOn.add hf add_cont.continuousOn)
  rw [IsMinOn, IsMinFilter, eventually_principal] at hxₘ hxₚ
  have m_neg : f xₘ < 0 := lt_of_le_of_lt (hxₘ.right _ (Set.mem_Icc_of_Ioo hxₙ.left)) hxₙ.right
  have ne_a : a ≠ xₘ := λ x => (by simp_all : f a ≠ f xₘ) (congr_arg f x)
  have ne_b : b ≠ xₘ := λ x => (by simp_all : f b ≠ f xₘ) (congr_arg f x)
  have := ne_a.symm
  have := ne_b.symm
  have xₚ_ne_a : xₚ ≠ a := by
    refine λ h => (?_ : fₑ xₚ ≠ fₑ a) (congr_arg fₑ h)
    intro h
    have cont := hxₚ.right xₘ hxₘ.left
    have : 2⁻¹ * (f xₘ) / max (xₘ - a)² (xₘ - b)² * (a - xₘ)² > f xₘ := calc
      _ ≥ 2⁻¹ * (f xₘ) / (xₘ - a)² * (a - xₘ)² := by
        rw [div_eq_mul_inv, div_eq_mul_inv, ge_iff_le, mul_le_mul_iff_of_pos_right (pow_two_pos_of_ne_zero (by simp_all [sub_ne_zero]))]
        rw [mul_le_mul_left_of_neg (mul_neg_of_pos_of_neg (by norm_num) m_neg)]
        rw [inv_le_inv₀ (lt_sup_iff.mpr (Or.inl (pow_two_pos_of_ne_zero (by simp_all [sub_ne_zero])))) (pow_two_pos_of_ne_zero (by simp_all [sub_ne_zero]))]
        simp
      _ = 2⁻¹ * (f xₘ) := by
        have : (a - xₘ)² ≠ 0 := ne_of_gt (pow_two_pos_of_ne_zero (by simp_all [sub_ne_zero]))
        rw [(by ring : (xₘ - a)² = (a - xₘ)²)]
        simp [div_mul_comm, (div_eq_one_iff_eq this).mpr rfl]
      _ > 1 * (f xₘ) := by
        rw [gt_iff_lt, mul_lt_mul_right_of_neg m_neg]
        norm_num
      _ = _ := by simp
    rw [h] at cont
    simp [fₑ, ε] at cont
    linarith
  have xₚ_ne_b : xₚ ≠ b := by
    refine λ h => (?_ : fₑ xₚ ≠ fₑ b) (congr_arg fₑ h)
    intro h
    have cont := hxₚ.right xₘ hxₘ.left
    have : 2⁻¹ * (f xₘ) / max (xₘ - a)² (xₘ - b)² * (xₘ - b)² > f xₘ := calc
      _ ≥ 2⁻¹ * (f xₘ) / (xₘ - b)² * (xₘ - b)² := by
        rw [div_eq_mul_inv, div_eq_mul_inv, ge_iff_le, mul_le_mul_iff_of_pos_right (pow_two_pos_of_ne_zero (by simp_all [sub_ne_zero]))]
        rw [mul_le_mul_left_of_neg (mul_neg_of_pos_of_neg (by norm_num) m_neg)]
        rw [inv_le_inv₀ (lt_sup_iff.mpr (Or.inl (pow_two_pos_of_ne_zero (by simp_all [sub_ne_zero])))) (pow_two_pos_of_ne_zero (by simp_all [sub_ne_zero]))]
        simp
      _ = 2⁻¹ * (f xₘ) := by
        have : (b - xₘ)² ≠ 0 := ne_of_gt (pow_two_pos_of_ne_zero (by simp_all [sub_ne_zero]))
        rw [(by ring : (xₘ - b)² = (b - xₘ)²)]
        simp [div_mul_comm, (div_eq_one_iff_eq this).mpr rfl]
      _ > 1 * (f xₘ) := by
        rw [gt_iff_lt, mul_lt_mul_right_of_neg m_neg]
        norm_num
      _ = _ := by simp
    rw [h] at cont
    simp [fₑ, ε] at cont
    linarith
  have lim : ∀ x ∈ Set.Ioo a b, Tendsto (expansion fₑ x) (𝓝[≠] 0) (𝓝 (2 * ε)) := λ x hx => by
    let f' := (λ x => f x + ε * (x - xₘ)²)
    rw [(funext λ x => rfl : expansion f' x = λ t => (f' (x + t) + f' (x - t) - 2 * f' x) / t²), (by simp : 2 * ε = 0 + 2 * ε)]
    simp only [f']
    rw [(funext λ x => by simp_all; ring_nf : (λ t =>
      (f (x + t) + ε * (x + t - xₘ)² + (f (x - t) + ε * (x - t - xₘ)²) - 2 * (f x + ε * (x - xₘ)²)) / t²) =
      (λ t => (f (x + t) + f (x - t) - 2 * f x) / t²) + (λ t => (ε * (x + t - xₘ)² + ε * (x - t - xₘ)² - 2 * ε * (x - xₘ)²) / t²))]
    apply Tendsto.add (hgl x hx)
    simp_all only [Set.mem_Ioo, and_imp, Set.mem_Icc, ne_eq]
    ring_nf
    exact Tendsto.congr' (f₁ := λ _ => ε * 2)
      (Filter.eventually_of_mem (U := Set.univ \ {0}) (diff_mem_nhdsWithin_compl (by simp) _) (by simp_all))
      tendsto_const_nhds
  have xₚ_in_open : xₚ ∈ Set.Ioo a b :=
    Set.mem_Ioo.mpr ⟨lt_of_le_of_ne (by simp_all) xₚ_ne_a.symm, lt_of_le_of_ne (by simp_all) xₚ_ne_b⟩
  have : 2 * ε ≥ 0 := by
    by_contra! abs
    have ev_lt := Filter.Tendsto.eventually_lt_const abs (lim xₚ xₚ_in_open)
    have ev_ge : ∀ᶠ (a : ℝ) in 𝓝[≠] 0, expansion fₑ xₚ a ≥ 0 :=
      Filter.mem_of_superset (x := Set.Ioo (max (a - xₚ) (xₚ - b)) (min (b - xₚ) (xₚ - a)) \ {0}) (by simp_all [diff_mem_nhdsWithin_compl, Ioo_mem_nhds]) <| by
        intro x ⟨⟨hxl, hxr⟩, _⟩
        simp only [expansion, Set.mem_setOf_eq]
        refine div_nonneg ?_ (sq_nonneg _)
        calc
          (0 : ℝ) = 0 + 0 := by simp
          _ ≤ (fₑ (xₚ + x) - fₑ xₚ) + (fₑ (xₚ - x) - fₑ xₚ) := by
            gcongr
            . exact sub_nonneg.mpr (hxₚ.right _ (Set.mem_Icc_of_Ioo (by simp_all; split_ands; repeat linarith)))
            . exact sub_nonneg.mpr (hxₚ.right _ (Set.mem_Icc_of_Ioo (by simp_all; split_ands; repeat linarith)))
          _ = _ := by ring
    rw [Filter.Eventually] at ev_lt ev_ge
    have ⟨x, hx⟩ := Filter.nonempty_of_mem (inter_mem ev_lt ev_ge)
    simp_all
    linarith
  have : 2 * ε < 0 := by
    simp only [ε]
    apply mul_neg_of_pos_of_neg zero_lt_two
    apply mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) m_neg)
    rw [inv_pos, lt_sup_iff]
    exact Or.inl (pow_two_pos_of_ne_zero (by simp_all [sub_ne_zero]))
  linarith

lemma nonpos_of_zero_expansion
    (hgl : ∀ x ∈ Set.Ioo a b, Tendsto (expansion f x) (𝓝[≠] 0) (𝓝 0))
    (hfa : f a = 0)
    (hfb : f b = 0) :
    ∀ x ∈ Set.Ioo a b, f x ≤ 0 := by
  have := by
    refine nonneg_of_zero_expansion a b hab (-f) hf.neg ?_ (by simp_all) (by simp_all)
    intro x hx
    rw [(funext λ x => by simp_all [expansion]; ring_nf : expansion (-f) x = -(expansion f x))]
    have th := Tendsto.neg (hgl x hx)
    ring_nf at th
    exact th
  simp_all

lemma zero_of_zero_expansion
    (hgl : ∀ x ∈ Set.Ioo a b, Tendsto (expansion f x) (𝓝[≠] 0) (𝓝 0))
    (hfa : f a = 0)
    (hfb : f b = 0) :
    ∀ x ∈ Set.Ioo a b, f x = 0 := by
  intro x hx
  have := nonneg_of_zero_expansion a b hab f hf hgl hfa hfb x hx
  have := nonpos_of_zero_expansion a b hab f hf hgl hfa hfb x hx
  linarith

-- Exercise 3.B.1
theorem linear_of_zero_expansion
    (hgl : ∀ x ∈ Set.Ioo a b, Tendsto (expansion f x) (𝓝[≠] 0) (𝓝 0)) :
    ∃ m q : ℝ, ∀ x ∈ Set.Ioo a b, f x = m * x + q := by
  apply (Classical.em (a = b)).elim
  . intro hab
    use 0, f a
    simp_all
  . intro hab'
    let m := (f b - f a) / (b - a)
    let q := f a - m * a
    use m, q
    intro x hx
    have eq := by
      refine zero_of_zero_expansion a b hab (λ x => f x - m * x - q) ?_ ?_ ?_ ?_ x hx
      . exact (ContinuousOn.sub (ContinuousOn.sub hf (Continuous.mul continuous_const continuous_id).continuousOn) continuousOn_const)
      . intro x hx
        rw [(funext λ x => by simp_all; ring_nf : (expansion (λ x => f x - m * x - q) x) = expansion f x)]
        exact hgl x hx
      . simp_all [m, q]
      . simp_all only [Set.mem_Ioo, and_imp, m, q]
        have ne_zero := (sub_ne_zero.mpr (ne_comm.mp hab'))
        rw [sub_eq_zero, ←mul_left_inj' ne_zero, sub_mul, sub_mul]
        conv in (f b - f a) / (b - a) * b * (b - a) =>
          rw [mul_assoc, mul_comm, mul_div_left_comm, mul_div_assoc, (div_eq_one_iff_eq ne_zero).mpr rfl]
        conv in (f b - f a) / (b - a) * a * (b - a) =>
          rw [mul_assoc, mul_comm, mul_div_left_comm, mul_div_assoc, (div_eq_one_iff_eq ne_zero).mpr rfl]
        ring_nf
    simp_all
    rwa [sub_sub, sub_eq_zero] at eq
