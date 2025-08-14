import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.MetricSpace.UniformConvergence

open Filter
open Topology

def prop₁ {E : Type} [MetricSpace E] (fₕ : ℕ → E → ℝ) (f : E → ℝ) :=
  TendstoUniformly fₕ f atTop

def prop₂ {E : Type} [MetricSpace E] (fₕ : ℕ → E → ℝ) (f : E → ℝ) :=
  ∀ e : ℕ → E, (∃ ℓ, Tendsto e atTop (𝓝 ℓ)) → Tendsto (λ n => fₕ n (e n) - f (e n)) atTop (𝓝 0)

def prop₃ {E : Type} [MetricSpace E] (fₕ : ℕ → E → ℝ) (f : E → ℝ) :=
  ∀ x, Tendsto (fₕ · x) atTop (𝓝 (f x))

section proofs

variable {E : Type} [MetricSpace E]
variable (fₕ : ℕ → E → ℝ) (f : E → ℝ)
variable (hfₕ : ∀ n, Continuous (fₕ n)) (hf : Continuous f)

-- Exercise 2.A (i → ii)
theorem prop₂_of_prop₁ (h : prop₁ fₕ f) : prop₂ fₕ f := by
  intro e _
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h := Metric.tendstoUniformly_iff.mp h ε hε
  simp_all only [dist, eventually_atTop, sub_zero]
  have ⟨m, hm⟩ := h
  use m
  conv at hm in |_| => rw [abs_sub_comm]
  exact λ n hn => hm n hn (e n)

-- Exercise 2.A (ii → iii)
theorem prop₃_of_prop₂ (h : prop₂ fₕ f) : prop₃ fₕ f := by
  intro e
  have ℓ₁ := h (λ _ => e) (by simp)
  have ℓ₂ : Tendsto (λ _ : ℕ => f e) atTop (𝓝 (f e)) := by simp
  have := Tendsto.add ℓ₁ ℓ₂
  simp_all

-- Exercise 2.C (iii ∧ equicontinuity → ii)
include hf
theorem prop₂_of_prop₃_of_equicontinuity (h₁ : prop₃ fₕ f) (h₂ : Equicontinuous fₕ) : prop₂ fₕ f := by
  intro e ⟨ℓ, he⟩
  rw [Metric.tendsto_nhds]
  rw [Metric.tendsto_nhds] at he
  intro ε hε
  have ⟨δ₁, hδ₁⟩ := Metric.equicontinuousAt_iff.mp (h₂ ℓ) (ε / 3) (by linarith)
  have has_lim := Metric.tendsto_nhds.mp (h₁ ℓ) (ε / 3) (by linarith)
  have ⟨δ₂, hδ₂⟩ := (Metric.continuous_iff.mp hf) ℓ (ε / 3) (by linarith)
  simp_all only [dist, sub_zero, eventually_atTop]
  have ⟨m₁, hm₁⟩ := has_lim
  have ⟨m₂, hm₂⟩ := he (min δ₁ δ₂) (by simp_all)
  use max m₁ m₂
  intro b hb
  calc
    _ ≤ |fₕ b (e b) - fₕ b ℓ| + |fₕ b ℓ - f ℓ| + |f ℓ - f (e b)| := by
      have := dist_triangle4 (fₕ b (e b)) (fₕ b ℓ) (f ℓ) (f (e b))
      simp_all [dist]
    _ < (ε / 3) + (ε / 3) + (ε / 3) := by
      gcongr
      . rw [abs_sub_comm]
        exact hδ₁.right (e b) (by simp_all) b
      . exact hm₁ b (by simp_all)
      . rw [abs_sub_comm]
        exact hδ₂.right (e b) (by simp_all)
    _ = ε := by ring

-- Exercise 2.C (ii ∧ compact domain → i)
omit hf
theorem prop₁_of_prop₂_of_compact_domain (h₁ : prop₂ fₕ f) [CompactSpace E] : prop₁ fₕ f := by
  by_contra abs
  rw [prop₁, Metric.tendstoUniformly_iff, not_forall] at abs
  have ⟨ε, hε⟩ := abs
  simp only [eventually_atTop, Classical.not_imp, not_exists, not_forall, not_lt] at hε
  have ⟨g', hg'⟩ := Classical.skolem.mp hε.right
  let g : ℕ → ℕ := Nat.rec (g' 0) (λ _ i => g' (i + 1))
  have hg : ∀ n, ∃ x_1, ε ≤ dist (f x_1) (fₕ (g n) x_1) := by
    intro n
    induction n
    repeat exact (hg' _).right
  have hmg : StrictMono g := by
    apply strictMono_nat_of_lt_succ
    intro n
    induction n
    repeat
      simp_all only [g]
      exact lt_of_lt_of_le (by simp) (hg' _).left
  have ⟨z, hz⟩ := Classical.skolem.mp hg
  simp only [dist] at hz
  have ⟨ℓ, hℓ, φ, hφ⟩ := IsCompact.isSeqCompact (X := E) CompactSpace.isCompact_univ (λ n => (by simp_all : z n ∈ Set.univ))
  have hig := hmg.injective
  have hiφ := hφ.left.injective
  have (k : ℕ) := Classical.dec (∃ i, k = (g (φ i)))
  let x := λ k => dite (∃ i, k = (g (φ i))) (λ h => z (φ h.choose)) (λ _ => ℓ)
  have : Tendsto x atTop (𝓝 ℓ) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    rw [eventually_atTop]
    have ⟨m, hm⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp hφ.right ε hε)
    use g (φ m)
    intro b hb
    simp only [x]
    split_ifs with h
    . apply hm _
      exact hφ.left.le_iff_le.mp (hmg.le_iff_le.mp (le_of_le_of_eq hb h.choose_spec))
    . simp_all
  have ⟨m, hm⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp (h₁ x ⟨ℓ, this⟩) ε hε.left)
  have hm := λ i => hm (g (φ i))
  simp only [dist, sub_zero, x] at hm
  have eq (i : ℕ) : dite (∃ i₁, (g (φ i)) = (g (φ i₁))) (λ h => z (φ h.choose)) (λ _ => ℓ) = z (φ i) := by
    split_ifs with h
    . rw [←hig (congrArg g (hiφ (hig h.choose_spec)))]
    . exact (h ⟨i, rfl⟩).elim
  repeat conv at hm in (dite _ _ _) => rw [eq]
  have small_abs := hm m (le_trans hφ.left.le_apply hmg.le_apply)
  have big_abs := (hz (φ m))
  rw [abs_sub_comm] at big_abs
  linarith

end proofs

section counterexamples

-- Exercise 2.B ¬(iii → ii)
theorem not_prop₂_of_prop₃ :
    ¬(
      ∀ (E : Type) [MetricSpace E] (fₕ : ℕ → E → ℝ) (f : E → ℝ),
      (prop₃ fₕ f) ∧ (∀ n, Continuous (fₕ n)) ∧ (Continuous f)
      → prop₂ fₕ f
    ) := by
  let g := λ x => x * (Real.exp (-x))
  let h := λ n => (n * · : NNReal → ℝ)
  rw [not_forall]; use NNReal
  rw [not_forall]; use instMetricSpaceNNReal
  rw [not_forall]; use (λ n => g ∘ h n)
  rw [not_forall]; use (λ x => 0)
  simp only [and_imp, Classical.not_imp]
  refine ⟨?_, ?_, continuous_const, ?_⟩
  . intro x
    cases em (x = 0) with
    | inl zero => simp_all [g, h]
    | inr nonzero =>
      simp only [Function.comp_apply]
      have gt_zero : 0 < x.val := by
        refine lt_of_le_of_ne x.prop ?_
        have th := Subtype.coe_ne_coe.mpr nonzero
        norm_cast at th
        rw [←ne_eq] at th
        exact th.symm
      have ℓ₁ : Tendsto (λ (n : ℕ) => h n x) atTop atTop := by
        simp only [h]
        exact tendsto_atTop_atTop_of_monotone
          (λ i j ihj => (mul_le_mul_iff_of_pos_right gt_zero).mpr (by norm_cast))
          (λ b => ⟨⌈b / x⌉₊, (div_le_iff₀ gt_zero).mp (Nat.le_ceil _)⟩)
      have ℓ₂ : Tendsto g atTop (𝓝 0) := by
        have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
        simp_all [g]
      exact Tendsto.comp ℓ₂ ℓ₁
  . intro n
    simp only [g, h]
    exact Continuous.comp
      (Continuous.mul continuous_id (Continuous.rexp continuous_neg))
      (Continuous.mul continuous_const NNReal.continuous_coe)
  . rw [prop₂, not_forall]
    use (1 / ·)
    rw [Classical.not_imp]
    constructor
    . exact ⟨0, NNReal.tendsto_const_div_atTop_nhds_zero_nat _⟩
    . rw [Metric.tendsto_nhds, not_forall]
      use 1 / Real.exp 1
      rw [Classical.not_imp, eventually_atTop, not_exists]
      refine ⟨one_div_pos.mpr (Real.exp_pos 1), ?_⟩
      intro n
      rw [not_forall]
      use max 1 n
      rw [Classical.not_imp]
      refine ⟨by simp_all, ?_⟩
      have : max 1 (n : ℝ) ≠ 0 := by norm_cast; simp_all
      simp_all [g, h, Real.exp_neg]

-- Exercise 2.B ¬(ii → i)
theorem not_prop₁_of_prop₂ :
    ¬(
      ∀ (E : Type) [MetricSpace E] (fₕ : ℕ → E → ℝ) (f : E → ℝ),
      (prop₂ fₕ f) ∧ (∀ n, Continuous (fₕ n)) ∧ (Continuous f)
      → prop₁ fₕ f
    ) := by
  let g := Real.arctan
  let g' := λ (x : ℝ) => 1 / (1 + x ^ 2)
  let h := λ (n : ℕ) => (n + · : ℝ → ℝ)
  have hh (i : ℕ) : Differentiable ℝ (h i) := (Differentiable.add (differentiable_const _) differentiable_id)
  have hh' (i : ℕ) : deriv (h i) = λ _ => 1 := calc
    _ = deriv ((λ (_ : ℝ) => (i : ℝ)) + id) := congr_arg deriv (funext λ _ => by simp_all [h])
    _ = deriv i + deriv id := funext λ _ => deriv_add (differentiableAt_const _) (differentiableAt_id)
    _ = _ := funext λ _ => by simp_all
  rw [not_forall]; use ℝ
  rw [not_forall]; use Real.metricSpace
  rw [not_forall]; use (λ n => g ∘ h n)
  rw [not_forall]; use (λ x => Real.pi / 2)
  simp only [and_imp, Classical.not_imp]
  refine ⟨?_, ?_, continuous_const, ?_⟩
  . have eq_lip (i : ℕ) := lipschitzWith_of_nnnorm_deriv_le (C := 1) (f := g ∘ h i)
      (Differentiable.arctan (hh _))
      λ x => Subtype.coe_le_coe.mp <| by
        have : |1 + (i + x) ^ 2|⁻¹ ≤ 1 := by
          apply inv_le_one_of_one_le₀
          have diseq : 1 ≤ 1 + (i + x) ^ 2 := by simp_all [sq_nonneg]
          rwa [abs_of_nonneg (le_trans zero_le_one diseq)]
        have : deriv (Real.arctan ∘ fun x ↦ ↑i + x) x = _ := deriv_arctan (hh i x)
        simp_all [g, h]
    have eq_cont := (LipschitzWith.uniformEquicontinuous (g ∘ h ·) 1 eq_lip).equicontinuous
    have : prop₃ (λ n => g ∘ h n) (λ x => Real.pi / 2) := by
      intro x
      have ℓ₁ : Tendsto (λ (n : ℕ) => h n x) atTop atTop := by
        simp only [h]
        exact tendsto_atTop_atTop_of_monotone
          (λ _ _ _ => by simp_all)
          (λ b => ⟨⌈b - x⌉₊, tsub_le_iff_right.mp (Nat.le_ceil _)⟩)
      have ℓ₂ : Tendsto g atTop (𝓝 (Real.pi / 2)) := by
        have : Tendsto Real.arctan atTop (𝓝 (Real.pi / 2)) := Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds
        simp_all [g]
      exact Tendsto.comp ℓ₂ ℓ₁
    exact prop₂_of_prop₃_of_equicontinuity (λ n => g ∘ h n) (λ x => Real.pi / 2) continuous_const this eq_cont
  . intro n
    simp only [g, h]
    exact Continuous.comp Real.continuous_arctan (Continuous.add continuous_const continuous_id)
  . rw [prop₁, Metric.tendstoUniformly_iff, not_forall]
    use Real.pi / 2
    rw [Classical.not_imp, eventually_atTop, not_exists]
    refine ⟨Real.pi_div_two_pos, ?_⟩
    intro b
    rw [not_forall]
    use b
    rw [Classical.not_imp]
    simp_all only [le_refl, Function.comp_apply, not_forall, not_lt, true_and, g, h]
    use -b
    simp [abs_of_nonneg Real.pi_nonneg]

end counterexamples
