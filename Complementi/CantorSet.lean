import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Int.Log
import Mathlib.Data.Real.Cardinality
import Mathlib.Tactic.Rify
import Mathlib.Topology.Instances.CantorSet

open Cardinal

variable (χ : ℕ → ({0, 2} : Set ℤ))

lemma isComplete_cantorSet : IsComplete cantorSet :=
  IsClosed.isComplete isClosed_cantorSet

lemma third_in_cantorSet {x : ℝ} (h : x ∈ cantorSet) :
    x * (1 / 3) ∈ cantorSet := by
  rw [(by field_simp : x * (1 / 3) = x / 3)]
  have mem_left_half := Set.mem_image_of_mem (· / 3) h
  have left_half_subset : (· / 3) '' cantorSet ⊆ cantorSet := by
    conv_rhs => rw [cantorSet_eq_union_halves]
    simp
  exact left_half_subset mem_left_half

lemma third_plus_two_thirds_in_cantorSet {x : ℝ} (h : x ∈ cantorSet) :
    2 / 3 + x * (1 / 3) ∈ cantorSet := by
  rw [(by field_simp : 2 / 3 + x * (1 / 3) = (2 + x) / 3)]
  have mem_right_half := Set.mem_image_of_mem (fun x => (2 + x) / 3) h
  have right_half_subset : ((2 + ·) / 3) '' cantorSet ⊆ cantorSet := by
    conv_rhs => rw [cantorSet_eq_union_halves]
    simp
  exact right_half_subset mem_right_half

lemma either_anc_in_cantorSet {x : ℝ} (h : x ∈ cantorSet) :
    x * 3 ∈ cantorSet ∨ x * 3 - 2 ∈ cantorSet := by
  rw [cantorSet_eq_union_halves] at h
  simp only [Set.mem_union, Set.mem_image] at h
  apply h.elim
  . intro ⟨x', ⟨hx'₀, hx'₁⟩⟩
    apply Or.inl
    rwa [(by linarith : x' = x * 3)] at hx'₀
  . intro ⟨x', ⟨hx'₀, hx'₁⟩⟩
    apply Or.inr
    rwa [(by linarith : x' = x * 3 - 2)] at hx'₀

@[simp]
noncomputable def cantorSet_series :=
  fun i ↦ χ i * (1 / 3 : ℝ) ^ i * (1 / 3)

lemma partial_sums_cantorSet_series_in_cantorSet (n : ℕ) :
    ∑ i ∈ Finset.range n, cantorSet_series χ i ∈ cantorSet := by
  revert χ
  induction n with
  | zero =>
    simp [zero_mem_cantorSet]
  | succ n ih =>
    intro χ
    apply (Subtype.coe_prop (χ 0)).elim
    all_goals
      intro
      simp_all only [Finset.sum_range_succ', cantorSet_series, Int.cast_zero,
        zero_mul, add_zero, Set.mem_singleton_iff,
        Finset.sum_range_succ', Int.cast_ofNat, pow_zero, mul_one]
      rw [←Finset.sum_mul]
      ring_nf
      first | apply third_in_cantorSet | apply third_plus_two_thirds_in_cantorSet
      exact ih (fun i ↦ χ (1 + i))

lemma cantorSet_series_summable : Summable (cantorSet_series χ) := by
  have summable_geo : Summable (fun i ↦ 2 / 3 * (1 / 3 : ℝ) ^ i) := by
    apply Summable.mul_left
    exact summable_geometric_of_lt_one (by simp) (by norm_num)
  refine Summable.of_nonneg_of_le ?_ ?_ summable_geo
  all_goals
    intro i
    apply (Subtype.coe_prop (χ i)).elim <;>
      (simp_all; try ring_nf; try field_simp)

lemma cantorSet_series_in_cantorSet : tsum (cantorSet_series χ) ∈ cantorSet := by
  have ⟨l, hl⟩ := cantorSet_series_summable χ
  have partial_sums_cauchy : CauchySeq (fun n ↦ ∑ i ∈ Finset.range n, cantorSet_series χ i) := by
    apply Filter.Tendsto.cauchySeq (x := l)
    exact (Summable.hasSum_iff_tendsto_nat (cantorSet_series_summable χ)).mp hl
  have ⟨l', ⟨_, hl'⟩⟩ := cauchySeq_tendsto_of_isComplete
    isComplete_cantorSet
    (partial_sums_cantorSet_series_in_cantorSet χ)
    partial_sums_cauchy
  rw [HasSum.tsum_eq hl]
  rw [Summable.hasSum_iff_tendsto_nat (cantorSet_series_summable χ)] at hl
  rwa [tendsto_nhds_unique hl hl']

@[simp]
noncomputable def cantorSet_series_sum :=
  Subtype.mk (tsum (cantorSet_series χ)) (cantorSet_series_in_cantorSet χ)

lemma sum_of_cantorSet_series_injective : Function.Injective cantorSet_series_sum := by
  have diff (χ₁ χ₂ : _) : χ₁ ≠ χ₂ → cantorSet_series_sum χ₁ ≠ cantorSet_series_sum χ₂ := by
    intro h
    let n := Nat.find (Function.ne_iff.mp h)
    have hn := Nat.find_spec (Function.ne_iff.mp h)
    simp only [cantorSet_series_sum, ne_eq, Subtype.mk.injEq]
    rw [←Summable.sum_add_tsum_nat_add (n + 1) (cantorSet_series_summable χ₁)]
    rw [←Summable.sum_add_tsum_nat_add (n + 1) (cantorSet_series_summable χ₂)]
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have first_eq :
        ∑ x ∈ Finset.range n, cantorSet_series χ₁ x =
        ∑ x ∈ Finset.range n, cantorSet_series χ₂ x := by
      refine Finset.sum_congr rfl ?_
      have (x : ℕ) (hx : x < n) :=
        Subtype.ext_iff.mp (not_ne_iff.mp (Nat.find_min (Function.ne_iff.mp h) hx))
      simp_all

    rw [add_assoc, add_assoc, first_eq, add_right_inj _]
    rw [←sub_eq_zero, sub_add_eq_sub_sub, add_sub_right_comm, add_sub_assoc]
    rw [←eq_neg_iff_add_eq_zero]
    apply (fun h x ↦ h (congrArg abs x) : |_| ≠ |_| → _ ≠ _)
    have first_ge_two_thirds :
        |cantorSet_series χ₁ n - cantorSet_series χ₂ n| ≥ 2 / 3 * (1 / 3) ^ n := by
      simp
      rw [←mul_sub_right_distrib, abs_mul, ←mul_sub_right_distrib, abs_mul]
      rw [(by aesop : |(3 : ℝ)⁻¹| = 3⁻¹), (by aesop : |((3 : ℝ) ^ n)⁻¹| = ((3 : ℝ) ^ n)⁻¹)]
      have eq : |(χ₁ n : ℝ) - ↑↑(χ₂ n)| = 2 := by
        match (Subtype.coe_prop (χ₁ n)), (Subtype.coe_prop (χ₂ n)) with
        | Or.inl hχ₁, Or.inl hχ₂ | Or.inr hχ₁, Or.inr hχ₂ =>
          exact False.elim (hn (Subtype.ext (Eq.trans hχ₁ hχ₂.symm)))
        | Or.inr hχ₁, Or.inl hχ₂ | Or.inl hχ₁, Or.inr hχ₂ =>
          simp_all
      rw [eq]
      linarith
    have tail_le_third :
        |∑' (i : ℕ), cantorSet_series χ₂ (i + (n + 1))
        - ∑' (i : ℕ), cantorSet_series χ₁ (i + (n + 1))| ≤ 1 / 3 * (1 / 3) ^ n := by
      simp only [cantorSet_series]
      rw [tsum_mul_right, tsum_mul_right]
      ring_nf
      conv in (occs := 1) (_ * _ * _) => rw [mul_right_comm]
      conv in (occs := 3) (_ * _ * _) => rw [mul_assoc, mul_right_comm, ←mul_assoc]
      conv in (occs := 1) (∑' _, _) => rw [tsum_mul_right]
      conv in (occs := 2) (∑' _, _) => rw [tsum_mul_right]
      rw [(by ring : ((-1 : ℝ) / 3) = -(1 / 3))]
      rw [mul_neg, ←sub_eq_add_neg, ←sub_mul, ←sub_mul, abs_mul, abs_mul]
      rw [(by aesop : |(1 : ℝ) / 3| = (1 : ℝ) / 3),
        (by aesop : |(((1 : ℝ) / 3) ^ n)| = (((1 : ℝ) / 3) ^ n))]

      simp only [one_div, inv_pow, inv_pos, Nat.ofNat_pos, mul_le_mul_right, pow_pos,
        mul_le_iff_le_one_left]
      have merge_sums := Summable.tsum_sub
        (cantorSet_series_summable (fun i ↦ χ₂ (1 + i + n)))
        (cantorSet_series_summable (fun i ↦ χ₁ (1 + n + i)))
      simp only [cantorSet_series, one_div, inv_pow] at merge_sums
      rw [←merge_sums]
      simp only [←sub_mul]
      let χ₃ : ℕ → ({0, 2} : Set ℤ) := fun i ↦ Subtype.mk |χ₂ (1 + i + n) - χ₁ (1 + n + i)| <| by
        apply (Subtype.coe_prop (χ₁ (1 + n + i))).elim <;>
          apply (Subtype.coe_prop (χ₂ (1 + i + n))).elim <;>
            simp_all
      have eq₃ :
            (fun i ↦ |(χ₂ (1 + i + n) : ℝ) - χ₁ (1 + n + i)| * (1 / 3) ^ i * (1 / 3)) =
            (fun i ↦ cantorSet_series χ₃ i) := by
          simp [χ₃]
      have norm_diff_summable :
          Summable
          fun i ↦ ‖((χ₂ (1 + i + n) : ℝ) - (χ₁ (1 + n + i)))  * (1 / 3 : ℝ) ^ i * (1 / 3)‖ := by
        simp only [Real.norm_eq_abs, abs_mul]
        conv =>
          arg 1; intro n
          rw [(by aesop : |(1 : ℝ) / 3| = (1 : ℝ) / 3),
            (by aesop : |(((1 : ℝ) / 3) ^ n)| = (((1 : ℝ) / 3) ^ n))]
        rw [eq₃]
        exact cantorSet_series_summable χ₃
      have le_abs := norm_tsum_le_tsum_norm norm_diff_summable
      simp only [one_div, inv_pow, Real.norm_eq_abs, norm_mul, norm_inv, norm_pow] at le_abs
      calc
        _ ≤ _ := le_abs
        _ ≤ _ := by
          conv in (_ * _ * _) =>
            rw [(by aesop : |(3 : ℝ)|⁻¹ = 1 / 3), (by aesop : (|(3 : ℝ)| ^ i)⁻¹ = (1 / 3) ^ i)]
          rw [eq₃]
          exact (cantorSet_subset_unitInterval (cantorSet_series_in_cantorSet χ₃)).right
    have diseq : (1 : ℝ) / 3 * (1 / 3) ^ n < 2 / 3 * (1 / 3) ^ n := by
      simp
      linarith
    simp only [neg_sub]
    apply ne_of_gt
    calc
      _ ≤ _ := tail_le_third
      _ < _ := diseq
      _ ≤ _ := first_ge_two_thirds

  exact Function.injective_iff_pairwise_ne.mpr diff

@[simp]
theorem cantor_set_continuum_card : #cantorSet = continuum := by
  apply le_antisymm
  · rw [←Cardinal.mk_real]
    exact Cardinal.mk_set_le cantorSet
  · have := Cardinal.mk_le_of_injective sum_of_cantorSet_series_injective
    simp_all

def is_triadic (x : ℝ) :=
  ∃ n : ℤ, ∃ k : ℕ, x = n / (2 * 3 ^ k) ∧ Int.gcd n 2 = 1

lemma triadic_not_in_cantorSet (x : ℝ) (h : is_triadic x) : x ∉ cantorSet := by
  have ⟨n, k, ⟨h₁, h₂⟩⟩ := h
  rw [h₁]
  revert n x
  induction k with
  | zero =>
    intro _ _ n h₁ h₂
    simp only [pow_zero, mul_one]
    rcases lt_trichotomy n 1 with _ | h | _
    . apply (LE.le.eq_or_lt' (by omega : n ≤ 0)).elim
      . intro a
        simp [←a] at h₂
      . intro h abs
        have : (n : ℝ) / 2 < 0 := by rify at h; linarith
        have := (cantorSet_subset_unitInterval abs).left
        linarith
    . simp [cantorSet, h]
      use 1
      simp
      exact ⟨fun _ _ _ ↦ by linarith, fun _ _ _ ↦ by linarith⟩
    . apply (LE.le.eq_or_lt' (by omega : n ≥ 2)).elim
      . intro
        simp_all
      . intro h abs
        have : (n : ℝ) / 2 > 1 := by rify at h; linarith
        have := (cantorSet_subset_unitInterval abs).right
        linarith
  | succ k ih =>
    conv at ih =>
      intro _ _ _ h
      rw [←h]
    intro x hx n h₁ h₂
    rw [←h₁]
    let p₀ := x * 3
    let p₁ := x * 3 - 2
    have abs₀ := by
      refine ih p₀ ?_ n ?g1 ?g2
      use n, k
      refine ⟨?g3, ?g4⟩
      case g1 | g3 =>
        simp only [p₀, h₁]
        ring_nf
      case g2 | g4 =>
        assumption
    have abs₁ := by
      refine ih p₁ ?_ (n - 4 * (3 ^ k)) ?g1 ?g2
      use (n - 4 * (3 ^ k)), k
      refine ⟨?g3, ?g4⟩
      case g1 | g3 =>
        field_simp [p₁, h₁]
        ring_nf
      case g2 | g4 =>
        rw [←h₂]
        apply Int.gcd_sub_right_left_of_dvd
        omega
    intro abs
    exact (either_anc_in_cantorSet abs).elim abs₀ abs₁

lemma triadic_dense : Dense is_triadic := by
  apply dense_of_exists_between
  intro a b h
  rw [←sub_pos] at h

  have big_k {x : ℝ} : x > 0 → ∃ k : ℕ, 1 / (3 ^ k) < x := by
    intro h
    use (Int.log 3 (1 / x) + 1).toNat
    calc
      _ = 1 / (3 : ℝ) ^ ((Int.log 3 (1 / x) + 1).toNat : ℤ) := by rfl
      _ ≤ 1 / (3 : ℝ) ^ (Int.log 3 (1 / x) + 1) := by
        rw [←one_div_zpow, ←one_div_zpow]
        apply (zpow_le_zpow_iff_right_of_lt_one₀ (by linarith) (by linarith)).mpr
        exact Int.self_le_toNat _
      _ < 1 / (1 / x) := by
        apply one_div_lt_one_div_of_lt
        . exact one_div_pos.mpr h
        . apply Int.lt_zpow_succ_log_self (by norm_cast)
      _ = _ := by simp

  have ⟨k, hk⟩ := big_k h

  let n := ⌊(a * (2 * 3 ^ k) - 1) / 2⌋ + 1
  use (2 * n + 1) / (2 * 3 ^ k)
  refine ⟨?_, ?_, ?_⟩
  . use 2 * n + 1, k
    simp
  . simp only [Int.cast_add, Int.cast_one, n]
    apply (lt_div_iff₀ (by norm_cast; simp : ((2 : ℝ) * 3 ^ k) > 0)).mpr
    ring_nf
    calc
      _ > (3 : ℝ) + (-1 / 2 + a * 3 ^ k - 1) * 2 := by simp
      _ ≥ _ := by ring_nf; simp
  . have : (2 * n + 1) / (2 * 3 ^ k) - a < b - a := calc
      _ ≤ 1 / (3 ^ k) := by
        simp only [Int.cast_add, Int.cast_one, n]
        rw [OrderedSub.tsub_le_iff_right]
        apply (div_le_iff₀ (by norm_cast; simp : ((2 : ℝ) * 3 ^ k) > 0)).mpr
        ring_nf
        calc
          _ ≤ 3 + (-1 / 2 + a * 3 ^ k) * 2 := by
            simp
            exact Int.floor_le _
          _ ≤ _ := by simp; ring_nf; simp
      _ < _ := hk
    simp_all

theorem empty_interior_cantorSet : interior cantorSet = ∅ := by
  apply interior_eq_empty_iff_dense_compl.mpr
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_univ_subset
  calc
    _ ⊇ _ := closure_mono triadic_not_in_cantorSet
    _ = _ := dense_iff_closure_eq.mp triadic_dense
