import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall

set_option maxHeartbeats 0

postfix:max "´" => deriv

variable (f : ℝ → ℝ → ℝ) (hf : ContDiff ℝ 1 f.uncurry) (hl : ∃ K : NNReal, ∀ t : ℝ, LipschitzWith K (f t))

include hf
lemma is_picard_lindelof_constant_radius_on_rectangle_of_contdiff
    {a b r : ℝ}
    (x₀ : ℝ)
    (hab : a ≤ b)
    (hr : r ≥ 0) :
    ∃ ℓ₁ ℓ₂ L K : NNReal, ℓ₁ > (0 : ℝ) ∧ ∀ t₀ ∈ Set.Icc a b, ∀ x₀' ∈ Metric.closedBall x₀ r,
    IsPicardLindelof f ⟨t₀, (by simp : t₀ ∈ Set.Icc (t₀ - ℓ₁) (t₀ + ℓ₁))⟩ x₀' ℓ₂ 0 L K  := by
  have ⟨xₘ, hxₘ⟩ := IsCompact.exists_isMaxOn (s := Set.Icc (a - 1) (b + 1) ×ˢ Metric.closedBall x₀ (r + 1))
    (IsCompact.prod isCompact_Icc (isCompact_closedBall _ _))
    (by simp_all; split_ands; repeat linarith)
    (Continuous.norm hf.continuous).continuousOn
  have ⟨xₘ', hxₘ'⟩ := IsCompact.exists_isMaxOn (s := Set.Icc (a - 1) (b + 1) ×ˢ Metric.closedBall x₀ (r + 1))
    (IsCompact.prod isCompact_Icc (isCompact_closedBall _ _))
    (by simp_all; split_ands; repeat linarith)
    (Continuous.norm (hf.continuous_fderiv (by rfl))).continuousOn
  rw [IsMaxOn, IsMaxFilter, Filter.eventually_principal] at hxₘ hxₘ'

  let ℓ₁ : NNReal := ⟨1 / max 1 ‖f.uncurry xₘ‖, by simp_all⟩
  let ℓ₂ : NNReal := 1
  let L : NNReal := ‖f.uncurry xₘ‖₊
  let K : NNReal := ‖fderiv ℝ f.uncurry xₘ'‖₊

  use ℓ₁, ℓ₂, L, K
  refine ⟨by simp [ℓ₁], ?_⟩
  intro t₀' ht₀' x₀' hx₀'
  constructor
  . intro t₀ ht₀ x₁ hx₁ x₂ hx₂
    have d₁ : a - 1 ≤ t₀' - ℓ₁ := by gcongr <;> simp_all [ℓ₁, inv_le_one_of_one_le₀]
    have d₂ : t₀' + ℓ₁ ≤ b + 1 := by gcongr <;> simp_all [ℓ₁, inv_le_one_of_one_le₀]
    have m₁ := (Set.mk_mem_prod ((Set.Icc_subset_Icc d₁ d₂) ht₀) (Metric.closedBall_subset_closedBall (ε₂ := 1) (by simp [ℓ₂]) hx₁))
    have m₂ := (Set.mk_mem_prod ((Set.Icc_subset_Icc d₁ d₂) ht₀) (Metric.closedBall_subset_closedBall (ε₂ := 1) (by simp [ℓ₂]) hx₂))
    have lip : ∀ x ∈ Set.Icc (a - 1) (b + 1) ×ˢ Metric.closedBall x₀' 1, ‖fderivWithin ℝ (f.uncurry) (Set.Icc (a - 1) (b + 1) ×ˢ Metric.closedBall x₀' 1) x - 0‖ ≤ K := λ x hx => calc
      _ = ‖fderiv ℝ (f.uncurry) x‖ := by
        rw [sub_zero]
        apply congr_arg norm
        refine (hf.differentiable (by simp)).differentiableAt.fderivWithin (uniqueDiffWithinAt_convex ?_ ?_ ?_)
        . exact Convex.prod (convex_Icc _ _) (convex_closedBall _ _)
        . refine ⟨(a - 1 / 2, x₀'), mem_interior.mpr ?_⟩
          refine ⟨Set.Ioo (a - 1) (b + 1) ×ˢ Metric.ball x₀' 1, ⟨?_, ?_, ?_⟩⟩
          . exact Set.prod_mono Set.Ioo_subset_Icc_self Metric.ball_subset_closedBall
          . exact IsOpen.prod isOpen_Ioo Metric.isOpen_ball
          . refine Set.mk_mem_prod (Set.mem_Ioo.mpr ⟨by simp; norm_num, ?_⟩) (Metric.mem_ball_self zero_lt_one)
            calc
              _ < a := by simp
              _ ≤ b := by assumption
              _ < _ := by simp
        . exact subset_closure hx
      _ ≤ ‖fderiv ℝ f.uncurry xₘ'‖ := by
        refine hxₘ'.right x (Set.mk_mem_prod hx.left ?_)
        have := dist_triangle x.2 x₀' x₀
        exact Metric.mem_closedBall.mpr <| calc
          _ ≤ _ := dist_triangle x.2 x₀' x₀
          _ ≤ _ := by
            rw [add_comm]
            gcongr <;> simp_all
      _ = K := by simp [K]
    have th := Convex.norm_image_sub_le_of_norm_fderivWithin_le' (hf.differentiable (by rfl)).differentiableOn lip (Convex.prod (convex_Icc _ _) (convex_closedBall _ _)) m₂ m₁
    simp at th
    rw [edist_dist, edist_dist]
    rw [(by rw [ENNReal.ofReal]; exact congr_arg _ (nndist_dist _ _).symm : ENNReal.ofReal (dist x₁ x₂) = ENNReal.ofNNReal (nndist x₁ x₂)), ←ENNReal.coe_mul]
    rw [(by rw [ENNReal.ofReal]; exact congr_arg _ (nndist_dist _ _).symm : ENNReal.ofReal (dist (f t₀ x₁) (f t₀ x₂)) = ENNReal.ofNNReal (nndist (f t₀ x₁) (f t₀ x₂)))]
    refine ENNReal.coe_le_coe_of_le (Subtype.coe_le_coe.mp ?_)
    simpa [dist]
  . intro x₀' hx₀'
    exact (Continuous.comp hf.continuous (Continuous.prodMk continuous_id continuous_const)).continuousOn
  . intro t₀ ht₀ x₁ hx₁
    have d₁ : a - 1 ≤ t₀' - ℓ₁ := by gcongr <;> simp_all [ℓ₁, inv_le_one_of_one_le₀]
    have d₂ : t₀' + ℓ₁ ≤ b + 1 := by gcongr <;> simp_all [ℓ₁, inv_le_one_of_one_le₀]
    calc
      _ = ‖f.uncurry (t₀, x₁)‖ := congr_arg _ (Function.uncurry_apply_pair _ _ _)
      _ ≤ _ := by
        refine hxₘ.right (t₀, x₁) (Set.mk_mem_prod ((Set.Icc_subset_Icc d₁ d₂) ht₀) ?_)
        exact Metric.mem_closedBall.mpr <| calc
          _ ≤ _ := dist_triangle x₁ x₀' x₀
          _ ≤ _ := by
            rw [add_comm]
            gcongr <;> simp_all [ℓ₂]
      _ = _ := by simp [L]
  . simp [ℓ₁, ℓ₂]
    rw [(by simp [L] : L = |f.uncurry xₘ|)]
    apply (le_or_gt |f.uncurry xₘ| 1).elim
    . simp_all
    . intro h
      rw [(by simp; linarith : max 1 |f.uncurry xₘ| = |f.uncurry xₘ|)]
      exact le_of_eq (CommGroupWithZero.mul_inv_cancel |f.uncurry xₘ| (by linarith))

omit hf
theorem ODE_solution_unique_of_open_interval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {v : ℝ → E → E}
    {s : ℝ → Set E} {K : NNReal} {f g : ℝ → E} {t₀ : ℝ} {U : Set ℝ}
    (hU : IsOpen U ∧ IsConnected U)
    (hv : ∀ t ∈ U, LipschitzOnWith K (v t) (s t)) (ht : t₀ ∈ U)
    (hf : ∀ t ∈ U, HasDerivAt f (v t (f t)) t ∧ f t ∈ s t)
    (hg : ∀ t ∈ U, HasDerivAt g (v t (g t)) t ∧ g t ∈ s t) (heq : f t₀ = g t₀) :
    Set.EqOn f g U :=  by
  rw [Set.EqOn]
  by_contra! abs
  have ⟨t', ht'⟩ := abs
  have ⟨a, b, hab⟩ : ∃ a b : ℝ, t' ∈ Set.Ioo a b ∧ t₀ ∈ Set.Ioo a b ∧ Set.Ioo a b ⊆ U := by
    have ⟨ε₁, hε₁⟩ := Metric.isOpen_iff.mp hU.left t₀ ht
    have ⟨ε₂, hε₂⟩ := Metric.isOpen_iff.mp hU.left t' ht'.1
    use min (t₀ - ε₁) (t' - ε₂), max (t₀ + ε₁) (t' + ε₂)
    split_ands
    any_goals simp_all
    intro x hx
    rw [Set.mem_Ioo, lt_sup_iff, inf_lt_iff] at hx
    rcases hx with ⟨(_ | _), (_ | _)⟩
    . exact hε₁.2 (by simp_all [Real.ball_eq_Ioo])
    . apply (Classical.em (x ∈ Set.Icc t₀ t')).elim
      . exact λ hx => hU.2.isPreconnected.Icc_subset ht ht'.1 hx
      . intro hx
        rw [Set.mem_Icc, not_and_or, not_le] at hx
        rcases hx with (_ | _)
        . exact hε₁.2 (by simp_all [Real.ball_eq_Ioo]; linarith)
        . exact hε₂.2 (by simp_all [Real.ball_eq_Ioo]; linarith)
    . apply (Classical.em (x ∈ Set.Icc t' t₀)).elim
      . exact λ hx => hU.2.isPreconnected.Icc_subset ht'.1 ht hx
      . intro hx
        rw [Set.mem_Icc, not_and_or, not_le] at hx
        rcases hx with (_ | _)
        . exact hε₂.2 (by simp_all [Real.ball_eq_Ioo]; linarith)
        . exact hε₁.2 (by simp_all [Real.ball_eq_Ioo]; linarith)
    . exact hε₂.2 (by simp_all [Real.ball_eq_Ioo])
  have cont := ODE_solution_unique_of_mem_Ioo
    (λ t ht => hv t (hab.2.2 ht))
    hab.2.1
    (λ t ht => hf t (hab.2.2 ht))
    (λ t ht => hg t (hab.2.2 ht))
    heq
  exact ht'.right (cont hab.1)

def local_solutions (t₀ x₀ : ℝ) :=
  {
    x : Set ℝ × (ℝ → ℝ) //
    (IsOpen x.1 ∧ IsConnected x.1 ∧ t₀ ∈ x.1) ∧
    ((∀ y ∈ x.1, HasDerivAt x.2 (f y (x.2 y)) y) ∧ x.2 t₀ = x₀)
  }

def free_local_solutions :=
  {
    x : Set ℝ × (ℝ → ℝ) //
    (IsOpen x.1 ∧ IsConnected x.1) ∧
    (∀ y ∈ x.1, HasDerivAt x.2 (f y (x.2 y)) y)
  }

instance (t₀ x₀ : ℝ) : LE (local_solutions f t₀ x₀) :=
  ⟨λ α β => α.val.1 ⊆ β.val.1 ∧ Set.EqOn α.val.2 β.val.2 α.val.1⟩

instance : LE (free_local_solutions f) :=
  ⟨λ α β => α.val.1 ⊆ β.val.1 ∧ Set.EqOn α.val.2 β.val.2 α.val.1⟩

include hl
lemma is_extension_of_subset_domain {t₀ x₀ : ℝ} (α β : local_solutions f t₀ x₀) (h : α.val.1 ⊆ β.val.1) : α ≤ β := by
  refine ⟨h, ?_⟩
  have ⟨K, hK⟩ := hl
  exact ODE_solution_unique_of_open_interval
    ⟨α.prop.1.1, α.prop.1.2.1⟩
    (λ t ht => (hK t).lipschitzOnWith)
    α.prop.1.2.2
    (λ x hx => ⟨α.prop.2.1 x hx, Set.mem_univ _⟩)
    (λ x hx => ⟨β.prop.2.1 x (h hx), Set.mem_univ _⟩)
    (Eq.trans α.prop.2.2 β.prop.2.2.symm)

lemma equal_on_inter {t₀ x₀ : ℝ} (α β : local_solutions f t₀ x₀) : Set.EqOn α.val.2 β.val.2 (α.val.1 ∩ β.val.1) := by
  let α' : local_solutions f t₀ x₀ := by
    refine ⟨(α.val.1 ∩ β.val.1, α.val.2), ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩⟩
    . exact IsOpen.inter α.prop.1.1 β.prop.1.1
    . exact Convex.isConnected
        (Convex.inter (Real.convex_iff_isPreconnected.mpr (α.prop.1.2.1.isPreconnected)) (Real.convex_iff_isPreconnected.mpr (β.prop.1.2.1.isPreconnected)))
        ⟨t₀, ⟨α.prop.1.2.2, β.prop.1.2.2⟩⟩
    . exact ⟨α.prop.1.2.2, β.prop.1.2.2⟩
    . exact λ y hy => α.prop.2.1 y (Set.inter_subset_left hy)
    . exact α.prop.2.2
  let β' : local_solutions f t₀ x₀ := by
    refine ⟨(α.val.1 ∩ β.val.1, β.val.2), ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩⟩
    . exact IsOpen.inter α.prop.1.1 β.prop.1.1
    . exact Convex.isConnected
        (Convex.inter (Real.convex_iff_isPreconnected.mpr (α.prop.1.2.1.isPreconnected)) (Real.convex_iff_isPreconnected.mpr (β.prop.1.2.1.isPreconnected)))
        ⟨t₀, ⟨α.prop.1.2.2, β.prop.1.2.2⟩⟩
    . exact ⟨α.prop.1.2.2, β.prop.1.2.2⟩
    . exact λ y hy => β.prop.2.1 y (Set.inter_subset_right hy)
    . exact β.prop.2.2
  exact (is_extension_of_subset_domain f hl α' β' (by simp [α', β'])).2

lemma union_of_free_solutions
    {α : Type} [Nonempty α] (ι : α → free_local_solutions f)
    (h : ∀ i j : α, ∃ x : ℝ, x ∈ (ι i).val.1 ∧ x ∈ (ι j).val.1 ∧ (ι i).val.2 x = (ι j).val.2 x) :
    ∃ β : free_local_solutions f, ∀ i : α, (ι i ≤ β) := by
  let U := ⋃ (i : α), (ι i).val.1
  have := λ x => Classical.dec (x ∈ U)
  let β : ℝ → ℝ := λ x => dite (x ∈ U) (λ hx => (ι (Set.mem_iUnion.mp hx).choose).val.2 x) (λ _ => 0)
  have eq (i : α) : Set.EqOn β (ι i).val.2 (ι i).val.1 := λ x₀ hx₀ => by
    have mem : x₀ ∈ U := Set.mem_iUnion_of_mem i hx₀
    let j := (Set.mem_iUnion.mp mem).choose
    have ⟨x₁, hx₁⟩ := h i j
    let fi : local_solutions f x₁ ((ι i).val.2 x₁) := ⟨(ι i).val, by simp_all [(ι i).prop]⟩
    let fj : local_solutions f x₁ ((ι i).val.2 x₁) := ⟨(ι j).val, by simp_all [(ι j).prop]⟩
    have := (Set.mem_iUnion.mp mem).choose_spec
    have := equal_on_inter f hl fi fj (x := x₀) (Set.mem_inter (by simp_all [fi]) (by simp_all [fj, j]))
    simp_all [fi, fj, j, β]
  have is_sol : ∀ y ∈ U, HasDerivAt β (f y (β y)) y := by
    intro x hx
    have ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    rw [eq i hi]
    apply HasDerivAt.congr_of_eventuallyEq ((ι i).prop.2 x hi)
    rw [Filter.EventuallyEq, eventually_nhds_iff]
    exact ⟨(ι i).val.1, ⟨λ y hy => eq i hy, (ι i).prop.1.1, hi⟩⟩
  let β : free_local_solutions f := by
    refine ⟨(U, β), ⟨⟨?_, ?_⟩, ?_⟩⟩
    . exact isOpen_iUnion (λ i => (ι i).prop.1.1)
    . exact IsConnected.iUnion_of_reflTransGen
        (λ i => ((ι i).prop.1.2))
        (λ i j => Relation.ReflTransGen.single ((h i j).imp (by simp_all)))
    . exact is_sol
  exact ⟨β, λ i => ⟨Set.subset_iUnion_of_subset i (λ ⦃a⦄ a => a), (eq i).symm⟩⟩

instance nonempty_local_solutions (t₀ x₀ : ℝ) : Nonempty (local_solutions f t₀ x₀) := by
  have ⟨ℓ₁, ℓ₂, L, K, h⟩ :=
      is_picard_lindelof_constant_radius_on_rectangle_of_contdiff f hf x₀ (by rfl : t₀ ≤ t₀) (by rfl : (0 : ℝ) ≤ 0)
  have is_picard_lindelof := h.2 t₀ (by simp) x₀ (by simp)
  have ⟨β', hβ'⟩ := is_picard_lindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt (by simp : x₀ ∈ _)
  let β : local_solutions f t₀ x₀ := by
    refine Subtype.mk (Set.Ioo (t₀ - ℓ₁) (t₀ + ℓ₁), β') ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩
    . exact isOpen_Ioo
    . exact isConnected_Ioo (by linarith)
    . simp_all
    . exact λ x hx => (hβ'.2 x (Set.mem_Icc_of_Ioo hx)).hasDerivAt
        (mem_nhds_iff.mpr ⟨Set.Ioo (t₀ - ℓ₁) (t₀ + ℓ₁), ⟨Set.Ioo_subset_Icc_self, isOpen_Ioo, hx⟩⟩)
    . simp_all
  exact Nonempty.intro β

include hf
lemma top_local_solutions (t₀ x₀ : ℝ) : ∃ α : local_solutions f t₀ x₀, ∀ β : local_solutions f t₀ x₀, β ≤ α := by
  have ex := nonempty_local_solutions f hf t₀ x₀
  have := nonempty_local_solutions f hf t₀ x₀
  have ⟨α, hα⟩ := union_of_free_solutions f hl
    (λ (β : local_solutions f t₀ x₀) => ⟨β.val, by simp_all [β.prop]⟩)
    (λ i j => ⟨t₀, by simp_all [i.prop, j.prop]⟩)
  have : t₀ ∈ α.val.1 := (hα (Classical.choice ex)).1 (by simp [(Classical.choice ex).prop])
  have := (hα (Classical.choice ex)).2 (by simp [(Classical.choice ex).prop] : t₀ ∈ _)
  use ⟨α.val, by simp_all [α.prop, (Classical.choice ex).prop]⟩
  exact λ β => ⟨by simp [(hα β).1], by simp [(hα β).2]⟩
