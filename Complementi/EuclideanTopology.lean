import Mathlib.Data.Real.Cardinality

set_option maxHeartbeats 0

@[simp]
def open_intervals : Set (Set ℝ) :=
  (fun ((x, y) : ℝ × ℝ) ↦ (Set.Ioo x y)) '' Set.univ

@[simp]
def subopen_intervals (s : Set ℝ) : { x : ℝ × ℝ // Set.Ioo x.1 x.2 ⊆ s } → Set ℝ :=
  fun x ↦ (Set.Ioo x.val.1 x.val.2)

lemma open_intervals_continuum_card : Cardinal.mk open_intervals ≤ Cardinal.continuum := by
  let f : ℝ × ℝ → open_intervals :=
    fun ((x, y) : ℝ × ℝ) ↦ Subtype.mk (Set.Ioo x y) (by simp)
  have f_sur : Function.Surjective f := by
    intro ⟨x, hx⟩
    simp only [open_intervals, Set.image_univ, Set.mem_range] at hx
    have ⟨y, hy⟩ := hx
    use y
    simpa [f]
  exact le_trans (Cardinal.mk_le_of_surjective f_sur) (by simp [Cardinal.mk_real])

lemma countable_union (s : {x : Set ℝ // IsOpen x}) : ∃ t ⊆ open_intervals, t.Countable ∧ t.Nonempty ∧  ↑s = ⋃₀ t := by
  have countable_subcover (s : { x : Set ℝ // IsOpen x}) :=
    isLindelof_iff_countable_subcover.mp
    (HereditarilyLindelofSpace.isHereditarilyLindelof_univ s (by simp))
    (subopen_intervals s)
    fun _ ↦ by simp [isOpen_Ioo]
    fun x hx ↦ by
      simp only [Set.mem_iUnion, Set.mem_Ioo, Subtype.exists, exists_prop, Prod.exists, subopen_intervals]
      have ⟨ε, hε⟩:= Metric.isOpen_iff.mp s.prop x hx
      use x - ε, x + ε
      simp_all [Real.ball_eq_Ioo]
  have ⟨t, ht⟩ := countable_subcover s
  cases em (t.Nonempty) with
  | inl _ =>
    use subopen_intervals s '' t
    refine ⟨?_, ?_, ?_, ?_⟩
    . exact fun _ _ ↦ by aesop
    . simp_all [Set.Countable.image]
    . simpa
    . simp_all [Set.sUnion_image, Set.Subset.antisymm_iff]
  | inr empty =>
    use {∅}
    refine ⟨?_, by simp, by simp, ?_⟩
    . simp only [Set.singleton_subset_iff]
      use (0, 0)
      simp
    . simp_all [Set.not_nonempty_iff_eq_empty]

@[simp]
lemma euclidean_topology_continuum_card : Cardinal.mk { x : Set ℝ // IsOpen x } = Cardinal.continuum := by
  have ⟨f, hf⟩ :
      ∃ f : { x : Set ℝ // IsOpen x } → { x : Set (Set ℝ) // x ⊆ open_intervals ∧ x.Countable ∧ x.Nonempty },
      ∀ x : _, x.val = ⋃₀ (f x) := by
    have ⟨f, hf⟩ := Classical.skolem.mp countable_union
    use fun x ↦ Subtype.mk (f x) (by simp_all)
    aesop
  have f_inj : Function.Injective f := by
    intro x y h
    ext
    simp_all [hf x, hf y]
  have ⟨g, g_sur⟩ :
      ∃ g : (ℕ → { x : Set ℝ // open_intervals x }) → { x : Set (Set ℝ) // x ⊆ open_intervals ∧ x.Countable ∧ x.Nonempty },
      Function.Surjective g := by
    use fun x ↦ Subtype.mk ((fun i ↦ x i) '' Set.univ) <| by
      refine ⟨?_, ?_, ?_⟩
      . intro y hy
        simp only [Set.image_univ, Set.mem_range] at hy
        have ⟨z, hz⟩ := hy
        rw [←hz]
        exact (x z).prop
      . exact Set.Countable.image Set.countable_univ _
      . exact Set.Nonempty.of_subtype
    intro x
    have ⟨_, ⟨sc, sn⟩⟩ := x.prop
    rw [Set.Countable] at sc
    rw [←Set.nonempty_coe_sort] at sn
    have ⟨f, hf⟩ := exists_surjective_nat x
    use fun s ↦ Subtype.mk (f s) (x.prop.left (f s).prop)
    ext x'
    simp only [Set.image_univ, Set.mem_range]
    apply Iff.intro
    . intro ⟨y, hy⟩
      rw [←hy]
      simp
    . intro hx'
      have ⟨y', hy'⟩ := hf (Subtype.mk x' hx')
      exact ⟨y', Subtype.ext_iff.mp hy'⟩
  apply le_antisymm
  . calc
      _ ≤ _ := Cardinal.mk_le_of_injective f_inj
      _ ≤ _ := Cardinal.mk_le_of_surjective g_sur
      _ ≤ Cardinal.mk { x // open_intervals x } ^ Cardinal.aleph0 := by simp
      _ ≤ _ := Cardinal.power_le_power_right open_intervals_continuum_card
      _ = _ := by simp
  . let f : ℝ → { x // IsOpen x } :=
      fun x ↦ Subtype.mk {x}ᶜ (by simp)
    have f_inj : Function.Injective f := by
      intro x y h
      simp [f] at h
      exact h
    rw [←Cardinal.mk_real]
    exact Cardinal.mk_le_of_injective f_inj

@[simp]
lemma euclidean_topology_closed_continuum_card : Cardinal.mk {x : Set ℝ // IsClosed x} = Cardinal.continuum := calc
  _ = Cardinal.mk {x : Set ℝ // IsOpen x} := by
    let f : {x : Set ℝ // IsOpen x} → {x : Set ℝ // IsClosed x} :=
      λ x => Subtype.mk (x.val)ᶜ (isOpen_compl_iff.mp (by simp; exact x.prop))
    have f_bij : Function.Bijective f := by
      constructor
      . intro a b h
        simp only [Subtype.mk.injEq, compl_inj_iff, f] at h
        exact Subtype.ext_iff.mpr h
      . intro x
        use Subtype.mk (x.val)ᶜ (isOpen_compl_iff.mpr x.prop)
        simp [f]
    symm
    exact Cardinal.mk_congr (Equiv.ofBijective (f := f) f_bij)
  _ = _ := by simp
