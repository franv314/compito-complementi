import Mathlib.Data.Real.Cardinality
import Mathlib.Logic.Function.Defs
import Mathlib.SetTheory.Cardinal.Defs
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Topology.MetricSpace.Basic

import Complementi.CantorSet
import Complementi.EuclideanTopology

variable {X : Type} [TopologicalSpace X]

def first_category₁ (s : Set X) :=
  ∃ f : ℕ → { x : Set X // IsNowhereDense x },
  (⋃ (i : ℕ), (f i).val) = s

def first_category₂ (s : Set X) :=
  ∃ f : ℕ → { x : Set X // IsClosed x ∧ interior x = ∅},
  (⋃ (i : ℕ), (f i).val) ⊇ s

lemma first_category₁_of_first_category₂ {s : Set X} (h : first_category₂ s) : first_category₁ s := by
  let strip (x : { x : Set X // IsClosed x ∧ interior x = ∅}) : { x : Set X // IsNowhereDense x } := by
    apply Subtype.mk (x.val ∩ s)
    rw [IsNowhereDense]
    have ⟨hx₁, hx₂⟩ := x.prop
    have contains : interior (closure (↑x ∩ s)) ⊆ interior (closure ↑x) :=
      interior_mono (closure_mono Set.inter_subset_left)
    simp only [IsClosed.closure_eq, hx₂, Set.subset_empty_iff] at contains
    exact contains

  let ⟨f, hf⟩ := h
  use strip ∘ f
  ext
  refine ⟨?_, ?_⟩
  . simp_all [strip]
  . intro h
    have := hf h
    simp_all [strip]

lemma first_category₂_of_first_category₁ {s : Set X} (h : first_category₁ s) : first_category₂ s := by
  let close : (x : { x : Set X // IsNowhereDense x }) → { x : Set X // IsClosed x ∧ interior x = ∅} :=
    λ x => Subtype.mk (closure x) (by rw [x.prop]; simp)

  let ⟨f, hf⟩ := h
  rw [←hf]
  use close ∘ f
  apply Set.iUnion_mono
  simp only [Function.comp_apply, close]
  exact λ i => subset_closure

-- Exercise 1.A
theorem first_category₁_iff_first_category₂ (s : Set X) : first_category₁ s ↔ first_category₂ s :=
  ⟨first_category₂_of_first_category₁, first_category₁_of_first_category₂⟩

@[simp]
def first_category :=
  { x : Set X // first_category₂ x }

-- Exercise 1.B
theorem first_category_reals_parts_continuum_card : Cardinal.mk (first_category (X := ℝ)) = 2 ^ Cardinal.continuum := by
  apply le_antisymm
  . let f (x : first_category) : Set ℝ := x.val
    have f_inj : Function.Injective f :=
      (Set.injective_codRestrict Subtype.property).mp (λ a₁ a₂ a => a)
    have le_powerset := Cardinal.mk_le_of_injective f_inj
    rwa [Cardinal.mk_set, Cardinal.mk_real] at le_powerset
  . let f (x : 𝒫 cantorSet) : first_category (X := ℝ) := by
      apply Subtype.mk x.val
      use λ _ => (Subtype.mk cantorSet ⟨isClosed_cantorSet, empty_interior_cantorSet⟩)
      intro y h
      simp [x.prop h]
    have f_inj : Function.Injective f := by
      simp only [Function.Injective, f]
      intro x₁ x₂ h
      apply Subtype.val_injective
      exact congr_arg (·.1) h
    have le_powerset := Cardinal.mk_le_of_injective f_inj
    simp_all

-- Exercise 1.C
theorem first_category_not_union_of_closed_sets_with_empty_interior :
    ∃ s : first_category (X := ℝ), ∀ (f : ℕ → { x : Set ℝ // IsClosed x ∧ interior x = ∅}),
    s.val ≠ ⋃ (i : ℕ), f i := by
  by_contra! abs
  have ⟨f, hf⟩ := Classical.skolem.mp abs
  let g (f : ℕ → { x : Set ℝ // IsClosed x ∧ interior x = ∅ }) : first_category :=
    Subtype.mk (⋃ (i : ℕ), (f i).val) (by use f)
  have f_inj : Function.Injective f :=
    (Function.LeftInverse.injective (g := g)) (λ x => by simp [g, (hf x).symm])
  have card_bound : Cardinal.mk { x : Set ℝ // IsClosed x ∧ interior x = ∅ } ≤ Cardinal.continuum := calc
    _ ≤ Cardinal.mk { x : Set ℝ // IsClosed x } := by
      let f : { x : Set ℝ // IsClosed x ∧ interior x = ∅ } → { x : Set ℝ // IsClosed x } :=
        λ x => Subtype.mk x.val x.prop.left
      have f_inj : Function.Injective f := by
        intro a b h
        simp only [Subtype.mk.injEq, f] at h
        exact Subtype.ext_iff.mpr h
      exact Cardinal.mk_le_of_injective f_inj
    _ = _ := by simp
  have few_first_category := Cardinal.mk_le_of_injective f_inj
  rw [first_category_reals_parts_continuum_card] at few_first_category
  simp only [Cardinal.mk_pi, Cardinal.prod_const, Cardinal.lift_id, Cardinal.mk_eq_aleph0] at few_first_category
  have cont : 2 ^ Cardinal.continuum ≤ Cardinal.continuum := calc
    _ ≤ _ := few_first_category
    _ ≤ _ := Cardinal.power_le_power_right card_bound
    _ = _ := by simp
  apply lt_iff_not_ge.mp (Cardinal.cantor Cardinal.continuum) cont
