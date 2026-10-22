module
public import LeanShared.Analysis.DomainPressureRefinement

/-! Restricting a full open-cylinder supremum to the actual compact
region cannot increase the minimum cover coefficient. -/
@[expose] public noncomputable section
open Set
open scoped BigOperators
namespace LeanShared.PressureCoverDomainComparison
open PressureCoverRefinement DomainPressureRefinement
variable {X I : Type*}

theorem coefficient (K L S : Set X) (u : I → Set X) (f : X → ℝ)
    (hKL : K ⊆ L) (hb : ∀ i, BddAbove ({0} ∪ f '' (L ∩ u i)))
    (hc : ∃ c : Finset I, S ⊆ ⋃ i ∈ c, u i) :
    coverCoefficient K S u f ≤ coverCoefficient L S u f := by
  have hbK : ∀ i, BddAbove ({0} ∪ f '' (K ∩ u i)) := fun i =>
    (hb i).mono (union_subset_union_right _ (image_mono (inter_subset_inter_left _ hKL)))
  have hbelow : BddBelow {a : ℝ | ∃ c : Finset I, S ⊆ ⋃ i ∈ c, u i ∧
      a = ∑ i ∈ c, domainCoefficient K (u i) f} := by
    refine ⟨0, ?_⟩
    rintro a ⟨c, _, rfl⟩
    exact Finset.sum_nonneg fun i _ => domainCoefficient_nonneg_of_bdd (hbK i)
  have hne : {a : ℝ | ∃ c : Finset I, S ⊆ ⋃ i ∈ c, u i ∧
      a = ∑ i ∈ c, domainCoefficient L (u i) f}.Nonempty := by
    obtain ⟨c, hc⟩ := hc
    exact ⟨_, c, hc, rfl⟩
  apply le_csInf hne
  rintro a ⟨c, hc, rfl⟩
  apply (csInf_le hbelow ⟨c, hc, rfl⟩).trans
  apply Finset.sum_le_sum
  intro i hi
  exact csSup_le_csSup (hb i) ⟨0, Or.inl (mem_singleton 0)⟩
    (union_subset_union_right _ (image_mono (inter_subset_inter_left _ hKL)))

end LeanShared.PressureCoverDomainComparison
