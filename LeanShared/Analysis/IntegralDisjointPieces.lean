module
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Integrals over finite disjoint pieces. A function vanishing outside a finite
pairwise disjoint union of measurable sets, integrable on each piece, has integral equal
to the sum of its integrals over the pieces. -/
public noncomputable section
open MeasureTheory Set Finset
namespace LeanShared.IntegralDisjointPieces

theorem integral_eq_sum {X ι : Type*} [MeasurableSpace X] {μ : Measure X}
    (s : Finset ι) (A : ι → Set X) (measurable : ∀ i ∈ s, MeasurableSet (A i))
    (disjoint : Set.PairwiseDisjoint (s : Set ι) A) (f : X → ℝ)
    (integrable : ∀ i ∈ s, IntegrableOn f (A i) μ)
    (vanish : ∀ x, x ∉ ⋃ i ∈ s, A i → f x = 0) :
    ∫ x, f x ∂μ = ∑ i ∈ s, ∫ x in A i, f x ∂μ := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero vanish,
    integral_biUnion_finset s measurable disjoint integrable]

end LeanShared.IntegralDisjointPieces
