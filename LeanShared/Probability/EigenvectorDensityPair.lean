module

public import LeanShared.Probability.PositiveSupportLocalization

/-!
# Symmetry and support of two eigenvector densities

The forward product `g (m σ)` is exactly the inverse product `m (g σ)`.
Its normalization and support therefore pass to the inverse dynamics without
an additional probability or support hypothesis.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace LeanShared.EigenvectorDensityPair

variable {X : Type*} [MeasurableSpace X]

theorem product_comm (σ : Measure X) (g m : X → ℝ)
    (hg : Measurable g) (hm : Measurable m) :
    eigenvectorMeasure (eigenvectorMeasure σ m) g =
      eigenvectorMeasure (eigenvectorMeasure σ g) m := by
  unfold eigenvectorMeasure
  rw [← withDensity_mul σ hm.ennreal_ofReal hg.ennreal_ofReal,
    ← withDensity_mul σ hg.ennreal_ofReal hm.ennreal_ofReal, mul_comm]

theorem integral_comm (σ : Measure X) (g m : X → ℝ)
    (hg : Measurable g) (hm : Measurable m)
    (hg0 : ∀ x, 0 ≤ g x) (hm0 : ∀ x, 0 ≤ m x) :
    (∫ x, g x ∂eigenvectorMeasure σ m) =
      ∫ x, m x ∂eigenvectorMeasure σ g := by
  rw [integral_eigenvectorMeasure σ m hm hm0,
    integral_eigenvectorMeasure σ g hg hg0]
  congr 1
  funext x
  exact mul_comm _ _

variable [TopologicalSpace X]

/-- Strict positivity of both continuous densities puts a supported reference
point in the product support. Continuity is only required on the conull live
region, so no extension across the killing boundary is involved. -/
theorem mem_support_product (σ : Measure X) (K : Set X)
    (hσK : ∀ᵐ x ∂σ, x ∈ K) (g m : X → ℝ)
    (hg : Measurable g) (hm : Measurable m)
    (hgc : ContinuousOn g K) (hmc : ContinuousOn m K)
    {x : X} (hx : x ∈ σ.support) (hxK : x ∈ K)
    (hgx : 0 < g x) (hmx : 0 < m x) :
    x ∈ (eigenvectorMeasure (eigenvectorMeasure σ m) g).support := by
  have hxm : x ∈ (eigenvectorMeasure σ m).support :=
    PositiveSupportLocalization.mem_support_withDensity_of_pos σ K hσK m hm hmc hx hxK hmx
  have hmK : ∀ᵐ y ∂eigenvectorMeasure σ m, y ∈ K :=
    (show eigenvectorMeasure σ m ≪ σ from
      withDensity_absolutelyContinuous σ (fun y => ENNReal.ofReal (m y))).ae_le hσK
  exact PositiveSupportLocalization.mem_support_withDensity_of_pos
    (eigenvectorMeasure σ m) K hmK g hg hgc hxm hxK hgx

theorem subset_support_product (σ : Measure X) (K A : Set X)
    (hσK : ∀ᵐ x ∂σ, x ∈ K) (hAσ : A ⊆ σ.support) (hAK : A ⊆ K)
    (g m : X → ℝ) (hg : Measurable g) (hm : Measurable m)
    (hgc : ContinuousOn g K) (hmc : ContinuousOn m K)
    (hgpos : ∀ x ∈ A, 0 < g x) (hmpos : ∀ x ∈ A, 0 < m x) :
    A ⊆ (eigenvectorMeasure (eigenvectorMeasure σ m) g).support := by
  intro x hx
  exact mem_support_product σ K hσK g m hg hm hgc hmc
    (hAσ hx) (hAK hx) (hgpos x hx) (hmpos x hx)

end LeanShared.EigenvectorDensityPair
