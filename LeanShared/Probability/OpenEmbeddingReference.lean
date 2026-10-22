module

public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Reference support and exact integrals after passing to an open embedded
live region. Positivity is required only at image points. -/

@[expose] public noncomputable section
open Set MeasureTheory
namespace LeanShared.OpenEmbeddingReference
variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  {f : X → Y}

theorem support_comap (μ : Measure Y) (hf : Topology.IsOpenEmbedding f)
    (positive : ∀ x : X, f x ∈ μ.support) :
    ∀ x : X, x ∈ (μ.comap f).support := by
  intro x
  rw [Measure.support_eq_forall_isOpen]
  intro O hxO hO
  rw [hf.measurableEmbedding.comap_apply]
  have hp := positive x
  rw [Measure.support_eq_forall_isOpen] at hp
  exact hp (f '' O) ⟨x, hxO, rfl⟩ (hf.isOpenMap O hO)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [TopologicalSpace X] [BorelSpace X] [TopologicalSpace Y] [BorelSpace Y] in
theorem integral_comap (μ : Measure Y) (hf : MeasurableEmbedding f) (g : Y → F) :
    (∫ x, g (f x) ∂μ.comap f) = ∫ y in range f, g y ∂μ := by
  rw [← hf.integral_map, hf.map_comap]

end LeanShared.OpenEmbeddingReference
