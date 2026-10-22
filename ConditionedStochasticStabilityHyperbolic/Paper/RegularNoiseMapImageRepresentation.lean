module

public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseMapImage

/-! The already constructed actual-map image supplies the exact representation
record used by the physical model. In particular, the model's parameter space
does not have to be changed to all continuous maps or given a stronger Cʳ
topology. The original varying laws and noise-scale dependence are retained. -/

@[expose] public noncomputable section
open Set
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise.MapImage

variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [CompactSpace M]
  [ChartedSpace E M] [Fintype ι]
  {T : M ≃ₜ M} {r : ℝ}

/-- All representation fields are derived from the literal map assumptions
and the chosen positive cap. This is the parameter space already used by
`ConstructedHolderNoiseImageModel` and `ConstructedHolderCanonicalNoise`. -/
def representation (F : Maps (E := E) (ι := ι) T r) (hr : 1 ≤ r)
    (η : ℝ≥0) (window : η ≤ F.window) (positive : 0 < η) :
    Representation F (Space F hr η window) (maps F hr η window) where
  window := η
  window_positive := positive
  window_le := window
  reference := reference F hr η window
  reference_map := rfl
  represent := noise F hr η window
  actual_map := fun _ _ _ _ => rfl
  constant := F.constant
  constant_nonnegative := F.constant_positive.le
  close := noise_proximity F hr η window
  continuous := noise_continuous F hr η window

omit [FiniteDimensional ℝ E] in
@[simp] theorem representation_window (F : Maps (E := E) (ι := ι) T r) (hr : 1 ≤ r)
    (η : ℝ≥0) (window : η ≤ F.window) (positive : 0 < η) :
    (representation F hr η window positive).window = η := rfl

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise.MapImage
