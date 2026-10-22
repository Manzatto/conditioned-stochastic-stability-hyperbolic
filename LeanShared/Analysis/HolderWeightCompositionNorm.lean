module
public import LeanShared.Analysis.HolderWeightComposition

/-! An explicit common norm majorant for the actual weighted composition
operators, obtained from the same value/Hölder/Lipschitz constants. -/
public noncomputable section
open scoped BoundedContinuousFunction
namespace LeanShared.HolderWeightComposition
variable {X Y:Type*} [MetricSpace X] [MetricSpace Y]
  {a:ℝ} (ha:0≤a) (ψ:X→ᵇℂ) {Cψ:ℝ} (hCψ:0≤Cψ)
  (holderψ:∀x y,‖ψ x-ψ y‖≤Cψ*dist x y^a)
  {L:NNReal} (g:X→Y) (lip:LipschitzWith L g)

 theorem operator_norm_le :
    ‖operator ha ψ hCψ holderψ g lip‖≤max ‖ψ‖ (‖ψ‖*(L:ℝ)^a+Cψ) :=
  LinearMap.mkContinuous_norm_le _ (le_trans (norm_nonneg ψ) (le_max_left _ _)) _
end LeanShared.HolderWeightComposition
