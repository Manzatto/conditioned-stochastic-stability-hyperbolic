module
public import LeanShared.Analysis.GraphLeafNorm
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! Orthogonal reparametrization gives a common parameter space for chart
leaves with different reference planes. The actual ambient measure is unchanged. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace LeanShared.GraphLeafNorm.GraphLeaf
variable {P U E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup E]
  [MeasurableSpace P] [BorelSpace P] [MeasurableSpace U] [BorelSpace U]
  [MeasurableSpace E] {J : ℝ}

def reparam (leaf : GraphLeaf U E J) (e : P ≃ₗᵢ[ℝ] U) : GraphLeaf P E J where
  domain := e ⁻¹' leaf.domain
  measurable_domain := e.continuous.measurable leaf.measurable_domain
  graph := leaf.graph ∘ e
  measurable_graph := leaf.measurable_graph.comp e.continuous.measurable
  injective_graph := leaf.injective_graph.comp e.injective
  parameter_norm_le := fun x => (e.norm_map x).symm.trans_le (leaf.parameter_norm_le (e x))
  density := leaf.density ∘ e
  measurable_density := leaf.measurable_density.comp e.continuous.measurable
  density_le := fun x => leaf.density_le (e x)

theorem reparam_sourceMeasure_map (leaf : GraphLeaf U E J) (e : P ≃ₗᵢ[ℝ] U)
    (μ : Measure P) :
    ((leaf.reparam e).sourceMeasure μ).map e = leaf.sourceMeasure (μ.map e) := by
  unfold sourceMeasure
  rw [Measure.restrict_map e.continuous.measurable leaf.measurable_domain]
  ext s hs
  rw [Measure.map_apply e.continuous.measurable hs,
    withDensity_apply _ (e.continuous.measurable hs),
    withDensity_apply _ hs]
  exact (setLIntegral_map hs leaf.measurable_density e.continuous.measurable).symm

theorem reparam_measure (leaf : GraphLeaf U E J) (e : P ≃ₗᵢ[ℝ] U)
    (μ : Measure P) :
    (leaf.reparam e).measure μ = leaf.measure (μ.map e) := by
  change (((leaf.reparam e).sourceMeasure μ).map (leaf.graph ∘ e)) = _
  rw [← Measure.map_map leaf.measurable_graph e.continuous.measurable,
    reparam_sourceMeasure_map]
  rfl

theorem reparam_image (leaf : GraphLeaf U E J) (e : P ≃ₗᵢ[ℝ] U) :
    (leaf.reparam e).graph '' (leaf.reparam e).domain = leaf.graph '' leaf.domain := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨e x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨e.symm x, ?_, ?_⟩
    · change e (e.symm x) ∈ leaf.domain
      simpa only [e.apply_symm_apply] using hx
    · change leaf.graph (e (e.symm x)) = leaf.graph x
      rw [e.apply_symm_apply]

end LeanShared.GraphLeafNorm.GraphLeaf
