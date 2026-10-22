module

public import LeanShared.Analysis.ConeGraphGeometry
public import LeanShared.Analysis.GraphLeafJacobian

/-!
# Intrinsic Euclidean graph measures with Gram density

Graphs live in their actual ambient inner-product space, using an orthogonal
subspace decomposition. The domain can be a proper measurable subset of the
parameter space; derivative bounds are needed only on that domain. The area
formula identifying this parameter measure with induced leaf volume remains
a standard geometric input. No product max-norm is substituted for Euclidean
geometry.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace LeanShared.EuclideanGraphLeaf

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A genuine orthogonal graph leaf, with its Gram density on the domain. -/
def ofDerivativeField (U : Submodule ℝ E) (b : OrthonormalBasis ι ℝ U)
    (g : U → Uᗮ) (hg : Measurable g) (s : Set U) (hs : MeasurableSet s)
    (D : U → U →L[ℝ] Uᗮ) [MeasurableSpace (U →L[ℝ] Uᗮ)] [BorelSpace (U →L[ℝ] Uᗮ)]
    (hD : Measurable D) {L : ℝ} (hbound : ∀ u ∈ s, ‖D u‖ ≤ L) :
    GraphLeafNorm.GraphLeaf U E (GraphJacobian.densityBound (ι := ι) L) where
  domain := s
  measurable_domain := hs
  graph := ConeGraphGeometry.graphPoint U g
  measurable_graph := by
    change Measurable (fun u : U => (u : E) + (g u : E))
    exact continuous_subtype_val.measurable.add (continuous_subtype_val.measurable.comp hg)
  injective_graph := ConeGraphGeometry.graphPoint_injective U g
  parameter_norm_le := ConeGraphGeometry.parameter_norm_le_graphPoint U g
  density := s.indicator (fun u => ENNReal.ofReal (GraphJacobian.density b (D u)))
  measurable_density :=
    (ENNReal.measurable_ofReal.comp
      ((GraphJacobian.continuous_density b).measurable.comp hD)).indicator hs
  density_le := by
    intro u
    by_cases hu : u ∈ s
    · rw [indicator_of_mem hu]
      exact ENNReal.ofReal_le_ofReal (GraphJacobian.density_le b (D u) (hbound u hu))
    · rw [indicator_of_notMem hu]
      exact bot_le

theorem density_on_domain (U : Submodule ℝ E) (b : OrthonormalBasis ι ℝ U)
    (g : U → Uᗮ) (hg : Measurable g) (s : Set U) (hs : MeasurableSet s)
    (D : U → U →L[ℝ] Uᗮ) [MeasurableSpace (U →L[ℝ] Uᗮ)] [BorelSpace (U →L[ℝ] Uᗮ)]
    (hD : Measurable D) {L : ℝ} (hbound : ∀ u ∈ s, ‖D u‖ ≤ L) (u : U) (hu : u ∈ s) :
    (ofDerivativeField U b g hg s hs D hD hbound).density u =
      ENNReal.ofReal (GraphJacobian.density b (D u)) := by
  change s.indicator (fun v => ENNReal.ofReal (GraphJacobian.density b (D v))) u = _
  exact indicator_of_mem hu _

end LeanShared.EuclideanGraphLeaf
