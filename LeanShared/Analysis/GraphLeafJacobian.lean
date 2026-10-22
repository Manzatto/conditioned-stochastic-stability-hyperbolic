module

public import LeanShared.Analysis.GraphJacobian
public import LeanShared.Analysis.GraphLeafNorm

/-!
# Graph leaves with their Gram density

This constructs the parameterized graph measure used by the leaf estimates
from a measurable derivative field and its uniform slope bound. The classical
graph area formula identifying this measure with geometric induced volume is
still a separate background input. The product carries its usual norm; this
construction asserts no product inner-product instance or metric identity.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace LeanShared.GraphLeafJacobian

variable {ι U V : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Tangent vectors in a slope cone give the required operator-norm bound. -/
theorem opNorm_le_of_graph_cone (D : U →L[ℝ] V) {L : ℝ} (hL : 0 ≤ L)
    (hcone : ∀ v, ‖D v‖ ≤ L * ‖v‖) : ‖D‖ ≤ L :=
  D.opNorm_le_bound hL hcone

variable [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
  [MeasurableSpace (U →L[ℝ] V)] [BorelSpace (U →L[ℝ] V)]

/-- A literal graph with the square-root Gram determinant as its density. -/
def ofDerivativeField (b : OrthonormalBasis ι ℝ U)
    (g : U → V) (hg : Measurable g) (s : Set U) (hs : MeasurableSet s)
    (D : U → U →L[ℝ] V) (hD : Measurable D) {L : ℝ}
    (hbound : ∀ u, ‖D u‖ ≤ L) :
    GraphLeafNorm.GraphLeaf U (U × V) (GraphJacobian.densityBound (ι := ι) L) :=
  GraphLeafNorm.GraphLeaf.ofFunction g hg s hs
    (fun u => ENNReal.ofReal (GraphJacobian.density b (D u)))
    (ENNReal.measurable_ofReal.comp ((GraphJacobian.continuous_density b).measurable.comp hD))
    (fun u => ENNReal.ofReal_le_ofReal (GraphJacobian.density_le b (D u) (hbound u)))

omit [BorelSpace U] [BorelSpace V] in
theorem ofDerivativeField_density (b : OrthonormalBasis ι ℝ U)
    (g : U → V) (hg : Measurable g) (s : Set U) (hs : MeasurableSet s)
    (D : U → U →L[ℝ] V) (hD : Measurable D) {L : ℝ}
    (hbound : ∀ u, ‖D u‖ ≤ L) (u : U) :
    (ofDerivativeField b g hg s hs D hD hbound).density u =
      ENNReal.ofReal (GraphJacobian.density b (D u)) := rfl

end LeanShared.GraphLeafJacobian
