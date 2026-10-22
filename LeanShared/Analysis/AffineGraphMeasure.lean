module
public import LeanShared.Analysis.AffineGraphParameter
import all LeanShared.Analysis.EuclideanGraphLeaf
import all LeanShared.Analysis.GraphLeafNorm
import Mathlib.Analysis.Calculus.FDeriv.Add

/-! The derived fake-leaf measure on a full affine graph equals the actual
pushforward of a constant positive Gram-density parameter measure. -/
public noncomputable section
open Set MeasureTheory
namespace LeanShared.AffineGraphParameter
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Fintype ι] [DecidableEq ι]

theorem measure (U : Submodule ℝ E) (L : U →L[ℝ] Uᗮ) (v : Uᗮ)
    {R : ℝ} (hR : 0 ≤ R)
    (slope : ∀ x ∈ carrier U L v, ∀ y ∈ carrier U L v,
      ‖Uᗮ.starProjection (x-y)‖ ≤ R*‖U.starProjection (x-y)‖)
    (measurable : MeasurableSet (carrier U L v))
    (b : OrthonormalBasis ι ℝ U)
    (openDomain : IsOpen (FakeLeafGraph.parameterDomain U (carrier U L v)))
    (μ : Measure U) :
    (FakeLeafGraph.asGraphLeaf U (carrier U L v) hR slope measurable b openDomain).measure μ =
      (μ.withDensity (fun _ => ENNReal.ofReal (GraphJacobian.density b L))).map (point U L v) := by
  have height := heightExtension U L v hR slope
  have derivative : fderiv ℝ (fun u : U => L u+v)=fun _ => L := by
    funext u
    exact (L.hasFDerivAt.add_const v).fderiv
  change Measure.map (ConeGraphGeometry.graphPoint U
      (FakeLeafGraph.heightExtension U (carrier U L v) hR slope))
    ((μ.restrict (FakeLeafGraph.parameterDomain U (carrier U L v))).withDensity
      ((FakeLeafGraph.parameterDomain U (carrier U L v)).indicator
        (fun u => ENNReal.ofReal (GraphJacobian.density b
          (fderiv ℝ (FakeLeafGraph.heightExtension U (carrier U L v) hR slope) u))))) = _
  rw [height,derivative,parameterDomain,Measure.restrict_univ,Set.indicator_univ]
  congr 1
  funext u
  change (u:E)+(L u+v:E)=((u:E)+(L u:E))+(v:E)
  simp only [add_assoc]
end LeanShared.AffineGraphParameter
