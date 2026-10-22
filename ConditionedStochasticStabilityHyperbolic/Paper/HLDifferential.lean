module

public import ConditionedStochasticStabilityHyperbolic.Paper.Hypotheses
public import LeanShared.Geometry.DiffeomorphismDifferential
public import LeanShared.Dynamics.HyperbolicThermodynamics

/-! HL supplies the actual invertible tangent differential used in the
intrinsic principal coefficient, without an arbitrary cocycle input. -/

@[expose] public noncomputable section
open Set Bundle
open scoped Manifold ContDiff Bundle
namespace ConditionedStochasticStabilityHyperbolic.Paper.HL
open LeanShared
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {g : M → ℝ} {Λ V : Set M} (h : HL (E := E) T g Λ V)

def differential (x : M) :
    TangentSpace (𝓘(ℝ, E)) x ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) (T x) :=
  DiffeomorphismDifferential.differential T
    (h.map_regular.mdifferentiable h.regularity_gt_one.le)
    (h.inverse_regular.mdifferentiable h.regularity_gt_one.le) x

omit [FiniteDimensional ℝ E] in
@[simp] theorem differential_apply (x : M) (v : TangentSpace (𝓘(ℝ, E)) x) :
    h.differential x v = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x v := rfl

/-- The genuine unstable tangent volume factor is positive, including the
zero-dimensional endpoint. No chosen global frame is needed. -/
theorem unstableJacobian_pos (x : M) : 0 < h.basic.hyperbolic.unstableJacobian x := by
  let A := mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (T : M → M) x
  let U := h.basic.hyperbolic.unstable x
  let B := A.restrict (show MapsTo A U (U.map A.toLinearMap) from
    fun v hv => Submodule.mem_map.mpr ⟨v, hv, rfl⟩)
  have hinj : Function.Injective B.toLinearMap := by
    intro u v huv
    apply Subtype.ext
    apply (h.differential x).injective
    exact congrArg Subtype.val huv
  have hne := (B.toLinearMap.normDet_ne_zero_tfae.out 5 1).mp hinj
  exact lt_of_le_of_ne (LinearMap.normDet_nonneg _) (Ne.symm hne)

end ConditionedStochasticStabilityHyperbolic.Paper.HL
