module

public import LeanShared.Dynamics.HyperbolicBasicSet
public import LeanShared.Dynamics.ThermodynamicDefinitions
public import Mathlib.Analysis.InnerProductSpace.NormDet

/-! The manuscript's thermodynamic potential uses the actual unstable
tangent Jacobian. Equilibrium packages below are precise cited deterministic
results, containing no random/noisy spectral or conditioned conclusion. -/

@[expose] public noncomputable section
open Set MeasureTheory Bundle
open scoped Manifold ContDiff Topology Bundle
namespace LeanShared.HyperbolicBasicSet

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ : Set M}

/-- Intrinsic volume expansion of the actual unstable tangent restriction.
Using its image as codomain works without a choice of tangent frames. -/
def HyperbolicData.unstableJacobian (h : HyperbolicData (E := E) T Λ) (x : M) : ℝ :=
  let A := mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (T : M → M) x
  (A.restrict (show MapsTo A (h.unstable x) ((h.unstable x).map A.toLinearMap) from
    fun v hv => Submodule.mem_map.mpr ⟨v, hv, rfl⟩)).toLinearMap.normDet

def HyperbolicData.potential (h : HyperbolicData (E := E) T Λ) (g : M → ℝ) : M → ℝ :=
  fun x => Real.log (g x) - Real.log (h.unstableJacobian x)

variable [MeasurableSpace M] [BorelSpace M]

/-- Exact deterministic pressure/equilibrium theorem output to be discharged
by Bowen/GL/BT theory. The pressure scalar is tied to separated-set pressure,
and the state to the actual entropy-plus-potential variational equality. -/
structure EquilibriumPackage (h : HyperbolicData (E := E) T Λ) (g : M → ℝ) where
  pressure : ℝ
  pressure_identity : ThermodynamicDefinitions.pressure T (h.potential g) Λ = (pressure : EReal)
  state : ProbabilityMeasure M
  equilibrium : ThermodynamicDefinitions.IsEquilibriumState T (h.potential g) Λ state
  unique : ∀ ν, ThermodynamicDefinitions.IsEquilibriumState T (h.potential g) Λ ν → ν = state

end LeanShared.HyperbolicBasicSet
