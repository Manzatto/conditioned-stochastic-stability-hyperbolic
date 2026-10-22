module

public import ConditionedStochasticStabilityHyperbolic.Paper.ToralCatMapRegularNoise
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedAuxiliaryPressureZero
public import ConditionedStochasticStabilityHyperbolic.Paper.UniformCubeRegularNoiseLaws

/-! A fully concrete auxiliary mixing Anosov instance at every finite
real regularity r>1. The map, manifold, metric, splitting, mixing,
fractional regularity, finite Whitney noise atlas, noise submersion,
driving laws, equilibrium and zero pressure are all constructed.
No full-HL, periodic-density, thermodynamic or noise source is supplied. -/

@[expose] public noncomputable section
open Set Bundle
open scoped Bundle Manifold ContDiff NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.ToralCatMap

def auxiliary (r : ℝ) (hr : 1 < r) : AuxiliaryAnosov (F := Model) (Y := Torus) (ι := Fin 2) r :=
  AuxiliaryAnosov.of_full_hl_with_proved_thermodynamics LeanShared.ToralCatMap.homeomorph
    (hl r hr) rfl (hl_stable_positive r hr) (hl_unstable_positive r hr)
    (noise r hr) RegularNoise.uniformCubeLaws

theorem auxiliary_map (r : ℝ) (hr : 1 < r) :
    (auxiliary r hr).map = LeanShared.ToralCatMap.homeomorph := rfl

theorem auxiliary_noise_family (r : ℝ) (hr : 1 < r) (ε : ℝ≥0)
    (u : LeanShared.ToralCatMap.Control) (x : Torus) :
    (auxiliary r hr).noise.family ε u x = LeanShared.ToralCatMap.perturbation u x := rfl

theorem auxiliary_pressure (r : ℝ) (hr : 1 < r) : (auxiliary r hr).equilibrium.pressure = 0 :=
  (auxiliary r hr).pressure_zero

end ConditionedStochasticStabilityHyperbolic.Paper.ToralCatMap
