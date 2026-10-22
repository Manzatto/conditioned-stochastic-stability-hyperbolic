module
public import ConditionedStochasticStabilityHyperbolic.Paper.HilbertProductHL
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
public import LeanShared.Dynamics.HyperbolicThermodynamics

/-! Ordinary full-manifold auxiliary data for saddle stabilization. This
record contains no original or auxiliary noisy gap, eigenfunction, spectral
projector or conditioned conclusion. A fixed smooth mixing Anosov map may
supply it at every finite regularity; periodic density and pressure zero are
precisely the ordinary Anosov and geometric-potential theorems. -/
@[expose] public noncomputable section
open Set Function Bundle MeasureTheory
open scoped Manifold ContDiff Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper
open LeanShared HyperbolicBasicSet
variable {F Y ι : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace Y] [ChartedSpace F Y] [IsManifold (𝓘(ℝ, F)) ∞ Y]
  [RiemannianBundle (fun y : Y => TangentSpace (𝓘(ℝ, F)) y)]
  [MeasurableSpace Y] [BorelSpace Y] [Fintype ι]

/-- Everything here precedes the analytic construction of noisy spectral
sources. The weight and both auxiliary core/collar are fixed literally. -/
structure AuxiliaryAnosov (r : ℝ) where
  map : Y ≃ₜ Y
  hl : HL (E := F) map (fun _ => 1) univ univ
  regularity : hl.r = r
  stable_positive : ∀ y, 0 < Module.finrank ℝ (hl.basic.hyperbolic.stable y)
  unstable_positive : ∀ y, 0 < Module.finrank ℝ (hl.basic.hyperbolic.unstable y)
  periodic_dense : closure (periodicPts (map : Y → Y)) = univ
  equilibrium : EquilibriumPackage hl.basic.hyperbolic (fun _ => 1)
  pressure_zero : equilibrium.pressure = 0
  noise : RegularNoise.Maps (E := F) (ι := ι) map r
  laws : RegularNoise.Laws (ι := ι)

omit [BorelSpace Y]
namespace AuxiliaryAnosov
variable {r : ℝ} (a : AuxiliaryAnosov (F := F) (Y := Y) (ι := ι) r)
include a

theorem nonempty : Nonempty Y := a.hl.nonempty_core.to_subtype.map Subtype.val

theorem compact : IsCompact (univ : Set Y) := a.hl.compact_core

theorem pressure_identity : ThermodynamicDefinitions.pressure a.map
    (a.hl.basic.hyperbolic.potential (fun _ => 1)) univ = (0 : EReal) := by
  rw [a.equilibrium.pressure_identity, a.pressure_zero]
  rfl

end AuxiliaryAnosov
end ConditionedStochasticStabilityHyperbolic.Paper
