module

public import ConditionedStochasticStabilityHyperbolic.Paper.ProductRegularNoiseConstructor
public import ConditionedStochasticStabilityHyperbolic.Paper.LinearRechartedNoise
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The stabilized noise family in genuine Hilbert product coordinates,
suitable for the actual Fourier/anisotropic model. No points, maps, controls
or laws are changed by this coordinate-model choice. -/

@[expose] public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared

variable {E F X Y ι κ : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace X] [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X]
  [MetricSpace Y] [ChartedSpace F Y] [IsManifold (𝓘(ℝ, F)) ∞ Y]
  [Fintype ι] [Fintype κ]
  {T : X ≃ₜ X} {S : Y ≃ₜ Y} {r : ℝ}

local instance hilbertProductRegularNoiseLocal1 : ChartedSpace (E × F) (X × Y) := productCharts
local instance hilbertProductRegularNoiseLocal2 : IsManifold (𝓘(ℝ, E × F)) ∞ (X × Y) := productManifold

variable
  (P : Maps (E := E) (ι := ι) T r) (Q : Maps (E := F) (ι := κ) S r)
  (hT : FractionalManifoldRegularity.Regular (E := E) (F := E) r T)
  (hS : FractionalManifoldRegularity.Regular (E := F) (F := F) r S)
  (productCalculus : FractionalProductCalculus (E := E) (F := F) (X := X) (Y := Y) r)
  (linearCalculus : LinearFractionalCalculus (T := T.prodCongr S)
    (LinearRechartedManifold.hilbertProductEquiv (A := E) (B := F)) r)

/-- Actual regular perturbations of the product map, with a Hilbert model.
The two calculus inputs are deterministic coordinate identities only. -/
def productHilbertMaps :
    letI := LinearRechartedManifold.productCharts (A := E) (B := F) (X := X) (Y := Y);
      Maps (E := WithLp 2 (E × F)) (ι := ι ⊕ κ) (T.prodCongr S) r := by
  exact Maps.linearRechart (E := E × F) (F := WithLp 2 (E × F))
    (LinearRechartedManifold.hilbertProductEquiv (A := E) (B := F))
    (productMaps P Q hT hS productCalculus) (productCalculus.regular T S hT hS) linearCalculus

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Coordinate changes do not alter the actual stabilized random map. -/
theorem productHilbertMaps_family (ε : ℝ≥0) (a : Control (ι := ι ⊕ κ)) (z : X × Y) :
    letI := LinearRechartedManifold.productCharts (A := E) (B := F) (X := X) (Y := Y);
    (productHilbertMaps P Q hT hS productCalculus linearCalculus).family ε a z =
      (P.family ε (fun i => a (.inl i)) z.1, Q.family ε (fun j => a (.inr j)) z.2) := rfl

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
