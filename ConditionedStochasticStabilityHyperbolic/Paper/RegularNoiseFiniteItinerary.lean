module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseChartItinerary
public import LeanShared.Analysis.FiniteCoordinateItinerary

/-! Actual Whitney perturbations composed along a finite chart itinerary.
The valid deterministic initial domain is computed from that itinerary; no
iterated-noise or invariant-neighborhood certificate is assumed. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set Filter IsManifold
open scoped Topology Manifold ContDiff NNReal
open LeanShared.FiniteJetComposition

theorem Maps.finite_itinerary_jetConvergesOn
    {E M ι A : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (ε : A → ℝ≥0) (controls : ℕ → ∀ a, cube (ι := ι) (ε a)) (l : Filter A)
    (limit : Tendsto ε l (𝓝 0)) (positive : ∀ᶠ a in l, 0 < ε a)
    (chart : ℕ → Fin F.atlas.count) (N : ℕ) :
    let noisy := fun n a => F.atlas.stepCoordinate (F.family (ε a) (controls n a).val)
      (chart n) (chart (n + 1))
    let reference := fun n => F.atlas.stepCoordinate T (chart n) (chart (n + 1))
    let domains := fun n => F.atlas.stepDomain (chart n) (chart (n + 1))
    JetConvergesOn (fun a => word (fun n => noisy n a) N) (word reference N) l
      (prefixDomain reference domains N) := by
  exact JetConvergesOn.finite_coordinate_itinerary _ _ l _ N (fun n _ =>
    F.itinerary_jetConvergesOn regularity deterministic ε (controls n) l limit positive
      (chart n) (chart (n + 1)))

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
