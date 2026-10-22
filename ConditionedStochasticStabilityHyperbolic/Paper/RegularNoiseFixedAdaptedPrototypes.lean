module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedChartWindow
public import LeanShared.Dynamics.HyperbolicAdaptedBoundedNonlinearBlocks
import Mathlib.Tactic.Linarith

/-! Fixed prototype selection precedes EVERY noise scale and control.

 One common spatial radius, reference tolerance and noise window give
actual one-step noisy derivatives uniformly close to the contracting
diagonal blocks, on the same finite adapted atlas and original generator. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared LeanShared.HyperbolicAdaptedPatchSystem LeanShared.HyperbolicBasicSet
open LeanShared.CenteredManifoldCoordinates
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}

theorem Maps.fixed_adapted_prototypes {r : ℝ} (F : Maps (E := E) (ι := ι) T r)
    (regularity : 1 ≤ r) (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T : M → M))
    (backward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T.symm : M → M))
    {system : PatchSystem b} (atlas : ChartAtlas system) :
    ∃ K > 0, ∀ δ : ℝ, 0 < δ → ∃ radius > 0, ∃ η > 0, ∃ cutoff : ℝ≥0, 0 < cutoff ∧
      ∀ c ∈ atlas.centers, ∀ d ∈ atlas.centers,
      ∀ x (hx : x ∈ atlas.patch c), ∀ y (hy : y ∈ atlas.patch d),
      dist (T x.val) y.val < η →
      let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
        (system.referenceFrame c ⟨x, atlas.inside c hx⟩)
      let R := ContinuousCenteredFrameCharts.chartFrame d.val y.val (atlas.inside d hy).2
        (system.referenceFrame d ⟨y, atlas.inside d hy⟩)
      ∃ S : EuclideanSpace ℝ (Fin system.framing.stableDimension) ≃L[ℝ]
          EuclideanSpace ℝ (Fin system.framing.stableDimension),
      ∃ U : EuclideanSpace ℝ (Fin system.framing.unstableDimension) ≃L[ℝ]
          EuclideanSpace ℝ (Fin system.framing.unstableDimension),
        ‖S.toContinuousLinearMap‖ ≤ system.rate ∧ ‖U.symm.toContinuousLinearMap‖ ≤ system.rate ∧
        ‖(U.prodCongr S).toContinuousLinearMap‖ ≤ K ∧
        ‖(U.prodCongr S).symm.toContinuousLinearMap‖ ≤ K ∧
        ∀ ε : ℝ≥0, 0 < ε → ε ≤ cutoff → ∀ control : cube (ι := ι) ε,
        ∀ z, ‖z‖ ≤ radius →
          let f := centered L R ((chartAt E c.val) x.val) ((chartAt E d.val) y.val)
            (chartAt E d.val ∘ F.family ε control.val ∘ (chartAt E c.val).symm)
          DifferentiableAt ℝ f z ∧
            ‖fderiv ℝ f z - U.toContinuousLinearMap.prodMap S.toContinuousLinearMap‖ ≤ δ := by
  obtain ⟨K, positiveK, deterministics⟩ := atlas.bounded_nonlinear_blocks forward backward
  refine ⟨K, positiveK, fun δ positiveδ => ?_⟩
  obtain ⟨radius₀, positiveRadius₀, η₀, positiveη₀, deterministic⟩ :=
    deterministics (δ / 2) (half_pos positiveδ)
  obtain ⟨radius₁, positiveRadius₁, η₁, positiveη₁, cutoff, positiveCutoff, noisy⟩ :=
    F.adapted_chart_noise_window regularity forward atlas (δ / 2) (half_pos positiveδ)
  refine ⟨min radius₀ radius₁, lt_min positiveRadius₀ positiveRadius₁,
    min η₀ η₁, lt_min positiveη₀ positiveη₁, cutoff, positiveCutoff, ?_⟩
  intro c hc d hd x hx y hy near
  obtain ⟨S, U, boundS, boundU, prototype, inversePrototype, deterministicBounds⟩ :=
    deterministic c hc d hd x hx y hy (near.trans_le (min_le_left _ _))
  dsimp only
  refine ⟨S, U, boundS, boundU, prototype, inversePrototype, ?_⟩
  intro ε hp hw control z small
  have noiseBounds := noisy ε hp hw control c hc d hd x hx y hy
    (near.trans_le (min_le_right _ _)) z (small.trans (min_le_right _ _))
  have referenceBounds := deterministicBounds z (small.trans (min_le_left _ _))
  refine ⟨noiseBounds.1, ?_⟩
  let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
    (system.referenceFrame c ⟨x, atlas.inside c hx⟩)
  let R := ContinuousCenteredFrameCharts.chartFrame d.val y.val (atlas.inside d hy).2
    (system.referenceFrame d ⟨y, atlas.inside d hy⟩)
  let f := centered L R ((chartAt E c.val) x.val) ((chartAt E d.val) y.val)
    (chartAt E d.val ∘ F.family ε control.val ∘ (chartAt E c.val).symm)
  let g := centered L R ((chartAt E c.val) x.val) ((chartAt E d.val) y.val)
    (chartAt E d.val ∘ T ∘ (chartAt E c.val).symm)
  have derivativeNoise : ‖fderiv ℝ f z - fderiv ℝ g z‖ ≤ δ / 2 :=
    (le_add_of_nonneg_left (norm_nonneg _)).trans noiseBounds.2
  have triangle := norm_add_le (fderiv ℝ f z - fderiv ℝ g z)
    (fderiv ℝ g z - U.toContinuousLinearMap.prodMap S.toContinuousLinearMap)
  rw [sub_add_sub_cancel] at triangle
  exact triangle.trans ((add_le_add derivativeNoise referenceBounds.2.2.2).trans_eq (add_halves δ))

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
