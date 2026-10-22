module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseFixedAdaptedPrototypes
public import LeanShared.Dynamics.HyperbolicAdaptedEuclideanCalculus
import Mathlib.Tactic.Linarith

/-! Actual noisy one-step block approximation in the genuine Euclidean
adapted model, with common prototype bounds chosen before the error. -/
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

theorem Maps.fixed_euclidean_prototypes {r : ℝ} (F : Maps (E := E) (ι := ι) T r)
    (regularity : 1 ≤ r) (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T : M → M))
    (backward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T.symm : M → M))
    {system : PatchSystem b} (atlas : ChartAtlas system) :
    ∃ K > 0, ∀ δ : ℝ, 0 < δ → ∃ radius > 0, ∃ η > 0,
      ∃ cutoff : ℝ≥0, 0 < cutoff ∧
      ∀ c ∈ atlas.centers, ∀ d ∈ atlas.centers,
      ∀ x (hx : x ∈ atlas.patch c), ∀ y (hy : y ∈ atlas.patch d),
      dist (T x.val) y.val < η →
      let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
        (system.euclideanReferenceFrame c ⟨x, atlas.inside c hx⟩)
      let R := ContinuousCenteredFrameCharts.chartFrame d.val y.val (atlas.inside d hy).2
        (system.euclideanReferenceFrame d ⟨y, atlas.inside d hy⟩)
      ∃ S : EuclideanSpace ℝ (Fin system.framing.stableDimension) ≃L[ℝ]
          EuclideanSpace ℝ (Fin system.framing.stableDimension),
      ∃ U : EuclideanSpace ℝ (Fin system.framing.unstableDimension) ≃L[ℝ]
          EuclideanSpace ℝ (Fin system.framing.unstableDimension),
        ‖S.toContinuousLinearMap‖ ≤ system.rate ∧ ‖U.symm.toContinuousLinearMap‖ ≤ system.rate ∧
        ‖(system.euclideanDiagonal U S).toContinuousLinearMap‖ ≤ K ∧
        ‖(system.euclideanDiagonal U S).symm.toContinuousLinearMap‖ ≤ K ∧
        ∀ ε : ℝ≥0, 0 < ε → ε ≤ cutoff → ∀ control : cube (ι := ι) ε,
        ∀ z, ‖z‖ ≤ radius →
          let f := centered L R ((chartAt E c.val) x.val) ((chartAt E d.val) y.val)
            (chartAt E d.val ∘ F.family ε control.val ∘ (chartAt E c.val).symm)
          DifferentiableAt ℝ f z ∧
            ‖fderiv ℝ f z - (system.euclideanDiagonal U S).toContinuousLinearMap‖ ≤ δ := by
  obtain ⟨K, positiveK, windows⟩ := F.fixed_adapted_prototypes regularity forward backward atlas
  refine ⟨2 * K, by positivity, fun δ positiveδ => ?_⟩
  obtain ⟨radius, positiveRadius, η, positiveη, cutoff, positiveCutoff, estimates⟩ :=
    windows (δ / 2) (half_pos positiveδ)
  refine ⟨radius, positiveRadius, η, positiveη, cutoff, positiveCutoff, ?_⟩
  intro c hc d hd x hx y hy near
  obtain ⟨S, U, boundS, boundU, prototype, inversePrototype, bounds⟩ :=
    estimates c hc d hd x hx y hy near
  dsimp only
  refine ⟨S, U, boundS, boundU,
    (system.euclideanDiagonal_bounds U S).1.trans (mul_le_mul_of_nonneg_left prototype (by norm_num)),
    (system.euclideanDiagonal_bounds U S).2.trans (mul_le_mul_of_nonneg_left inversePrototype (by norm_num)), ?_⟩
  intro ε hp hw control z small
  have inverseSmall : ‖system.euclideanEquiv.symm z‖ ≤ radius := by
    have estimate := (system.euclideanEquiv.symm.toContinuousLinearMap.le_opNorm z).trans
      (mul_le_mul_of_nonneg_right system.euclideanEquiv_norm.2 (norm_nonneg z))
    have estimate' : ‖system.euclideanEquiv.symm z‖ ≤ ‖z‖ := by
      simpa only [ContinuousLinearEquiv.coe_coe, one_mul] using estimate
    exact estimate'.trans small
  have data := bounds ε hp hw control (system.euclideanEquiv.symm z) inverseSmall
  let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
    (system.referenceFrame c ⟨x, atlas.inside c hx⟩)
  let R := ContinuousCenteredFrameCharts.chartFrame d.val y.val (atlas.inside d hy).2
    (system.referenceFrame d ⟨y, atlas.inside d hy⟩)
  let f := centered L R ((chartAt E c.val) x.val) ((chartAt E d.val) y.val)
    (chartAt E d.val ∘ F.family ε control.val ∘ (chartAt E c.val).symm)
  rw [system.euclidean_chartFrame c ⟨x, atlas.inside c hx⟩,
    system.euclidean_chartFrame d ⟨y, atlas.inside d hy⟩, system.centered_euclidean_eq]
  refine ⟨system.euclideanEquiv.differentiableAt.comp z
    (data.1.comp z system.euclideanEquiv.symm.differentiableAt), ?_⟩
  exact (system.euclidean_derivative_error f U S z).trans
    ((mul_le_mul_of_nonneg_left data.2 (by norm_num)).trans_eq (by ring))

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
