module
public import LeanShared.Dynamics.HyperbolicAdaptedNearbyBlocks
public import LeanShared.Dynamics.HyperbolicAdaptedPrototypeBounds
public import LeanShared.Dynamics.HyperbolicAdaptedDerivativeBound
public import LeanShared.Analysis.CenteredRelativeDerivativeError
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! Actual one-step linearization on the fixed adapted atlas: arbitrary
nearby target references have uniformly small error from contracting
diagonal blocks, in the same chosen adapted norm. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff
namespace LeanShared.HyperbolicAdaptedPatchSystem
open HyperbolicBasicSet CenteredManifoldCoordinates
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}

theorem ChartAtlas.bounded_linearization_window {system : PatchSystem b} (atlas : ChartAtlas system)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T : M → M))
    (backward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T.symm : M → M)) :
    ∃ K > 0, ∀ δ : ℝ, 0 < δ → ∃ η > 0, ∀ c ∈ atlas.centers, ∀ d ∈ atlas.centers,
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
        ‖fderiv ℝ (centered L R ((chartAt E c.val) x.val) ((chartAt E d.val) y.val)
          (chartAt E d.val ∘ T ∘ (chartAt E c.val).symm)) 0 -
            U.toContinuousLinearMap.prodMap S.toContinuousLinearMap‖ ≤ δ := by
  obtain ⟨K, positiveK, prototype⟩ := system.prototype_bounds forward backward
  refine ⟨K, positiveK, fun δ positiveδ => ?_⟩
  obtain ⟨B, positiveB, η₀, positiveη₀, bound⟩ := atlas.derivative_bound forward
  let θ := min (1 / 4) (δ / (4 * (B + 1)))
  have positiveθ : 0 < θ := lt_min (by norm_num) (div_pos positiveδ (by positivity))
  have halfθ : θ ≤ 1 / 2 := (min_le_left _ _).trans (by norm_num)
  have smallθ : θ < 1 := by linarith
  have nonnegativeRatio : 0 ≤ θ / (1 - θ) := div_nonneg positiveθ.le (by linarith)
  have ratio : θ / (1 - θ) ≤ 2 * θ :=
    (div_le_iff₀ (sub_pos.mpr smallθ)).mpr (by nlinarith)
  have budget : 2 * θ * B ≤ δ := by
    have upper := (le_div_iff₀ (show 0 < 4 * (B + 1) by positivity)).mp
      (min_le_right (1 / 4) (δ / (4 * (B + 1))))
    change θ * (4 * (B + 1)) ≤ δ at upper
    nlinarith [mul_pos positiveθ positiveB]
  obtain ⟨η₁, positiveη₁, blocks⟩ := atlas.near_image_blocks forward backward θ positiveθ
  refine ⟨min η₀ η₁, lt_min positiveη₀ positiveη₁, ?_⟩
  intro c hc d hd x hx y hy near
  obtain ⟨ht, S, U, boundS, boundU, diagonal, relative⟩ :=
    blocks c hc d hd x hx y hy (near.trans_le (min_le_right _ _))
  let e := system.referenceFrame c ⟨x, atlas.inside c hx⟩
  let f := system.referenceFrame d ⟨forwardPoint b x, ht⟩
  let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2 e
  let R := ContinuousCenteredFrameCharts.chartFrame d.val (T x.val) ht.2 f
  let Q := ContinuousCenteredFrameCharts.chartFrame d.val y.val (atlas.inside d hy).2
    (system.referenceFrame d ⟨y, atlas.inside d hy⟩)
  let raw := chartAt E d.val ∘ T ∘ (chartAt E c.val).symm
  have trueDerivative := ContinuousCenteredFrameCharts.coordinate_hasFDerivAt T x.val c.val d.val
    (atlas.inside c hx).2 ht.2 e f (forward.mdifferentiable one_ne_zero x.val)
  change HasFDerivAt (centered L R ((chartAt E c.val) x.val) ((chartAt E d.val) (T x.val)) raw)
    (f.symm.toContinuousLinearMap.comp
      ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x.val).comp e.toContinuousLinearMap)) 0 at trueDerivative
  have trueAtZero := trueDerivative.fderiv.trans diagonal
  have error := relative_target_derivative_error L R Q ((chartAt E c.val) x.val)
    ((chartAt E d.val) (T x.val)) ((chartAt E d.val) y.val) raw 0 θ smallθ relative.le
  rw [trueAtZero] at error
  have prototypeBounds := prototype c d x (atlas.inside c hx) ht S U diagonal
  refine ⟨S, U, boundS, boundU, prototypeBounds.1, prototypeBounds.2, error.trans ?_⟩
  calc
    _ ≤ (θ / (1 - θ)) * B := mul_le_mul_of_nonneg_left
      (bound c hc d hd x hx y hy (near.trans_le (min_le_left _ _))) nonnegativeRatio
    _ ≤ 2 * θ * B := mul_le_mul_of_nonneg_right ratio positiveB.le
    _ ≤ δ := budget

end LeanShared.HyperbolicAdaptedPatchSystem
