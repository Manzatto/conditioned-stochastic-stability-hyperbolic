module
public import LeanShared.Dynamics.HyperbolicAdaptedBoundedLinearization
public import LeanShared.Dynamics.HyperbolicAdaptedNonlinearWindow
import Mathlib.Tactic.Linarith

/-! One common nonlinear radius and reference tolerance on the actual
finite adapted atlas, for the original one-step map and chosen norm. -/
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

theorem ChartAtlas.bounded_nonlinear_blocks {system : PatchSystem b} (atlas : ChartAtlas system)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T : M → M))
    (backward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T.symm : M → M)) :
    ∃ K > 0, ∀ δ : ℝ, 0 < δ → ∃ radius > 0, ∃ η > 0, ∀ c ∈ atlas.centers, ∀ d ∈ atlas.centers,
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
        ∀ z, ‖z‖ ≤ radius →
          (chartAt E c.val) x.val + L z ∈ (chartAt E c.val).target ∧
          T ((chartAt E c.val).symm ((chartAt E c.val) x.val + L z)) ∈ (chartAt E d.val).source ∧
          DifferentiableAt ℝ (centered L R ((chartAt E c.val) x.val) ((chartAt E d.val) y.val)
            (chartAt E d.val ∘ T ∘ (chartAt E c.val).symm)) z ∧
          ‖fderiv ℝ (centered L R ((chartAt E c.val) x.val) ((chartAt E d.val) y.val)
            (chartAt E d.val ∘ T ∘ (chartAt E c.val).symm)) z -
              U.toContinuousLinearMap.prodMap S.toContinuousLinearMap‖ ≤ δ := by
  obtain ⟨K, positiveK, linears⟩ := atlas.bounded_linearization_window forward backward
  refine ⟨K, positiveK, fun δ positiveδ => ?_⟩
  obtain ⟨radius, positiveRadius, η₀, positiveη₀, nonlinear⟩ :=
    atlas.nonlinear_window forward (δ / 2) (half_pos positiveδ)
  obtain ⟨η₁, positiveη₁, linear⟩ := linears (δ / 2) (half_pos positiveδ)
  refine ⟨radius, positiveRadius, min η₀ η₁, lt_min positiveη₀ positiveη₁, ?_⟩
  intro c hc d hd x hx y hy near
  obtain ⟨S, U, boundS, boundU, prototype, inversePrototype, origin⟩ := linear c hc d hd x hx y hy
    (near.trans_le (min_le_right _ _))
  dsimp only
  refine ⟨S, U, boundS, boundU, prototype, inversePrototype, ?_⟩
  intro z small
  have data :=  nonlinear c hc d hd x hx y hy (near.trans_le (min_le_left _ _)) z small
  refine ⟨data.1, data.2.1, data.2.2.1, ?_⟩
  let f := centered
    (ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
      (system.referenceFrame c ⟨x, atlas.inside c hx⟩))
    (ContinuousCenteredFrameCharts.chartFrame d.val y.val (atlas.inside d hy).2
      (system.referenceFrame d ⟨y, atlas.inside d hy⟩))
    ((chartAt E c.val) x.val) ((chartAt E d.val) y.val)
    (chartAt E d.val ∘ T ∘ (chartAt E c.val).symm)
  have triangle := norm_add_le
    (fderiv ℝ f z - fderiv ℝ f 0)
    (fderiv ℝ f 0 - U.toContinuousLinearMap.prodMap S.toContinuousLinearMap)
  rw [sub_add_sub_cancel] at triangle
  exact triangle.trans ((add_le_add data.2.2.2.le origin).trans_eq (add_halves δ))

end LeanShared.HyperbolicAdaptedPatchSystem
