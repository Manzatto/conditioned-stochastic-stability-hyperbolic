module

public import LeanShared.Dynamics.BasicHyperbolicProperPressureGap
public import LeanShared.Dynamics.FiniteCodingMatchingImages

/-! The SAME pruned main coding has a single compact invariant higher
matching image of strictly smaller actual base pressure.  Its common
boundary and all coding geometry are produced from the original retained
closed classifier; no pressure-comparison or gap source is assumed. -/

public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle MeasureTheory
open scoped Manifold ContDiff Bundle NNReal BigOperators BoundedContinuousFunction
open ThermodynamicDefinitions BilateralShadowingCoding MarkovFinitePathRealization FiniteClosedRefinement

theorem BasicData.main_matching_image_pressure_gap
    {E M J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [TopologicalSpace J] [Fintype J]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    (mixing : MixingOn T Λ)
    (ψ : M → ℝ) (α : ℝ) (positiveα : 0 < α) (smallα : α < 1)
    (regular : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) α ψ)
    {d : ℕ} (C : Fin d → Set Λ) (closed : ∀ i, IsClosed (C i))
    (rectangles : J → Set Λ) (statuses : J ≃ (Fin d → Bool))
    (law : ∀ j, rectangles j = atom C (statuses j))
    (code : Path (Transition (invariantCoreHomeomorphism T Λ b.hyperbolic.invariant) rectangles) → Λ)
    (properties : MarkovCodingProperties (invariantCoreHomeomorphism T Λ b.hyperbolic.invariant) rectangles code) :
    let S := invariantCoreHomeomorphism T Λ b.hyperbolic.invariant
    let main := reindexedInteriorCode S C rectangles statuses law code
    let K := FiniteCodingManning.higherMatchingImage S (interiorRectangles C) main
    K.Nonempty → pressure S (fun x => ψ x.val) K < pressure T ψ Λ := by
  classical
  let : CompactSpace Λ := isCompact_iff_compactSpace.mp b.hyperbolic.compact
  let : Nonempty Λ := b.nonempty.to_subtype
  let S := invariantCoreHomeomorphism T Λ b.hyperbolic.invariant
  let main := reindexedInteriorCode S C rectangles statuses law code
  have geometry := reindexedInteriorCode_finiteGeometry S C rectangles statuses law closed code properties
  obtain ⟨B, _closedB, emptyInterior, boundary⟩ :=
    reindexedInteriorCode_boundary S C rectangles statuses law code properties
  obtain ⟨_P, _pressureP, _ν, _state, _ergodic, _unique, _support, gaps⟩ :=
    b.exists_full_support_core_equilibrium forward inverse mixing ψ α positiveα smallα regular
  change (FiniteCodingManning.higherMatchingImage S (interiorRectangles C) main).Nonempty →
    pressure S (fun x => ψ x.val) (FiniteCodingManning.higherMatchingImage S (interiorRectangles C) main) < pressure T ψ Λ
  intro nonempty
  exact gaps _ (FiniteCodingManning.higherMatchingImage_compact S (interiorRectangles C) main geometry).isClosed
    nonempty (FiniteCodingManning.higherMatchingImage_invariant S (interiorRectangles C) main geometry)
    (FiniteCodingManning.higherMatchingImage_proper S (interiorRectangles C) main geometry B emptyInterior boundary)

end LeanShared.HyperbolicBasicSet
