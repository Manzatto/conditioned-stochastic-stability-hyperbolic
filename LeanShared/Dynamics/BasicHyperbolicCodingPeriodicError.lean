module

public import LeanShared.Dynamics.BasicHyperbolicMatchingPressureGap
public import LeanShared.Dynamics.FiniteCodingPressureError

/-! The actual hyperbolic basic data and retained closed classifier
produce a strict exponential error between the SAME primitive main
coding's literal periodic weights and the original core's periodic
weights.  No finite-extension pressure, entropy or correction-gap oracle
is an input. -/

public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle MeasureTheory
open scoped Manifold ContDiff Bundle NNReal BigOperators BoundedContinuousFunction
open ThermodynamicDefinitions BilateralShadowingCoding MarkovFinitePathRealization FiniteClosedRefinement

theorem BasicData.main_periodic_weight_exponential_error
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
    ∃ P : ℝ, pressure T ψ Λ = (P : EReal) ∧ ∃ β D : ℝ,
      0 < β ∧ β < Real.exp P ∧ 0 < D ∧ ∀ n : ℕ, ∀ s : Finset Λ,
        (∀ x, x ∈ s ↔ (S : Λ → Λ)^[n + 1] x = x) →
        |bilateralPeriodicWeightSum ((fun x : Λ => ψ x.val) ∘ main) (n + 1) -
          ∑ x ∈ s, Real.exp (orbitSum S (fun x => ψ x.val) (n + 1) x)| ≤ D * β ^ (n + 1) := by
  classical
  let S := invariantCoreHomeomorphism T Λ b.hyperbolic.invariant
  let : CompactSpace Λ := isCompact_iff_compactSpace.mp b.hyperbolic.compact
  let : Nonempty Λ := b.nonempty.to_subtype
  have forwardS (x : Λ) : (S x).val = T x.val := rfl
  have backwardS (x : Λ) : (S.symm x).val = T.symm x.val := rfl
  let φ : Λ →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun x => ψ x.val, regular.differentiable.continuous.comp continuous_subtype_val⟩
  obtain ⟨c, positiveC, expansive⟩ := b.exists_expansivity_radius forward inverse
  have expansiveS : ∀ x y : Λ, (∀ j : ℕ,
      dist ((S : Λ → Λ)^[j] x) ((S : Λ → Λ)^[j] y) ≤ c ∧
      dist ((S.symm : Λ → Λ)^[j] x) ((S.symm : Λ → Λ)^[j] y) ≤ c) → x = y := by
    intro x y close
    apply Subtype.ext
    apply expansive x.val x.property y.val y.property
    intro j
    have small := close j
    change dist (((S : Λ → Λ)^[j] x).val) (((S : Λ → Λ)^[j] y).val) ≤ c ∧
      dist (((S.symm : Λ → Λ)^[j] x).val) (((S.symm : Λ → Λ)^[j] y).val) ≤ c at small
    simpa only [iterate_coe_restriction S forwardS, iterate_coe_restriction S.symm backwardS] using small
  let main := reindexedInteriorCode S C rectangles statuses law code
  have geometry := reindexedInteriorCode_finiteGeometry S C rectangles statuses law closed code properties
  have gap : (FiniteCodingManning.higherMatchingImage S (interiorRectangles C) main).Nonempty →
      pressure S φ (FiniteCodingManning.higherMatchingImage S (interiorRectangles C) main) < pressure S φ univ := by
    have actual := b.main_matching_image_pressure_gap forward inverse mixing ψ α positiveα smallα regular
      C closed rectangles statuses law code properties
    change (FiniteCodingManning.higherMatchingImage S (interiorRectangles C) main).Nonempty →
      pressure S (fun x => ψ x.val) (FiniteCodingManning.higherMatchingImage S (interiorRectangles C) main) < pressure T ψ Λ at actual
    intro nonempty
    have result := actual nonempty
    rw [← pressure_restriction S forwardS ψ] at result
    exact result
  obtain ⟨P, pressureP, β, D, positiveβ, smallerβ, positiveD, bound⟩ :=
    FiniteCodingManning.periodic_weight_exponential_error S c positiveC expansiveS φ
      (interiorRectangles C) main geometry gap
  refine ⟨P, ?_, β, D, positiveβ, smallerβ, positiveD, bound⟩
  rw [← pressure_restriction S forwardS ψ]
  exact pressureP

end LeanShared.HyperbolicBasicSet
