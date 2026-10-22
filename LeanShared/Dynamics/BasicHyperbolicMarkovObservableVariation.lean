module

public import LeanShared.Dynamics.BasicHyperbolicMarkovCoordinateDecay
public import LeanShared.Geometry.CoherentFractionalObservableFrameBound
public import LeanShared.Analysis.UniformGeometricTailBound
public import Mathlib.Analysis.SpecificLimits.Normed

/-! Fractional regular observables acquire exponential symbolic cylinder
variations under the actual finite-to-one Markov coding.  Actual
coordinate contraction supplies the decay; the finite initial scales
are controlled by compact boundedness.  This applies to the proved
regular representative of the literal weighted potential.
-/

public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle Function ThermodynamicDefinitions Filter
open BilateralShadowingCoding ExpansiveLocalProduct FiniteClosedRefinement MarkovFinitePathRealization
open CoherentCenteredCoordinateMaps
open scoped Topology Manifold ContDiff BoundedContinuousFunction

theorem BasicData.exists_markov_observable_variation
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (ψ : M → ℝ) (α : ℝ) (positiveα : 0 < α) (smallα : α < 1)
    (regular : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) α ψ) :
    let S := invariantCoreHomeomorphism T Λ b.hyperbolic.invariant
    ∃ N : ℕ, ∃ rectangles : ((Fin N ⊕ ((Fin N × Fin N) × Bool)) → Bool) → Set Λ,
      ∃ code : Path (Transition S rectangles) → Λ,
        MarkovCodingProperties S rectangles code ∧
        ∃ block : ℕ, 0 < block ∧ ∃ θ > 0, θ < 1 ∧ ∃ C ≥ 0,
          ∀ n : ℕ, ∀ a a' : Path (Transition S rectangles),
            (∀ k : ℤ, -((block * n : ℕ) : ℤ) ≤ k → k ≤ (block * n : ℕ) → a.val k = a'.val k) →
            |ψ (code a').val - ψ (code a).val| ≤ C * θ ^ n := by
  let S := invariantCoreHomeomorphism T Λ b.hyperbolic.invariant
  obtain ⟨frame, block, positiveBlock, B, d, N, rectangles, code,
    properties, coordinateDecay⟩ :=
    b.exists_markov_coordinate_decay forward inverse
  obtain ⟨r, positiveR, L, nonnegativeL, increment⟩ :=
    exists_holder_increment_of_frame_bound d frame.whole 2 (by norm_num)
      (fun x => (frame.whole_bounds x).1) ψ α positiveα smallα regular
  let q : ℝ := 3 / 8
  let θ := q ^ α
  have positiveQ : 0 < q := by norm_num [q]
  have smallQ : q < 1 := by norm_num [q]
  have positiveθ : 0 < θ := Real.rpow_pos_of_pos positiveQ _
  have smallθ : θ < 1 := Real.rpow_lt_one positiveQ.le smallQ positiveα
  have powered (n : ℕ) : (q ^ n) ^ α = θ ^ n := by
    dsimp only [θ]
    rw [← Real.rpow_natCast_mul positiveQ.le, mul_comm,
      Real.rpow_mul positiveQ.le, Real.rpow_natCast]
  have tends : Tendsto (fun n : ℕ => q ^ n * (2 * d.radius)) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one positiveQ.le smallQ).mul_const (2 * d.radius)
  have eventuallySmall : ∀ᶠ n : ℕ in atTop, q ^ n * (2 * d.radius) < r :=
    tends.eventually (gt_mem_nhds positiveR)
  obtain ⟨threshold, afterThreshold⟩ := eventually_atTop.mp eventuallySmall
  let agreement := fun n (a a' : Path (Transition S rectangles)) =>
    ∀ k : ℤ, -((block * n : ℕ) : ℤ) ≤ k → k ≤ (block * n : ℕ) → a.val k = a'.val k
  let observable := fun a : Path (Transition S rectangles) => ψ (code a).val
  let boundedψ : M →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨ψ, regular.differentiable.continuous⟩
  have bounded (a : Path (Transition S rectangles)) : ‖observable a‖ ≤ ‖boundedψ‖ :=
    boundedψ.norm_coe_le_norm (code a).val
  have nonnegativeRadius : 0 ≤ 2 * d.radius := mul_nonneg (by norm_num) d.positive.le
  have tail (n : ℕ) (large : threshold ≤ n) (a a' : Path (Transition S rectangles))
      (matching : agreement n a a') :
      ‖observable a' - observable a‖ ≤ (L * (2 * d.radius) ^ α) * θ ^ n := by
    have facts := coordinateDecay n a a' matching
    have smallCoordinate : ‖coordinate d frame.whole (code a) (code a').val‖ ≤ r :=
      facts.2.trans (afterThreshold n large).le
    have estimate := increment (code a) (coordinate d frame.whole (code a) (code a').val) smallCoordinate
    rw [decode_coordinate d frame.whole (code a) (code a').val facts.1] at estimate
    calc
      _ ≤ L * ‖coordinate d frame.whole (code a) (code a').val‖ ^ α := estimate
      _ ≤ L * (q ^ n * (2 * d.radius)) ^ α :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) facts.2 positiveα.le) nonnegativeL
      _ = (L * (2 * d.radius) ^ α) * θ ^ n := by
        rw [Real.mul_rpow (pow_nonneg positiveQ.le _) nonnegativeRadius, powered]
        ring
  obtain ⟨C, nonnegativeC, uniform⟩ := UniformGeometricTailBound.exists_bound observable agreement ‖boundedψ‖
    (L * (2 * d.radius) ^ α) θ (norm_nonneg _)
    (mul_nonneg nonnegativeL (Real.rpow_nonneg nonnegativeRadius _)) positiveθ smallθ.le bounded threshold tail
  refine ⟨N, rectangles, code, properties,
    block, positiveBlock, θ, positiveθ, smallθ, C, nonnegativeC, ?_⟩
  intro n a a' matching
  simpa only [observable, Real.norm_eq_abs] using uniform n a a' matching

end LeanShared.HyperbolicBasicSet
