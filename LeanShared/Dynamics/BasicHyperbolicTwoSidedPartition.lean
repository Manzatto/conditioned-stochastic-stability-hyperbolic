module
public import LeanShared.Dynamics.BasicHyperbolicRegularWeightedGluing
public import LeanShared.Dynamics.HyperbolicExpansivity
public import LeanShared.Dynamics.InvariantCoreHomeomorphism
public import LeanShared.Dynamics.PressureInvariantSubtype
public import LeanShared.Dynamics.PointSpecificationPartitionBounds

/-! Actual mixing hyperbolic basic data and actual fractional potential
regularity construct TWO-SIDED uniform separated-partition normalization at the
literal ambient pressure. No expansivity, specification, Bowen, pressure,
Gibbs or partition-growth source is assumed. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle NNReal BigOperators BoundedContinuousFunction
open FiniteOrbitWordAssembly ThermodynamicDefinitions

set_option maxHeartbeats 3200000 in
theorem BasicData.two_sided_partition_normalization
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    (mixing : MixingOn T Λ)
    (ψ : M → ℝ) (α : ℝ) (positiveα : 0 < α) (smallα : α < 1)
    (regular : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) α ψ) :
    ∃ ρ > 0, ∃ P : ℝ, pressure T ψ Λ = (P : EReal) ∧ ∃ A > 0, ∃ B > 0,
      ∀ n : ℕ, 0 < n →
        A * Real.exp ((n : ℝ) * P) ≤ (separatedPartitionSum T ψ Λ n ρ).toReal ∧
        (separatedPartitionSum T ψ Λ n ρ).toReal ≤ B * Real.exp ((n : ℝ) * P) := by
  classical
  let S := invariantCoreHomeomorphism T Λ b.hyperbolic.invariant
  let : CompactSpace Λ := isCompact_iff_compactSpace.mp b.hyperbolic.compact
  let : Nonempty Λ := b.nonempty.to_subtype
  let : MeasurableSpace Λ := borel Λ
  let : BorelSpace Λ := ⟨rfl⟩
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
  obtain ⟨η, positiveη, D, _, distortion⟩ :=
    b.bowen_distortion forward inverse ψ α positiveα smallα regular
  let ε := min (η / 4) (c / 12)
  have positiveε : 0 < ε := lt_min (by positivity) (by positivity)
  have upperη : ε ≤ η / 4 := min_le_left _ _
  have upperC : ε ≤ c / 12 := min_le_right _ _
  have bowen : ∀ n x y, (∀ j < n, dist (S^[j] x) (S^[j] y) < 3 * ε) →
      |orbitSum S φ n x - orbitSum S φ n y| ≤ D := by
    intro n x y close
    change |orbitSum S (fun z : Λ => ψ z.val) n x - orbitSum S (fun z : Λ => ψ z.val) n y| ≤ D
    rw [orbitSum_restriction S forwardS, orbitSum_restriction S forwardS]
    apply distortion n x.val x.property y.val y.property
    intro j hj
    have near := close j hj
    change dist ((S^[j] x).val) ((S^[j] y).val) < 3 * ε at near
    rw [iterate_coe_restriction S forwardS, iterate_coe_restriction S forwardS] at near
    exact near.trans (by linarith)
  have specification : ∀ δ > 0, ∃ gap : ℕ, 0 < gap ∧
      ∀ n m : ℕ, ∀ x y : Λ, ∃ z : Λ,
        (∀ j ≤ n, dist (S^[j] z) (S^[j] x) < δ) ∧
        ∀ j ≤ m, dist (S^[n + gap + j] z) (S^[j] y) < δ := by
    intro δ positiveδ
    obtain ⟨gap, positiveGap, trace⟩ := b.finite_specification forward
      (inverse.mdifferentiable one_ne_zero) mixing δ positiveδ
    refine ⟨gap, positiveGap, fun n m x y => ?_⟩
    let length := fun i : ℕ => if i = 0 then n else m
    let points := fun i : ℕ => if i = 0 then x else y
    obtain ⟨z, close⟩ := trace length points 1
    refine ⟨z, ?_, ?_⟩
    · intro j hj
      have near := close 0 (by omega) j (show j ≤ length 0 by simpa only [length, ite_eq_left rfl] using hj)
      change dist ((S^[j] z).val) ((S^[j] x).val) < δ
      rw [iterate_coe_restriction S forwardS, iterate_coe_restriction S forwardS]
      simpa only [offset, Finset.range_zero, Finset.sum_empty, zero_add, points, ite_eq_left rfl] using near
    · intro j hj
      have near := close 1 (by omega) j (show j ≤ length 1 by simpa only [length, ite_eq_right Nat.one_ne_zero] using hj)
      change dist ((S^[n + gap + j] z).val) ((S^[j] y).val) < δ
      rw [iterate_coe_restriction S forwardS, iterate_coe_restriction S forwardS]
      simpa [offset, length, points] using near
  obtain ⟨P, pressureP, A, positiveA, B, positiveB, normalization⟩ := partition_bounds_of_point_specification
    S c positiveC expansiveS φ ε D positiveε (by linarith) bowen specification
  refine ⟨3 * ε, by positivity, P, ?_, A, positiveA, B, positiveB, fun n hn => ?_⟩
  · rw [← pressure_restriction S forwardS ψ]
    exact pressureP
  · have bound := normalization n hn
    change A * Real.exp ((n : ℝ) * P) ≤
      (separatedPartitionSum S (fun z : Λ => ψ z.val) univ n (3 * ε)).toReal ∧
      (separatedPartitionSum S (fun z : Λ => ψ z.val) univ n (3 * ε)).toReal ≤
        B * Real.exp ((n : ℝ) * P) at bound
    simpa only [separatedPartitionSum_restriction S forwardS ψ] using bound

end LeanShared.HyperbolicBasicSet
