module

public import LeanShared.Dynamics.CenteredGibbsWeightCover
public import LeanShared.Dynamics.SpecificationGibbsIntersection
public import LeanShared.Dynamics.GibbsCorrelationNormalization

/-! A genuine Gibbs measure with point specification has a fixed positive
intersection constant for arbitrary compact subsets of open sets. Only the
intersection time varies. The constant is independent of the sets and of
the orbit-word lengths constructed by compact expansivity. -/
public noncomputable section
open Set MeasureTheory
open scoped BigOperators BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X]

set_option maxHeartbeats 2400000 in
theorem uniform_open_intersection_of_gibbs (T : X ≃ₜ X) (c : ℝ) (positiveC : 0 < c)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (φ : X →ᵇ ℝ) (ν : Measure X) [IsFiniteMeasure ν]
    (invariant : MeasurePreserving T ν ν) (ε A H P D : ℝ)
    (positive : 0 < ε) (coarse : 9 * ε ≤ c) (positiveA : 0 < A) (positiveH : 0 < H)
    (gap : ℕ) (positiveGap : 0 < gap)
    (tracing : ∀ n m : ℕ, ∀ x y : X, ∃ z : X,
      (∀ j ≤ n, dist (T^[j] z) (T^[j] x) < 3 * ε) ∧
      ∀ j ≤ m, dist (T^[n + gap + j] z) (T^[j] y) < 3 * ε)
    (bowen : ∀ n x y, (∀ j ≤ n, dist (T^[j] x) (T^[j] y) < 3 * ε) →
      |orbitSum T φ (n + 1) x - orbitSum T φ (n + 1) y| ≤ D)
    (lower : ∀ n y, ENNReal.ofReal (A * Real.exp (orbitSum T φ n y - (n : ℝ) * P)) ≤
      ν {x | ∀ j < n, dist (T^[j] x) (T^[j] y) < ε})
    (upper : ∀ n y, ν {x | ∀ j < n, dist (T^[j] x) (T^[j] y) ≤ 9 * ε} ≤
      ENNReal.ofReal (H * Real.exp (orbitSum T φ n y - (n : ℝ) * P))) :
    ∃ C > 0, ∀ K L U V : Set X, IsCompact K → IsCompact L → IsOpen U → IsOpen V →
      K ⊆ U → L ⊆ V → ∃ d : ℕ,
      C * ν.real K * ν.real L ≤ ν.real (U ∩ ((T : X → X)^[d]) ⁻¹' V) := by
  let C := A / H ^ 2 * Real.exp (-(2 * D + (gap - 1 : ℕ) * (‖φ‖ + P)))
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro K L U V compactK compactL openU openV subK subL
  obtain ⟨N, s, first, firstInside, firstWeight⟩ := exists_centered_gibbs_weight_cover
    T c positiveC expansive φ ν invariant ε H P positive coarse positiveH.le upper
    K U compactK openU subK
  obtain ⟨M, t, second, secondInside, secondWeight⟩ := exists_centered_gibbs_weight_cover
    T c positiveC expansive φ ν invariant ε H P positive coarse positiveH.le upper
    L V compactL openV subL
  let W := {x | T^[N] x ∈ U ∧ T^[2 * N + gap + M] x ∈ V}
  have packing := specification_gibbs_intersection T φ ν ε A P D positive positiveA.le
    gap positiveGap tracing bowen lower s t (2 * N) (2 * M) N M U V
    first second firstInside secondInside
  have nonnegativeSum (q : Finset X) (n : ℕ) :
      0 ≤ ∑ x ∈ q, Real.exp (orbitSum T φ n x) :=
    Finset.sum_nonneg (fun _ _ => Real.exp_nonneg _)
  have realPacking := ENNReal.toReal_mono (measure_ne_top ν W) packing
  rw [ENNReal.toReal_ofReal (by
    exact mul_nonneg (mul_nonneg positiveA.le (Real.exp_nonneg _))
      (mul_nonneg (mul_nonneg (Real.exp_nonneg _) (nonnegativeSum s _))
        (nonnegativeSum t _)))] at realPacking
  have total : ((2 * N + gap + 2 * M + 1 : ℕ) : ℝ) =
      ((2 * N + 1 : ℕ) : ℝ) + ((2 * M + 1 : ℕ) : ℝ) + (gap - 1 : ℕ) := by
    have h : 2 * N + gap + 2 * M + 1 = (2 * N + 1) + (2 * M + 1) + (gap - 1) := by omega
    rw [h]
    push_cast
    ring
  rw [total] at realPacking
  have mass := normalized_gluing_lower A H P D ‖φ‖ (gap - 1 : ℕ)
    ((2 * N + 1 : ℕ) : ℝ) ((2 * M + 1 : ℕ) : ℝ)
    (ν.real K) (ν.real L)
    (∑ x ∈ s, Real.exp (orbitSum T φ (2 * N + 1) x))
    (∑ y ∈ t, Real.exp (orbitSum T φ (2 * M + 1) y)) (ν.real W)
    positiveA positiveH (measureReal_nonneg) (measureReal_nonneg) firstWeight secondWeight realPacking
  refine ⟨N + gap + M, ?_⟩
  have eqW : W = ((T : X → X)^[N]) ⁻¹' (U ∩ ((T : X → X)^[N + gap + M]) ⁻¹' V) := by
    ext x
    have time : (T : X → X)^[N + gap + M] (T^[N] x) = T^[2 * N + gap + M] x := by
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    simp only [W, mem_ofPred_eq, mem_preimage, mem_inter_iff, time]
  have same : ν W = ν (U ∩ ((T : X → X)^[N + gap + M]) ⁻¹' V) := by
    rw [eqW]
    exact (invariant.iterate N).measure_preimage
      (openU.measurableSet.inter (openV.measurableSet.preimage (T.continuous.iterate _).measurable)).nullMeasurableSet
  simpa only [C, measureReal_def, same] using mass

end LeanShared.ThermodynamicDefinitions
