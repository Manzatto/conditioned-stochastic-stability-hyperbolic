module
public import LeanShared.Dynamics.BasicHyperbolicWeightedPartitionIntegral
public import LeanShared.Dynamics.BasicHyperbolicRegularPotentialRepresentative
public import LeanShared.Dynamics.BasicHyperbolicTwoSidedPartition
public import LeanShared.Dynamics.CoboundaryPartitionBounds
import Mathlib.Tactic.Ring

/-! Actual smooth-reference positive matrix coefficients have pressure-rate
lower growth. The supplied continuous metric is retained; its reference-metric
coboundary is constructed and has only a fixed endpoint cost. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff Bundle ENNReal BigOperators
open ThermodynamicDefinitions FractionalManifoldRegularity

set_option maxHeartbeats 3200000 in
theorem BasicData.exists_weighted_integral_growth
    {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    {r q : ℝ} (regularity : 1 < r) (weightOrder : 0 < q)
    (forwardRegular : Regular (E := E) (F := E) r T)
    (inverseRegular : Regular (E := E) (F := E) r T.symm)
    (mixing : MixingOn T Λ)
    (referenceMeasure : FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (μ : Measure E) [IsAddHaarMeasure μ]
    (g : M → ℝ) (weightRegular : Regular (E := E) (F := ℝ) q g)
    (positive : ∀ x ∈ Λ, 0 < g x) (γ : ℝ) (hγ : 1 < γ) :
    ∃ N : ℕ, 0 < N ∧ ∃ P : ℝ, pressure T (b.hyperbolic.potential g) Λ = (P : EReal) ∧
      ∀ ξ : ℝ, 0 < ξ → ∃ C : ℝ≥0∞, C ≠ (∞ : ℝ≥0∞) ∧ ∃ v : ℝ, 0 < v ∧
        ∀ p : ℕ, 0 < p →
          ENNReal.ofReal (v * Real.exp ((N * p : ℕ) * (P - ξ))) ≤
            C * ENNReal.ofReal (γ ^ p) *
              ∫⁻ y, ENNReal.ofReal (∏ j ∈ Finset.range (N * p), g ((T : M → M)^[j] y))
                ∂(referenceMeasure.measure μ) := by
  have oneFloor : (1 : ℕ) ≤ ⌊r⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using regularity.le)
  have forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T :=
    forwardRegular.differentiable.of_le (by exact_mod_cast oneFloor)
  have inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm :=
    inverseRegular.differentiable.of_le (by exact_mod_cast oneFloor)
  obtain ⟨α, positiveα, smallα, ψ, regularψ, u, continuousU, same⟩ :=
    b.exists_regular_potential_representative regularity weightOrder forwardRegular inverseRegular g weightRegular positive
  obtain ⟨ρ, positiveρ, P, pressureP, A, positiveA, B, _, normalization⟩ :=
    b.two_sided_partition_normalization forward inverse mixing ψ α positiveα smallα regularψ
  obtain ⟨D, _, boundD⟩ := (b.hyperbolic.compact.image continuousU).isBounded.exists_pos_norm_le
  have bounded (x : M) (hx : x ∈ Λ) : |u x| ≤ D := by
    simpa only [Real.norm_eq_abs] using boundD (u x) (mem_image_of_mem u hx)
  have invariant : MapsTo (T : M → M) Λ Λ := image_subset_iff.mp b.hyperbolic.invariant.subset
  have pressureEq := pressure_coboundary invariant D bounded same
  obtain ⟨N, positiveN, integral⟩ := b.exists_weighted_partition_integral_lower forward inverse referenceMeasure μ
    g weightRegular.differentiable.continuous positive γ hγ
  refine ⟨N, positiveN, P, pressureEq.trans pressureP, fun ξ positiveξ => ?_⟩
  obtain ⟨C, finiteC, v, positiveV, estimate⟩ := integral ξ positiveξ ρ positiveρ
  refine ⟨ENNReal.ofReal (Real.exp (2 * D)) * C,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top finiteC, v * A, mul_pos positiveV positiveA, fun p hp => ?_⟩
  let n := N * p
  have positiveN' : 0 < n := Nat.mul_pos positiveN hp
  have lower := ENNReal.ofReal_le_ofReal (normalization n positiveN').1
  have lower' := lower.trans ENNReal.ofReal_toReal_le
  have comparison := separatedPartitionSum_coboundary_lower invariant D bounded same n ρ
  have scaled := mul_le_mul' (le_refl (ENNReal.ofReal v * ENNReal.ofReal (Real.exp (-ξ * n))))
    (lower'.trans comparison)
  have next := mul_le_mul' (le_refl (ENNReal.ofReal (Real.exp (2 * D)))) (estimate p hp)
  have combine := scaled.trans (by simpa only [n, Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm] using next)
  have identity : (v * A) * Real.exp ((n : ℝ) * (P - ξ)) =
      v * Real.exp (-ξ * n) * (A * Real.exp ((n : ℝ) * P)) := by
    rw [show (n : ℝ) * (P - ξ) = -ξ * n + n * P by ring, Real.exp_add]
    ring
  rw [identity, ENNReal.ofReal_mul (mul_nonneg positiveV.le (Real.exp_pos _).le),
    ENNReal.ofReal_mul positiveV.le]
  simpa only [mul_assoc, mul_comm, mul_left_comm] using combine

end LeanShared.HyperbolicBasicSet
