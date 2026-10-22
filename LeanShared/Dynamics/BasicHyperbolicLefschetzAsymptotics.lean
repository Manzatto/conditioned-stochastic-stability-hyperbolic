module

public import LeanShared.Dynamics.BasicHyperbolicLefschetzPartition
public import LeanShared.Dynamics.HyperbolicPeriodicDenominatorAsymptotics

/-! Exponentially small relative error between the actual periodic
Lefschetz sum and the thermodynamic periodic partition sum.  This is the
coefficient bridge for the dynamical-determinant argument; it follows
from the actual hyperbolic return blocks, with no trace formula assumed.
-/

public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle Filter ThermodynamicDefinitions
open scoped Topology Manifold ContDiff BigOperators
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M}

set_option maxHeartbeats 2200000 in
theorem BasicData.lefschetz_partition_error (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (g : M → ℝ) (positive : ∀ x ∈ Λ, 0 < g x) :
    ∃ C > 0, ∀ᶠ p : ℕ in atTop,
      |b.periodicLefschetzSum forward inverse g p -
        b.periodicPartitionSum forward inverse (b.hyperbolic.potential g) p| ≤
      (C * b.hyperbolic.contraction ^ p) *
        b.periodicPartitionSum forward inverse (b.hyperbolic.potential g) p := by
  obtain ⟨C, positiveC, denominators⟩ := b.hyperbolic.periodic_denominator_ratio_error
    (forward.mdifferentiable one_ne_zero) (inverse.mdifferentiable one_ne_zero)
  have invariant : MapsTo (T : M → M) Λ Λ := image_subset_iff.mp b.hyperbolic.invariant.subset
  refine ⟨C, positiveC, ?_⟩
  filter_upwards [denominators, eventually_gt_atTop 0] with p denominator positiveP
  let s := b.periodicPoints forward inverse p positiveP
  let term (x : s) := (∏ j ∈ Finset.range p, g ((T : M → M)^[j] x.val)) /
    DiffeomorphismDifferential.periodicDenominator T (forward.mdifferentiable one_ne_zero)
      (inverse.mdifferentiable one_ne_zero) p x.val
      ((b.mem_periodicPoints forward inverse p positiveP x.val).mp x.property).2
  have localBound (x : s) :
      |term x - Real.exp (orbitSum T (b.hyperbolic.potential g) p x.val)| ≤
      (C * b.hyperbolic.contraction ^ p) *
        Real.exp (orbitSum T (b.hyperbolic.potential g) p x.val) := by
    obtain ⟨inside, fixed⟩ := (b.mem_periodicPoints forward inverse p positiveP x.val).mp x.property
    let W := ∏ j ∈ Finset.range p, g ((T : M → M)^[j] x.val)
    let J := ∏ j ∈ Finset.range p, b.hyperbolic.unstableJacobian ((T : M → M)^[j] x.val)
    let D := DiffeomorphismDifferential.periodicDenominator T (forward.mdifferentiable one_ne_zero)
      (inverse.mdifferentiable one_ne_zero) p x.val fixed
    have positiveJ : 0 < J := Finset.prod_pos (fun j _ => b.hyperbolic.unstableJacobian_positive
      (forward.mdifferentiable one_ne_zero) (inverse.mdifferentiable one_ne_zero) _ (invariant.iterate j inside))
    have energy := b.hyperbolic.exp_orbit_potential (forward.mdifferentiable one_ne_zero)
      (inverse.mdifferentiable one_ne_zero) g positive p x.val inside
    rw [b.hyperbolic.unstableCocycle_normDet] at energy
    change Real.exp (orbitSum T (b.hyperbolic.potential g) p x.val) = W / J at energy
    have weightFactor : W / D = Real.exp (orbitSum T (b.hyperbolic.potential g) p x.val) * (J / D) := by
      rw [energy]
      by_cases zeroD : D = 0
      · simp [zeroD]
      · field_simp [positiveJ.ne', zeroD]
    have ratio : |J / D - 1| ≤ C * b.hyperbolic.contraction ^ p := denominator x.val inside fixed
    change |W / D - Real.exp (orbitSum T (b.hyperbolic.potential g) p x.val)| ≤ _
    calc
      _ = |Real.exp (orbitSum T (b.hyperbolic.potential g) p x.val) * (J / D - 1)| := by
        rw [weightFactor]
        congr 1
        ring
      _ = Real.exp (orbitSum T (b.hyperbolic.potential g) p x.val) * |J / D - 1| := by
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp (orbitSum T (b.hyperbolic.potential g) p x.val) *
          (C * b.hyperbolic.contraction ^ p) :=
        mul_le_mul_of_nonneg_left ratio (Real.exp_pos _).le
      _ = _ := mul_comm _ _
  rw [b.periodicPartitionSum_eq forward inverse (b.hyperbolic.potential g) p positiveP,
    periodicLefschetzSum, dite_eq_left positiveP]
  rw [← Finset.sum_coe_sort (b.periodicPoints forward inverse p positiveP)
    (fun x : M => Real.exp (orbitSum T (b.hyperbolic.potential g) p x))]
  change |(∑ x : s, term x) - (∑ x : s, Real.exp (orbitSum T (b.hyperbolic.potential g) p x.val))| ≤
    (C * b.hyperbolic.contraction ^ p) *
      (∑ x : s, Real.exp (orbitSum T (b.hyperbolic.potential g) p x.val))
  calc
    _ = |∑ x : s, (term x - Real.exp (orbitSum T (b.hyperbolic.potential g) p x.val))| := by
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ x : s, |term x - Real.exp (orbitSum T (b.hyperbolic.potential g) p x.val)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x : s, (C * b.hyperbolic.contraction ^ p) *
        Real.exp (orbitSum T (b.hyperbolic.potential g) p x.val) :=
      Finset.sum_le_sum (fun x _ => localBound x)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem BasicData.normalized_lefschetz_partition_error (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (g : M → ℝ) (positive : ∀ x ∈ Λ, 0 < g x) (rate : ℝ) (positiveRate : 0 < rate) :
    ∃ C > 0, ∀ᶠ p : ℕ in atTop,
      |b.periodicLefschetzSum forward inverse g p / rate ^ p -
        b.periodicPartitionSum forward inverse (b.hyperbolic.potential g) p / rate ^ p| ≤
      (C * b.hyperbolic.contraction ^ p) *
        (b.periodicPartitionSum forward inverse (b.hyperbolic.potential g) p / rate ^ p) := by
  obtain ⟨C, positiveC, errors⟩ := b.lefschetz_partition_error forward inverse g positive
  refine ⟨C, positiveC, ?_⟩
  filter_upwards [errors] with p error
  rw [← sub_div, abs_div, abs_of_pos (pow_pos positiveRate p)]
  exact (div_le_div_of_nonneg_right error (pow_pos positiveRate p).le).trans_eq
    (mul_div_assoc _ _ _)

end LeanShared.HyperbolicBasicSet
