module

public import LeanShared.Dynamics.BasicHyperbolicPeriodicPartition
public import LeanShared.Dynamics.HyperbolicPeriodicDenominatorBounds
public import LeanShared.Dynamics.HyperbolicOrbitPotentialProduct

/-! Literal periodic Lefschetz sums, defined from actual return derivatives,
are uniformly comparable with the actual thermodynamic periodic sums.
This is a geometric periodic-orbit statement; no operator trace formula
is asserted or assumed. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle Filter ThermodynamicDefinitions
open scoped Topology Manifold ContDiff BigOperators
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M}

@[expose] def BasicData.periodicLefschetzSum (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm) (g : M → ℝ) (p : ℕ) : ℝ :=
  if hp : 0 < p then ∑ x : b.periodicPoints forward inverse p hp,
    (∏ j ∈ Finset.range p, g ((T : M → M)^[j] x.val)) /
      DiffeomorphismDifferential.periodicDenominator T (forward.mdifferentiable one_ne_zero)
        (inverse.mdifferentiable one_ne_zero) p x.val
        ((b.mem_periodicPoints forward inverse p hp x.val).mp x.property).2
  else 0

set_option maxHeartbeats 2000000 in
theorem BasicData.lefschetz_partition_comparison (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (g : M → ℝ) (positive : ∀ x ∈ Λ, 0 < g x) :
    ∃ L > 0, ∃ B > 0, ∀ᶠ p : ℕ in atTop,
      b.periodicPartitionSum forward inverse (b.hyperbolic.potential g) p ≤
        B * b.periodicLefschetzSum forward inverse g p ∧
      b.periodicLefschetzSum forward inverse g p ≤
        L * b.periodicPartitionSum forward inverse (b.hyperbolic.potential g) p := by
  obtain ⟨L, positiveL, B, positiveB, denominators⟩ := b.hyperbolic.periodic_denominator_bounds
    (forward.mdifferentiable one_ne_zero) (inverse.mdifferentiable one_ne_zero)
  have invariant : MapsTo (T : M → M) Λ Λ := image_subset_iff.mp b.hyperbolic.invariant.subset
  refine ⟨L, positiveL, B, positiveB, ?_⟩
  filter_upwards [denominators, eventually_gt_atTop 0] with p denominator positiveP
  let s := b.periodicPoints forward inverse p positiveP
  let term (x : s) := (∏ j ∈ Finset.range p, g ((T : M → M)^[j] x.val)) /
    DiffeomorphismDifferential.periodicDenominator T (forward.mdifferentiable one_ne_zero)
      (inverse.mdifferentiable one_ne_zero) p x.val
      ((b.mem_periodicPoints forward inverse p positiveP x.val).mp x.property).2
  have localBound (x : s) :
      Real.exp (orbitSum T (b.hyperbolic.potential g) p x.val) ≤ B * term x ∧
      term x ≤ L * Real.exp (orbitSum T (b.hyperbolic.potential g) p x.val) := by
    obtain ⟨inside, fixed⟩ := (b.mem_periodicPoints forward inverse p positiveP x.val).mp x.property
    let W := ∏ j ∈ Finset.range p, g ((T : M → M)^[j] x.val)
    let J := ∏ j ∈ Finset.range p, b.hyperbolic.unstableJacobian ((T : M → M)^[j] x.val)
    let D := DiffeomorphismDifferential.periodicDenominator T (forward.mdifferentiable one_ne_zero)
      (inverse.mdifferentiable one_ne_zero) p x.val fixed
    have positiveW : 0 < W := Finset.prod_pos (fun j _ => positive _ (invariant.iterate j inside))
    have positiveJ : 0 < J := Finset.prod_pos (fun j _ => b.hyperbolic.unstableJacobian_positive
      (forward.mdifferentiable one_ne_zero) (inverse.mdifferentiable one_ne_zero) _ (invariant.iterate j inside))
    have bounds : J ≤ L * D ∧ D ≤ B * J := denominator x.val inside fixed
    have positiveD : 0 < D := (mul_pos_iff_of_pos_left positiveL).mp (positiveJ.trans_le bounds.1)
    have energy := b.hyperbolic.exp_orbit_potential (forward.mdifferentiable one_ne_zero)
      (inverse.mdifferentiable one_ne_zero) g positive p x.val inside
    rw [b.hyperbolic.unstableCocycle_normDet] at energy
    change Real.exp (orbitSum T (b.hyperbolic.potential g) p x.val) = W / J at energy
    change Real.exp (orbitSum T (b.hyperbolic.potential g) p x.val) ≤ B * (W / D) ∧
      W / D ≤ L * Real.exp (orbitSum T (b.hyperbolic.potential g) p x.val)
    rw [energy]
    constructor
    · rw [← mul_div_assoc]
      apply (div_le_div_iff₀ positiveJ positiveD).mpr
      nlinarith [mul_le_mul_of_nonneg_left bounds.2 positiveW.le]
    · rw [← mul_div_assoc]
      apply (div_le_div_iff₀ positiveD positiveJ).mpr
      nlinarith [mul_le_mul_of_nonneg_left bounds.1 positiveW.le]
  rw [b.periodicPartitionSum_eq forward inverse (b.hyperbolic.potential g) p positiveP,
    periodicLefschetzSum, dite_eq_left positiveP]
  rw [← Finset.sum_coe_sort (b.periodicPoints forward inverse p positiveP)
    (fun x : M => Real.exp (orbitSum T (b.hyperbolic.potential g) p x))]
  change (∑ x : s, Real.exp (orbitSum T (b.hyperbolic.potential g) p x.val)) ≤ B * (∑ x : s, term x) ∧
    (∑ x : s, term x) ≤ L * (∑ x : s, Real.exp (orbitSum T (b.hyperbolic.potential g) p x.val))
  constructor
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun x _ => (localBound x).1)
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun x _ => (localBound x).2)

end LeanShared.HyperbolicBasicSet
