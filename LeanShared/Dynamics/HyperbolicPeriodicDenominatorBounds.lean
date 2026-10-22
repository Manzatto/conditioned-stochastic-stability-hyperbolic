module

public import LeanShared.Dynamics.HyperbolicPeriodicReturnBounds
public import LeanShared.Geometry.DimensionalOneSubJacobian
public import LeanShared.Geometry.PeriodicDiffeomorphismDifferential

/-! For every sufficiently large period, the literal Lefschetz return
denominator is uniformly comparable with the actual unstable Jacobian
product. Constants depend only on ambient dimension; no periodic point,
preferred coordinates or determinant-comparison source is supplied. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle Filter
open scoped Topology Manifold ContDiff BigOperators
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ : Set M}

@[expose] def _root_.LeanShared.DiffeomorphismDifferential.periodicDenominator (T : M ≃ₜ M)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (p : ℕ) (x : M) (fixed : (T : M → M)^[p] x = x) : ℝ :=
  |(ContinuousLinearMap.id ℝ (TangentSpace (𝓘(ℝ,E)) x) -
    (LeanShared.DiffeomorphismDifferential.periodicReturn T forward inverse p x fixed).toContinuousLinearMap).det|

set_option maxHeartbeats 2200000 in
theorem HyperbolicData.periodic_denominator_bounds (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm) :
    ∃ L > 0, ∃ B > 0, ∀ᶠ p : ℕ in atTop, ∀ x ∈ Λ,
      ∀ fixed : (T : M → M)^[p] x = x,
      (∏ j ∈ Finset.range p, h.unstableJacobian ((T : M → M)^[j] x)) ≤
        L * DiffeomorphismDifferential.periodicDenominator T forward inverse p x fixed ∧
      DiffeomorphismDifferential.periodicDenominator T forward inverse p x fixed ≤
        B * (∏ j ∈ Finset.range p, h.unstableJacobian ((T : M → M)^[j] x)) := by
  let d := Module.finrank ℝ E
  let K := DimensionalJacobianBound.bound d 2
  let H := DimensionalJacobianBound.bound d (3 / 2)
  have positiveK : 0 < K := DimensionalJacobianBound.positive _ _
  have positiveH : 0 < H := DimensionalJacobianBound.positive _ _
  have limit : Tendsto (fun n : ℕ => h.constant * h.contraction ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one h.contraction_pos.le h.contraction_lt_one)
  refine ⟨K ^ 2, sq_pos_of_pos positiveK, H ^ 2, sq_pos_of_pos positiveH, ?_⟩
  filter_upwards [(tendsto_order.mp limit).2 (1 / 2) (by norm_num)] with p small
  intro x hx fixed
  obtain ⟨A, S, U, actualA, determinantU, determinant, stableBound, inverseBound⟩ :=
    h.exists_periodic_return_bounds forward inverse p x hx fixed
  have stableSmall : ‖S.toContinuousLinearMap‖ ≤ (1 / 2 : ℝ) := stableBound.trans small.le
  have inverseSmall : ‖U.symm.toContinuousLinearMap‖ ≤ (1 / 2 : ℝ) := inverseBound.trans small.le
  have dimensionS : Module.finrank ℝ (h.stable x) ≤ d := (h.stable x).finrank_le
  have dimensionU : Module.finrank ℝ (h.unstable x) ≤ d := (h.unstable x).finrank_le
  obtain ⟨upperS, lowerS⟩ := DimensionalOneSubJacobian.small_bounds d dimensionS S.toContinuousLinearMap stableSmall
  obtain ⟨upperU, lowerU⟩ := DimensionalOneSubJacobian.small_bounds d dimensionU U.symm.toContinuousLinearMap inverseSmall
  let s := (ContinuousLinearMap.id ℝ (h.stable x) - S.toContinuousLinearMap).toLinearMap.normDet
  let u := (ContinuousLinearMap.id ℝ (h.unstable x) - U.symm.toContinuousLinearMap).toLinearMap.normDet
  have nonnegativeS : 0 ≤ s := LinearMap.normDet_nonneg _
  have nonnegativeU : 0 ≤ u := LinearMap.normDet_nonneg _
  have lower : 1 ≤ K ^ 2 * (s * u) := by
    have multiply := mul_le_mul lowerS lowerU (by norm_num) (mul_nonneg positiveK.le nonnegativeS)
    calc
      1 = (1 : ℝ) * 1 := by ring
      _ ≤ (K * s) * (K * u) := multiply
      _ = _ := by ring
  have upper : s * u ≤ H ^ 2 := by
    have multiply := mul_le_mul upperS upperU nonnegativeU positiveH.le
    simpa only [pow_two] using multiply
  have sameReturn : A = DiffeomorphismDifferential.periodicReturn T forward inverse p x fixed := by
    apply DFunLike.ext
    intro v
    exact (actualA v).trans
      (DiffeomorphismDifferential.periodicReturn_apply T forward inverse p x fixed v).symm
  have literal : |(LinearMap.id - A.toLinearMap).det| =
      DiffeomorphismDifferential.periodicDenominator T forward inverse p x fixed := by
    rw [sameReturn]
    rfl
  have split := congrArg abs determinant
  rw [abs_mul, ← LinearMap.normDet_eq_abs_det (LinearMap.id - S.toLinearMap),
    ← LinearMap.normDet_eq_abs_det (LinearMap.id - U.toLinearMap)] at split
  have unstableFactor := NormDetOneSub.factor U
  change (LinearMap.id - U.toLinearMap).normDet = _ at unstableFactor
  rw [unstableFactor, determinantU, literal] at split
  change DiffeomorphismDifferential.periodicDenominator T forward inverse p x fixed =
    s * ((∏ j ∈ Finset.range p, h.unstableJacobian ((T : M → M)^[j] x)) * u) at split
  have factor :
      DiffeomorphismDifferential.periodicDenominator T forward inverse p x fixed =
      (∏ j ∈ Finset.range p, h.unstableJacobian ((T : M → M)^[j] x)) * (s * u) := by
    exact split.trans (by ring)
  have jacobianNonnegative : 0 ≤ ∏ j ∈ Finset.range p, h.unstableJacobian ((T : M → M)^[j] x) :=
    Finset.prod_nonneg (fun _ _ => LinearMap.normDet_nonneg _)
  rw [factor]
  constructor
  · have bound := mul_le_mul_of_nonneg_left lower jacobianNonnegative
    simpa only [mul_one, mul_left_comm, mul_assoc] using bound
  · have bound := mul_le_mul_of_nonneg_left upper jacobianNonnegative
    simpa only [mul_comm] using bound

end LeanShared.HyperbolicBasicSet
