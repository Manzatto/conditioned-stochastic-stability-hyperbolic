module

public import LeanShared.Dynamics.HyperbolicPeriodicDenominatorBounds
public import LeanShared.Geometry.DimensionalOneSubJacobianDeviation
import Mathlib.Tactic.FieldSimp

/-! The literal periodic Lefschetz denominator differs from the unstable
Jacobian product by an exponentially small relative error.  Constants are
uniform in the periodic point and period and are derived from the actual
stable and inverse-unstable return blocks.
-/

public noncomputable section
namespace LeanShared.PeriodicDeterminantDeviation

theorem product_deviation {s u K ε H : ℝ} (hu : 0 ≤ u) (huH : u ≤ H)
    (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hs : |s - 1| ≤ K * ε) (he : |u - 1| ≤ K * ε) :
    |s * u - 1| ≤ K * (H + 1) * ε := by
  have identity : s * u - 1 = (s - 1) * u + (u - 1) := by ring
  calc
    |s * u - 1| ≤ |s - 1| * u + |u - 1| := by
      rw [identity]
      exact (abs_add_le _ _).trans_eq (by rw [abs_mul, abs_of_nonneg hu])
    _ ≤ (K * ε) * H + K * ε :=
      add_le_add (mul_le_mul hs huH hu (mul_nonneg hK hε)) he
    _ = K * (H + 1) * ε := by ring

theorem inverse_deviation {x L : ℝ} (hx : 0 < x) (lower : 1 ≤ L * x) :
    |x⁻¹ - 1| ≤ L * |x - 1| := by
  have identity : x⁻¹ - 1 = (1 - x) / x := by
    field_simp [hx.ne']
  rw [identity, abs_div, abs_of_pos hx, abs_sub_comm 1 x]
  apply (div_le_iff₀ hx).mpr
  calc
    |x - 1| = |x - 1| * 1 := (mul_one _).symm
    _ ≤ |x - 1| * (L * x) := mul_le_mul_of_nonneg_left lower (abs_nonneg _)
    _ = (L * |x - 1|) * x := by ring

end LeanShared.PeriodicDeterminantDeviation

namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle Filter
open scoped Topology Manifold ContDiff BigOperators
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ : Set M}

set_option maxHeartbeats 2200000 in
theorem HyperbolicData.periodic_denominator_ratio_error (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm) :
    ∃ C > 0, ∀ᶠ p : ℕ in atTop, ∀ x ∈ Λ,
      ∀ fixed : (T : M → M)^[p] x = x,
      |(∏ j ∈ Finset.range p, h.unstableJacobian ((T : M → M)^[j] x)) /
        DiffeomorphismDifferential.periodicDenominator T forward inverse p x fixed - 1| ≤
          C * h.contraction ^ p := by
  let d := Module.finrank ℝ E
  let L := DimensionalJacobianBound.bound d 2
  let H := DimensionalJacobianBound.bound d (3 / 2)
  let K := DimensionalOneSubJacobianDeviation.bound d
  have positiveL : 0 < L := DimensionalJacobianBound.positive _ _
  have positiveH : 0 < H := DimensionalJacobianBound.positive _ _
  have positiveK : 0 < K := DimensionalOneSubJacobianDeviation.positive _
  have limit : Tendsto (fun n : ℕ => h.constant * h.contraction ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one h.contraction_pos.le h.contraction_lt_one)
  refine ⟨L ^ 2 * K * (H + 1) * h.constant, ?_, ?_⟩
  · exact mul_pos (mul_pos (mul_pos (sq_pos_of_pos positiveL) positiveK)
      (by linarith)) h.constant_pos
  filter_upwards [(tendsto_order.mp limit).2 (1 / 2) (by norm_num)] with p small
  intro x hx fixed
  obtain ⟨A, S, U, actualA, determinantU, determinant, stableBound, inverseBound⟩ :=
    h.exists_periodic_return_bounds forward inverse p x hx fixed
  have stableSmall : ‖S.toContinuousLinearMap‖ ≤ (1 / 2 : ℝ) := stableBound.trans small.le
  have inverseSmall : ‖U.symm.toContinuousLinearMap‖ ≤ (1 / 2 : ℝ) := inverseBound.trans small.le
  have dimensionS : Module.finrank ℝ (h.stable x) ≤ d := (h.stable x).finrank_le
  have dimensionU : Module.finrank ℝ (h.unstable x) ≤ d := (h.unstable x).finrank_le
  obtain ⟨_upperS, lowerS⟩ := DimensionalOneSubJacobian.small_bounds d dimensionS
    S.toContinuousLinearMap stableSmall
  obtain ⟨upperU, lowerU⟩ := DimensionalOneSubJacobian.small_bounds d dimensionU
    U.symm.toContinuousLinearMap inverseSmall
  let s := (ContinuousLinearMap.id ℝ (h.stable x) - S.toContinuousLinearMap).toLinearMap.normDet
  let u := (ContinuousLinearMap.id ℝ (h.unstable x) - U.symm.toContinuousLinearMap).toLinearMap.normDet
  have nonnegativeS : 0 ≤ s := LinearMap.normDet_nonneg _
  have nonnegativeU : 0 ≤ u := LinearMap.normDet_nonneg _
  have lower : 1 ≤ L ^ 2 * (s * u) := by
    have multiply := mul_le_mul lowerS lowerU (by norm_num) (mul_nonneg positiveL.le nonnegativeS)
    calc
      1 = (1 : ℝ) * 1 := by ring
      _ ≤ (L * s) * (L * u) := multiply
      _ = _ := by ring
  have productPositive : 0 < s * u := by
    by_contra failure
    have nonpositive := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg L) (le_of_not_gt failure)
    linarith
  have stableError : |s - 1| ≤ K * (h.constant * h.contraction ^ p) :=
    (DimensionalOneSubJacobianDeviation.normDet_one_sub_deviation d dimensionS
      S.toContinuousLinearMap stableSmall).trans
      (mul_le_mul_of_nonneg_left stableBound positiveK.le)
  have unstableError : |u - 1| ≤ K * (h.constant * h.contraction ^ p) :=
    (DimensionalOneSubJacobianDeviation.normDet_one_sub_deviation d dimensionU
      U.symm.toContinuousLinearMap inverseSmall).trans
      (mul_le_mul_of_nonneg_left inverseBound positiveK.le)
  have error : |s * u - 1| ≤ K * (H + 1) * (h.constant * h.contraction ^ p) :=
    PeriodicDeterminantDeviation.product_deviation nonnegativeU upperU positiveK.le
      (mul_nonneg h.constant_pos.le (pow_nonneg h.contraction_pos.le p)) stableError unstableError
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
  have factor : DiffeomorphismDifferential.periodicDenominator T forward inverse p x fixed =
      (∏ j ∈ Finset.range p, h.unstableJacobian ((T : M → M)^[j] x)) * (s * u) :=
    split.trans (by ring)
  have jacobianPositive : 0 < ∏ j ∈ Finset.range p,
      h.unstableJacobian ((T : M → M)^[j] x) := by
    rw [← determinantU]
    apply lt_of_le_of_ne (LinearMap.normDet_nonneg _) (Ne.symm ?_)
    intro zero
    exact (LinearMap.normDet_eq_zero_iff_ker_ne_bot.mp zero)
      (LinearMap.ker_eq_bot.mpr U.injective)
  rw [factor, div_mul_cancel_left₀ jacobianPositive.ne']
  calc
    |(s * u)⁻¹ - 1| ≤ L ^ 2 * |s * u - 1| :=
      PeriodicDeterminantDeviation.inverse_deviation productPositive lower
    _ ≤ L ^ 2 * (K * (H + 1) * (h.constant * h.contraction ^ p)) :=
      mul_le_mul_of_nonneg_left error (sq_nonneg L)
    _ = (L ^ 2 * K * (H + 1) * h.constant) * h.contraction ^ p := by ring

end LeanShared.HyperbolicBasicSet
