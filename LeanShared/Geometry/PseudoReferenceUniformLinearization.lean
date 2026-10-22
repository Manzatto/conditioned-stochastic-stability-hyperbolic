module
public import LeanShared.Dynamics.PseudoReferenceEuclideanBlocks
public import LeanShared.Geometry.PseudoReferenceCenteredDerivative
public import LeanShared.Geometry.PseudoReferenceDerivativeFactorBounds
public import LeanShared.Geometry.PseudoReferenceLinearBounds
public import Mathlib.Tactic.FieldSimp

/-! The ACTUAL centered deterministic block derivative is uniformly close to
contracting diagonal blocks for every sufficiently accurate pseudo-reference
pair. The transport error is chosen AFTER the block length and derivative
bounds, avoiding a circular smallness assumption. -/
public noncomputable section
namespace LeanShared.PseudoReferenceCoordinateMaps
open Set IsManifold Bundle
open scoped Topology Manifold ContDiff Bundle
open CenteredManifoldCoordinates HyperbolicBasicSet

set_option maxHeartbeats 2400000 in
theorem exists_uniform_linearization
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ : Set M} {h : HyperbolicData (E := E) T Λ}
    (d : PseudoReferenceGeometry h) (a : IsometricFraming h)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T) (δ : ℝ) (positiveδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ ∀ x y : Λ, dist ((T ^ d.blockLength) x.val) y.val < η →
      ∃ S : EuclideanSpace ℝ (Fin a.stableDimension) ≃L[ℝ] EuclideanSpace ℝ (Fin a.stableDimension),
      ∃ U : EuclideanSpace ℝ (Fin a.unstableDimension) ≃L[ℝ] EuclideanSpace ℝ (Fin a.unstableDimension),
        ‖S.toContinuousLinearMap‖ ≤ 1 / 4 ∧ ‖U.symm.toContinuousLinearMap‖ ≤ 1 / 4 ∧
        ‖fderiv ℝ (centered (linear d a.whole x) (linear d a.whole y)
            ((chart d x) x.val) ((chart d y) y.val)
            (chart d y ∘ (T ^ d.blockLength : M ≃ₜ M) ∘ (chart d x).symm)) 0 -
          U.toContinuousLinearMap.prodMap S.toContinuousLinearMap‖ ≤ δ := by
  let H : M → M := (T ^ d.blockLength : M ≃ₜ M)
  have smooth : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 H := by
    dsimp only [H]
    rw [DiffeomorphismIterates.coe_pow]
    exact forward.iterate d.blockLength
  obtain ⟨B,positiveB,bounds⟩ := a.exists_uniform_bound
  obtain ⟨C,positiveC,linearBounds⟩ := exists_uniform_linear_bound d a.whole positiveB bounds
  obtain ⟨D,positiveD,η0,positiveη0,factors⟩ := exists_derivative_factor_bound d a.whole positiveB
    (fun x => (bounds x).1) H smooth
  let θ := min (1 / 4) (δ / (4 * C * D))
  have positiveθ : 0 < θ := lt_min (by norm_num) (div_pos positiveδ (by positivity))
  have halfθ : θ ≤ 1 / 2 := (min_le_left _ _).trans (by norm_num)
  have θlt : θ < 1 := by linarith
  have ratioNonneg : 0 ≤ θ / (1 - θ) := div_nonneg positiveθ.le (sub_pos.mpr θlt).le
  have ratio : θ / (1 - θ) ≤ 2 * θ :=
    (div_le_iff₀ (sub_pos.mpr θlt)).2 (by nlinarith)
  have θbound : θ * (4 * C * D) ≤ δ :=
    (le_div_iff₀ (show 0 < 4 * C * D by positivity)).mp (min_le_right _ _)
  have scalar : C * (θ / (1 - θ)) * D ≤ δ := calc
    _ ≤ C * (2 * θ) * D := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left ratio positiveC.le) positiveD.le
    _ ≤ δ := by nlinarith
  obtain ⟨η1,positiveη1,blocks⟩ := d.exists_euclidean_blocks a θ positiveθ halfθ
  refine ⟨min η0 η1,lt_min positiveη0 positiveη1,fun x y near => ?_⟩
  have factor := factors x y (near.trans_le (min_le_left _ _))
  obtain ⟨_source,_target,R,S,U,_normR,_inverseR,stableBound,unstableBound,action,closeR⟩ :=
    blocks x y (near.trans_le (min_le_right _ _))
  have error := centered_derivative_error d a.whole H x y (smooth.mdifferentiable one_ne_zero x.val)
    factor.1 R θ θlt closeR.le
  rw [action] at error
  refine ⟨S,U,stableBound,unstableBound,error.trans ?_⟩
  calc
    _ ≤ C * (θ / (1 - θ)) * D := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (linearBounds y).2 ratioNonneg
      · exact factor.2
      · exact norm_nonneg ((trivializationAt E (fun z : M => TangentSpace (𝓘(ℝ, E)) z)
          (d.index y).val).continuousLinearMapAt ℝ (H x.val) |>.comp
            ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) H x.val).comp (a.whole x).toContinuousLinearMap))
      · exact mul_nonneg positiveC.le ratioNonneg
    _ ≤ δ := scalar

end LeanShared.PseudoReferenceCoordinateMaps
