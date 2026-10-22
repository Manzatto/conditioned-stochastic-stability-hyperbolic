module
public import LeanShared.Geometry.PseudoReferenceUniformLinearization
public import LeanShared.Geometry.PseudoReferenceNonlinearVariation

/-! A common genuine nonlinear radius and reference tolerance produce actual
contracting diagonal blocks for every nearby reference pair. The derivative
estimate holds on the whole closed coordinate ball, in the chosen actual
coherent charts and native Riemannian frame construction. -/
public noncomputable section
namespace LeanShared.PseudoReferenceCoordinateMaps
open Set IsManifold Bundle
open scoped Topology Manifold ContDiff Bundle
open CenteredManifoldCoordinates HyperbolicBasicSet

set_option maxHeartbeats 2400000 in
theorem exists_nonlinear_blocks
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ : Set M} {h : HyperbolicData (E := E) T Λ}
    (d : PseudoReferenceGeometry h) (a : IsometricFraming h)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T) (δ : ℝ) (positiveδ : 0 < δ) :
    ∃ radius : ℝ, 0 < radius ∧ ∃ η : ℝ, 0 < η ∧
      ∀ x y : Λ, dist ((T ^ d.blockLength) x.val) y.val < η →
      ∃ S : EuclideanSpace ℝ (Fin a.stableDimension) ≃L[ℝ] EuclideanSpace ℝ (Fin a.stableDimension),
      ∃ U : EuclideanSpace ℝ (Fin a.unstableDimension) ≃L[ℝ] EuclideanSpace ℝ (Fin a.unstableDimension),
        ‖S.toContinuousLinearMap‖ ≤ 1 / 4 ∧ ‖U.symm.toContinuousLinearMap‖ ≤ 1 / 4 ∧
        ∀ z : EuclideanSpace ℝ (Fin a.unstableDimension) × EuclideanSpace ℝ (Fin a.stableDimension),
        ‖z‖ ≤ radius →
          chart d x x.val + linear d a.whole x z ∈ (chart d x).target ∧
          (T ^ d.blockLength) (decode d a.whole x z) ∈ (chart d y).source ∧
          DifferentiableAt ℝ (centered (linear d a.whole x) (linear d a.whole y)
            ((chart d x) x.val) ((chart d y) y.val)
            (chart d y ∘ (T ^ d.blockLength : M ≃ₜ M) ∘ (chart d x).symm)) z ∧
          ‖fderiv ℝ (centered (linear d a.whole x) (linear d a.whole y)
              ((chart d x) x.val) ((chart d y) y.val)
              (chart d y ∘ (T ^ d.blockLength : M ≃ₜ M) ∘ (chart d x).symm)) z -
            U.toContinuousLinearMap.prodMap S.toContinuousLinearMap‖ ≤ δ := by
  let H : M → M := (T ^ d.blockLength : M ≃ₜ M)
  have smooth : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 H := by
    dsimp only [H]
    rw [DiffeomorphismIterates.coe_pow]
    exact forward.iterate d.blockLength
  obtain ⟨B,positiveB,bounds⟩ := a.exists_uniform_bound
  obtain ⟨radius,positiveRadius,η0,positiveη0,variation⟩ := exists_nonlinear_variation_window
    d a.whole positiveB bounds H smooth (δ / 2) (half_pos positiveδ)
  obtain ⟨η1,positiveη1,linearization⟩ := exists_uniform_linearization d a forward (δ / 2) (half_pos positiveδ)
  refine ⟨radius,positiveRadius,min η0 η1,lt_min positiveη0 positiveη1,fun x y near => ?_⟩
  obtain ⟨S,U,stableBound,unstableBound,atZero⟩ := linearization x y (near.trans_le (min_le_right _ _))
  refine ⟨S,U,stableBound,unstableBound,fun z hz => ?_⟩
  have localData := variation x y (near.trans_le (min_le_left _ _)) z hz
  refine ⟨localData.1,localData.2.1,localData.2.2.1,?_⟩
  let f := centered (linear d a.whole x) (linear d a.whole y)
    ((chart d x) x.val) ((chart d y) y.val) (chart d y ∘ H ∘ (chart d x).symm)
  change ‖fderiv ℝ f z - U.toContinuousLinearMap.prodMap S.toContinuousLinearMap‖ ≤ δ
  have triangle := norm_add_le (fderiv ℝ f z - fderiv ℝ f 0)
    (fderiv ℝ f 0 - U.toContinuousLinearMap.prodMap S.toContinuousLinearMap)
  rw [sub_add_sub_cancel] at triangle
  have oscillation := localData.2.2.2
  change ‖fderiv ℝ f z - fderiv ℝ f 0‖ < δ / 2 at oscillation
  change ‖fderiv ℝ f 0 - U.toContinuousLinearMap.prodMap S.toContinuousLinearMap‖ ≤ δ / 2 at atZero
  linarith

end LeanShared.PseudoReferenceCoordinateMaps
