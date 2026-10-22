module

public import Mathlib.Topology.VectorBundle.Riemannian
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Topology.Instances.Matrix

/-! Actual norm determinants of continuous finite-dimensional families
of linear maps into a continuous Riemannian bundle are continuous. The
proof uses the genuine Gram determinant, without a volume-continuity source. -/
public noncomputable section
open Set Function Bundle
open scoped Topology
namespace LeanShared.BundleNormDetContinuity
variable {X B F U : Type*} [TopologicalSpace X] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  (E : B → Type*) [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [IsContinuousRiemannianBundle F E]

theorem continuousOn_normDet (f : X → B) (K : Set X)
    (A : ∀ x, U →L[ℝ] E (f x))
    (sections : ∀ u : U, ContinuousOn (fun x => (⟨f x,A x u⟩ : TotalSpace F E)) K) :
    ContinuousOn (fun x => (A x).toLinearMap.normDet) K := by
  classical
  let b := stdOrthonormalBasis ℝ U
  let G (x : X) := Matrix.gram ℝ (fun i => A x (b i))
  have gram : ContinuousOn G K := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    simpa only [G,Matrix.gram_apply] using (sections (b i)).inner_bundle (sections (b j))
  have detContinuous : Continuous (fun m : Matrix (Fin (Module.finrank ℝ U)) (Fin (Module.finrank ℝ U)) ℝ => m.det) :=
    continuous_id.matrix_det
  have formula (x : X) : (A x).toLinearMap.normDet=Real.sqrt (G x).det := by
    have squared := (A x).toLinearMap.normDet_sq_eq_det_gram b
    change (A x).toLinearMap.normDet^2=(G x).det at squared
    rw [←squared,Real.sqrt_sq (LinearMap.normDet_nonneg _)]
  exact (Real.continuous_sqrt.comp_continuousOn (detContinuous.comp_continuousOn gram)).congr
    (fun x _ => formula x)

end LeanShared.BundleNormDetContinuity
