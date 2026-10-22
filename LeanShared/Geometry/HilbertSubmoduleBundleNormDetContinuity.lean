module

public import LeanShared.Geometry.HilbertBundleNormDetContinuity
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! Actual Gram-volume continuity for maps into the Hilbert product of two
varying Riemannian fibers, derived from the separate genuine sections. -/
public noncomputable section
open Set Bundle
namespace LeanShared.HilbertSubmoduleBundleNormDetContinuity
variable {X B C F G U : Type*} [TopologicalSpace X] [TopologicalSpace B] [TopologicalSpace C]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  (E : B → Type*) [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [IsContinuousRiemannianBundle F E]
  (D : C → Type*) [∀ c, NormedAddCommGroup (D c)] [∀ c, InnerProductSpace ℝ (D c)]
  [TopologicalSpace (TotalSpace G D)] [FiberBundle G D] [VectorBundle ℝ G D]
  [IsContinuousRiemannianBundle G D]


theorem continuousOn_normDet (f : X → B) (g : X → C) (K : Set X)
    (S : ∀ x, Submodule ℝ (E (f x))) (T : ∀ x, Submodule ℝ (D (g x)))
    (A : ∀ x, U →L[ℝ] WithLp 2 (S x × T x))
    (first : ∀ u : U, ContinuousOn (fun x => (⟨f x,(A x u).fst.val⟩ : TotalSpace F E)) K)
    (second : ∀ u : U, ContinuousOn (fun x => (⟨g x,(A x u).snd.val⟩ : TotalSpace G D)) K) :
    ContinuousOn (fun x => (A x).toLinearMap.normDet) K := by
  classical
  let b := stdOrthonormalBasis ℝ U
  let H (x : X) := Matrix.gram ℝ (fun i => A x (b i))
  have gram : ContinuousOn H K := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    simpa only [H,Matrix.gram_apply,WithLp.prod_inner_apply,WithLp.fst,WithLp.snd,Function.comp_def,Submodule.coe_inner] using
      continuous_add.comp_continuousOn
        (((first (b i)).inner_bundle (first (b j))).prodMk
          ((second (b i)).inner_bundle (second (b j))))
  have detContinuous : Continuous (fun m : Matrix (Fin (Module.finrank ℝ U))
      (Fin (Module.finrank ℝ U)) ℝ => m.det) := continuous_id.matrix_det
  have formula (x : X) : (A x).toLinearMap.normDet=Real.sqrt (H x).det := by
    have squared := (A x).toLinearMap.normDet_sq_eq_det_gram b
    change (A x).toLinearMap.normDet^2=(H x).det at squared
    rw [←squared,Real.sqrt_sq (LinearMap.normDet_nonneg _)]
  exact (Real.continuous_sqrt.comp_continuousOn (detContinuous.comp_continuousOn gram)).congr
    (fun x _ => formula x)

end LeanShared.HilbertSubmoduleBundleNormDetContinuity
