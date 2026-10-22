module
public import LeanShared.Analysis.GramNormalizedBasis
public import Mathlib.Topology.VectorBundle.Riemannian

/-! Actual continuous Riemannian frames with the original normed bundle
model unchanged. A fixed Euclidean input equivalence permits Gram normalization
without imposing an inner product on that model. -/
public noncomputable section
open Set Bundle
open scoped MatrixOrder Matrix.Norms.L2Operator BigOperators
namespace LeanShared.ContinuousRiemannianFramesNormedModel
variable {B F : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (E : B → Type*) [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [∀ b, FiniteDimensional ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [IsContinuousRiemannianBundle F E]
  (e : Trivialization F (Bundle.TotalSpace.proj (E := E))) [e.IsLinear ℝ]

abbrev Model := EuclideanSpace ℝ (Fin (Module.finrank ℝ F))

@[expose] def modelEquiv : Model (F := F) ≃L[ℝ] F :=
  ContinuousLinearEquiv.ofFinrankEq (by simp)

@[expose] def frame (b : e.baseSet) : Model (F := F) ≃L[ℝ] E b.val :=
  (modelEquiv (F := F)).trans (e.continuousLinearEquivAt ℝ b.val b.property).symm

omit [∀ b, FiniteDimensional ℝ (E b)]
  [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E] in
theorem continuous_frame_section (v : Model (F := F)) :
    Continuous (fun b : e.baseSet => (⟨b.val,frame E e b v⟩ : TotalSpace F E)) := by
  have actual := e.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
    (continuous_subtype_val.prodMk (continuous_const : Continuous (fun _ : e.baseSet => modelEquiv v)))
    (fun b : e.baseSet => e.mem_target.mpr b.property)
  apply actual.congr
  intro b
  exact e.symm_apply_eq_mk_continuousLinearEquivAt_symm (R := ℝ) b.val b.property (modelEquiv v)

omit [∀ b, FiniteDimensional ℝ (E b)] in
theorem continuous_gram : Continuous (fun b : e.baseSet => GramNormalizedBasis.gram (frame E e b)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simpa only [GramNormalizedBasis.gram,Matrix.gram_apply] using
    (continuous_frame_section E e (stdOrthonormalBasis ℝ (Model (F := F)) i)).inner_bundle
      (continuous_frame_section E e (stdOrthonormalBasis ℝ (Model (F := F)) j))

omit [∀ b, FiniteDimensional ℝ (E b)] in
theorem continuous_normalizer : Continuous
    (fun b : e.baseSet => MatrixGramNormalizer.normalize (GramNormalizedBasis.gram (frame E e b))) := by
  exact continuousOn_univ.mp (MatrixGramNormalizer.continuousOn Set.univ _ (continuous_gram E e).continuousOn
    (fun b _ => GramNormalizedBasis.positive (frame E e b)))

@[expose] def basis (b : e.baseSet) : OrthonormalBasis (Fin (Module.finrank ℝ (Model (F := F)))) ℝ (E b.val) :=
  GramNormalizedBasis.basis (frame E e b)

theorem continuous_basis_section (i : Fin (Module.finrank ℝ (Model (F := F)))) :
    Continuous (fun b : e.baseSet => (⟨b.val,basis E e b i⟩ : TotalSpace F E)) := by
  let R := fun b : e.baseSet => MatrixGramNormalizer.normalize (GramNormalizedBasis.gram (frame E e b))
  let v := fun b : e.baseSet => ∑ j, R b j i • stdOrthonormalBasis ℝ (Model (F := F)) j
  have continuousV : Continuous v := by
    apply continuous_finsetSum
    intro j _
    have entry : Continuous (fun b : e.baseSet => R b j i) :=
      (continuous_apply i).comp ((continuous_apply j).comp (continuous_normalizer E e))
    exact entry.smul continuous_const
  have actual := e.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
    (continuous_subtype_val.prodMk ((modelEquiv (F := F)).continuous.comp continuousV))
    (fun b : e.baseSet => e.mem_target.mpr b.property)
  apply actual.congr
  intro b
  change e.toOpenPartialHomeomorph.symm (b.val,modelEquiv (v b)) = (⟨b.val,basis E e b i⟩ : TotalSpace F E)
  rw [e.symm_apply_eq_mk_continuousLinearEquivAt_symm (R := ℝ) b.val b.property]
  congr 1
  change frame E e b (v b) = basis E e b i
  dsimp only [basis]
  rw [GramNormalizedBasis.basis_apply]
  simp only [v,GramNormalizedBasis.vectors,map_sum,map_smul,R]

end LeanShared.ContinuousRiemannianFramesNormedModel
