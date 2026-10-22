module
public import LeanShared.Analysis.GramNormalizedBasis
public import Mathlib.Topology.VectorBundle.Riemannian
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Continuous Gram normalization of local frames in genuine varying
subspaces, measured in the ambient continuous Riemannian bundle. A subbundle
structure or global choice of frames is not required. -/
public noncomputable section
open Set Bundle
open scoped MatrixOrder Matrix.Norms.L2Operator BigOperators
namespace LeanShared.ContinuousSubspaceFrameNormalization
variable {X B F H : Type*} [TopologicalSpace X] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  (E : B → Type*) [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- A finite-dimensional input turns continuity of fixed-vector sections into
joint continuity of the actual varying bundle-linear map. -/
theorem joint_linear (b : X → B) (cb : Continuous b) (A : ∀ x, H →L[ℝ] E (b x))
    (sections : ∀ v : H, Continuous (fun x => (⟨b x, A x v⟩ : TotalSpace F E))) :
    Continuous (fun p : X × H => (⟨b p.1, A p.1 p.2⟩ : TotalSpace F E)) := by
  rw [continuous_iff_continuousAt]
  intro p
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(cb.comp continuous_fst).continuousAt, ?_⟩
  let e := trivializationAt F E (b p.1)
  have hx : b p.1 ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' _
  have each (v : H) : ContinuousAt
      (fun x => e.continuousLinearMapAt ℝ (b x) (A x v)) p.1 := by
    have h := (sections v).continuousAt (x := p.1)
    rw [FiberBundle.continuousAt_totalSpace] at h
    apply h.2.congr_of_eventuallyEq
    filter_upwards [cb.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hx)] with x hx
    exact e.continuousLinearMapAt_apply_of_mem ℝ hx (A x v)
  have maps : ContinuousAt
      (fun x => (e.continuousLinearMapAt ℝ (b x)).comp (A x)) p.1 :=
    continuousAt_clm_apply.mpr each
  have applied := (maps.comp continuous_fst.continuousAt).clm_apply continuous_snd.continuousAt
  apply applied.congr_of_eventuallyEq
  filter_upwards [(cb.comp continuous_fst).continuousAt.preimage_mem_nhds
    (e.open_baseSet.mem_nhds hx)] with q hq
  exact (e.continuousLinearMapAt_apply_of_mem ℝ hq (A q.1 q.2)).symm

variable [∀ b, FiniteDimensional ℝ (E b)]

theorem continuous_basis_of_gram (b : X → B) (cb : Continuous b)
    (S : ∀ x, Submodule ℝ (E (b x))) (A : ∀ x, H ≃L[ℝ] S x)
    (sections : ∀ v : H, Continuous (fun x => (⟨b x, (A x v).val⟩ : TotalSpace F E)))
    (gram : Continuous (fun x => GramNormalizedBasis.gram (A x)))
    (i : Fin (Module.finrank ℝ H)) :
    Continuous (fun x => (⟨b x, (GramNormalizedBasis.basis (V := S x) (A x) i).val⟩ : TotalSpace F E)) := by
  let G := fun x => GramNormalizedBasis.gram (A x)
  have normalize : Continuous (fun x => MatrixGramNormalizer.normalize (G x)) :=
    continuousOn_univ.mp (MatrixGramNormalizer.continuousOn univ G gram.continuousOn
      (fun x _ => GramNormalizedBasis.positive (A x)))
  let v := fun x => ∑ j, MatrixGramNormalizer.normalize (G x) j i • stdOrthonormalBasis ℝ H j
  have cv : Continuous v := by
    apply continuous_finsetSum
    intro j _
    exact ((continuous_apply i).comp ((continuous_apply j).comp normalize)).smul continuous_const
  have joint := joint_linear E b cb
    (fun x => (S x).subtypeL.comp (A x).toContinuousLinearMap) sections
  apply (joint.comp (continuous_id.prodMk cv)).congr
  intro x
  change (⟨b x, (A x (v x)).val⟩ : TotalSpace F E) =
    ⟨b x, (GramNormalizedBasis.basis (V := S x) (A x) i).val⟩
  apply congrArg (fun z : S x => (⟨b x, z.val⟩ : TotalSpace F E))
  rw [GramNormalizedBasis.basis_apply]
  simp only [v, GramNormalizedBasis.vectors, G, map_sum, map_smul]

theorem continuous_normalized_basis [IsContinuousRiemannianBundle F E] (b : X → B) (cb : Continuous b)
    (S : ∀ x, Submodule ℝ (E (b x))) (A : ∀ x, H ≃L[ℝ] S x)
    (sections : ∀ v : H, Continuous (fun x => (⟨b x, (A x v).val⟩ : TotalSpace F E)))
    (i : Fin (Module.finrank ℝ H)) :
    Continuous (fun x => (⟨b x, (GramNormalizedBasis.basis (V := S x) (A x) i).val⟩ : TotalSpace F E)) := by
  let G := fun x => GramNormalizedBasis.gram (A x)
  have gram : Continuous G := by
    apply continuous_pi
    intro j
    apply continuous_pi
    intro k
    simpa only [G, GramNormalizedBasis.gram, Matrix.gram_apply, Submodule.coe_inner] using
      (sections (stdOrthonormalBasis ℝ H j)).inner_bundle
        (sections (stdOrthonormalBasis ℝ H k))
  exact continuous_basis_of_gram E b cb S A sections gram i

end LeanShared.ContinuousSubspaceFrameNormalization
