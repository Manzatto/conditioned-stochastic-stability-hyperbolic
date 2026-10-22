module
public import LeanShared.Dynamics.HyperbolicExtendedNativeJacobianContinuity
public import LeanShared.Geometry.LocalJointManifoldStateTangentContinuity

/-! Actual native determinant continuity on a local open joint domain.
This includes finite chart-jet families whose maps are defined only near
the current source and target chart points. -/
@[expose] public noncomputable section
open Set Filter Bundle IsManifold
open scoped Topology Manifold ContDiff
namespace LeanShared.HyperbolicBasicSet.HyperbolicData.NormedAdaptedProjection
variable {A E P M : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace P] [ChartedSpace A P] [IsManifold (𝓘(ℝ,A)) ∞ P]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ : Set M} {h : HyperbolicData (E := E) T Λ}

theorem continuousOn_localParametricNativeJacobian (a : h.NormedAdaptedProjection)
    (F : P × M → M) (R : Set (P × M)) (openR : IsOpen R)
    (regular : ContMDiffOn ((𝓘(ℝ,A)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) 1 F R) :
    ContinuousOn (fun z : P × M =>
      ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (fun x => F (z.1,x)) z.2).toLinearMap.domRestrict
        (a.unstable z.2)).normDet) (R ∩ (univ ×ˢ a.collar)) := by
  rintro ⟨p,x⟩ hx
  obtain ⟨O,openO,member,H,frames⟩ := a.exists_collar_kernel_frames x hx.2.2
  let K := a.collar ∩ O
  let Z := (R ∩ (univ ×ˢ a.collar)) ∩ (univ ×ˢ O)
  let base : Z → K := fun z => ⟨z.val.2,z.property.1.2.2,z.property.2.2⟩
  have continuousBase : Continuous base :=
    (continuous_snd.comp continuous_subtype_val).subtype_mk _
  let fibers : M → Type _ := TangentSpace (𝓘(ℝ,E))
  let B (z : Z) : (a.projection z.val.2).ker →L[ℝ] fibers (F z.val) :=
    (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (fun y => F (z.val.1,y)) z.val.2).comp
      (a.projection z.val.2).ker.subtypeL
  have localFrames (u : (a.projection x).ker) : Continuous (fun z : Z =>
      (⟨z.val.2,(H (base z) u).val⟩ : TangentBundle (𝓘(ℝ,E)) M)) :=
    (frames u).comp continuousBase
  have images (u : (a.projection x).ker) : Continuous (fun z : Z =>
      (⟨F z.val,B z (H (base z) u)⟩ : TangentBundle (𝓘(ℝ,E)) M)) := by
    have args := (continuous_fst.comp continuous_subtype_val).prodMk (localFrames u)
    have actual := (JointManifoldStateTangentContinuity.continuousOn_domain F R openR regular).comp
      args.continuousOn (s := univ) (fun z _ => z.property.1.1)
    exact continuousOn_univ.mp actual
  have jacobian : Continuous (fun z : Z => (B z).toLinearMap.normDet) := by
    apply continuousOn_univ.mp
    exact BundleFrameJacobianContinuity.continuousOn_normDet fibers fibers
      (fun z : Z => z.val.2) (fun z : Z => F z.val) univ
      (fun z : Z => (a.projection z.val.2).ker) (fun z => H (base z)) B
      (fun u => (localFrames u).continuousOn) (fun u => (images u).continuousOn)
  have onZ : ContinuousOn (fun z : P × M =>
      ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (fun y => F (z.1,y)) z.2).toLinearMap.domRestrict
        (a.unstable z.2)).normDet) Z :=
    continuousOn_iff_continuous_domRestrict.mpr jacobian
  exact (continuousWithinAt_inter ((isOpen_univ.prod openO).mem_nhds
    (show (p,x) ∈ (univ : Set P) ×ˢ O from ⟨mem_univ _,member⟩))).mp
      (onZ (p,x) ⟨hx,mem_univ _,member⟩)

end LeanShared.HyperbolicBasicSet.HyperbolicData.NormedAdaptedProjection
