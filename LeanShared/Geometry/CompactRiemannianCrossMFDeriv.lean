module
public import LeanShared.Geometry.CompactRiemannianTrivializations
public import LeanShared.Topology.CompactLocalBound
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Tactic.Linarith

/-! Uniform native Riemannian operator bounds for an actual C1 manifold
map on a compact set. Source and target tangent fibers may be different. -/
public noncomputable section
open Set Filter Bundle IsManifold
open scoped Topology Manifold ContDiff Bundle
namespace LeanShared.CompactRiemannianCrossMFDeriv
variable {E M F N:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x:M=>TangentSpace (𝓘(ℝ,E)) x)]

variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold (𝓘(ℝ,F)) ∞ N]
  [RiemannianBundle (fun x:N=>TangentSpace (𝓘(ℝ,F)) x)]
  [IsContinuousRiemannianBundle F (fun x:N=>TangentSpace (𝓘(ℝ,F)) x)]

omit [FiniteDimensional ℝ F] in
theorem exists_norm_bound (H:M→N) (smooth:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,F)) 1 H)
    (K:Set M) (compact:IsCompact K) :
    ∃C:ℝ,0<C ∧ ∀x∈K,‖mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) H x‖≤C := by
  apply CompactLocalBound.exists_bound compact
  intro x hx
  let fibers:=fun y:M=>TangentSpace (𝓘(ℝ,E)) y
  let e:=trivializationAt E fibers x
  let targetFibers:=fun y:N=>TangentSpace (𝓘(ℝ,F)) y
  let f:=trivializationAt F targetFibers (H x)
  let A:=fun y=>(f.continuousLinearMapAt ℝ (H y)).comp
    ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) H y).comp (e.symmL ℝ y))
  let U:=e.baseSet∩H⁻¹' f.baseSet
  have source:x∈e.baseSet:=FiberBundle.mem_baseSet_trivializationAt' x
  have target:H x∈f.baseSet:=FiberBundle.mem_baseSet_trivializationAt' (H x)
  have openU:IsOpen U:=e.open_baseSet.inter (f.open_baseSet.preimage smooth.continuous)
  have member:x∈U:=⟨source,target⟩
  have matrixContinuous:ContinuousOn A U:=by
    apply continuousOn_clm_apply.mpr
    intro v
    have input:ContinuousOn (fun y=>(⟨y,e.symm y v⟩:TotalSpace E fibers)) e.baseSet:=
      e.continuousOn_symm.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun y hy=>⟨hy,mem_univ v⟩)
    have middle:ContinuousOn
        (fun y=>tangentMap (𝓘(ℝ,E)) (𝓘(ℝ,F)) H (⟨y,e.symm y v⟩:TotalSpace E fibers))
        e.baseSet:=(smooth.continuous_tangentMap (by norm_num)).comp_continuousOn input
    have coded:=f.continuousOn.comp (middle.mono inter_subset_left)
      (fun y hy=>f.mem_source.mpr hy.2)
    apply coded.snd.congr
    intro y hy
    change A y v=(f ⟨H y,(mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) H y) (e.symm y v)⟩).2
    dsimp only [A,ContinuousLinearMap.comp_apply]
    rw [e.symmL_apply hy.1]
    exact Trivialization.continuousLinearMapAt_apply_of_mem ℝ f (b:=H y) hy.2 _
  have matrixAt:ContinuousAt A x:=matrixContinuous.continuousAt (openU.mem_nhds member)
  obtain ⟨Cs,positiveCs,sourceBounds⟩:=CompactRiemannianTrivializations.local_bound (F:=E) fibers x
  obtain ⟨Ct,positiveCt,targetBounds⟩:=CompactRiemannianTrivializations.local_bound (F:=F) targetFibers (H x)
  have pulledTarget:=smooth.continuous.continuousAt.tendsto.eventually targetBounds
  have matrixBound:=matrixAt.norm.eventually (gt_mem_nhds (lt_add_one ‖A x‖))
  refine ⟨Ct*((‖A x‖+1)*Cs)+1,by positivity,?_⟩
  filter_upwards [sourceBounds.filter_mono nhdsWithin_le_nhds,
    pulledTarget.filter_mono nhdsWithin_le_nhds,
    matrixBound.filter_mono nhdsWithin_le_nhds] with y hs ht hm
  have reconstruct:mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) H y=
      (f.symmL ℝ (H y)).comp ((A y).comp (e.continuousLinearMapAt ℝ y)):=by
    ext v
    simp only [A,ContinuousLinearMap.comp_apply,e.symmL_continuousLinearMapAt hs.1,
      f.symmL_continuousLinearMapAt ht.1]
  have bound:‖mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) H y‖≤
      ‖f.symmL ℝ (H y)‖*(‖A y‖*‖e.continuousLinearMapAt ℝ y‖):=by
    rw [reconstruct]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
  apply bound.trans
  apply (mul_le_mul ht.2.2
    (mul_le_mul hm.le hs.2.1 (norm_nonneg _) (by positivity))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) positiveCt.le).trans
  exact le_add_of_nonneg_right zero_le_one
end LeanShared.CompactRiemannianCrossMFDeriv
