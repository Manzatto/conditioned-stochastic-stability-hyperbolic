module
public import LeanShared.Geometry.CompactRiemannianBundleMaps
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-! Uniform actual differential bounds in a fixed chart on a compact subpatch. -/
public noncomputable section
open Set Filter Bundle IsManifold
open scoped Manifold Topology Bundle ContDiff
namespace LeanShared.CompactRiemannianChartBounds
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]

theorem forward (c : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (K : Set M) (compact : IsCompact K) (inside : K ⊆ c.source) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K,
      ‖(NormedSpace.fromTangentSpace (𝕜 := ℝ) (c x)).toContinuousLinearMap.comp
        (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) c x)‖ ≤ C := by
  let A := fun x => (NormedSpace.fromTangentSpace (𝕜 := ℝ) (c x)).toContinuousLinearMap.comp
    (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) c x)
  apply CompactRiemannianBundleMaps.to_fixed (F := E) (TangentSpace (𝓘(ℝ,E))) K compact A
  have smooth := contMDiffOn_of_mem_maximalAtlas hc
  have tangent := smooth.continuousOn_tangentMapWithin (by simp) c.open_source.uniqueMDiffOn
  have out := (tangentBundleModelSpaceHomeomorph (𝓘(ℝ,E))).continuous.snd.comp_continuousOn tangent
  apply (out.mono (fun v hv => inside hv)).congr
  intro v hv
  simp only [Function.comp_def,tangentMapWithin,tangentBundleModelSpaceHomeomorph_coe,
    TotalSpace.toProd,ContinuousLinearMap.comp_apply,A]
  rw [mfderivWithin_of_isOpen c.open_source (inside hv)]
  rfl

omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)] in
theorem chart_differentiable (c : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) :
    c.MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) :=
  ⟨(contMDiffOn_of_mem_maximalAtlas hc).mdifferentiableOn (by simp),
    (contMDiffOn_symm_of_mem_maximalAtlas hc).mdifferentiableOn (by simp)⟩

theorem inverse (c : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (K : Set M) (compact : IsCompact K) (inside : K ⊆ c.source) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : M) (hx : x ∈ K),
      ‖((chart_differentiable c hc).mfderiv (inside hx)).symm.toContinuousLinearMap.comp
        (NormedSpace.fromTangentSpace (𝕜 := ℝ) (c x)).symm.toContinuousLinearMap‖ ≤ C := by
  classical
  let A := fun x => if hx : x ∈ c.source then
    ((chart_differentiable c hc).mfderiv hx).symm.toContinuousLinearMap.comp
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (c x)).symm.toContinuousLinearMap else 0
  have continuous : ∀ v : E, ContinuousOn
      (fun x => (⟨x,A x v⟩ : TotalSpace E (TangentSpace (𝓘(ℝ,E))))) K := by
    intro v
    have input : ContinuousOn
        (fun x => (tangentBundleModelSpaceHomeomorph (𝓘(ℝ,E))).symm (c x,v)) K :=
      (tangentBundleModelSpaceHomeomorph (𝓘(ℝ,E))).symm.continuous.comp_continuousOn
        ((c.continuousOn.mono inside).prodMk continuousOn_const)
    have tangent := (contMDiffOn_symm_of_mem_maximalAtlas hc).continuousOn_tangentMapWithin
      (by simp) c.open_target.uniqueMDiffOn
    have out := tangent.comp input (fun x hx => c.map_source (inside hx))
    apply out.congr
    intro x hx
    change (⟨x,A x v⟩ : TotalSpace E (TangentSpace (𝓘(ℝ,E)))) =
      ⟨c.symm (c x),(mfderivWithin (𝓘(ℝ,E)) (𝓘(ℝ,E)) c.symm c.target (c x)) v⟩
    rw [mfderivWithin_of_isOpen c.open_target (c.map_source (inside hx))]
    apply TotalSpace.ext
    · exact (c.left_inv (inside hx)).symm
    · simp only [A,dite_eq_left (inside hx),ContinuousLinearMap.comp_apply]
      rfl
  obtain ⟨C,hC,bound⟩ := CompactRiemannianBundleMaps.from_fixed (F := E)
    (TangentSpace (𝓘(ℝ,E))) K compact A continuous
  refine ⟨C,hC,fun x hx => ?_⟩
  simpa only [A,dite_eq_left (inside hx)] using bound x hx
end LeanShared.CompactRiemannianChartBounds
