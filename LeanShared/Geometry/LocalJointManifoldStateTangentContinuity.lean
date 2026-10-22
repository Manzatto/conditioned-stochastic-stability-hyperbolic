module
public import LeanShared.Geometry.JointManifoldStateTangentContinuity

/-! State tangent continuity on a genuine open joint parameter/state
domain. This applies to chart-local finite jet families without extending
partial charts to globally smooth manifold maps. -/
@[expose] public noncomputable section
open Set Bundle IsManifold
open scoped Manifold ContDiff
namespace LeanShared.JointManifoldStateTangentContinuity
variable {A E P M : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace P] [ChartedSpace A P] [IsManifold (𝓘(ℝ,A)) ∞ P]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]

theorem continuousOn_domain (F : P × M → M) (R : Set (P × M)) (openR : IsOpen R)
    (regular : ContMDiffOn ((𝓘(ℝ,A)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) 1 F R) :
    ContinuousOn (stateTangentMap (E := E) F)
      {z : P × TangentBundle (𝓘(ℝ,E)) M | (z.1,z.2.proj) ∈ R} := by
  have paired : Continuous (fun z : P × TangentBundle (𝓘(ℝ,E)) M =>
      ((zeroSection A (TangentSpace (𝓘(ℝ,A))) z.1),z.2)) :=
    ((Bundle.Trivialization.continuous_zeroSection ℝ).comp continuous_fst).prodMk continuous_snd
  have injection : Continuous (fun z : P × TangentBundle (𝓘(ℝ,E)) M =>
      (equivTangentBundleProd (𝓘(ℝ,A)) P (𝓘(ℝ,E)) M).symm
        ((zeroSection A (TangentSpace (𝓘(ℝ,A))) z.1),z.2)) :=
    (contMDiff_equivTangentBundleProd_symm (I := 𝓘(ℝ,A)) (I' := 𝓘(ℝ,E))
      (M := P) (M' := M) (n := 0)).continuous.comp paired
  have actual := (regular.continuousOn_tangentMapWithin (by rfl) openR.uniqueMDiffOn).comp
    injection.continuousOn
    (s := {z : P × TangentBundle (𝓘(ℝ,E)) M | (z.1,z.2.proj) ∈ R}) (fun _ hz => hz)
  apply actual.congr
  intro z hz
  have atPoint := openR.mem_nhds hz
  have localRegular := (regular (z.1,z.2.proj) hz).contMDiffAt atPoint
  symm
  apply congrArg (fun v : TangentSpace (𝓘(ℝ,E)) (F (z.1,z.2.proj)) =>
    (⟨F (z.1,z.2.proj),v⟩ : TangentBundle (𝓘(ℝ,E)) M))
  change mfderivWithin ((𝓘(ℝ,A)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) F R
    (z.1,z.2.proj) (0,z.2.2) = _
  erw [mfderivWithin_of_mem_nhds atPoint,
    mfderiv_prod_eq_add_apply (localRegular.mdifferentiableAt one_ne_zero)]
  erw [map_zero,zero_add]

end LeanShared.JointManifoldStateTangentContinuity
