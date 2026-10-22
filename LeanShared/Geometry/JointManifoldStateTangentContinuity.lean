module
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! A genuinely jointly C1 manifold family has a continuous state tangent
action. The proof injects a zero parameter tangent into the actual product
tangent bundle and applies the chain rule, without a derivative source. -/
@[expose] public noncomputable section
open Set Bundle IsManifold
open scoped Manifold ContDiff
namespace LeanShared.JointManifoldStateTangentContinuity
variable {A E P M : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace P] [ChartedSpace A P] [IsManifold (𝓘(ℝ,A)) ∞ P]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]

def stateTangentMap (F : P × M → M) (z : P × TangentBundle (𝓘(ℝ,E)) M) :
    TangentBundle (𝓘(ℝ,E)) M :=
  ⟨F (z.1,z.2.proj),mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E))
    (fun x => F (z.1,x)) z.2.proj z.2.2⟩

theorem continuous (F : P × M → M)
    (regular : ContMDiff ((𝓘(ℝ,A)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) 1 F) :
    Continuous (stateTangentMap (E := E) F) := by
  have paired : Continuous (fun z : P × TangentBundle (𝓘(ℝ,E)) M =>
      ((zeroSection A (TangentSpace (𝓘(ℝ,A))) z.1),z.2)) :=
    ((Bundle.Trivialization.continuous_zeroSection ℝ).comp continuous_fst).prodMk continuous_snd
  have injection : Continuous (fun z : P × TangentBundle (𝓘(ℝ,E)) M =>
      (equivTangentBundleProd (𝓘(ℝ,A)) P (𝓘(ℝ,E)) M).symm
        ((zeroSection A (TangentSpace (𝓘(ℝ,A))) z.1),z.2)) :=
    (contMDiff_equivTangentBundleProd_symm (I := 𝓘(ℝ,A)) (I' := 𝓘(ℝ,E))
      (M := P) (M' := M) (n := 0)).continuous.comp paired
  have actual := (regular.continuous_tangentMap (by rfl)).comp injection
  apply actual.congr
  intro z
  apply congrArg (fun v : TangentSpace (𝓘(ℝ,E)) (F (z.1,z.2.proj)) =>
    (⟨F (z.1,z.2.proj),v⟩ : TangentBundle (𝓘(ℝ,E)) M))
  change mfderiv ((𝓘(ℝ,A)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) F (z.1,z.2.proj) (0,z.2.2) = _
  erw [mfderiv_prod_eq_add_apply (regular.mdifferentiable one_ne_zero _)]
  erw [map_zero,zero_add]

theorem continuousOn (F : P × M → M) (S : Set P) (openS : IsOpen S)
    (regular : ContMDiffOn ((𝓘(ℝ,A)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) 1 F (S ×ˢ univ)) :
    ContinuousOn (stateTangentMap (E := E) F) (S ×ˢ (univ : Set (TangentBundle (𝓘(ℝ,E)) M))) := by
  have paired : Continuous (fun z : P × TangentBundle (𝓘(ℝ,E)) M =>
      ((zeroSection A (TangentSpace (𝓘(ℝ,A))) z.1),z.2)) :=
    ((Bundle.Trivialization.continuous_zeroSection ℝ).comp continuous_fst).prodMk continuous_snd
  have injection : Continuous (fun z : P × TangentBundle (𝓘(ℝ,E)) M =>
      (equivTangentBundleProd (𝓘(ℝ,A)) P (𝓘(ℝ,E)) M).symm
        ((zeroSection A (TangentSpace (𝓘(ℝ,A))) z.1),z.2)) :=
    (contMDiff_equivTangentBundleProd_symm (I := 𝓘(ℝ,A)) (I' := 𝓘(ℝ,E))
      (M := P) (M' := M) (n := 0)).continuous.comp paired
  have openSource : IsOpen (S ×ˢ (univ : Set M)) := openS.prod isOpen_univ
  have actual := (regular.continuousOn_tangentMapWithin (by rfl) openSource.uniqueMDiffOn).comp
    injection.continuousOn (s := S ×ˢ (univ : Set (TangentBundle (𝓘(ℝ,E)) M)))
    (fun z hz => show (z.1,z.2.proj) ∈ S ×ˢ (univ : Set M) from ⟨hz.1,mem_univ _⟩)
  apply actual.congr
  intro z hz
  have atPoint := openSource.mem_nhds (show (z.1,z.2.proj) ∈ S ×ˢ (univ : Set M) from
    ⟨hz.1,mem_univ _⟩)
  have localRegular := (regular (z.1,z.2.proj) ⟨hz.1,mem_univ _⟩).contMDiffAt atPoint
  symm
  apply congrArg (fun v : TangentSpace (𝓘(ℝ,E)) (F (z.1,z.2.proj)) =>
    (⟨F (z.1,z.2.proj),v⟩ : TangentBundle (𝓘(ℝ,E)) M))
  change mfderivWithin ((𝓘(ℝ,A)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) F (S ×ˢ univ)
    (z.1,z.2.proj) (0,z.2.2) = _
  erw [mfderivWithin_of_mem_nhds atPoint,
    mfderiv_prod_eq_add_apply (localRegular.mdifferentiableAt one_ne_zero)]
  erw [map_zero,zero_add]

end LeanShared.JointManifoldStateTangentContinuity
