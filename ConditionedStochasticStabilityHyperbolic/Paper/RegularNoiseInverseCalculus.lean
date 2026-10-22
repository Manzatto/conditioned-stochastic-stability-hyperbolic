module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseActualDiffeomorphisms
public import LeanShared.Geometry.CompactParametricInverseDomain
public import LeanShared.Geometry.OpenParameterExtension

/-! The original perturbations admit an actual jointly C1 inverse on an open
neighborhood of their whole legal control cube. No linear inverse Whitney
estimate is claimed or needed for this calculus statement. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set IsManifold Filter
open scoped Topology Manifold ContDiff NNReal

set_option maxHeartbeats 3200000 in
theorem Maps.exists_inverse_calculus
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm) (default : M) :
    ∃ η : ℝ≥0, 0 < η ∧ η ≤ F.window ∧ ∀ ε : ℝ≥0, 0 < ε → ε ≤ η →
      ∃ J : Control (ι := ι) × M → M, ∃ U : Set (Control (ι := ι)),
        IsOpen U ∧ (LeanShared.NoiseCubeRescaling.cube (ι := ι) ε : Set _) ⊆ U ∧
        ContMDiffOn ((𝓘(ℝ,Control (ι := ι))).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) 1 J (U ×ˢ univ) ∧
        (∀ a ∈ U, ∀ y, F.family ε a (J (a,y)) = y) ∧
        (∀ a ∈ U, ∀ x, J (a,F.family ε a x) = x) ∧
        ∀ a : cube (ι := ι) ε, ∀ y,
          Function.Bijective (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (F.family ε a.val) (J (a.val,y))) := by
  classical
  obtain ⟨ηh,positiveH,windowH,homeos⟩ := F.exists_actual_homeomorphisms regularity deterministic inverse
  obtain ⟨ηd,positiveD,differentials⟩ := F.exists_global_differential_window regularity deterministic inverse
  refine ⟨min ηh ηd,lt_min positiveH positiveD,(min_le_left _ _).trans windowH,fun ε hp hw => ?_⟩
  obtain ⟨H,identity,_continuousInverse⟩ := homeos ε hp (hw.trans (min_le_left _ _))
  obtain ⟨O,openO,cubeO,smooth⟩ := F.joint_C1 ε hp ((hw.trans (min_le_left _ _)).trans windowH)
  let P : TopologicalSpace.Opens (Control (ι := ι)) := ⟨O,openO⟩
  let f : P × M → M := fun p => F.family ε p.1.val p.2
  let lift : cube (ι := ι) ε → P := fun a => ⟨a.val,cubeO a.property⟩
  have continuousLift : Continuous lift := continuous_subtype_val.subtype_mk _
  have smoothF : ContMDiff ((𝓘(ℝ,Control (ι := ι))).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) 1 f := by
    exact smooth.comp_contMDiff
      ((contMDiff_subtype_val.comp contMDiff_fst).prodMk contMDiff_snd)
      (fun p => ⟨p.1.property,mem_univ _⟩)
  have bijective : ∀ a ∈ range lift, Function.Bijective (fun z => f (a,z)) := by
    rintro _ ⟨a,rfl⟩
    have eq : (fun z => f (lift a,z)) = H a := funext (fun z => (identity a z).symm)
    rw [eq]
    exact (H a).bijective
  have rank : ∀ a ∈ range lift, ∀ x,
      Function.Bijective (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (fun z => f (a,z)) x) := by
    rintro _ ⟨a,rfl⟩ x
    exact differentials ε hp (hw.trans (min_le_right _ _)) a x
  obtain ⟨V,openV,containsV,regular,right,left⟩ := LeanShared.CompactParametricInverseDomain.exists_domain
    f smoothF.continuous (range lift) (isCompact_range continuousLift) default
    (fun a _ x => smoothF.contMDiffAt) bijective rank
  let J := LeanShared.OpenParameterExtension.extend P
    (LeanShared.CompactLocalInverseUniqueness.root f default) default
  refine ⟨J,Subtype.val '' V,openO.isOpenMap_subtype_val _ openV,?_,?_,?_,?_,?_⟩
  · intro a ha
    exact ⟨lift ⟨a,ha⟩,containsV (mem_range_self _),rfl⟩
  · rintro ⟨a,y⟩ ⟨⟨u,hu,rfl⟩,_⟩
    exact (LeanShared.OpenParameterExtension.contMDiffAt P _ default u y
      ((regular (u,y) ⟨hu,mem_univ _⟩).contMDiffAt
        ((openV.prod isOpen_univ).mem_nhds ⟨hu,mem_univ _⟩))).contMDiffWithinAt
  · rintro a ⟨u,hu,rfl⟩ y
    simpa only [J,LeanShared.OpenParameterExtension.extend,dite_eq_left u.property] using right u hu y
  · rintro a ⟨u,hu,rfl⟩ x
    simpa only [J,LeanShared.OpenParameterExtension.extend,dite_eq_left u.property] using left u hu x
  · intro a y
    exact differentials ε hp (hw.trans (min_le_right _ _)) a _

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
