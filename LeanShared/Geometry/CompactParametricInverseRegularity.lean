module
public import LeanShared.Geometry.ManifoldLocalInjectivity
public import LeanShared.Geometry.ManifoldLocalInverse
public import LeanShared.Geometry.ParametricSkewDifferential
public import LeanShared.Topology.CompactLocalInverseUniqueness
public import LeanShared.Geometry.ManifoldSubmersionOpen

/-! A global root choice for a compact state family is genuinely C1 near
an invertible fiber, and is a right inverse on an open target neighborhood.
Both facts are derived from actual calculus and compact root localization. -/
public noncomputable section
namespace LeanShared.CompactParametricInverseRegularity
open Set Filter IsManifold
open scoped Topology Manifold ContDiff

set_option maxHeartbeats 2400000 in
theorem local_inverse
    {A E P M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace P] [ChartedSpace A P] [IsManifold (𝓘(ℝ,A)) ∞ P]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    (F : P × M → M) (continuous : Continuous F) (a : P) (x default : M)
    (smooth : ContMDiffAt ((𝓘(ℝ,A)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) 1 F (a,x))
    (injective : Function.Injective (fun z => F (a,z)))
    (rank : Function.Bijective (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (fun z => F (a,z)) x)) :
    ContMDiffAt ((𝓘(ℝ,A)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) 1
      (CompactLocalInverseUniqueness.root F default) (a,F (a,x)) ∧
    (∀ᶠ p : P × M in 𝓝 (a,F (a,x)),
      F (p.1,CompactLocalInverseUniqueness.root F default p) = p.2) ∧
    ∀ᶠ p : P × M in 𝓝 (a,x),
      CompactLocalInverseUniqueness.root F default (p.1,F p) = p.2 := by
  let S : P × M → P × M := fun p => (p.1,F p)
  let G : P × M → P × M := fun p => (p.1,CompactLocalInverseUniqueness.root F default p)
  have originalManifold : IsManifold ((𝓘(ℝ,A)).prod (𝓘(ℝ,E))) ∞ (P × M) := inferInstance
  let _ : ChartedSpace (A × E) (P × M) :=
    inferInstanceAs (ChartedSpace (ModelProd A E) (P × M))
  let _ : IsManifold (𝓘(ℝ,A × E)) ∞ (P × M) := by
    rw [modelWithCornersSelf_prod]
    exact originalManifold
  have smoothS : ContMDiffAt (𝓘(ℝ,A × E)) (𝓘(ℝ,A × E)) 1 S (a,x) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiffAt_fst.prodMk smooth
  have rankS : Function.Bijective (mfderiv (𝓘(ℝ,A × E)) (𝓘(ℝ,A × E)) S (a,x)) := by
    rw [modelWithCornersSelf_prod]
    exact ParametricSkewDifferential.bijective (smooth.mdifferentiableAt one_ne_zero) rank
  obtain ⟨V,openV,member,locally⟩ := ManifoldLocalInjectivity.exists_neighborhood S (a,x) smoothS rankS
  have left := CompactLocalInverseUniqueness.eventually_leftInverse F continuous a x default injective V openV member locally
  have regular : ContMDiffAt (𝓘(ℝ,A × E)) (𝓘(ℝ,A × E)) 1 G (S (a,x)) :=
    ManifoldLocalInverse.contMDiffAt_of_eventually_leftInverse smoothS rankS left
  have regularProduct : ContMDiffAt ((𝓘(ℝ,A)).prod (𝓘(ℝ,E))) ((𝓘(ℝ,A)).prod (𝓘(ℝ,E))) 1 G (S (a,x)) := by
    rw [← modelWithCornersSelf_prod]
    exact regular
  have result : ContMDiffAt ((𝓘(ℝ,A)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) 1
      (CompactLocalInverseUniqueness.root F default) (a,F (a,x)) :=
    contMDiffAt_snd.comp (S (a,x)) regularProduct
  refine ⟨result,?_,left.mono (fun p hp => congrArg Prod.snd hp)⟩
  have mapNeighborhoods := SubmersionOpen.map_nhds_eq_of_mfderiv_surjective smoothS rankS.2
  have right : ∀ᶠ p in 𝓝 (a,x), S (G (S p)) = S p := by
    filter_upwards [left] with p hp
    exact congrArg S hp
  have mapped : ∀ᶠ p in 𝓝 (S (a,x)), S (G p) = p := by
    rw [← mapNeighborhoods]
    exact right
  filter_upwards [mapped] with p hp
  exact congrArg Prod.snd hp

end LeanShared.CompactParametricInverseRegularity
