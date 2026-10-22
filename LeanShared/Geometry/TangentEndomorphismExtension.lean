module
public import LeanShared.Geometry.LocalBundleEndomorphism
public import LeanShared.Geometry.ContinuousBundleFiniteSum
public import LeanShared.Geometry.TangentChartTrivialization
public import LeanShared.Geometry.ConstructedManifoldLocalization
public import LeanShared.Analysis.FiniteDimensionalTietze

/-! An actual continuous tangent endomorphism on a compact closed core
extends to a global continuous endomorphism. The finite atlas, smooth
partition, coordinate extensions and chart-boundary continuity are built. -/
public noncomputable section
namespace LeanShared.TangentEndomorphismExtension
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle BigOperators
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]

theorem exists_extension (K : Set M) (compact : IsCompact K)
    (P : ∀ x : M, TangentSpace (𝓘(ℝ,E)) x →L[ℝ] TangentSpace (𝓘(ℝ,E)) x)
    (continuous : ContinuousOn
      (fun v : TotalSpace E (TangentSpace (𝓘(ℝ,E))) =>
        (⟨v.proj,P v.proj v.2⟩ : TotalSpace E (TangentSpace (𝓘(ℝ,E)))))
      {v | v.proj ∈ K}) :
    ∃ Q : ∀ x : M, TangentSpace (𝓘(ℝ,E)) x →L[ℝ] TangentSpace (𝓘(ℝ,E)) x,
      Continuous (fun v : TotalSpace E (TangentSpace (𝓘(ℝ,E))) =>
        (⟨v.proj,Q v.proj v.2⟩ : TotalSpace E (TangentSpace (𝓘(ℝ,E))))) ∧
      ∀ x ∈ K, Q x=P x := by
  classical
  let d := ConstructedManifoldLocalization.data (chartAt E : M → OpenPartialHomeomorph M E)
    compact (fun x _ => mem_iUnion.mpr ⟨x,mem_chart_source E x⟩)
  let θ := fun i : d.indices => fun x : M => (d.cutoff i x).re
  let e := fun i : d.indices => trivializationAt E (TangentSpace (𝓘(ℝ,E))) i.val
  have support (i : d.indices) : tsupport (θ i) ⊆ (e i).baseSet := by
    rw [show (e i).baseSet=(chartAt E i.val).source from TangentChartTrivialization.baseSet i.val]
    exact (tsupport_comp_subset (show Complex.re 0=0 from rfl) (d.cutoff i)).trans (d.support i)
  have continuousθ (i : d.indices) : Continuous (θ i) := Complex.reCLM.continuous.comp (d.smooth i).continuous
  have partition (x : M) (hx : x ∈ K) : ∑ i : d.indices, θ i x=1 := by
    have result := congrArg Complex.reCLM (d.partition x hx)
    rw [map_sum,show Complex.reCLM 1=(1:ℝ) from rfl] at result
    exact result
  have extensions (i : d.indices) : ∃ G : M → E →L[ℝ] E, Continuous G ∧
      EqOn G (BundleEndomorphismCoordinates.coordinates (TangentSpace (𝓘(ℝ,E))) (e i) P)
        (K∩tsupport (θ i)) := by
    apply FiniteDimensionalTietze.exists_extension (K∩tsupport (θ i))
      (compact.isClosed.inter (isClosed_tsupport _))
    exact (BundleEndomorphismCoordinates.continuousOn_coordinates
      (TangentSpace (𝓘(ℝ,E))) (e i) P K continuous).mono
      (fun x hx => ⟨hx.1,support i hx.2⟩)
  choose G continuousG agreesG using extensions
  let Q := fun x => ∑ i : d.indices, LocalBundleEndomorphism.decode
    (TangentSpace (𝓘(ℝ,E))) (e i) (fun y => θ i y • G i y) x
  refine ⟨Q,?_,?_⟩
  · have individual (i : d.indices) := LocalBundleEndomorphism.continuous_cutoff_action
      (TangentSpace (𝓘(ℝ,E))) (e i) (θ i) (continuousθ i) (support i) (G i) (continuousG i)
    have total := ContinuousBundleFiniteSum.continuous (TangentSpace (𝓘(ℝ,E))) Finset.univ
      (Bundle.TotalSpace.proj : TotalSpace E (TangentSpace (𝓘(ℝ,E))) → M)
      (fun i v => LocalBundleEndomorphism.decode (TangentSpace (𝓘(ℝ,E))) (e i)
        (fun y => θ i y • G i y) v.proj v.2)
      (FiberBundle.continuous_proj _ _) (fun i _ => individual i)
    simpa only [Q,sum_apply] using total
  · intro x hx
    have local_eq (i : d.indices) : LocalBundleEndomorphism.decode (TangentSpace (𝓘(ℝ,E)))
        (e i) (fun y => θ i y • G i y) x=θ i x • P x := by
      by_cases zero : θ i x=0
      · ext v
        simp only [LocalBundleEndomorphism.decode,ContinuousLinearMap.comp_apply,zero,
          zero_smul,zero_apply,map_zero]
      · have inSupport : x ∈ tsupport (θ i) := subset_tsupport _ zero
        have inside := support i inSupport
        have coordinate := agreesG i ⟨hx,inSupport⟩
        ext v
        simp only [LocalBundleEndomorphism.decode,ContinuousLinearMap.comp_apply,
          smul_apply,coordinate,BundleEndomorphismCoordinates.coordinates,map_smul,
          (e i).symmL_continuousLinearMapAt inside]
    change (∑ i : d.indices, LocalBundleEndomorphism.decode (TangentSpace (𝓘(ℝ,E)))
      (e i) (fun y => θ i y • G i y) x)=P x
    simp only [local_eq]
    rw [← Finset.sum_smul,partition x hx,one_smul]
end LeanShared.TangentEndomorphismExtension
