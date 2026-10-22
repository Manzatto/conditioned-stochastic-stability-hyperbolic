module
public import LeanShared.Analysis.CompactSubmersionVolumeBound
public import LeanShared.Analysis.EndpointDerivativeSurjective
public import LeanShared.Analysis.RestrictedParametricVolumeDomination

/-! A compact family of C1 full-control-rank maps has one source-to-target
volume bound valid at every state in the interior of the state chart patch.
The bound is produced from differential rank, compactness, and Haar volume. -/
public noncomputable section
namespace LeanShared.SubmersionLinearCoordinates
open Set MeasureTheory
open scoped ENNReal

theorem exists_uniform_volume_bound
    {X A Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace A] [BorelSpace A]
    [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) (ρ : Measure A) (σ : Measure Y)
    [μ.IsAddHaarMeasure] [ρ.IsAddHaarMeasure] [σ.IsAddHaarMeasure]
    {K : Set X} {L : Set A} (compactK : IsCompact K) (compactL : IsCompact L)
    {f : X × A → Y} (continuousF : Continuous f)
    (smooth : ∀ x ∈ K, ∀ a ∈ L, ContDiffAt ℝ 1 f (x, a))
    (rank : ∀ x ∈ K, ∀ a ∈ L,
      Function.Surjective (fderiv ℝ (fun b => f (x, b)) a)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ x ∈ interior K, (ρ.restrict L).map (fun a => f (x, a)) ≤ C • σ := by
  have endpointSmooth (z : X × A) (hz : z ∈ K ×ˢ L) :
      ContDiffAt ℝ 1 (fun z : X × A => (z.1, f z)) z :=
    contDiff_fst.contDiffAt.prodMk (smooth z.1 hz.1 z.2 hz.2)
  have endpointRank (z : X × A) (hz : z ∈ K ×ˢ L) :
      Function.Surjective (fderiv ℝ (fun z : X × A => (z.1, f z)) z) :=
    endpoint_fderiv_surjective ((smooth z.1 hz.1 z.2 hz.2).differentiableAt one_ne_zero)
      (rank z.1 hz.1 z.2 hz.2)
  obtain ⟨C, finiteC, joint⟩ := exists_compact_submersion_volume_bound
    (μ.prod ρ) (μ.prod σ) (compactK.prod compactL) endpointSmooth endpointRank
  rw [← Measure.prod_restrict] at joint
  have restricted := ParametricVolumeDomination.restrict_joint_endpoint_bound
    μ (ρ.restrict L) σ K compactK.measurableSet continuousF.measurable C joint
  exact ⟨C, finiteC, ParametricVolumeDomination.fiber_bound_on_interior
    μ (ρ.restrict L) σ K continuousF C finiteC restricted⟩

end LeanShared.SubmersionLinearCoordinates
