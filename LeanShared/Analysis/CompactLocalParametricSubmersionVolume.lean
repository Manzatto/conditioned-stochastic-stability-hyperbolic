module
public import LeanShared.Analysis.CompactParametricSubmersionVolume
public import LeanShared.Analysis.CompactSmoothExtension

/-! Uniform every-state volume domination uses only C1 regularity on an open
neighborhood of the compact state/control patch. No global continuation of the
given random maps is assumed. -/
public noncomputable section
namespace LeanShared.SubmersionLinearCoordinates
open Set MeasureTheory Filter
open scoped ENNReal Topology

theorem exists_uniform_volume_bound_of_neighborhood
    {X A Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace A] [BorelSpace A]
    [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) (ρ : Measure A) (σ : Measure Y)
    [μ.IsAddHaarMeasure] [ρ.IsAddHaarMeasure] [σ.IsAddHaarMeasure]
    {K : Set X} {L : Set A} (compactK : IsCompact K) (compactL : IsCompact L)
    {f : X × A → Y} {O : Set (X × A)}
    (openO : IsOpen O) (contained : K ×ˢ L ⊆ O) (smooth : ContDiffOn ℝ 1 f O)
    (rank : ∀ x ∈ K, ∀ a ∈ L,
      Function.Surjective (fderiv ℝ (fun b => f (x, b)) a)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ x ∈ interior K, (ρ.restrict L).map (fun a => f (x, a)) ≤ C • σ := by
  obtain ⟨g, smoothG, near⟩ := CompactSmoothExtension.exists_extension
    (compactK.prod compactL) openO contained smooth
  have rankG (x : X) (hx : x ∈ K) (a : A) (ha : a ∈ L) :
      Function.Surjective (fderiv ℝ (fun b => g (x, b)) a) := by
    have partialEq := (near (x, a) ⟨hx, ha⟩).comp_tendsto
      (continuous_const.prodMk continuous_id).continuousAt
    have derivativeEq : fderiv ℝ (fun b => g (x, b)) a =
        fderiv ℝ (fun b => f (x, b)) a := partialEq.fderiv_eq
    rw [derivativeEq]
    exact rank x hx a ha
  obtain ⟨C, finiteC, bound⟩ := exists_uniform_volume_bound μ ρ σ compactK compactL
    smoothG.continuous (fun _ _ _ _ => smoothG.contDiffAt) rankG
  refine ⟨C, finiteC, ?_⟩
  intro x hx
  have same : (ρ.restrict L).map (fun a => g (x, a)) =
      (ρ.restrict L).map (fun a => f (x, a)) := by
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem compactL.measurableSet] with a ha
    exact (near (x, a) ⟨interior_subset hx, ha⟩).eq_of_nhds
  rw [← same]
  exact bound x hx

end LeanShared.SubmersionLinearCoordinates
