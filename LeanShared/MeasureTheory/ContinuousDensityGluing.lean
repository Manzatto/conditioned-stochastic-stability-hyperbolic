module
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Topology.Compactness.Compact

/-! Continuous positive local Radon--Nikodym densities glue uniquely to a
genuine global density. Equality on overlaps is derived from the measures,
not supplied as a compatibility field. -/
public noncomputable section
namespace LeanShared.ContinuousDensityGluing
open Set MeasureTheory Measure Filter
open scoped Topology ENNReal

set_option maxHeartbeats 1600000 in
theorem exists_density
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (U : X → Set X) (openU : ∀ x, IsOpen (U x)) (contains : ∀ x, x ∈ U x)
    (f : X → X → ℝ) (continuous : ∀ x, ContinuousOn (f x) (U x))
    (positive : ∀ x, ∀ y ∈ U x, 0 < f x y)
    (localLaw : ∀ x, ν.restrict (U x) = (μ.restrict (U x)).withDensity (fun y => ENNReal.ofReal (f x y))) :
    ∃ g : X → ℝ, Continuous g ∧ (∀ x, 0 < g x) ∧
      ν = μ.withDensity (fun x => ENNReal.ofReal (g x)) ∧ ∀ x, EqOn g (f x) (U x) := by
  have compatibility (a b : X) : EqOn (f a) (f b) (U a ∩ U b) := by
    have lawA : ν.restrict (U a ∩ U b) = (μ.restrict (U a ∩ U b)).withDensity
        (fun y => ENNReal.ofReal (f a y)) := by
      rw [inter_comm,←Measure.restrict_restrict' (openU a).measurableSet,
        localLaw a,restrict_withDensity (openU b).measurableSet,
        Measure.restrict_restrict' (openU a).measurableSet]
    have lawB : ν.restrict (U a ∩ U b) = (μ.restrict (U a ∩ U b)).withDensity
        (fun y => ENNReal.ofReal (f b y)) := by
      rw [←Measure.restrict_restrict' (openU b).measurableSet,
        localLaw b,restrict_withDensity (openU a).measurableSet,
        Measure.restrict_restrict' (openU b).measurableSet]
    have fa := (continuous a).mono (show U a ∩ U b ⊆ U a from inter_subset_left)
    have fb := (continuous b).mono (show U a ∩ U b ⊆ U b from inter_subset_right)
    have measurableSet := ((openU a).inter (openU b)).measurableSet
    have equal := (withDensity_eq_iff_of_sigmaFinite
      (fa.aemeasurable measurableSet).ennreal_ofReal
      (fb.aemeasurable measurableSet).ennreal_ofReal).mp (lawA.symm.trans lawB)
    have realEqual : f a =ᵐ[μ.restrict (U a ∩ U b)] f b := by
      filter_upwards [equal,ae_restrict_mem measurableSet] with x hx hmem
      simpa only [ENNReal.toReal_ofReal (positive a x hmem.1).le,
        ENNReal.toReal_ofReal (positive b x hmem.2).le] using congrArg ENNReal.toReal hx
    exact eqOn_open_of_ae_eq realEqual ((openU a).inter (openU b)) fa fb
  let g : X → ℝ := fun x => f x x
  have same (a : X) : EqOn g (f a) (U a) := by
    intro x hx
    exact (compatibility a x ⟨hx,contains x⟩).symm
  have continuousG : Continuous g := continuous_iff_continuousAt.mpr (fun x => by
    apply ((continuous x).continuousAt ((openU x).mem_nhds (contains x))).congr_of_eventuallyEq
    filter_upwards [(openU x).mem_nhds (contains x)] with y hy
    exact same x hy)
  refine ⟨g,continuousG,fun x => positive x x (contains x),?_,same⟩
  have restrictions (a : X) : ν.restrict (U a) =
      (μ.withDensity (fun x => ENNReal.ofReal (g x))).restrict (U a) := by
    rw [localLaw a,restrict_withDensity (openU a).measurableSet]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem (openU a).measurableSet] with x hx
    exact congrArg ENNReal.ofReal (same a hx).symm
  obtain ⟨s,cover⟩ := isCompact_univ.elim_finite_subcover U openU (by
    intro x _
    exact mem_iUnion.mpr ⟨x,contains x⟩)
  have full : ⋃ i : s, U i.val = univ := by
    apply eq_univ_of_univ_subset
    intro x hx
    obtain ⟨i,hi,inside⟩ := mem_iUnion₂.mp (cover hx)
    exact mem_iUnion.mpr ⟨⟨i,hi⟩,inside⟩
  rw [←Measure.restrict_univ (μ := ν),←Measure.restrict_univ (μ := μ.withDensity _),←full]
  exact Measure.restrict_iUnion_congr.mpr (fun i => restrictions i.val)

end LeanShared.ContinuousDensityGluing
