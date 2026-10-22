module
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.Semicontinuity.Basic

/-! Open-set masses of continuous random maps are lower semicontinuous in
the starting state. Full-support reference volume therefore upgrades almost
everywhere domination to domination at every starting state. -/
public noncomputable section
namespace LeanShared.OpenFiberMass
open MeasureTheory Set Filter
open scoped ENNReal

theorem lowerSemicontinuous_section
    {X A : Type*} [TopologicalSpace X] [TopologicalSpace A]
    [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) [μ.Regular] {U : Set (X × A)} (openU : IsOpen U) :
    LowerSemicontinuous (fun x => μ {a | (x, a) ∈ U}) := by
  apply lowerSemicontinuous_iff_isOpen_preimage.mpr
  intro c
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  have fiberOpen : IsOpen {a | (x, a) ∈ U} :=
    openU.preimage (continuous_const.prodMk continuous_id)
  obtain ⟨K, subset, compact, large⟩ := fiberOpen.exists_lt_isCompact hx
  have cylinder : ({x} : Set X) ×ˢ K ⊆ U := by
    rintro ⟨y, a⟩ ⟨hy, ha⟩
    have equal : y = x := mem_singleton_iff.mp hy
    subst y
    exact subset ha
  obtain ⟨v, w, openV, _openW, xv, kw, contained⟩ :=
    generalized_tube_lemma isCompact_singleton compact openU cylinder
  refine ⟨v, ?_, openV, xv (mem_singleton x)⟩
  intro y hy
  exact large.trans_le (measure_mono (fun a ha => contained ⟨hy, kw ha⟩))

theorem lowerSemicontinuous_pushforward_open
    {X A Y : Type*} [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace Y]
    [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) [μ.Regular] {f : X × A → Y} (continuousF : Continuous f)
    {B : Set Y} (openB : IsOpen B) :
    LowerSemicontinuous (fun x => μ {a | f (x, a) ∈ B}) :=
  lowerSemicontinuous_section μ (openB.preimage continuousF)

theorem lowerSemicontinuous_le_of_ae
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [μ.IsOpenPosMeasure]
    {f : X → ℝ≥0∞} (semicontinuous : LowerSemicontinuous f) {c : ℝ≥0∞}
    (bound : ∀ᵐ x ∂μ, f x ≤ c) : ∀ x, f x ≤ c := by
  have openBad : IsOpen {x | c < f x} := semicontinuous.isOpen_preimage c
  have zero : μ {x | c < f x} = 0 := by
    simpa only [not_le] using ae_iff.mp bound
  have empty : {x | c < f x} = ∅ := openBad.eq_empty_of_measure_zero zero
  intro x
  by_contra h
  have : x ∈ ({y | c < f y} : Set X) := lt_of_not_ge h
  simp only [empty, mem_empty_iff_false] at this

end LeanShared.OpenFiberMass
