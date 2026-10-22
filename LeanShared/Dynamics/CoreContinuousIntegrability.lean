module

public import Mathlib.Topology.TietzeExtension
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-! A potential continuous only on a compact core is genuinely integrable
for every finite measure supported on that core, with an actual bound. -/
public noncomputable section
open Set MeasureTheory Filter
open scoped BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem bounded_integrable_of_continuousOn_compact (K : Set X) (compact : IsCompact K)
    (f : X → ℝ) (continuous : ContinuousOn f K) (μ : Measure X) [IsFiniteMeasure μ]
    (supported : μ Kᶜ=0) : ∃ B : ℝ, 0 ≤ B ∧ (∀ x ∈ K, |f x| ≤ B) ∧ Integrable f μ := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp compact
  let fk : K →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨(fun x => f x.val),continuous.domRestrict⟩
  obtain ⟨g,_,extension⟩ := fk.exists_extension_norm_eq_of_isClosedEmbedding
    compact.isClosed.isClosedEmbedding_subtypeVal
  have equal (x : X) (hx : x ∈ K) : g x=f x := congrFun extension ⟨x,hx⟩
  refine ⟨‖g‖,norm_nonneg _,fun x hx => ?_,?_⟩
  · rw [←equal x hx]
    exact g.norm_coe_le_norm x
  · apply (g.integrable μ).congr
    filter_upwards [mem_ae_iff.mpr supported] with x hx
    exact equal x hx

end LeanShared.ThermodynamicDefinitions
