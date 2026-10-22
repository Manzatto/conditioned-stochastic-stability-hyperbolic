module

public import LeanShared.Probability.EigenvectorMeasure
public import Mathlib.MeasureTheory.Measure.Support

/-!
# Product support from continuity on a conull region

This relative version only requires continuity on the compact state region;
the eigenfunction need not have a continuous ambient extension.
-/

@[expose] public noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace LeanShared.PositiveSupportLocalization

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- A positive continuous-on-region density preserves every supported point
in that conull region. -/
theorem mem_support_withDensity_of_pos (μ : Measure X) (K : Set X)
    (hμK : ∀ᵐ x ∂μ, x ∈ K) (g : X → ℝ) (hg : Measurable g)
    (hgc : ContinuousOn g K) {x : X} (hx : x ∈ μ.support) (hxK : x ∈ K)
    (hgx : 0 < g x) : x ∈ (μ.withDensity fun y => ENNReal.ofReal (g y)).support := by
  rw [Measure.support_eq_forall_isOpen]
  intro V hxV hV
  have hevent : {y | 0 < g y} ∈ 𝓝[K] x := (hgc x hxK) (lt_mem_nhds hgx)
  obtain ⟨O, hO, hOg⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hevent
  obtain ⟨W, hWO, hW, hxW⟩ := mem_nhds_iff.mp hO
  have hpos : 0 < μ (W ∩ V) :=
    (Measure.mem_support_iff_forall x).mp hx _ ((hW.inter hV).mem_nhds ⟨hxW, hxV⟩)
  have heq : μ ((W ∩ V) ∩ K) = μ (W ∩ V) := by
    apply measure_congr
    filter_upwards [hμK] with y hy
    simp only [mem_inter_iff, hy, and_true]
  have hsub : (W ∩ V) ∩ K ⊆ {y | ENNReal.ofReal (g y) ≠ 0} ∩ V := by
    rintro y ⟨⟨hyW, hyV⟩, hyK⟩
    exact ⟨ENNReal.ofReal_ne_zero_iff.mpr (hOg ⟨hWO hyW, hyK⟩), hyV⟩
  apply pos_iff_ne_zero.mpr
  intro hzero
  have hz : μ ({y | ENNReal.ofReal (g y) ≠ 0} ∩ V) = 0 :=
    (withDensity_apply_eq_zero hg.ennreal_ofReal).mp hzero
  have hle : μ (W ∩ V) ≤ 0 := by
    rw [← heq]
    exact (measure_mono hsub).trans_eq hz
  exact (not_le_of_gt hpos) hle

theorem mem_live_of_pos_supported (μ : Measure X) (K V : Set X)
    (hμK : ∀ᵐ x ∂μ, x ∈ K) (g : X → ℝ) (hg : Measurable g)
    (hgc : ContinuousOn g K) (hν : (eigenvectorMeasure μ g).support ⊆ V)
    {x : X} (hx : x ∈ μ.support) (hxK : x ∈ K) (hgx : 0 < g x) : x ∈ V :=
  hν (mem_support_withDensity_of_pos μ K hμK g hg hgc hx hxK hgx)

end LeanShared.PositiveSupportLocalization
