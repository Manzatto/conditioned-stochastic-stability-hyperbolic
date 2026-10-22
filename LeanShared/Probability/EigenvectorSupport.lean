module

public import LeanShared.Probability.EigenvectorMeasure
public import Mathlib.MeasureTheory.Measure.Support

/-!
# Positive supported seeds and eigenvector-product support

Normalization gives a positive eigenfunction value in the left measure's
support. A continuous positive density preserves support at that point.
Thus localization of the product measure places every such supported positive
point in the live interior, without assuming a continuous left density.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace LeanShared

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

omit [BorelSpace X] in
theorem exists_support_pos_of_integral_pos (μ : Measure X) (g : X → ℝ)
    (hμae : ∀ᵐ x ∂μ, x ∈ μ.support) (hpos : 0 < ∫ x, g x ∂μ) :
    ∃ x ∈ μ.support, 0 < g x := by
  by_contra hn
  have hnonpos : ∀ᵐ x ∂μ, g x ≤ 0 := by
    filter_upwards [hμae] with x hx
    exact le_of_not_gt (fun hp => hn ⟨x, hx, hp⟩)
  exact (not_le_of_gt hpos) (integral_nonpos_of_ae hnonpos)

theorem mem_support_eigenvectorMeasure_of_pos (μ : Measure X) (g : X → ℝ)
    (hg : Continuous g) (x : X) (hx : x ∈ μ.support) (hpos : 0 < g x) :
    x ∈ (eigenvectorMeasure μ g).support := by
  rw [Measure.support_eq_forall_isOpen]
  intro V hxV hV
  rw [eigenvectorMeasure, withDensity_apply _ hV.measurableSet]
  apply (lintegral_pos_iff_support hg.measurable.ennreal_ofReal).mpr
  let W := V ∩ {y | 0 < g y}
  have hW : IsOpen W := hV.inter (isOpen_lt continuous_const hg)
  have hμW : 0 < μ W := (Measure.mem_support_iff_forall x).mp hx W
    (hW.mem_nhds ⟨hxV, hpos⟩)
  apply hμW.trans_le
  rw [Measure.restrict_apply (measurableSet_support hg.measurable.ennreal_ofReal)]
  apply measure_mono
  intro y hy
  exact ⟨ENNReal.ofReal_ne_zero_iff.mpr hy.2, hy.1⟩

theorem support_pos_mem_of_product_localized (μ : Measure X) (g : X → ℝ)
    (hg : Continuous g) (V : Set X) (hlocal : (eigenvectorMeasure μ g).support ⊆ V)
    (x : X) (hx : x ∈ μ.support) (hpos : 0 < g x) : x ∈ V :=
  hlocal (mem_support_eigenvectorMeasure_of_pos μ g hg x hx hpos)

theorem exists_live_support_pos_of_normalized (μ : Measure X) (g : X → ℝ)
    (hg : Continuous g) (hμae : ∀ᵐ x ∂μ, x ∈ μ.support)
    (hnorm : ∫ x, g x ∂μ = 1) (V : Set X)
    (hlocal : (eigenvectorMeasure μ g).support ⊆ V) :
    ∃ x ∈ V, x ∈ μ.support ∧ 0 < g x := by
  obtain ⟨x, hx, hpos⟩ := exists_support_pos_of_integral_pos μ g hμae
    (by rw [hnorm]; exact zero_lt_one)
  exact ⟨x, support_pos_mem_of_product_localized μ g hg V hlocal x hx hpos, hx, hpos⟩

end LeanShared
