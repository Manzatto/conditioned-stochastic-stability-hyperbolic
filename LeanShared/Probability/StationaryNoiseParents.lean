module

public import LeanShared.Probability.NoiseEigenmeasureSupport

/-! Exact ambient parents of a stationary mapped measure. Compactness is
needed only for its ambient support, so an open Doob state space is allowed. -/

@[expose] public noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LeanShared.NoiseEigenmeasureSupport

variable {Z X Ω : Type*} [MeasurableSpace Z]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X]
  [TopologicalSpace Ω] [CompactSpace Ω]

/-- Stationarity and actual noise images give exact parents in the compact
ambient support. No compactness of the positive Doob-state subtype is used. -/
theorem exists_support_parent_of_stationary_map
    (κ : Kernel Z Z) (η : Measure Z) (hstation : κ ∘ₘ η = η)
    (i : Z → X) (hi : Measurable i) (ν : Measure X) (hmap : η.map i = ν)
    (hcompact : IsCompact ν.support) (hae : ∀ᵐ x ∂ν, x ∈ ν.support)
    (F : X × Ω → X) (hF : Continuous F)
    (hstep : ∀ z : Z, ∀ᵐ y ∂κ z, ∃ ω : Ω, F (i z, ω) = i y)
    (p : X) (hp : p ∈ ν.support) :
    ∃ x ∈ ν.support, ∃ ω : Ω, F (x, ω) = p := by
  let S : Set X := F '' (ν.support ×ˢ (univ : Set Ω))
  have hS : IsClosed S := ((hcompact.prod isCompact_univ).image hF).isClosed
  have hiS : MeasurableSet (i ⁻¹' S) := hS.measurableSet.preimage hi
  have hsource : ∀ᵐ z ∂η, i z ∈ ν.support := by
    have hh : ∀ᵐ x ∂η.map i, x ∈ ν.support := hmap.symm ▸ hae
    exact (ae_map_iff hi.aemeasurable ν.isClosed_support.measurableSet).mp hh
  have htarget : ∀ᵐ y ∂κ ∘ₘ η, i y ∈ S := by
    apply Measure.ae_comp_of_ae_ae hiS
    filter_upwards [hsource] with z hz
    filter_upwards [hstep z] with y hy
    obtain ⟨ω, hω⟩ := hy
    exact ⟨(i z, ω), ⟨hz, mem_univ _⟩, hω⟩
  rw [hstation] at htarget
  have hνS : ∀ᵐ x ∂ν, x ∈ S := by
    rw [← hmap]
    exact (ae_map_iff hi.aemeasurable hS.measurableSet).mpr htarget
  have hpS := ν.support_subset_of_isClosed hS hνS hp
  obtain ⟨⟨x, ω⟩, hx, heq⟩ := hpS
  exact ⟨x, hx.1, ω, heq⟩

end LeanShared.NoiseEigenmeasureSupport
