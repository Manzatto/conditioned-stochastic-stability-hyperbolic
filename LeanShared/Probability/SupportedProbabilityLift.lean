module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Restrict

/-! A probability carried by a measurable subset has a canonical probability
on the literal subtype. Its ambient pushforward and uniqueness are exact. -/

@[expose] public noncomputable section
open Set MeasureTheory
namespace LeanShared.SupportedProbabilityLift
variable {X : Type*} [MeasurableSpace X]
  (K : Set X) (hK : MeasurableSet K) (ν : ProbabilityMeasure X)
  (carried : (ν : Measure X) Kᶜ = 0)

include carried in
private theorem ae_mem : ∀ᵐ x ∂(ν : Measure X), x ∈ K := by
  exact ae_iff.mpr carried

def probability : ProbabilityMeasure K := by
  have hprob : IsProbabilityMeasure ((ν : Measure X).comap (Subtype.val : K → X)) :=
    (MeasurableEmbedding.subtype_coe hK).isProbabilityMeasure_comap (by
      simpa only [Subtype.range_coe] using ae_mem K ν carried)
  exact ⟨(ν : Measure X).comap Subtype.val, hprob⟩

theorem map_probability :
    ((probability K hK ν carried : ProbabilityMeasure K) : Measure K).map Subtype.val =
      (ν : Measure X) := by
  change ((ν : Measure X).comap (Subtype.val : K → X)).map Subtype.val = _
  rw [map_comap_subtype_coe hK]
  exact Measure.restrict_eq_self_of_ae_mem (ae_mem K ν carried)

theorem unique (ζ : ProbabilityMeasure K)
    (hζ : (ζ : Measure K).map Subtype.val = (ν : Measure X)) :
    ζ = probability K hK ν carried := by
  apply Subtype.ext
  exact ((MeasurableEmbedding.subtype_coe hK).map_injective)
    (hζ.trans (map_probability K hK ν carried).symm)

end LeanShared.SupportedProbabilityLift
