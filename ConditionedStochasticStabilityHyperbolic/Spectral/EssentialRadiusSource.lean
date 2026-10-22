module

public import LeanShared.Analysis.CompactTwoNormFredholm
public import ConditionedStochasticStabilityHyperbolic.Spectral.EssentialRadiusBridge

/-! Discharge of the compact-two-norm Fredholm source. The contract needed
by KL asks for injective spectral shifts to be surjective above the strong
growth rate. The descending-range compactness proof constructs precisely
this result; no essential-radius, index, or perturbation contract is assumed. -/

public section

namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- The deferred essential-radius/Fredholm source follows from compact weak inclusion and the actual
all-power two-norm bound. -/
theorem essentialRadiusContract : EssentialRadiusContract (E := E) (W := W) := by
  intro P i _ hic α R C D _ hα hαR hC hD _ _ hstrong z hz hinj
  have hnegative : Function.Injective (P - z • 1 : E →L[ℂ] E) := by
    intro x y hxy
    apply hinj
    have hh := congrArg Neg.neg hxy
    simpa only [sub_apply, smul_apply, one_apply_eq_self, neg_sub] using hh
  have surj := LeanShared.CompactTwoNormFredholm.surjective_of_twoNorm P i hic α R C D
    hα.le (hα.le.trans hαR.le) hC hD hstrong z hz hnegative
  intro y
  obtain ⟨x, hx⟩ := surj (-y)
  refine ⟨x, ?_⟩
  have hh := congrArg Neg.neg hx
  simpa only [sub_apply, smul_apply, one_apply_eq_self, neg_sub, neg_neg] using hh

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
