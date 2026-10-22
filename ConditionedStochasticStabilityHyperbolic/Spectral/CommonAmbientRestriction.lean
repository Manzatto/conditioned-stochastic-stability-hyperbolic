module

public import ConditionedStochasticStabilityHyperbolic.Spectral.CommonAmbientClassicalComparison

/-! Compare first in the faithful full global test dual, then restrict the
matching identities to the supported regular dual used by probability limits.
Injectivity is needed only before this restriction. -/

@[expose] public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.CommonAmbientClassicalComparison
variable {A F Z Z' : Type*}
  [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [NormedAddCommGroup Z'] [NormedSpace ℂ Z']

theorem Facts.map_ambient
    {P : A →L[ℂ] A} {Q : F →L[ℂ] F}
    {a : A →L[ℂ] Z} {b : F →L[ℂ] Z} {ρ : ℝ}
    (facts : Facts P Q a b ρ) (r : Z →L[ℂ] Z') :
    Facts P Q (r.comp a) (r.comp b) ρ where
  ordinary := by
    intro f hf z he hz
    obtain ⟨v, hv, heP, hmatch⟩ := facts.ordinary f hf z he hz
    exact ⟨v, hv, heP, congrArg r hmatch⟩
  generalized := by
    intro z hz k f hf he
    obtain ⟨v, heP, hmatch⟩ := facts.generalized z hz k f hf he
    exact ⟨v, heP, congrArg r hmatch⟩
  reverse := by
    intro γ hγ z he hz
    obtain ⟨f, hf, heQ, hmatch⟩ := facts.reverse γ hγ z he hz
    exact ⟨f, hf, heQ, congrArg r hmatch⟩

end ConditionedStochasticStabilityHyperbolic.CommonAmbientClassicalComparison
