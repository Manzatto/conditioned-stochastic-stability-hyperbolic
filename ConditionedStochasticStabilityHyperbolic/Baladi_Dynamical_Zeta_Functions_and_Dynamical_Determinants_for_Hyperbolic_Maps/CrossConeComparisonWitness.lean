module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.CrossConeCompactEmbedding

/-! Consume a proved comparison witness in abstract normed carriers. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.CrossConeCompactEmbedding.Canonical
open LeanShared
variable {Core B F S : Type*} [AddCommGroup Core] [Module ℂ Core]
  [NormedAddCommGroup B] [NormedSpace ℂ B]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  (qPrime:Core→ₗ[ℂ]B) (q:Core→ₗ[ℂ]DyadicCompletion.BlockSpace (F:=F) (S:=S))
  {η:ℝ} (positive:0<η) (δ:S→ℝ) (nonnegative:∀s,0≤δ s)
  (comparison:∃A:ℝ,0≤A ∧ ∀c,‖q c‖≤A*‖qPrime c‖)

include comparison in
theorem embedding_core_of_comparison (c:Core) :
    embedding qPrime q positive δ nonnegative (DyadicCompletion.coreLift qPrime c)=
      DyadicCompletion.coreLift (DyadicCompletion.finalCore q η positive δ nonnegative) c := by
  obtain ⟨A,_,bound⟩ := comparison
  exact embedding_core qPrime q positive δ nonnegative A bound c

variable {Z:Type*} [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z] [T2Space Z]
  (pPrime:DyadicCompletion.closedCore qPrime→L[ℂ]Z)
  (p:DyadicCompletion.closedCore q→L[ℂ]Z)
  (common:∀c,p (DyadicCompletion.coreLift q c)=pPrime (DyadicCompletion.coreLift qPrime c))
  (faithful:Function.Injective pPrime)

include comparison pPrime p common faithful in
theorem embedding_injective_of_comparison : Function.Injective (embedding qPrime q positive δ nonnegative) := by
  obtain ⟨A,_,bound⟩ := comparison
  exact embedding_injective qPrime q positive δ nonnegative pPrime p common A bound faithful
end ConditionedStochasticStabilityHyperbolic.CrossConeCompactEmbedding.Canonical
