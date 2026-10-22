module
public import LeanShared.Analysis.CompletedCorePairing

/-! The constructed completed test pairing is a continuous linear map into
the common Hausdorff space of test evaluations. Each coordinate continuity
is proved from its actual core bound. -/
public noncomputable section
namespace LeanShared.CompletedCorePairing
variable {Core B Test : Type*}
  [AddCommGroup Core] [Module ℂ Core]
  [NormedAddCommGroup B] [NormedSpace ℂ B]
  [AddCommGroup Test] [Module ℂ Test]
  (q:Core→ₗ[ℂ]B) (p:Core→ₗ[ℂ](Test→ₗ[ℂ]ℂ))

@[expose] def realization : DyadicCompletion.closedCore q→L[ℂ](Test→ℂ) :=
  ContinuousLinearMap.pi (fun test=>atTest q p test)

theorem realization_pairing
    (bounded:∀test,∃C:ℝ,∀f,‖p f test‖≤C*‖q f‖)
    (z:DyadicCompletion.closedCore q) (test:Test) :
    realization q p z test=pairing q p bounded z test := rfl

include p in
theorem realization_injective
    (bounded:∀test,∃C:ℝ,∀f,‖p f test‖≤C*‖q f‖)
    (faithful:Function.Injective (pairing q p bounded)) :
    Function.Injective (realization q p) := by
  intro z w equal
  apply faithful
  apply LinearMap.ext
  intro test
  exact congrFun equal test
end LeanShared.CompletedCorePairing
