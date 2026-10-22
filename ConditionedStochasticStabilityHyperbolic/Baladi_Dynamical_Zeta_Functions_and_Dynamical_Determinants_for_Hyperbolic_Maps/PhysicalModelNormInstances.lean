module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Complex.Basic

/-! Canonical normed-group parents for the nested supremum-block spaces used
by the physical model. The scoped instances select existing inherited
structures; they introduce no new norm or arithmetic operation. Opting in
avoids repeated searches through alternative seminormed parents of nested
`lp` and finite-product submodules. -/
@[expose] public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelNormInstances

scoped instance (priority := 1100) supBlockSeminormed
    (J : Type*) (F : J → Type*) [∀ j, NormedAddCommGroup (F j)] :
    SeminormedAddCommGroup (lp F (⊤ : ENNReal)) :=
  (inferInstance : NormedAddCommGroup (lp F (⊤ : ENNReal))).toSeminormedAddCommGroup

scoped instance (priority := 1100) chartPiSeminormed
    (J : Type*) [Fintype J] (F : J → Type*) [∀ j, NormedAddCommGroup (F j)] :
    SeminormedAddCommGroup (∀ j, F j) :=
  (inferInstance : NormedAddCommGroup (∀ j, F j)).toSeminormedAddCommGroup

scoped instance (priority := 1100) coreSubmoduleSeminormed
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℂ H] (s : Submodule ℂ H) :
    SeminormedAddCommGroup s :=
  (inferInstance : NormedAddCommGroup s).toSeminormedAddCommGroup

end ConditionedStochasticStabilityHyperbolic.PhysicalModelNormInstances
