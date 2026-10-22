module

public import Mathlib.Basic.Real.Basic

/-! Generic output package for proved core realization and scalar row bounds.
All fields are deductions; the record itself contains no analytic assumptions.
Physical targets remain parameters, avoiding public nested-completion proofs. -/

public section
namespace ConditionedStochasticStabilityHyperbolic.ProducedCoreRows

structure Data {Core Reg Target Ω : Type*}
    (regularCore : Core → Reg) (targetCore : Core → Target) (realize : Reg → Target)
    (strong rectangular weak : Ω → Core → ℝ)
    (strongNorm intermediateNorm weakNorm : Core → ℝ) (L LR LW : ℝ) : Type where
  core : ∀ c, realize (regularCore c) = targetCore c
  strong : ∀ a c, strong a c ≤ L * strongNorm c
  rectangular : ∀ a c, rectangular a c ≤ LR * intermediateNorm c
  weak : ∀ a c, weak a c ≤ LW * weakNorm c

end ConditionedStochasticStabilityHyperbolic.ProducedCoreRows
