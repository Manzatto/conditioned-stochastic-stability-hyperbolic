module
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-! Powers of a continuous linear endomorphism act as iterates. Stated once for
an abstract space, so that concrete instances only instantiate it. -/
public section
namespace LeanShared.ContinuousLinearMapPowApply

theorem pow_apply {R H : Type*} [Semiring R] [TopologicalSpace H] [AddCommMonoid H] [Module R H]
    (P : H →L[R] H) (n : ℕ) (x : H) : (P ^ n) x = P^[n] x :=
  congrFun (FunLike.coe_pow_eq_iterate P n) x

end LeanShared.ContinuousLinearMapPowApply
