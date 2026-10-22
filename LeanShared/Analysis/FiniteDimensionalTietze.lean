module
public import Mathlib.Topology.TietzeExtension
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Actual continuous extension into any finite-dimensional real normed
space, using its constructed finite coordinate homeomorphism. -/
public noncomputable section
namespace LeanShared.FiniteDimensionalTietze
variable {X V : Type*} [TopologicalSpace X] [NormalSpace X]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem exists_extension (K : Set X) (closed : IsClosed K)
    (f : X → V) (continuous : ContinuousOn f K) :
    ∃ g : X → V, Continuous g ∧ Set.EqOn g f K := by
  let e := (Module.finBasis ℝ V).equivFun.toContinuousLinearEquiv.toHomeomorph
  let : TietzeExtension V := TietzeExtension.of_homeo e
  let fK : C(K,V) := ⟨fun x => f x.val,continuous.domRestrict⟩
  obtain ⟨g,agreement⟩ := ContinuousMap.exists_restrict_eq closed fK
  refine ⟨g,g.continuous,fun x hx => ?_⟩
  exact congrArg (fun h : C(K,V) => h ⟨x,hx⟩) agreement
end LeanShared.FiniteDimensionalTietze
