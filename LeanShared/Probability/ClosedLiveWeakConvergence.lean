module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.TietzeExtension

/-! # Ambient weak convergence implies weak convergence on a closed live space

Tietze extends each bounded continuous live observable. Thus the exact
inclusion of the live probabilities preserves the converse weak-limit
implication needed for the literal global state space.
-/

@[expose] public section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace LeanShared.ClosedLiveWeakConvergence
variable {X J : Type*} [TopologicalSpace X] [NormalSpace X]
  [MeasurableSpace X] [BorelSpace X]

theorem tendsto_of_map_subtype {K : Set X} (hK : IsClosed K)
    (ν : J → ProbabilityMeasure K) (ν₀ : ProbabilityMeasure K) (l : Filter J)
    (h : Tendsto (fun j => (ν j).map (Subtype.val : K → X)) l
      (𝓝 (ν₀.map (Subtype.val : K → X)))) : Tendsto ν l (𝓝 ν₀) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  obtain ⟨g, _, hgf⟩ := f.exists_extension_norm_eq_of_isClosedEmbedding hK.isClosedEmbedding_subtypeVal
  have he (η : ProbabilityMeasure K) :
      (∫ x, g x ∂(η.map (Subtype.val : K → X) : Measure X)) = ∫ x, f x ∂(η : Measure K) := by
    change (∫ x, g x ∂(η : Measure K).map Subtype.val) = _
    rw [integral_map_of_stronglyMeasurable measurable_subtype_coe g.continuous.stronglyMeasurable]
    have hp : ∀ x : K, g x.val = f x := fun x => congrFun hgf x
    simp_rw [hp]
  have ht := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h) g
  simpa only [he] using ht

end LeanShared.ClosedLiveWeakConvergence
