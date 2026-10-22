module

public import LeanShared.Dynamics.BasicHyperbolicShadowing
public import LeanShared.Dynamics.HyperbolicExpansivity
public import LeanShared.Dynamics.EntireOrbitIdentity

/-! Every sufficiently accurate periodic pseudo-orbit in the actual basic
set is shadowed by a genuine periodic point of the same period. Both the
uniform tolerance and the periodicity are derived from actual hyperbolic
shadowing and expansivity, not supplied as a closing/specification source. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Topology Manifold ContDiff
open BilateralHomeomorphismOrbit
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M}

set_option maxHeartbeats 1800000 in
theorem BasicData.periodic_shadowing (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (ε : ℝ) (positiveε : 0 < ε) :
    ∃ η > 0, ∀ p : ℕ, ∀ reference : ℤ → Λ,
      (∀ n, reference (n + (p : ℤ)) = reference n) →
      (∀ n, dist (T (reference (n + 1)).val) (reference n).val < η) →
      ∃ z ∈ Λ, (T : M → M)^[p] z = z ∧
        ∀ n, dist (BilateralHomeomorphismOrbit.orbit T z n) (reference n).val < ε := by
  obtain ⟨c, positiveC, expansive⟩ := b.exists_expansivity_radius forward inverse
  let δ := min ε (c / 3)
  have positiveδ : 0 < δ := lt_min positiveε (by positivity)
  obtain ⟨η, positiveη, shadows⟩ := b.bilateral_shadowing forward (inverse.mdifferentiable one_ne_zero) δ positiveδ
  refine ⟨η, positiveη, fun p reference periodic step => ?_⟩
  obtain ⟨q, qStep, qClose⟩ := shadows reference step
  let qm : ℤ → M := fun n => (q n).val
  let shifted : ℤ → M := fun n => qm (n + (p : ℤ))
  have shiftedStep (n : ℤ) : T (shifted (n + 1)) = shifted n := by
    simpa only [shifted, qm, add_assoc, add_comm (1 : ℤ) (p : ℤ)] using qStep (n + (p : ℤ))
  have qCanonical := eq_canonical T qm qStep
  have shiftedCanonical := eq_canonical T shifted shiftedStep
  have close (n : ℤ) : dist (qm n) (shifted n) ≤ c := by
    have first := qClose n
    have other := qClose (n + (p : ℤ))
    rw [periodic n] at other
    have triangle := dist_triangle (qm n) (reference n).val (shifted n)
    have reverse : dist (reference n).val (shifted n) < δ := by
      rw [dist_comm]
      exact other
    have δsmall : δ ≤ c / 3 := min_le_right _ _
    linarith
  have base : qm 0 = shifted 0 := by
    apply expansive (qm 0) (q 0).property (shifted 0) (q (0 + (p : ℤ))).property
    intro j
    constructor
    · have bound := close (-(j : ℤ))
      rw [congrFun qCanonical (-(j : ℤ)), congrFun shiftedCanonical (-(j : ℤ)),
        neg_nat_time, neg_nat_time] at bound
      exact bound
    · have bound := close (j : ℤ)
      rw [congrFun qCanonical (j : ℤ), congrFun shiftedCanonical (j : ℤ), nat_time, nat_time] at bound
      exact bound
  have periodicOrbit := eq_of_initial T qm shifted qStep shiftedStep base
  have previous : qm (-(p : ℤ)) = qm 0 := by
    have same := congrFun periodicOrbit (-(p : ℤ))
    simpa only [shifted, neg_add_cancel] using same
  have forwardTime := congrFun qCanonical (-(p : ℤ))
  rw [neg_nat_time] at forwardTime
  refine ⟨qm 0, (q 0).property, forwardTime.symm.trans previous, ?_⟩
  intro n
  rw [← congrFun qCanonical n]
  exact (qClose n).trans_le (min_le_left _ _)

end LeanShared.HyperbolicBasicSet
