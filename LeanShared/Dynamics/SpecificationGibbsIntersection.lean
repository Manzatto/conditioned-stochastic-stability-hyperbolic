module

public import LeanShared.Dynamics.GibbsTracedPairMass
public import LeanShared.Dynamics.OrbitEnergyConcatenation
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! Actual two-word specification and Bowen energy distortion produce
quantitative Gibbs mass in a prescribed intersection of two time-shifted
open neighbourhoods. The same tracing points supply both the energy and
the set membership, and finite cylinder packing supplies the measure. -/
public noncomputable section
open Set MeasureTheory
open scoped BigOperators BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

set_option maxHeartbeats 1600000 in
theorem specification_gibbs_intersection (T : X ≃ₜ X) (φ : X →ᵇ ℝ) (ν : Measure X)
    (ε A P D : ℝ) (positive : 0 < ε) (nonnegative : 0 ≤ A)
    (gap : ℕ) (positiveGap : 0 < gap)
    (tracing : ∀ n m : ℕ, ∀ x y : X, ∃ z : X,
      (∀ j ≤ n, dist (T^[j] z) (T^[j] x) < 3 * ε) ∧
      ∀ j ≤ m, dist (T^[n + gap + j] z) (T^[j] y) < 3 * ε)
    (bowen : ∀ n x y, (∀ j ≤ n, dist (T^[j] x) (T^[j] y) < 3 * ε) →
      |orbitSum T φ (n + 1) x - orbitSum T φ (n + 1) y| ≤ D)
    (lower : ∀ n y, ENNReal.ofReal (A * Real.exp
      (orbitSum T φ n y - (n : ℝ) * P)) ≤
      ν {x | ∀ j < n, dist (T^[j] x) (T^[j] y) < ε})
    (s t : Finset X) (n m r r' : ℕ) (U V : Set X)
    (first : Separated T univ (n + 1) (9 * ε) s)
    (second : Separated T univ (m + 1) (9 * ε) t)
    (firstInside : ∀ y ∈ s, ∀ x,
      (∀ j ≤ n, dist (T^[j] x) (T^[j] y) < 4 * ε) → T^[r] x ∈ U)
    (secondInside : ∀ y ∈ t, ∀ x,
      (∀ j ≤ m, dist (T^[j] x) (T^[j] y) < 4 * ε) → T^[r'] x ∈ V) :
    ENNReal.ofReal (A * Real.exp (-((n + gap + m + 1 : ℕ) : ℝ) * P) *
      (Real.exp (-(2 * D + (gap - 1 : ℕ) * ‖φ‖)) *
        (∑ x ∈ s, Real.exp (orbitSum T φ (n + 1) x)) *
        (∑ y ∈ t, Real.exp (orbitSum T φ (m + 1) y)))) ≤
      ν {x | T^[r] x ∈ U ∧ T^[n + gap + r'] x ∈ V} := by
  classical
  choose z traceFirst traceSecond using
    (fun p : {p : X × X // p ∈ s.product t} => tracing n m p.val.1 p.val.2)
  apply gibbs_traced_pair_mass T φ ν s t n m gap ε A P
    (Real.exp (-(2 * D + (gap - 1 : ℕ) * ‖φ‖))) positive nonnegative
    first second z traceFirst traceSecond
  · intro p
    have firstEnergy := bowen n (z p) p.val.1 (traceFirst p)
    have secondEnergy := bowen m (T^[n + gap] (z p)) p.val.2 (fun j hj => by
      rw [← Function.iterate_add_apply, Nat.add_comm j (n + gap)]
      exact traceSecond p j hj)
    have energy := orbitSum_gluing_lower T φ univ (fun _ _ => mem_univ _) ‖φ‖
      (fun x _ => (abs_le.mp (φ.norm_coe_le_norm x)).1) n m gap positiveGap
      p.val.1 p.val.2 (z p) (mem_univ _) D firstEnergy secondEnergy
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  · intro y
    have opened := isOpen_biInter_finset (s := Finset.range (n + gap + m + 1))
      (f := fun j => {x | dist (T^[j] x) (T^[j] y) < ε})
      (fun j _ => isOpen_lt ((T.continuous.iterate j).dist continuous_const) continuous_const)
    have eqSet : (⋂ j ∈ Finset.range (n + gap + m + 1),
        {x | dist (T^[j] x) (T^[j] y) < ε}) =
        {x | ∀ j < n + gap + m + 1, dist (T^[j] x) (T^[j] y) < ε} := by
      ext x
      simp only [mem_iInter, Finset.mem_range, mem_ofPred_eq]
    rw [eqSet] at opened
    exact opened.measurableSet
  · intro p x close
    refine ⟨firstInside p.val.1 (Finset.mem_product.mp p.property).1 x ?_, ?_⟩
    · intro j hj
      have one := close j (by omega)
      have two := traceFirst p j hj
      have tri := dist_triangle (T^[j] x) (T^[j] (z p)) (T^[j] p.val.1)
      linarith
    have final := secondInside p.val.2 (Finset.mem_product.mp p.property).2
      (T^[n + gap] x) (fun j hj => by
        rw [← Function.iterate_add_apply, Nat.add_comm j (n + gap)]
        have one := close (n + gap + j) (by omega)
        have two := traceSecond p j hj
        have tri := dist_triangle (T^[n + gap + j] x)
          (T^[n + gap + j] (z p)) (T^[j] p.val.2)
        linarith)
    simpa only [← Function.iterate_add_apply, Nat.add_comm r' (n + gap)] using final
  · exact lower _

end LeanShared.ThermodynamicDefinitions
