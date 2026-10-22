module
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Dynamics.FixedPoints.Basic

/-! All finitely many actual iterates have one common uniform continuity
tolerance on a compact metric phase space. -/
public section
namespace LeanShared.FiniteIterateUniformity
variable {X:Type*} [MetricSpace X] [CompactSpace X]

theorem exists_tolerance (T:X→X) (continuous:Continuous T) (N:ℕ) (ε:ℝ) (positive:0<ε) :
    ∃η:ℝ,0<η ∧ ∀x y:X,dist x y<η →
      ∀j:ℕ,j≤N → dist ((T^[j]) x) ((T^[j]) y)<ε := by
  let family := fun x:X=>fun j:Fin (N+1)=>(T^[j.val]) x
  have continuousFamily : Continuous family := continuous_pi (fun j=>continuous.iterate j.val)
  obtain ⟨η,hη,variation⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous continuousFamily) ε positive
  refine ⟨η,hη,fun x y near j hj=>?_⟩
  exact (dist_le_pi_dist (family x) (family y) ⟨j,Nat.lt_succ_iff.mpr hj⟩).trans_lt (variation near)

end LeanShared.FiniteIterateUniformity
