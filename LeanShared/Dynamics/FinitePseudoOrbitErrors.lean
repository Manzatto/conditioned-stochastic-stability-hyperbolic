module
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! One common one-step pseudo-orbit tolerance controls every fixed finite
block error, using only actual continuity on the compact phase space. -/
public noncomputable section
namespace LeanShared.FinitePseudoOrbitErrors
open Function
variable {X:Type*} [MetricSpace X] [CompactSpace X]

theorem exists_tolerance (T:X→X) (continuous:Continuous T) (N:ℕ) :
    ∀ε:ℝ,0<ε → ∃η:ℝ,0<η ∧ ∀p:ℕ→X,
      (∀j<N,dist (T (p (j+1))) (p j)<η) → dist ((T^[N]) (p N)) (p 0)<ε := by
  induction N with
  | zero =>
    intro ε hε
    exact ⟨1,zero_lt_one,fun _ _=>by simpa only [iterate_zero, id_eq,dist_self] using hε⟩
  | succ N ih =>
    intro ε hε
    obtain ⟨η0,positiveη0,prior⟩ := ih (ε/2) (half_pos hε)
    obtain ⟨η1,positiveη1,variation⟩ := Metric.uniformContinuous_iff.mp
      (CompactSpace.uniformContinuous_of_continuous (continuous.iterate N)) (ε/2) (half_pos hε)
    refine ⟨min η0 η1,lt_min positiveη0 positiveη1,fun p step=>?_⟩
    have first := prior p (fun j hj=>(step j (Nat.lt_succ_of_lt hj)).trans_le (min_le_left _ _))
    have last := variation ((step N (Nat.lt_succ_self N)).trans_le (min_le_right _ _))
    have triangle := dist_triangle ((T^[N]) (T (p (N+1)))) ((T^[N]) (p N)) (p 0)
    rw [iterate_succ_apply]
    linarith

theorem exists_uniform_tolerance (T:X→X) (continuous:Continuous T) (N:ℕ) (ε:ℝ) (positive:0<ε) :
    ∃η:ℝ,0<η ∧ ∀p:ℕ→X,
      (∀j<N,dist (T (p (j+1))) (p j)<η) →
      ∀j≤N,dist ((T^[j]) (p j)) (p 0)<ε := by
  induction N with
  | zero =>
    refine ⟨1,zero_lt_one,fun p _ j hj=>?_⟩
    have same : j=0 := Nat.eq_zero_of_le_zero hj
    simpa only [same,iterate_zero,id_eq,dist_self] using positive
  | succ N ih =>
    obtain ⟨η0,hη0,prior⟩ := ih
    obtain ⟨η1,hη1,last⟩ := exists_tolerance T continuous (N+1) ε positive
    refine ⟨min η0 η1,lt_min hη0 hη1,fun p step j hj=>?_⟩
    by_cases lower:j≤N
    · exact prior p (fun i hi=>(step i (Nat.lt_succ_of_lt hi)).trans_le (min_le_left _ _)) j lower
    · have same : j=N+1 := by omega
      subst j
      exact last p (fun i hi=>(step i hi).trans_le (min_le_right _ _))

end LeanShared.FinitePseudoOrbitErrors
