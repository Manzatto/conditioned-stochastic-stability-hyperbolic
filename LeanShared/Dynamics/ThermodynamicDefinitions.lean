module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Order.LiminfLimsup

/-! Literal pressure and equilibrium-state semantics for classical sources. Pressure uses weighted
finite Bowen-separated sets. Metric entropy uses finite measurable partitions and their
dynamical refinements. -/

@[expose] public noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace LeanShared.ThermodynamicDefinitions

section Pressure
variable {X : Type*} [MetricSpace X]

def Separated (T : X → X) (K : Set X) (n : ℕ) (ε : ℝ) (s : Finset X) : Prop :=
  (∀ x ∈ s, x ∈ K) ∧ ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
    ∃ i : ℕ, i < n ∧ ε ≤ dist (T^[i] x) (T^[i] y)

def orbitSum (T : X → X) (φ : X → ℝ) (n : ℕ) (x : X) : ℝ :=
  ∑ i ∈ Finset.range n, φ (T^[i] x)

def separatedPartitionSum (T : X → X) (φ : X → ℝ) (K : Set X) (n : ℕ) (ε : ℝ) : ℝ≥0∞ := by
  classical
  exact ⨆ s : Finset X, ⨆ (_hs : Separated T K n ε s),
    ∑ x ∈ s, ENNReal.ofReal (Real.exp (orbitSum T φ n x))

/-- Bowen separated-set topological pressure, as an extended real value. -/
def pressure (T : X → X) (φ : X → ℝ) (K : Set X) : EReal :=
  ⨆ ε : {ε : ℝ // 0 < ε},
    limsup (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) *
      (separatedPartitionSum T φ K n ε.val).log) atTop
end Pressure

section Entropy
variable {X : Type*} [MeasurableSpace X]

/-- Finite measurable partitions of the entire state space. Null atoms are
allowed; their Shannon contribution is zero by the real-log convention. -/
structure MeasurablePartition (k : ℕ) where
  atom : Fin k → Set X
  measurable : ∀ i, MeasurableSet (atom i)
  disjoint : Pairwise (fun i j => Disjoint (atom i) (atom j))
  covering : ⋃ i, atom i = univ

def dynamicalAtom {k : ℕ} (P : MeasurablePartition (X := X) k)
    (T : X → X) (n : ℕ) (word : Fin n → Fin k) : Set X :=
  ⋂ i : Fin n, (T^[i.val]) ⁻¹' P.atom (word i)

def dynamicalEntropy {k : ℕ} (P : MeasurablePartition (X := X) k)
    (T : X → X) (μ : Measure X) (n : ℕ) : ℝ :=
  -∑ word : Fin n → Fin k,
    μ.real (dynamicalAtom P T n word) * Real.log (μ.real (dynamicalAtom P T n word))

/-- Kolmogorov–Sinai entropy via finite measurable partitions. For an
invariant probability the usual subadditivity theorem supplies the limit
in place of the liminf appearing in this definition. -/
def entropy (T : X → X) (μ : Measure X) : EReal :=
  ⨆ k : ℕ, ⨆ P : MeasurablePartition (X := X) k,
    liminf (fun n : ℕ => (((n : ℝ)⁻¹ * dynamicalEntropy P T μ n : ℝ) : EReal)) atTop
end Entropy

section Equilibrium
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The actual variational equality, with invariant probability and support
on the specified invariant set. No noisy measure occurs in this predicate. -/
def IsEquilibriumState (T : X → X) (φ : X → ℝ) (K : Set X)
    (ν : ProbabilityMeasure X) : Prop :=
  Measurable T ∧ (ν : Measure X).map T = ν ∧ (ν : Measure X) Kᶜ = 0 ∧
    Integrable φ (ν : Measure X) ∧
    entropy T ν + ((∫ x, φ x ∂(ν : Measure X) : ℝ) : EReal) = pressure T φ K

end Equilibrium
end LeanShared.ThermodynamicDefinitions
