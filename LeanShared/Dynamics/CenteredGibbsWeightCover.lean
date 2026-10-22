module

public import LeanShared.Dynamics.ExpansiveCenteredCylinderContainment
public import LeanShared.Dynamics.GibbsCoverNormalization
public import LeanShared.Dynamics.SeparatedSpanningSubset
public import LeanShared.Dynamics.ExpansiveSeparatedCardinality

/-! Actual compact subsets admit centered separated spanning orbit families
whose Gibbs weights control their original measure, while every nearby
tracing word has its center in the prescribed open set. The radius is fixed
before the compact set and its open neighbourhood are chosen. -/
public noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X] [MeasurableSpace X] [BorelSpace X]

set_option maxHeartbeats 1000000 in
theorem exists_centered_gibbs_weight_cover (T : X ≃ₜ X) (c : ℝ) (positiveC : 0 < c)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (φ : X → ℝ) (ν : Measure X) [IsFiniteMeasure ν]
    (invariant : MeasurePreserving T ν ν) (ε H P : ℝ)
    (positive : 0 < ε) (coarse : 9 * ε ≤ c) (nonnegative : 0 ≤ H)
    (upper : ∀ n y, ν {x | ∀ j < n, dist (T^[j] x) (T^[j] y) ≤ 9 * ε} ≤
      ENNReal.ofReal (H * Real.exp (orbitSum T φ n y - (n : ℝ) * P)))
    (K U : Set X) (compact : IsCompact K) (opened : IsOpen U) (inside : K ⊆ U) :
    ∃ N : ℕ, ∃ s : Finset X,
      Separated T univ (2 * N + 1) (9 * ε) s ∧
      (∀ y ∈ s, ∀ x, (∀ j ≤ 2 * N, dist (T^[j] x) (T^[j] y) < 4 * ε) →
        T^[N] x ∈ U) ∧
      ν.real K ≤ H * Real.exp (-((2 * N + 1 : ℕ) : ℝ) * P) *
        ∑ y ∈ s, Real.exp (orbitSum T φ (2 * N + 1) y) := by
  classical
  obtain ⟨N, centered⟩ := FiniteExpansiveWords.exists_centered_cylinder_containment
    T c expansive K U compact opened inside
  let V := ((T : X → X)^[N]) ⁻¹' K
  obtain ⟨a, _, counts⟩ := FiniteExpansiveWords.exists_uniform_card_bound T c positiveC expansive
  obtain ⟨p, count⟩ := counts (9 * ε) (by positivity)
  obtain ⟨s, separated, spans⟩ := exists_separated_spanning_subset T V (2 * N + 1)
    (9 * ε) (by positivity) (a ^ (2 * N + 1 + p))
    (fun s hs => count _ s ⟨fun _ _ => mem_univ _, hs.2⟩)
  refine ⟨N, s, ⟨fun _ _ => mem_univ _, separated.2⟩, ?_, ?_⟩
  · intro y hy x close
    have belongs : T^[N] y ∈ K := separated.1 y hy
    have cancel : (T.symm : X → X)^[N] ((T : X → X)^[N] y) = y :=
      T.left_inv.iterate N y
    apply centered (T^[N] y) belongs x
    intro j hj
    rw [cancel]
    exact (close j (by omega)).le.trans (by linarith)
  · have bound := gibbs_cover_real_weight T φ ν V s (2 * N + 1) (9 * ε) H P
      nonnegative (fun x hx => by
        obtain ⟨y, hy, near⟩ := spans x hx
        exact ⟨y, hy, fun j hj => (near j hj).le⟩) (fun y _ => upper _ y)
    have same : ν V = ν K :=
      (invariant.iterate N).measure_preimage compact.isClosed.measurableSet.nullMeasurableSet
    simpa only [measureReal_def, same] using bound

end LeanShared.ThermodynamicDefinitions
