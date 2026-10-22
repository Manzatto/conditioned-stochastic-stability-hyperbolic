module

public import LeanShared.Dynamics.ExpansivePartitionCoding
public import LeanShared.Dynamics.FiniteExpansiveCylinders

/-! Actual finite null-boundary generators for compact expansive systems,
with quantitative shrinking of their two-sided cylinders. -/
public noncomputable section
open Set Function MeasureTheory
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The partition is constructed for the specified finite measure; both
its Borel generating property and shrinking cylinders are proved. -/
theorem exists_expansive_null_boundary_generator (T : X ≃ₜ X) (c : ℝ) (positive : 0 < c)
    (expansive : ∀ x y, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x=y)
    (μ : Measure X) [IsFiniteMeasure μ] :
    ∃ k : ℕ, ∃ P : MeasurablePartition (X := X) k,
      (∀ i, μ (frontier (P.atom i))=0) ∧
      (∀ i x y, x ∈ P.atom i → y ∈ P.atom i → dist x y < c) ∧
      MeasurableEmbedding (P.itinerary T) ∧
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ x y,
        (∀ n ≤ N, P.label ((T : X → X)^[n] x)=P.label ((T : X → X)^[n] y) ∧
          P.label ((T.symm : X → X)^[n] x)=P.label ((T.symm : X → X)^[n] y)) → dist x y < ε := by
  obtain ⟨k,P,boundary,mesh⟩ := exists_small_boundary_partition μ c positive
  have mesh' (i : Fin k) (x y : X) (hx : x ∈ P.atom i) (hy : y ∈ P.atom i) : dist x y ≤ c :=
    (mesh i x y hx hy).le
  refine ⟨k,P,boundary,mesh,P.itinerary_measurableEmbedding T c expansive mesh',?_⟩
  intro ε hε
  obtain ⟨N,_,detect⟩ := LeanShared.FiniteExpansiveCylinders.exists_finite_separation T
    (isCompact_univ : IsCompact (univ : Set X)) c (fun x _ y _ => expansive x y) ε hε
  refine ⟨N,?_⟩
  intro x y equal
  apply detect x y
  intro n hn
  refine ⟨mem_univ _,mem_univ _,?_,mem_univ _,mem_univ _,?_⟩
  · exact mesh' _ _ _ (P.label_mem _) ((P.label_eq_iff _ _).mp (equal n hn).1.symm)
  · exact mesh' _ _ _ (P.label_mem _) ((P.label_eq_iff _ _).mp (equal n hn).2.symm)

end LeanShared.ThermodynamicDefinitions
