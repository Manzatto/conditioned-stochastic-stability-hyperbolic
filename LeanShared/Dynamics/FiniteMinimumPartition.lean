module

public import LeanShared.Dynamics.ThermodynamicDefinitions
public import Mathlib.Data.Finset.Max
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! Actual measurable nearest-score cells with deterministic tie breaking.
The least minimizing index is constructed from the finite set; cells
partition the state space and contain every strict-minimizer point. -/
public noncomputable section
open Set MeasureTheory
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MeasurableSpace X] {k : ℕ}

@[expose] def finiteMinimumPartition (score : Fin k → X → ℝ)
    (measurable : ∀ i, Measurable (score i)) (positive : 0 < k) :
    MeasurablePartition (X := X) k where
  atom i := {x | (∀ j, score i x ≤ score j x) ∧ ∀ j < i, score i x < score j x}
  measurable i := by
    have result := (MeasurableSet.iInter (fun j => measurableSet_le (measurable i) (measurable j))).inter
      (MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun (_ : j < i) =>
        measurableSet_lt (measurable i) (measurable j))))
    convert result using 1
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter]
  disjoint := by
    intro i j different
    apply Set.disjoint_left.mpr
    intro x hi hj
    rcases lt_or_gt_of_ne different with less | greater
    · exact (not_lt_of_ge (hi.1 j)) (hj.2 i less)
    · exact (not_lt_of_ge (hj.1 i)) (hi.2 j greater)
  covering := by
    classical
    apply eq_univ_of_forall
    intro x
    let : Nonempty (Fin k) := ⟨⟨0, positive⟩⟩
    obtain ⟨i, _, minimizes⟩ := Finset.exists_min_image Finset.univ (fun i : Fin k => score i x)
      Finset.univ_nonempty
    let good := Finset.univ.filter (fun i : Fin k => ∀ j, score i x ≤ score j x)
    have nonempty : good.Nonempty := ⟨i, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, fun j => minimizes j (Finset.mem_univ _)⟩⟩
    let chosen := good.min' nonempty
    have member : chosen ∈ good := Finset.min'_mem good nonempty
    have minimum : ∀ j, score chosen x ≤ score j x := (Finset.mem_filter.mp member).2
    refine mem_iUnion.mpr ⟨chosen, minimum, ?_⟩
    intro j earlier
    by_contra failure
    have reverse : score j x ≤ score chosen x := le_of_not_gt failure
    have goodJ : j ∈ good := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, fun l => reverse.trans (minimum l)⟩
    exact (not_le_of_gt earlier) (Finset.min'_le good j goodJ)

theorem strict_minimum_mem_partition (score : Fin k → X → ℝ)
    (measurable : ∀ i, Measurable (score i)) (positive : 0 < k) (i : Fin k) (x : X)
    (strict : ∀ j ≠ i, score i x < score j x) :
    x ∈ (finiteMinimumPartition score measurable positive).atom i := by
  constructor
  · intro j
    by_cases same : j = i
    · subst j; exact le_rfl
    · exact (strict j same).le
  · intro j earlier
    exact strict j (ne_of_lt earlier)

end LeanShared.ThermodynamicDefinitions
