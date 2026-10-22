module
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-! Construct a global measure from compatible local coordinate measures.
The result is independent of the disjoint refinement and uniquely determined
by its chart restrictions. -/
public noncomputable section
open Set MeasureTheory
namespace LeanShared.CompatibleChartMeasures
variable {X : Type*} [MeasurableSpace X]

@[expose] def glue (U : ℕ → Set X) (μ : ℕ → Measure X) : Measure X :=
  Measure.sum (fun n => (μ n).restrict (disjointed U n))

theorem restrict_glue (U : ℕ → Set X) (μ : ℕ → Measure X)
    (measurable : ∀ n, MeasurableSet (U n)) (cover : ⋃ n, U n = univ)
    (compatible : ∀ i j, ((μ i).restrict (U i)).restrict (U j) =
      ((μ j).restrict (U j)).restrict (U i)) (i : ℕ) :
    (glue U μ).restrict (U i) = (μ i).restrict (U i) := by
  rw [glue, Measure.restrict_sum _ (measurable i)]
  have summands : ∀ j, ((μ j).restrict (disjointed U j)).restrict (U i) =
      ((μ i).restrict (U i)).restrict (disjointed U j) := by
    intro j
    calc
      ((μ j).restrict (disjointed U j)).restrict (U i) =
          (((μ j).restrict (U j)).restrict (disjointed U j)).restrict (U i) := by
        rw [Measure.restrict_restrict_of_subset (disjointed_le U j)]
      _ = (((μ j).restrict (U j)).restrict (U i)).restrict (disjointed U j) :=
        Measure.restrict_comm (measurable i)
      _ = (((μ i).restrict (U i)).restrict (U j)).restrict (disjointed U j) := by
        rw [compatible j i]
      _ = ((μ i).restrict (U i)).restrict (disjointed U j) :=
        Measure.restrict_restrict_of_subset (disjointed_le U j)
  simp_rw [summands]
  rw [← Measure.restrict_iUnion (disjoint_disjointed U) (MeasurableSet.disjointed measurable),
    iUnion_disjointed, cover, Measure.restrict_univ]

theorem unique (U : ℕ → Set X) (cover : ⋃ n, U n = univ)
    {μ ν : Measure X} (same : ∀ n, μ.restrict (U n) = ν.restrict (U n)) : μ = ν := by
  rw [← Measure.restrict_univ (μ := μ), ← Measure.restrict_univ (μ := ν), ← cover]
  exact Measure.restrict_iUnion_congr.mpr same
/-- In particular, two coordinate atlases defining the same local density
on every overlap construct exactly the same global measure. -/
theorem glue_eq_glue (U V : ℕ → Set X) (μ ν : ℕ → Measure X)
    (hU : ∀ i, MeasurableSet (U i)) (hV : ∀ j, MeasurableSet (V j))
    (coverU : ⋃ i, U i = univ) (coverV : ⋃ j, V j = univ)
    (compatU : ∀ i j, ((μ i).restrict (U i)).restrict (U j) =
      ((μ j).restrict (U j)).restrict (U i))
    (compatV : ∀ i j, ((ν i).restrict (V i)).restrict (V j) =
      ((ν j).restrict (V j)).restrict (V i))
    (overlap : ∀ i j, ((μ i).restrict (U i)).restrict (V j) =
      ((ν j).restrict (V j)).restrict (U i)) :
    glue U μ = glue V ν := by
  apply unique U coverU
  intro i
  apply unique V coverV
  intro j
  calc
    ((glue U μ).restrict (U i)).restrict (V j) =
        ((μ i).restrict (U i)).restrict (V j) := by
      rw [restrict_glue U μ hU coverU compatU]
    _ = ((ν j).restrict (V j)).restrict (U i) := overlap i j
    _ = ((glue V ν).restrict (V j)).restrict (U i) := by
      rw [restrict_glue V ν hV coverV compatV]
    _ = ((glue V ν).restrict (U i)).restrict (V j) := Measure.restrict_comm (hU i)
end LeanShared.CompatibleChartMeasures
