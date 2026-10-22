module

public import LeanShared.Dynamics.ThermodynamicDefinitions
public import Mathlib.MeasureTheory.Measure.Real

/-! The exact dynamical atoms in the manuscript entropy definition form a
finite measurable probability partition. Null atoms and n=0 are retained. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MeasurableSpace X] {k : ℕ}

namespace MeasurablePartition

theorem dynamicalAtom_measurable (P : MeasurablePartition (X := X) k)
    (T : X → X) (measurable : Measurable T) (n : ℕ) (word : Fin n → Fin k) :
    MeasurableSet (dynamicalAtom P T n word) :=
  MeasurableSet.iInter (fun i => (P.measurable (word i)).preimage (measurable.iterate i.val))

theorem dynamicalAtoms_disjoint (P : MeasurablePartition (X := X) k)
    (T : X → X) (n : ℕ) : Pairwise (fun u v : Fin n → Fin k =>
      Disjoint (dynamicalAtom P T n u) (dynamicalAtom P T n v)) := by
  intro u v different
  have position : ∃ i, u i ≠ v i := by
    by_contra hn
    push Not at hn
    exact different (funext hn)
  obtain ⟨i,hi⟩ := position
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact (Set.disjoint_left.mp (P.disjoint hi)) (mem_iInter.mp hx i) (mem_iInter.mp hy i)

theorem dynamicalAtoms_cover (P : MeasurablePartition (X := X) k)
    (T : X → X) (n : ℕ) : (⋃ word : Fin n → Fin k, dynamicalAtom P T n word)=univ := by
  classical
  apply eq_univ_of_forall
  intro x
  have membership (i : Fin n) : ∃ j : Fin k, T^[i.val] x ∈ P.atom j := by
    have member : T^[i.val] x ∈ ⋃ j, P.atom j := by rw [P.covering]; exact mem_univ _
    exact mem_iUnion.mp member
  choose word member using membership
  exact mem_iUnion.mpr ⟨word,mem_iInter.mpr member⟩

theorem dynamicalAtoms_total (P : MeasurablePartition (X := X) k)
    (T : X → X) (measurable : Measurable T) (μ : Measure X) [IsProbabilityMeasure μ]
    (n : ℕ) : ∑ word : Fin n → Fin k, μ.real (dynamicalAtom P T n word)=1 := by
  rw [←measureReal_iUnion_fintype (P.dynamicalAtoms_disjoint T n)
    (fun w => P.dynamicalAtom_measurable T measurable n w),P.dynamicalAtoms_cover T n]
  simp only [measureReal_def,measure_univ,ENNReal.toReal_one]

end MeasurablePartition
end LeanShared.ThermodynamicDefinitions
