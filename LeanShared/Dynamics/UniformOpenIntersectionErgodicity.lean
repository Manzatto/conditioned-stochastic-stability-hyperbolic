module

public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-! A uniform lower correlation on compact subsets of arbitrary open sets
rules out nontrivial invariant measurable sets. Regular approximation is
performed only after the positive correlation constant has been fixed. -/
public noncomputable section
open Set MeasureTheory
namespace LeanShared
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

theorem invariant_zero_one_of_open_intersections (T : X → X) (ν : Measure X)
    [IsFiniteMeasure ν] [ν.InnerRegularCompactLTTop] [ν.OuterRegular]
    (invariant : MeasurePreserving T ν ν) (C : ℝ) (positive : 0 < C)
    (correlation : ∀ K L U V : Set X, IsCompact K → IsCompact L → IsOpen U → IsOpen V →
      K ⊆ U → L ⊆ V → ∃ d : ℕ,
      C * ν.real K * ν.real L ≤ ν.real (U ∩ (T^[d]) ⁻¹' V))
    (E : Set X) (measurable : MeasurableSet E) (fixed : T ⁻¹' E = E) :
    ν E = 0 ∨ ν Eᶜ = 0 := by
  by_contra failure
  push Not at failure
  obtain ⟨K, subK, compactK, positiveK⟩ := measurable.exists_lt_isCompact_of_ne_top
    (measure_ne_top ν E) (pos_iff_ne_zero.mpr failure.1)
  obtain ⟨L, subL, compactL, positiveL⟩ := measurable.compl.exists_lt_isCompact_of_ne_top
    (measure_ne_top ν Eᶜ) (pos_iff_ne_zero.mpr failure.2)
  have realK : 0 < ν.real K := ENNReal.toReal_pos positiveK.ne' (measure_ne_top ν K)
  have realL : 0 < ν.real L := ENNReal.toReal_pos positiveL.ne' (measure_ne_top ν L)
  let e := C * ν.real K * ν.real L / 4
  have positiveE : 0 < e := by dsimp [e]; positivity
  obtain ⟨U, subU, openU, _, errorU⟩ := measurable.exists_isOpen_sdiff_lt
    (measure_ne_top ν E) (ENNReal.ofReal_ne_zero_iff.mpr positiveE)
  obtain ⟨V, subV, openV, _, errorV⟩ := measurable.compl.exists_isOpen_sdiff_lt
    (measure_ne_top ν Eᶜ) (ENNReal.ofReal_ne_zero_iff.mpr positiveE)
  have realErrorU : ν.real (U \ E) < e := by
    have bound := (ENNReal.toReal_lt_toReal (measure_ne_top ν (U \ E)) ENNReal.ofReal_ne_top).mpr errorU
    simpa only [measureReal_def, ENNReal.toReal_ofReal positiveE.le] using bound
  have realErrorV : ν.real (V \ Eᶜ) < e := by
    have bound := (ENNReal.toReal_lt_toReal (measure_ne_top ν (V \ Eᶜ)) ENNReal.ofReal_ne_top).mpr errorV
    simpa only [measureReal_def, ENNReal.toReal_ofReal positiveE.le] using bound
  obtain ⟨d, lower⟩ := correlation K L U V compactK compactL openU openV
    (subK.trans subU) (subL.trans subV)
  have fixedIterate : (T^[d]) ⁻¹' E = E := Function.IsFixedPt.preimage_iterate fixed d
  have included : U ∩ (T^[d]) ⁻¹' V ⊆ (U \ E) ∪ (T^[d]) ⁻¹' (V \ Eᶜ) := by
    intro x hx
    by_cases inside : x ∈ E
    · apply Or.inr
      have along : T^[d] x ∈ E := by
        change x ∈ (T^[d]) ⁻¹' E
        rw [fixedIterate]
        exact inside
      exact ⟨hx.2, by simpa only [mem_compl_iff, not_not] using along⟩
    · exact Or.inl ⟨hx.1, inside⟩
  have upper := (measureReal_mono (μ := ν) included).trans
    (measureReal_union_le (μ := ν) (U \ E) ((T^[d]) ⁻¹' (V \ Eᶜ)))
  have preimage : ν ((T^[d]) ⁻¹' (V \ Eᶜ)) = ν (V \ Eᶜ) :=
    (invariant.iterate d).measure_preimage
      (openV.measurableSet.diff measurable.compl).nullMeasurableSet
  simp only [measureReal_def, preimage] at upper
  have contradiction := lower.trans upper
  have productPositive : 0 < C * ν.real K * ν.real L := mul_pos (mul_pos positive realK) realL
  dsimp [e] at realErrorU realErrorV
  simp only [measureReal_def] at realErrorU realErrorV productPositive contradiction
  linarith


theorem ergodic_of_open_intersections (T : X → X) (ν : Measure X)
    [IsFiniteMeasure ν] [ν.InnerRegularCompactLTTop] [ν.OuterRegular]
    (invariant : MeasurePreserving T ν ν) (C : ℝ) (positive : 0 < C)
    (correlation : ∀ K L U V : Set X, IsCompact K → IsCompact L → IsOpen U → IsOpen V →
      K ⊆ U → L ⊆ V → ∃ d : ℕ,
      C * ν.real K * ν.real L ≤ ν.real (U ∩ (T^[d]) ⁻¹' V)) :
    Ergodic T ν := by
  refine Ergodic.of_preimage_eq invariant (fun E measurable fixed => ?_)
  have zero := invariant_zero_one_of_open_intersections T ν invariant C positive correlation
    E measurable fixed
  simpa only [Filter.eventuallyEmptyOrUniv_iff', ae_eq_empty, ae_eq_univ] using zero

end LeanShared
