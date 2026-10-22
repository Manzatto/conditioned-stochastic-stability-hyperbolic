module

public import Mathlib.Topology.UniformSpace.Dini
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.MeasureTheory.Measure.Real

/-! Compact setwise-continuous families of finite positive measures are
uniformly continuous from above. This is the measure-theoretic uniformity
behind the composition of strong-Feller kernels. -/

public section
open Filter Topology Set MeasureTheory
namespace LeanShared.StrongFellerUniformRows
variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace Y]

/-- Dini upgrades continuity from above for every finite row to a bound
uniform in all states, including when the decreasing intersection is merely
null for every row. -/
theorem uniform_vanishing (κ : X → Measure Y) [∀ x, IsFiniteMeasure (κ x)]
    (continuous_rows : ∀ B, MeasurableSet B → Continuous (fun x => (κ x).real B))
    (B : ℕ → Set Y) (measurable : ∀ n, MeasurableSet (B n)) (decreasing : Antitone B)
    (null : ∀ x, κ x (⋂ n, B n)=0) :
    TendstoUniformly (fun n x => (κ x).real (B n)) (fun _ => 0) atTop := by
  apply Antitone.tendstoUniformly_of_forall_tendsto
    (fun n => continuous_rows (B n) (measurable n))
    (fun n m hnm x => measureReal_mono (decreasing hnm)) continuous_const
  intro x
  have rows := tendsto_measure_iInter_atTop (μ := κ x)
    (fun n => (measurable n).nullMeasurableSet) decreasing ⟨0, measure_ne_top _ _⟩
  have realRows := ENNReal.continuousAt_toReal (measure_ne_top (κ x) (⋂ n, B n)) |>.tendsto.comp rows
  simpa only [Function.comp_def, Measure.real, null x, ENNReal.toReal_zero] using realRows

end LeanShared.StrongFellerUniformRows
