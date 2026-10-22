module

public import LeanShared.Dynamics.PartitionEntropyRate
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp

/-! A fixed finite padding of the actual observation horizon has zero
asymptotic entropy cost. -/
public noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MeasurableSpace X] {k : ℕ}

theorem MeasurablePartition.padded_entropyRate_tendsto
    (P : MeasurablePartition (X := X) k) (T : X → X) (μ : Measure X)
    [IsProbabilityMeasure μ] (invariant : MeasurePreserving T μ μ) (p : ℕ) :
    Tendsto (fun n : ℕ => dynamicalEntropy P T μ (n+p)/n) atTop (𝓝 (P.entropyRate T μ)) := by
  have rate := (P.entropyRate_tendsto T μ invariant).comp (tendsto_add_atTop_nat p)
  have factor : Tendsto (fun n : ℕ => 1+(p : ℝ)/n) atTop (𝓝 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add
      (tendsto_const_div_atTop_nhds_zero_nat (p : ℝ))
  have convergence := factor.mul rate
  simp only [one_mul] at convergence
  apply convergence.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have npos : (0 : ℝ) < n := by exact_mod_cast hn
  have ppos : (0 : ℝ) < (n+p : ℕ) := by exact_mod_cast (show 0 < n+p by omega)
  dsimp only [Function.comp_apply]
  field_simp
  push_cast
  ring

end LeanShared.ThermodynamicDefinitions
