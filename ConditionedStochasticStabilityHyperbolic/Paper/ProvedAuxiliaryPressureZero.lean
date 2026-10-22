module

public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedAuxiliaryPeriodicDensity
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedHyperbolicEquilibrium
public import LeanShared.Dynamics.BasicHyperbolicFullCorePressureZero

/-! Full-core HL constructs the auxiliary geometric-potential normalization.
The reference volume and equilibrium are constructed internally. The
auxiliary constructor asks for neither periodic density nor an equilibrium
package nor its pressure normalization. -/

public noncomputable section
open Set Function Bundle MeasureTheory
open scoped Manifold ContDiff Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper
open LeanShared HyperbolicBasicSet

variable {F Y : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace Y] [ChartedSpace F Y] [IsManifold (𝓘(ℝ, F)) ∞ Y]
  [RiemannianBundle (fun y : Y => TangentSpace (𝓘(ℝ, F)) y)]
  [IsContinuousRiemannianBundle F (fun y : Y => TangentSpace (𝓘(ℝ, F)) y)]
  [MeasurableSpace Y] [BorelSpace Y] {T : Y ≃ₜ Y}

/-- The full HL core has literal zero geometric pressure. Its smooth
reference charts and chart Haar measure are chosen from proved existence. -/
theorem HL.full_core_pressure_one_eq_zero
    (h : HL (E := F) T (fun _ => 1) univ univ) :
    ThermodynamicDefinitions.pressure T (h.basic.hyperbolic.potential (fun _ => 1)) univ =
      (0 : EReal) := by
  let : CompactSpace Y := isCompact_univ_iff.mp h.compact_core
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  obtain ⟨reference⟩ := FiniteSmoothReferenceCharts.exists_data (E := F) (M := Y)
  exact h.basic.full_core_pressure_one_eq_zero h.regularity_gt_one h.map_regular
    h.inverse_regular h.mixing reference (Measure.addHaar : Measure F)

/-- A full HL map supplies all the auxiliary periodic and thermodynamic
fields. Actual stable/unstable ranks and the original noise data remain
ordinary geometric inputs. -/
@[expose] def AuxiliaryAnosov.of_full_hl_with_proved_thermodynamics {ι : Type*} [Fintype ι]
    {r : ℝ} (T : Y ≃ₜ Y)
    (h : HL (E := F) T (fun _ => 1) univ univ) (regularity : h.r = r)
    (stable_positive : ∀ y, 0 < Module.finrank ℝ (h.basic.hyperbolic.stable y))
    (unstable_positive : ∀ y, 0 < Module.finrank ℝ (h.basic.hyperbolic.unstable y))
    (noise : RegularNoise.Maps (E := F) (ι := ι) T r)
    (laws : RegularNoise.Laws (ι := ι)) : AuxiliaryAnosov (F := F) (Y := Y) (ι := ι) r := by
  letI : CompactSpace Y := isCompact_univ_iff.mp h.compact_core
  let equilibrium := h.proved_equilibriumPackage
  have zero : equilibrium.pressure = 0 := by
    apply EReal.coe_injective
    simpa only [EReal.coe_zero] using
      equilibrium.pressure_identity.symm.trans h.full_core_pressure_one_eq_zero
  exact AuxiliaryAnosov.of_full_hl T h regularity stable_positive unstable_positive
    equilibrium zero noise laws

end ConditionedStochasticStabilityHyperbolic.Paper
