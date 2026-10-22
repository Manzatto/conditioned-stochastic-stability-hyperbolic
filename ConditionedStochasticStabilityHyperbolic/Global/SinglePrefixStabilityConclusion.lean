module
public import ConditionedStochasticStabilityHyperbolic.Global.AssembleShiftedPrefixFamilies

/-! The single selected prefix needed by HG1. This is an output-consumer
inside the ordinary-source application: its At and local weak family are
constructed by the analytic/product source factories, not cited inputs. HG1
needs only the unshifted prefix; the all-shifts/basin assembly is for HG2. -/
public noncomputable section
open Set MeasureTheory Filter
open scoped Topology BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.SinglePrefixStabilityConclusion
open LeanShared ShiftedFiltrationGeometry ActualFiltrationGrowth
open FiltrationPressureConfinement ComplexStrongFeller RestrictedLayerChain
open LayerQuasiErgodic DerivedHG2Application AssembleShiftedPrefixFamilies

variable {X I : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (T : X ≃ₜ X) (A : Set X) (hA : IsOpen A) (Λ : I → Set X) (ℓ : ℕ)
  (D : AdaptedSource T A Λ ℓ) (t : ℕ) (terminal : Fin t → Fin ℓ)
  (root : ∀ s, Fin ((terminal s).val + 1))
  (C : NNReal → AbsorbingMarkovChains.CanonicalChain X)
  (sf : ∀ ε, 0 < ε → HasStrongFellerKernel (C ε))

local instance singlePrefixCompact (s : Fin t) :
    CompactSpace (actualPrefix T A Λ ℓ D (terminal s) 0) :=
  isCompact_iff_compactSpace.mp
    (levels_positive_compact T A Λ ℓ 0 D ((terminal s).val + 1)
      (by omega) (by have _h := (terminal s).isLt; omega))

omit [CompactSpace X] in
/-- The same canonical local probabilities are global QEMs and converge
weakly to their prescribed equilibrium, using only the derived unshifted
prefix identity. No independently selected global probability is needed. -/
theorem same_family
    (localFamily : ∀ s, NNReal → ProbabilityMeasure
      (closedLayer T A Λ ℓ 0 D (selectedIndex ℓ t terminal root s)))
    (s : Fin t) (νeq : ProbabilityMeasure X)
    (weak : Tendsto (fun ε => ProbabilityMeasure.map (localFamily s ε) Subtype.val)
      (𝓝[>] 0) (𝓝 νeq))
    (produced : ∀ᶠ ε : NNReal in 𝓝[>] 0, ∀ hε : 0 < ε,
      Nonempty (At T A hA Λ ℓ D t terminal root C sf
        (fun q ε => (localFamily q ε : Measure _)) s 0 ε hε)) :
    ∃ ν : NNReal → ProbabilityMeasure X,
      Tendsto ν (𝓝[>] 0) (𝓝 νeq) ∧
      ∀ᶠ ε : NNReal in 𝓝[>] 0, ∀ _hε : 0 < ε,
        (C ε).IsQuasiErgodic (ν ε : Measure X) ∧
          Λ (D.index (selectedIndex ℓ t terminal root s)) ⊆ (ν ε : Measure X).support := by
  refine ⟨fun ε => ProbabilityMeasure.map (localFamily s ε) Subtype.val, weak, ?_⟩
  filter_upwards [produced] with ε output
  intro hε
  let point := Classical.choice (output hε)
  have qem := PrefixQuasiErgodic.full_process_isQuasiErgodic_of_prefix (C ε)
    (actualPrefix T A Λ ℓ D (terminal s) 0)
    (ambient_levels_measurable T A hA Λ ℓ 0 D ((terminal s).val + 1))
    point.invariant _ (productMeasure_isQuasiErgodic _ _ point.data)
  have support := point.support
  rw [point.base_identity rfl] at qem support
  exact ⟨qem, support⟩

end ConditionedStochasticStabilityHyperbolic.Global.SinglePrefixStabilityConclusion
