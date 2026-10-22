module
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeFiltrationLayers
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeLocalOutcomeProducer
public import ConditionedStochasticStabilityHyperbolic.Paper.AdaptedLocalWeightSupportedProduct
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseRegularityChange
meta import Lean.LibrarySuggestions.Basic

/-! The native local outcome on the selected closed layer of an adapted filtration. On a mixing
retained basic set, a regular extension of the physical weight supported inside the isolating
neighborhood and the layer interior is an HL weight; the native local outcome of its adapted
setup gives literal local stability with the actual noise and laws, the physical weight `exp φ`
and the potential `φ`. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "NativeFiltrationLocal"

public noncomputable section
set_option linter.unusedSectionVars false
open Set Filter IsManifold Bundle MeasureTheory
open scoped Manifold ContDiff NNReal Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.NativeFiltrationLocal
open LeanShared LeanShared.HyperbolicBasicSet RegularNoise Global
open Global.ShiftedFiltrationGeometry Global.FiltrationPressureConfinement

variable {E ι : Type*} {M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [ChartedSpace E M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M] [Fintype ι]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]

local instance layerCompact {T : M ≃ₜ M} {A : Set M} {I : Type*} {Λ : I → Set M} {ℓ : ℕ} (N : ℕ)
    (D : AdaptedSource T A Λ ℓ) (i : Fin ℓ) : CompactSpace (closedLayer T A Λ ℓ N D i) :=
  isCompact_iff_compactSpace.mp (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))

set_option maxHeartbeats 3200000 in
/-- The native local outcome on the selected closed layer. -/
theorem exists_local_outcome
    {T : M ≃ₜ M} {I : Type*} (Λ : I → Set M) (A : Set M) (hA : IsOpen A)
    (strict : MapsTo T (closure A) A) {ℓ : ℕ} (N : ℕ) (D : AdaptedSource T A Λ ℓ)
    {Vb : Fin ℓ → Set M} (basic : ∀ i : Fin ℓ, BasicData (E := E) T (Λ (D.index i)) (Vb i))
    (live : ∀ i : Fin ℓ, Λ (D.index i) ⊆ Aᶜ)
    {r : ℝ} (r1 : 1 < r)
    (regularT : FractionalManifoldRegularity.Regular (E := E) (F := E) r T)
    (inverseRegular : FractionalManifoldRegularity.Regular (E := E) (F := E) r T.symm)
    (φ : M → ℝ) (hφ : Continuous φ) (j : Fin ℓ)
    (localWeight : ∃ W : Set M, IsOpen W ∧ Λ (D.index j) ⊆ W ∧
      ∀ ζ : M → ℝ, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ)) ∞ ζ → tsupport ζ ⊆ W →
        FractionalManifoldRegularity.Regular (E := E) (F := ℝ) (r - 1)
          (ζ * fun x => Real.exp (φ x)))
    (stable : ∀ x ∈ Λ (D.index j),
      0 < Module.finrank ℝ ((basic j).hyperbolic.stable x))
    (mixing : HyperbolicBasicSet.MixingOn T (Λ (D.index j)))
    (P : RegularNoise.Maps (E := E) (ι := ι) T r) (L : RegularNoise.Laws (ι := ι)) (floor : ℝ) :
    ∃ (g' : M → ℝ) (V' : Set M) (h' : HL (E := E) T g' (Λ (D.index j)) V'),
      h'.basic.hyperbolic = (basic j).hyperbolic ∧
      ∃ d : NativeLocalOutcome h' ι (closedLayer T A Λ ℓ N D j)
          (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))
          (fun x => Real.exp (φ x.val)) φ,
        (∀ ε a x, d.maps.family ε a x = P.family ε a x) ∧ d.maps.window = P.window ∧
        d.laws = L ∧ floor ≤ d.scale := by
  classical
  let w : M → ℝ := fun x => Real.exp (φ x)
  have hw : Continuous w := Real.continuous_exp.comp hφ
  let K := closedLayer T A Λ ℓ N D j
  have hK : IsCompact K := isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _)
  obtain ⟨W, hW, coreW, smooth⟩ := localWeight
  let W₁ := W ∩ Vb j ∩ interior K
  have hW₁ : IsOpen W₁ :=
    (hW.inter (basic j).open_neighborhood).inter isOpen_interior
  have coreW₁ : Λ (D.index j) ⊆ W₁ := fun x hx =>
    ⟨⟨coreW hx, (basic j).subset_neighborhood hx⟩,
      NativeFiltrationLayers.core_interior Λ A hA strict N D basic live j hx⟩
  obtain ⟨O, hO, coreO, gp, hgp, gpNonneg, -, agree, gpSupp⟩ :=
    NativeRegularWeightExtension.exists_regular_extension (r - 1) (Λ (D.index j)) W₁
      (basic j).hyperbolic.compact hW₁ coreW₁ w (fun x => (Real.exp_pos _).le)
      (fun ζ hζ hs => smooth ζ hζ (hs.trans fun x hx => hx.1.1))
  let b := (basic j).restrictNeighborhood W₁ hW₁ coreW₁ (fun x hx => hx.1.2)
  let hl : HL (E := E) T gp (Λ (D.index j)) W₁ :=
    { r := r
      regularity_gt_one := r1
      map_regular := regularT
      inverse_regular := inverseRegular
      basic := b
      weight_regular := hgp
      weight_nonnegative := gpNonneg
      weight_supported := gpSupp
      weight_positive := fun x hx => (agree x (coreO hx)).symm ▸ Real.exp_pos _
      mixing := mixing }
  let s := AdaptedLocalWeightSetup.of_supported_product hl w W₁ hW₁ coreW₁ subset_rfl hw
    (fun x hx => (agree x (coreO hx)).symm)
    (fun ζ hζ hs => smooth ζ hζ (hs.trans fun x hx => hx.1.1))
  have e : r = s.fresh.r := s.regularity_eq.symm
  have hcoreK : LeanShared.isolatedCore T K = Λ (D.index j) :=
    closed_layer_core T A Λ ℓ N D hA j
  obtain ⟨d, hmaps, hlaws, hfloor⟩ := NativeLocalOutcomeProducer.native_local_outcome hl w hw
    (fun x => (Real.exp_pos _).le) s K hK hcoreK (fun x hx => interior_subset hx.2)
    (fun x hx => s.hyperbolic_eq ▸ stable x hx) (P.changeRegularity e) L φ
    (fun x hx => (s.core_agreement hx).trans (agree x (coreO hx))) floor
  refine ⟨_, _, s.fresh, s.hyperbolic_eq, d, fun ε a x => ?_, ?_, hlaws, hfloor⟩
  · rw [hmaps]
    exact Maps.changeRegularity_family P e ε a x
  · rw [hmaps]
    exact Maps.changeRegularity_window P e

end ConditionedStochasticStabilityHyperbolic.Paper.NativeFiltrationLocal
