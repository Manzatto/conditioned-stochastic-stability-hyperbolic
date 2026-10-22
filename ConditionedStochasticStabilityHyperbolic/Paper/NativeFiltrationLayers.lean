module
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeSelectedLayer
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeRegularWeightExtension
public import ConditionedStochasticStabilityHyperbolic.Paper.GlobalHypotheses
public import ConditionedStochasticStabilityHyperbolic.Global.LayerCoreInterior
public import LeanShared.Dynamics.TrappingBoundarySeparation
meta import Lean.LibrarySuggestions.Basic

/-! Native packets on every closed layer of an adapted filtration of a spectral decomposition. The
retained basic sets are live and strictly separated from the absorbing set; the physical weight
is positive, equals the weight `g` on each retained basic set and is locally regular near it.
The packet pressure is the pressure of `g`, and the selected layer uses the unique equilibrium
state of `g`. No spectral or stochastic statement is assumed. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "NativeFiltrationLayers"

public noncomputable section
set_option linter.unusedSectionVars false
open Set Filter IsManifold Bundle MeasureTheory
open scoped Manifold ContDiff NNReal Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.NativeFiltrationLayers
open LeanShared LeanShared.HyperbolicBasicSet RegularNoise Global
open Global.ShiftedFiltrationGeometry Global.FiltrationPressureConfinement

variable {E ι : Type*} {M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [ChartedSpace E M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M] [Fintype ι]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {I : Type*} (Λ : I → Set M) (g : M → ℝ) (A : Set M) (hA : IsOpen A)
  (strict : MapsTo T (closure A) A) {ℓ : ℕ} (N : ℕ) (D : AdaptedSource T A Λ ℓ)
    {Vb : Fin ℓ → Set M} (basic : ∀ i : Fin ℓ, BasicData (E := E) T (Λ (D.index i)) (Vb i))
  (live : ∀ i : Fin ℓ, Λ (D.index i) ⊆ Aᶜ)
  {r : ℝ} (r1 : 1 < r)
  (regularT : FractionalManifoldRegularity.Regular (E := E) (F := E) r T)
  (inverseRegular : FractionalManifoldRegularity.Regular (E := E) (F := E) r T.symm)
  (w : M → ℝ) (hw : Continuous w) (wPos : ∀ x, 0 < w x)
  (coreWeight : ∀ i : Fin ℓ, EqOn g w (Λ (D.index i)))
  (localWeight : ∀ i : Fin ℓ, ∃ W : Set M, IsOpen W ∧ Λ (D.index i) ⊆ W ∧
    ∀ ζ : M → ℝ, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ)) ∞ ζ → tsupport ζ ⊆ W →
      FractionalManifoldRegularity.Regular (E := E) (F := ℝ) (r - 1) (ζ * w))
  (stable : ∀ i : Fin ℓ, ∀ x ∈ Λ (D.index i),
    0 < Module.finrank ℝ ((basic i).hyperbolic.stable x))
  (pressure : I → ℝ)
  (pressure_identity : ∀ i : Fin ℓ, ThermodynamicDefinitions.pressure T ((basic i).hyperbolic.potential g)
      (Λ (D.index i)) = (pressure (D.index i) : EReal))
  (P : RegularNoise.Maps (E := E) (ι := ι) T r) (L : RegularNoise.Laws (ι := ι))
  (R : ℝ) (hR1 : 1 ≤ R) (hRP : ∀ i : Fin ℓ, Real.exp (pressure (D.index i)) + 1 ≤ R)
  (hwR : ∀ x, w x ≤ R)
  (Fg : ℝ≥0 → M × FixedControl (ι := ι) → M) (hFg : ∀ ε, Measurable (Fg ε))
  (hsame : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, Fg ε = fun z => P.fixedMap ε z.1 z.2)

local instance layerCompact (i : Fin ℓ) : CompactSpace (closedLayer T A Λ ℓ N D i) :=
  isCompact_iff_compactSpace.mp (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))

include hA strict basic live in
theorem core_interior (i : Fin ℓ) :
    Λ (D.index i) ⊆ interior (closedLayer T A Λ ℓ N D i) :=
  LayerCoreInterior.core_subset_interior_closedLayer T A Λ ℓ N D i
    (invariant_subset_interior_live_of_strict_trapping T A (Λ (D.index i))
      (by rintro _ ⟨x, hx, rfl⟩; exact strict hx)
      (basic i).hyperbolic.invariant.le
      (disjoint_left.mpr fun x hx ha => live i hx ha))

include wPos coreWeight localWeight in
/-- A regular weight equal to the physical weight near a retained basic set, with its pressure. -/
theorem exists_layer_weight (i : Fin ℓ) :
    ∃ O : Set M, IsOpen O ∧ Λ (D.index i) ⊆ O ∧ ∃ gp : M → ℝ,
      FractionalManifoldRegularity.Regular (E := E) (F := ℝ) (r - 1) gp ∧ (∀ x, 0 ≤ gp x) ∧
      (∀ x, gp x ≤ w x) ∧ (∀ x ∈ O, gp x = w x) ∧
      (∀ x ∈ Λ (D.index i), 0 < gp x) ∧
      EqOn ((basic i).hyperbolic.potential gp)
        ((basic i).hyperbolic.potential g) (Λ (D.index i)) := by
  obtain ⟨W, hW, coreW, smooth⟩ := localWeight i
  obtain ⟨O, hO, coreO, gp, hgp, gpNonneg, gpLe, agree, -⟩ :=
    NativeRegularWeightExtension.exists_regular_extension (r - 1) (Λ (D.index i)) W
      (basic i).hyperbolic.compact hW coreW w (fun x => (wPos x).le) smooth
  refine ⟨O, hO, coreO, gp, hgp, gpNonneg, gpLe, agree,
    fun x hx => (agree x (coreO hx)).symm ▸ wPos x, fun x hx => ?_⟩
  simp only [HyperbolicData.potential, agree x (coreO hx), coreWeight i hx]

include hA strict basic live r1 regularT inverseRegular wPos coreWeight localWeight stable
  pressure_identity hRP hsame in
/-- The native packet of every closed layer. -/
theorem exists_packet (i : Fin ℓ) :
    Nonempty (NativeNullPrefixSources.NativePacket.{0, 0} (closedLayer T A Λ ℓ N D i)
      (fun ε => RestrictedNoise.chain (L.fixedLaw ε) (Fg ε) (hFg ε)
        (closedLayer T A Λ ℓ N D i) (closedLayer_measurable T A Λ ℓ N D i)
        (fun x => w x.val) (hw.measurable.comp measurable_subtype_coe) R
        (zero_lt_one.trans_le hR1) (fun x => hwR x.val))
      L.fixedLaw (fun _ => inferInstance) R (pressure (D.index i))) := by
  obtain ⟨O, hO, coreO, gp, hgp, gpNonneg, gpLe, agree, gpPos, samePotential⟩ :=
    exists_layer_weight Λ g A D basic w wPos coreWeight localWeight i
  have mapsTo : MapsTo (T : M → M) (Λ (D.index i)) (Λ (D.index i)) := fun x hx =>
    (basic i).hyperbolic.invariant ▸ mem_image_of_mem _ hx
  have hP : ThermodynamicDefinitions.pressure T ((basic i).hyperbolic.potential gp)
      (Λ (D.index i)) = (pressure (D.index i) : EReal) :=
    (ThermodynamicDefinitions.pressure_eq_of_eqOn mapsTo samePotential).trans (pressure_identity i)
  exact NativeSubordinatePacket.exists_packet_of_layer (basic i) r1 regularT
    inverseRegular O hO coreO gp hgp gpNonneg gpPos w hw wPos agree (stable i) P L
    (closedLayer T A Λ ℓ N D i)
    (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))
    (closedLayer_measurable T A Λ ℓ N D i) (closed_layer_core T A Λ ℓ N D hA i)
    (core_interior Λ A hA strict N D basic live i) (pressure (D.index i)) hP R hR1 (hRP i) hwR
    (fun x => (gpLe x).trans (hwR x)) Fg hFg hsame

include hA strict basic live r1 regularT inverseRegular wPos coreWeight localWeight stable
  pressure_identity hRP hsame in
/-- The native selected layer, for a mixing retained basic set with an equilibrium package. -/
theorem exists_selected (j : Fin ℓ) (mixing : HyperbolicBasicSet.MixingOn T (Λ (D.index j)))
    (equilibrium : EquilibriumPackage (basic j).hyperbolic g) :
    Nonempty (NativeSelectedLayer.SelectedLayer T (Λ (D.index j))
      (closedLayer T A Λ ℓ N D j)
      (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))
      (fun ε => RestrictedNoise.chain (L.fixedLaw ε) (Fg ε) (hFg ε)
        (closedLayer T A Λ ℓ N D j) (closedLayer_measurable T A Λ ℓ N D j)
        (fun x => w x.val) (hw.measurable.comp measurable_subtype_coe) R
        (zero_lt_one.trans_le hR1) (fun x => hwR x.val))
      L R (pressure (D.index j)) (zero_lt_one.trans_le hR1) Fg hFg w hw hwR) := by
  obtain ⟨O, hO, coreO, gp, hgp, gpNonneg, gpLe, agree, gpPos, samePotential⟩ :=
    exists_layer_weight Λ g A D basic w wPos coreWeight localWeight j
  have mapsTo : MapsTo (T : M → M) (Λ (D.index j)) (Λ (D.index j)) := fun x hx =>
    (basic j).hyperbolic.invariant ▸ mem_image_of_mem _ hx
  have hP : ThermodynamicDefinitions.pressure T ((basic j).hyperbolic.potential gp)
      (Λ (D.index j)) = (pressure (D.index j) : EReal) :=
    (ThermodynamicDefinitions.pressure_eq_of_eqOn mapsTo samePotential).trans (pressure_identity j)
  exact NativeSelectedLayer.exists_selected_of_layer (basic j) r1 regularT
    inverseRegular mixing O hO coreO gp hgp gpNonneg gpPos equilibrium.state
    (ThermodynamicDefinitions.isEquilibriumState_congr mapsTo samePotential.symm
      equilibrium.equilibrium)
    (fun μ hμ => equilibrium.unique μ
      (ThermodynamicDefinitions.isEquilibriumState_congr mapsTo samePotential hμ))
    w hw wPos agree (stable j) P L (closedLayer T A Λ ℓ N D j)
    (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))
    (closedLayer_measurable T A Λ ℓ N D j) (closed_layer_core T A Λ ℓ N D hA j)
    (core_interior Λ A hA strict N D basic live j) (pressure (D.index j)) hP R hR1 (hRP j) hwR
    (fun x => (gpLe x).trans (hwR x)) Fg hFg hsame

end ConditionedStochasticStabilityHyperbolic.Paper.NativeFiltrationLayers
