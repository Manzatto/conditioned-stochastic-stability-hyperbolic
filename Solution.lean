module

public import ConditionedStochasticStabilityHyperbolic.MainTheorems
import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafModel
import all ConditionedStochasticStabilityHyperbolic.Paper.ActualHG2NoiseGeometry
import all ConditionedStochasticStabilityHyperbolic.Paper.ActualHG2BasinGeometry
import all ConditionedStochasticStabilityHyperbolic.Global.GreedyPrefixEncoding

/-!
# Palomar solution
MainTheorems supplies the original proofs. The comparison identities below
fix the graph measures, Fourier blocks, core maps and exponent losses used
in the independent compact-embedding statement. The final theorem packages
the constructed HG2 filtration and all of its original conclusion clauses
as explicit existential witnesses, together with the literal noisy process.
-/

public noncomputable section
open Set Function MeasureTheory
open scoped SchwartzMap FourierTransform Topology ENNReal
namespace ConditionedStochasticStabilityHyperbolic.Palomar
open LeanShared AllFakeLeafModel AllFakeLeafDyadicDistribution
section Leaves
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι] [DecidableEq ι]
  (U : Submodule ℝ E) (C : Set E) (cone : ConeData U C) (basis : OrthonormalBasis ι ℝ U)
/-- Leaf domains, graphs, and densities are the actual orthogonal graph data. -/
theorem family_description (Γ : Index U C) :
    let h := FakeLeafGraph.heightExtension U Γ.val (slope_positive U C cone).le (slope_bound U C cone Γ)
    (family U C cone basis Γ).domain = FakeLeafGraph.parameterDomain U Γ.val ∧
    (family U C cone basis Γ).graph = ConeGraphGeometry.graphPoint U h ∧
    (family U C cone basis Γ).density = (FakeLeafGraph.parameterDomain U Γ.val).indicator
      (fun u => ENNReal.ofReal (GraphJacobian.density basis (fderiv ℝ h u))) := by
  exact ⟨rfl, rfl, rfl⟩
/-- Projection domains are open, so the displayed derivatives are local graph derivatives. -/
theorem family_domain_open (Γ : Index U C) : IsOpen (family U C cone basis Γ).domain := by
  change IsOpen (FakeLeafGraph.parameterDomain U Γ.val)
  exact (AllFakeLeafModel.ClassicalGeometry.proved U (volume : Measure U) basis).projection_open
    Γ.val Γ.property.1 _ (slope_positive U C cone).le (slope_bound U C cone Γ)
end Leaves
section Symbols
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [MeasurableSpace E] [BorelSpace E] in
/-- Pointwise low-frequency and rescaled high-frequency cone symbols. -/
theorem symbols_apply {Cp Cm : Set E} (χ : ConeDyadicSymbols.RadialCutoff)
    (Φ : ConeDyadicSymbols.AngularCutoff Cp Cm) (j : ℕ × Bool) (ξ : E) :
    ConeDyadicSymbols.symbols χ Φ j ξ =
      if j.1 = 0 then ConeDyadicSymbols.low χ ξ else
        ConeDyadicSymbols.high χ Φ.toFun j.2 (((2 : ℝ) ^ j.1)⁻¹ • ξ) := by
  by_cases h : j.1 = 0
  · simp only [ConeDyadicSymbols.symbols, DyadicSymbols.symbolsFromMultipliers,
      DyadicSymbols.symbol, h, ↓reduceIte]
    rfl
  · simp only [ConeDyadicSymbols.symbols, DyadicSymbols.symbolsFromMultipliers,
      DyadicSymbols.symbol, h, ↓reduceIte, FourierSchwartzKernel.dilateSymbol_apply]
    rfl
end Symbols
section Core
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (U : Submodule ℝ E) (C : Set E) (cone : ConeData U C) (basis : OrthonormalBasis ι ℝ U)
  {Cp Cm : Set E} (χ : ConeDyadicSymbols.RadialCutoff) (Φ : ConeDyadicSymbols.AngularCutoff Cp Cm)
  {K : Set E} (compact : IsCompact K) (t : Bool → ℝ)
/-- Each Lp coordinate is exactly the weighted physical Fourier block on its leaf. -/
theorem core_ae (f : SchwartzJetSpace.supportedCore K) (j : ℕ × Bool) (Γ : Index U C) :
    AllFakeLeafCanonicalDistribution.core U C cone basis χ Φ compact t f j Γ
      =ᵐ[(family U C cone basis Γ).measure (volume : Measure U)]
      fun x => (((2 : ℝ) ^ (t j.2 * j.1) : ℝ) : ℂ) * ConeFourierBlocks.block
        (ConeDyadicSymbols.symbols χ Φ j) f.val x := by
  exact SchwartzAmbientBlocks.coreMap_ae (volume : Measure U)
    (slopeBound U C cone basis) (family U C cone basis) K (ConeDyadicSymbols.symbols χ Φ) t
    (AllFakeLeafCanonicalDistribution.bounded U C cone basis χ Φ compact t) f j Γ
/-- The completed space has exactly the closure of the physical block-core range. -/
theorem space_mem_iff
    (b : DyadicCompletion.BlockSpace
      (F := GraphLeafNorm.AmbientFamilySpace (volume : Measure U) (family U C cone basis))
      (S := Bool)) :
    b ∈ AllFakeLeafCanonicalDistribution.Space U C cone basis χ Φ compact t ↔
      b ∈ closure (Set.range (AllFakeLeafCanonicalDistribution.core U C cone basis χ Φ compact t)) := by
  rfl
end Core
section Reweight
attribute [local instance 2000] NormedCommRing.toNormedRing
attribute [local instance 3000] NormedField.toNormedCommRing
variable {Core F S : Type*} [AddCommGroup Core] [Module ℂ Core]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
/-- The target completion has precisely the stated independent exponent losses. -/
theorem finalCore_apply (q : Core →ₗ[ℂ] DyadicCompletion.BlockSpace (F := F) (S := S))
    (η : ℝ) (hη : 0 < η) (δ : S → ℝ) (hδ : ∀ s, 0 ≤ δ s) (f : Core) (j : ℕ × S) :
    DyadicCompletion.finalCore q η hη δ hδ f j =
      (((2 : ℝ) ^ (-δ j.2 * j.1) : ℝ) : ℂ) •
        (((((2 : ℝ) ^ (-η)) ^ j.1) : ℝ) : ℂ) • q f j := by
  rfl
end Reweight
end ConditionedStochasticStabilityHyperbolic.Palomar

public noncomputable section
open Set Function MeasureTheory Filter IsManifold Bundle
open scoped Manifold ContDiff Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Palomar
open LeanShared HyperbolicBasicSet Paper Paper.RegularNoise Global
open ShiftedFiltrationGeometry GreedyPrefixGeometry FiltrationPressureConfinement

variable {E ι : Type*} {X : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace X] [CompactSpace X] [SecondCountableTopology X] [ChartedSpace E X]
  [IsManifold (𝓘(ℝ, E)) ∞ X]
  [RiemannianBundle (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [MeasurableSpace X] [BorelSpace X] [Fintype ι] {T : X ≃ₜ X}

set_option maxHeartbeats 6400000 in
/-- Theorem 6.5: existentially package the constructed compatible filtration,
its selected prefix roots, the literal killed process, all conditioned-limit
clauses, equilibrium-state limits, and the selected local quasi-ergodic laws.
The geometric and probabilistic meanings of these clauses are stated above;
no auxiliary Anosov system or analytic proof interface is an input. -/
theorem Theorem6_5 [MeasurableSpace E] [BorelSpace E]
    (D0 : SpectralDecomposition (E := E) T) (g φ : X → ℝ) (A : Set X)
    (h : HG2 D0 g A) (strict : MapsTo T (closure A) A)
    (P : Maps (E := E) (ι := ι) T h.r) (L : Laws (ι := ι))
    (hw : Continuous (fun x => Real.exp (φ x)))
    (R : ℝ) (hR : 0 < R) (bound : ∀ x, Real.exp (φ x) ≤ R) (hφ : Measurable φ)
    (coreAgreement : ∀ i, D0.core i ⊆ Aᶜ → EqOn (fun x => Real.exp (φ x)) g (D0.core i))
    (localWeightX : ∀ i, D0.core i ⊆ Aᶜ → ∃ W : Set X, IsOpen W ∧ D0.core i ⊆ W ∧
      ∀ ζ : X → ℝ, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ)) ∞ ζ → tsupport ζ ⊆ W →
        FractionalManifoldRegularity.Regular (E := E) (F := ℝ) (h.r - 1)
          (ζ * fun x => Real.exp (φ x))) :
    letI : CompactSpace ↥(Aᶜ) := isCompact_iff_compactSpace.mp h.absorbing_open.isClosed_compl.isCompact
    let Λ := fun i : PaperHG2GreedySelection.Retained D0 A => D0.core i.val
    ∃ G : GreedyPrefixGeometry.Data (PaperHG2GreedySelection.edge D0 A)
        (PaperHG2GreedySelection.pressure D0 g A),
    ∃ D : AdaptedSource T A Λ G.order.length,
      D.index = PressureFiltrationSource.reversedVertex G.order ∧
      let j := AssembleShiftedPrefixFamilies.selectedIndex G.order.length G.number G.terminal G.selectedRoot
      ∃ C : ℝ≥0 → AbsorbingMarkovChains.CanonicalChain ↥(Aᶜ),
      ∃ ν : Fin G.number → ℝ≥0 → ProbabilityMeasure ↥(Aᶜ),
      ∃ equilibrium : Fin G.number → ProbabilityMeasure ↥(Aᶜ),
      ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ P.window ∧
        (∀ ε (he : 0 < ε) (window : ε ≤ P.window),
          C ε = RestrictedNoise.chain (L.law ε)
            (fun z : X × cube (ι := ι) ε => P.family ε z.2.val z.1)
            (P.raw_measurable ε he window) Aᶜ h.absorbing_open.measurableSet.compl
            (fun x => Real.exp (φ x.val)) (hw.measurable.comp measurable_subtype_coe)
            R hR (fun x => bound x.val)) ∧
        LiteralHG2Clauses.Clauses T A Λ G.order.length D G.number G.terminal G.selectedRoot
          C (ActualOriginalGlobalChain.fixedRawMap P) ν equilibrium δ ∧
        LabelledHG2Clauses.Clauses T A Λ G.order.length D G.number G.terminal G.selectedRoot C ν δ ∧
        (∀ s, ThermodynamicDefinitions.IsEquilibriumState T
          (fun x => φ x - Real.log ((D0.basic (D.index (j s)).val).hyperbolic.unstableJacobian x))
          (Λ (D.index (j s))) ((equilibrium s).map (Subtype.val : ↥(Aᶜ) → X))) ∧
        (∀ s (ζ : ProbabilityMeasure X), ThermodynamicDefinitions.IsEquilibriumState T
          (fun x => φ x - Real.log ((D0.basic (D.index (j s)).val).hyperbolic.unstableJacobian x))
          (Λ (D.index (j s))) ζ → ζ = (equilibrium s).map (Subtype.val : ↥(Aᶜ) → X)) ∧
        (∃ first : Fin G.number, first.val = 0 ∧ ∀ ε, 0 < ε → ε < δ →
          Nonempty (LocalConclusions.SimpleSpectralWitness (C ε) R (ν first ε))) ∧
        ∀ ε (he : 0 < ε) (_small : ε < δ) (window : ε ≤ P.window) (q : Fin G.number),
          let U := stratum T A Λ G.order.length 0 D (j q)
          ∃ νU : ProbabilityMeasure U,
            (νU : Measure U).map Subtype.val = (ν q ε : Measure ↥(Aᶜ)).map Subtype.val ∧
            let CU := RestrictedNoise.chain (L.law ε)
              (fun z : X × cube (ι := ι) ε => P.family ε z.2.val z.1)
              (P.raw_measurable ε he window) U
              (stratum_measurable T A Λ G.order.length 0 D h.absorbing_open (j q))
              (fun x => Real.exp (φ x.val)) (hw.measurable.comp measurable_subtype_coe)
              R hR (fun x => bound x.val)
            CU.IsQuasiErgodic (νU : Measure U) ∧
              {x : U | x.val ∈ Λ (D.index (j q))} ⊆ (νU : Measure U).support ∧
              ∀ ζ : Measure U, CU.IsQuasiErgodic ζ →
                {x : U | x.val ∈ Λ (D.index (j q))} ⊆ ζ.support → ζ = (νU : Measure U) := by
  let : CompactSpace ↥(Aᶜ) := isCompact_iff_compactSpace.mp h.absorbing_open.isClosed_compl.isCompact
  obtain ⟨sf, family, equilibrium, unique, δ, positive, window, clauses, labelled, spectral, localLaws⟩ :=
    ConditionedStochasticStabilityHyperbolic.Theorem6_5 D0 g φ A h strict P L hw R hR bound hφ
      coreAgreement localWeightX
  let G := ActualHG2BasinGeometry.greedy D0 g A h (HG2.proved_retained_pressure_finiteness h)
  refine ⟨G, _, ?_, _, _, _, δ, positive, window, ?_, clauses, labelled, equilibrium, unique, ?_, ?_⟩
  · exact (ProvedHG2Filtration.filtration (Y := Paper.ToralCatMap.Torus) D0 g A h _ strict).index
  · intro ε he hwindow
    change RestrictedNoise.chain (L.fixedLaw ε) (ActualOriginalGlobalChain.fixedRawMap P ε) _
      Aᶜ _ (fun x => Real.exp (φ x.val)) _ R hR _ = _
    simpa only [ActualOriginalGlobalChain.fixedRawMap,
      dite_eq_left (show 0 < ε ∧ ε ≤ P.window from ⟨he, hwindow⟩)] using
      P.chain_fixed_cube L ε he hwindow Aᶜ h.absorbing_open.measurableSet.compl
        (fun x => Real.exp (φ x.val)) (hw.measurable.comp measurable_subtype_coe)
        R hR (fun x => bound x.val)
  · exact ⟨⟨0, clauses.number_selected.1⟩, rfl, by simpa using spectral⟩
  · intro ε he small hwindow q
    have got := localLaws ε he small hwindow q
    dsimp only [ActualHG2BasinGeometry.retainedCore, ActualProductRestrictedChain.actualMap] at got
    dsimp only [G, ActualHG2BasinGeometry.retainedCore, ActualProductRestrictedChain.actualMap]
    exact got
end ConditionedStochasticStabilityHyperbolic.Palomar

public noncomputable section
open Set MeasureTheory
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
open LeanShared
/-- Exact definition contract for the normalized gap in the global statement. -/
theorem normalizedGap_iff {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (C : AbsorbingMarkovChains.CanonicalChain X)
    (core : Set X) (ν : ProbabilityMeasure X) :
    NormalizedGap C core ν ↔
  ∃ sf : HasStrongFellerKernel C,
  ∃ d : RankOneSpectralData (strongFellerTransferOperator C sf) (1 : X →ᵇ ℝ),
    (ν : Measure X) = eigenvectorMeasure
      (d.eigenmeasure (fun f hf x => by
        rw [strongFellerTransferOperator_represents]
        exact integral_nonneg hf)) d.eigenvector ∧
    ∀ x ∈ core, 0 < d.eigenvector x := by
  rfl
end ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
