module

public import ConditionedStochasticStabilityHyperbolic.Spectral.StrongFellerCutoffSources

/-! Exact same-cutoff classical comparisons plus actual retained kernel
certificates construct both original and cutoff canonical spectral sources. -/

@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction NNReal
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
open Restriction

variable {E W Z Zret Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [NormedAddCommGroup Zret] [NormedSpace ℂ Zret]
  [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  {P : ℝ≥0 → E →L[ℂ] E} {i : E →L[ℂ] W}
  {d : DeterministicLeading (P 0)} {q δ : ℝ}

structure SameCutoffClassicalSources
    (o : ProjectorOutputs P i d q δ) (ε : ℝ≥0)
    (C D : AbsorbingMarkovChains.CanonicalChain Y)
    (hC : HasStrongFellerKernel C) (hD : HasStrongFellerKernel D) (R : ℝ) where
  parameterSmall : ε ≤ o.window
  conjugation : RealOperatorConjugation (P ε)
  V : Set Y
  BC : Set Y
  BD : Set Y
  hV : MeasurableSet V
  heq : LeanShared.SubtypeKernel.restrict C.killedTransition V hV =
      LeanShared.SubtypeKernel.restrict D.killedTransition V hV
  hreturnC : ∀ x : V, ∀ᵐ y ∂C.killedTransition x.val, y ∉ V → y ∈ BC
  hextC : ∀ x ∈ BC, ∃ n : ℕ,
      C.pathMeasure x (AbsorbingMarkovChains.CanonicalChain.survival n) = 0
  hreturnD : ∀ x : V, ∀ᵐ y ∂D.killedTransition x.val, y ∉ V → y ∈ BD
  hextD : ∀ x ∈ BD, ∃ n : ℕ,
      D.pathMeasure x (AbsorbingMarkovChains.CanonicalChain.survival n) = 0
  NC : ℕ
  ND : ℕ
  hcompC : ∀ x : ↥(Vᶜ),
      ((LeanShared.SubtypeKernel.restrict C.killedTransition Vᶜ hV.compl) ^ NC) x univ = 0
  hcompD : ∀ x : ↥(Vᶜ),
      ((LeanShared.SubtypeKernel.restrict D.killedTransition Vᶜ hV.compl) ^ ND) x univ = 0
  aSource : E →L[ℂ] Z
  bSource : (Y →ᵇ ℂ) →L[ℂ] Z
  restrictSource : Z →L[ℂ] Zret
  ambientRetained : (V →ᵇ ℂ) →L[ℂ] Zret
  hRet : Function.Injective ambientRetained
  hcompat : restrictSource.comp bSource = ambientRetained.comp (restrictObservable V)
  hordinary : ComparedSpectralGap.EigenvectorComparison ((R : ℂ) • P ε)
      ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hC)
      aSource bSource (R * q)
  hgeneral : GeneralizedSpectralComparison.Comparison ((R : ℂ) • P ε)
      ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hC)
      aSource bSource ((R * (o.eigenvalue ε).re : ℝ) : ℂ)
  hreverse : CutoffEigenvectorLifting.ClassicalRealization ((R : ℂ) • P ε)
      ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hC)
      aSource bSource (R * q)
  hUltra : StrongFellerSquareCompact.UltraFellerContract (X := Y)
  hFredholm : PowerCompactGap.SquareCompactFredholm (F := Y →ᵇ ℂ)
  hRiesz : PowerCompactRealLeadingPair.ClassicalContract (X := Y)

variable (o : ProjectorOutputs P i d q δ) (hδsub : δ < q - d.subordinate)
  (hδlead : δ < d.rate - q) (hq : 0 < q) (ε : ℝ≥0)
  (C D : AbsorbingMarkovChains.CanonicalChain Y)
  (hC : HasStrongFellerKernel C) (hD : HasStrongFellerKernel D) (R : ℝ) (hR : 0 < R)
  (s : SameCutoffClassicalSources (Z := Z) (Zret := Zret) o ε C D hC hD R)

def SameCutoffClassicalSources.originalInputs :
    StrongFellerSpectralInputs (E := E) (W := W) (Z := Zret) D hD R :=
  strongFellerInputsOfSameCutoffSources o hδsub hδlead hq ε s.parameterSmall
    s.conjugation R hR C D hC hD s.V s.BC s.BD s.hV s.heq
    s.hreturnC s.hextC s.hreturnD s.hextD s.NC s.ND s.hcompC s.hcompD R hR
    s.aSource s.bSource s.restrictSource s.ambientRetained s.hRet s.hcompat
    s.hordinary s.hgeneral s.hreverse s.hUltra s.hFredholm s.hRiesz

def SameCutoffClassicalSources.cutoffInputs :
    StrongFellerSpectralInputs (E := E) (W := W) (Z := Zret) C hC R :=
  strongFellerInputsOfSameCutoffSources o hδsub hδlead hq ε s.parameterSmall
    s.conjugation R hR C C hC hC s.V s.BC s.BC s.hV rfl
    s.hreturnC s.hextC s.hreturnC s.hextC s.NC s.NC s.hcompC s.hcompC R hR
    s.aSource s.bSource s.restrictSource s.ambientRetained s.hRet s.hcompat
    s.hordinary s.hgeneral s.hreverse s.hUltra s.hFredholm s.hRiesz

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
