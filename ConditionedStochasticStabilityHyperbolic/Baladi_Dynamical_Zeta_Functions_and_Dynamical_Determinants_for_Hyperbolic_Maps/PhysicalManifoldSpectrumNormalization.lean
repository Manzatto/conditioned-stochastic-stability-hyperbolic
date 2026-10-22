module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldModel

/-! Spectrum through the generic and concrete operator ring structures. -/

public noncomputable section
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff SchwartzMap BigOperators
namespace ConditionedStochasticStabilityHyperbolic.PhysicalManifoldModel
open LeanShared DyadicCompletion CompletedChartPairTransfer FiniteRegularTransferRealization

variable {E U M AtlasIndex Reg A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]

@[expose, instance_reducible] def genericRing {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] :
    Ring (H →L[ℂ] H) := inferInstance

@[expose, instance_reducible] def genericAlgebra {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] :
    @Algebra ℂ (H →L[ℂ] H) inferInstance (genericRing.toSemiring) := inferInstance

@[expose] def genericSpectrum {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (P : H →L[ℂ] H) : Set ℂ := spectrum ℂ P

namespace Data

variable {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg) (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ i, CompleteSpace (LocalReg i)] in
theorem spectrum_normalization (P : m.StrongSpace →L[ℂ] m.StrongSpace) :
    genericSpectrum P = spectrum ℂ P := by
  let targetRing : Ring (m.StrongSpace →L[ℂ] m.StrongSpace) := inferInstance
  let targetAlgebra : @Algebra ℂ (m.StrongSpace →L[ℂ] m.StrongSpace)
      inferInstance targetRing.toSemiring := inferInstance
  let e : @AlgEquiv ℂ (m.StrongSpace →L[ℂ] m.StrongSpace)
      (m.StrongSpace →L[ℂ] m.StrongSpace) inferInstance genericRing.toSemiring
      targetRing.toSemiring genericAlgebra targetAlgebra := {
    toEquiv := Equiv.refl _
    map_mul' := by intro f g; apply DFunLike.coe_injective; funext v; rfl
    map_add' := by intro f g; apply DFunLike.coe_injective; funext v; apply Subtype.ext; rfl
    commutes' := by intro z; apply DFunLike.coe_injective; funext v; apply Subtype.ext; rfl }
  have equality := @AlgEquiv.spectrum_eq _ ℂ
    (m.StrongSpace →L[ℂ] m.StrongSpace) (m.StrongSpace →L[ℂ] m.StrongSpace)
    inferInstance genericRing targetRing genericAlgebra targetAlgebra inferInstance inferInstance e P
  have applied : e P = P := rfl
  have targetEquality := congrArg (fun Q => @spectrum ℂ
    (m.StrongSpace →L[ℂ] m.StrongSpace) inferInstance targetRing targetAlgebra Q) applied
  exact equality.symm.trans targetEquality

end Data
end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldModel
