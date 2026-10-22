module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldRowSources
public import LeanShared.Analysis.WeightedTransferMatrixCoefficients

/-! The literal physical completed generator has the same iterated weighted
products as its finite-regular realization. One-step compatibility is proved
from the local row estimates and smooth-core density. The input is the actual
regular weight seed; `NativeRoughHolderCore.exists_regular_native` supplies
its native-space membership from regularity and compact support. -/

public noncomputable section
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff BigOperators

namespace ConditionedStochasticStabilityHyperbolic.PhysicalManifoldModel
open LeanShared DyadicCompletion FiniteRegularTransferRealization

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

namespace Data
variable {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex)
    (Reg := Reg) (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
/-- The regular transfer is intertwined with the actual completed generator;
the compatibility is obtained from the physical rows, not assumed. -/
theorem generator_regular_intertwining (rows : PhysicalManifoldRowSources.Data m) (a : Ω) :
    m.realize.comp (InvariantFiniteRegularTransfer.operator m.view m.view_injective
      m.maps m.weight m.invariant m.regularConstant m.regularBound a) =
      (m.generator a).comp m.realize := by
  exact InvariantFiniteRegularCompatibility.analytic_intertwining m.qa
    (SmoothSupportedManifoldCore.functions V) m.regularCore m.regularCore_dense
    m.view m.view_injective m.view_core m.realize m.realize_core m.maps m.weight
    m.invariant m.coreRegular m.regularConstant m.regularBound rows.strongBound
    (rows.produced m).strong a

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
/-- Exact power identity on the physical completion for every supported
finite-regular input. -/
theorem generator_pow_realize (rows : PhysicalManifoldRowSources.Data m)
    (a : Ω) (seed : Reg) (n : ℕ) :
    (m.generator a ^ n) (m.realize seed) =
      m.realize ((InvariantFiniteRegularTransfer.operator m.view m.view_injective
        m.maps m.weight m.invariant m.regularConstant m.regularBound a ^ n)
          seed) :=
  InvariantFiniteRegularTransfer.realize_operator_pow m.view m.view_injective
    m.maps m.weight m.invariant m.regularConstant m.regularBound m.realize
    (m.generator a) a (m.generator_regular_intertwining rows a) n _

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
/-- The weighted integral is a matrix coefficient of the literal physical
operator. The row bounds supply operator compatibility internally. -/
theorem integral_weight_product_eq_generator_coefficient [MeasurableSpace M]
    (rows : PhysicalManifoldRowSources.Data m) (a : Ω)
    (σ : Measure M) (test : M → ℂ) (pairing : m.StrongSpace →L[ℂ] ℂ)
    (hpairing : ∀ f : Reg, pairing (m.realize f) = ∫ x, m.view f x * test x ∂σ)
    (seed : Reg) (hseed : ∀ x, m.view seed x = (m.weight x : ℂ)) (n : ℕ) :
    (∫ x, (((∏ j ∈ Finset.range (n + 1), m.weight ((m.maps a)^[j] x) : ℝ) : ℂ) *
      test x) ∂σ) = pairing ((m.generator a ^ n) (m.realize seed)) :=
  InvariantFiniteRegularTransfer.integral_weight_product_eq_matrixCoefficient
    m.view m.view_injective m.maps m.weight m.invariant m.regularConstant m.regularBound
    m.realize (m.generator a) a σ test pairing hpairing
    (m.generator_regular_intertwining rows a) seed hseed n

end Data
end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldModel
