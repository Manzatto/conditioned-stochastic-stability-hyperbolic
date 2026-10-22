module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelFullTestDistribution
public import LeanShared.Geometry.SupportedCorePhysicalRealization
meta import Lean.LibrarySuggestions.Basic

/-! The native supported-core pairing, stated over an abstract normed test space. A strong-space
distribution `a` on the tests whose core values are the literal reference integral, composed
with a regular-to-test inclusion `inc` whose tests view the regular functions, gives a
strong-to- regular-dual pairing whose smooth values are integrals over any closed `K ⊇ V` for
the comapped reference measure. The full-test identities `smoothFull` and `smoothRestriction` of
the scale-source companion follow. The test space is kept abstract so that no reduction through
a concrete test carrier is needed. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalModelNativeCoreData"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set MeasureTheory IsManifold
open scoped Manifold ContDiff SchwartzMap BoundedContinuousFunction NNReal
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelNativeCoreData
open LeanShared DyadicCompletion PhysicalManifoldModel SmoothSupportedManifoldCore

variable {E U M AtlasIndex Reg A Ω Test : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [T2Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]
  [NormedAddCommGroup Test] [NormedSpace ℂ Test]
  {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)
  (ν : Measure M) (a : m.StrongSpace →L[ℂ] (Test →L[ℂ] ℂ)) (view : Test → M → ℂ)
  (core : ∀ c t, a (coreLift m.qa c) t = ∫ x, functions V c x * view t x ∂ν)
  (inc : Reg →L[ℂ] Test) (incView : ∀ r x, view (inc r) x = m.view r x)

/-- The strong-to-regular-dual pairing through the tests. -/
def regEmbedding : m.StrongSpace →L[ℂ] (Reg →L[ℂ] ℂ) :=
  (ContinuousLinearMap.compL ℂ Reg Test ℂ).flip inc ∘L a

theorem regEmbedding_apply (z : m.StrongSpace) (r : Reg) :
    regEmbedding m a inc z r = a z (inc r) := rfl

/-- The integral of a function supported in `V` is the integral over a closed `K ⊇ V`. -/
theorem integral_on (K : Set M) (hK : IsClosed K) (hVK : V ⊆ K) (c : Core (E := E) V)
    (g : M → ℂ) :
    (∫ x, functions V c x * g x ∂ν) =
      ∫ x : K, functions V c x.val * g x.val ∂(ν.comap Subtype.val) := by
  rw [integral_subtype_comap hK.measurableSet (fun x => functions V c x * g x)]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have zero : functions V c x = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => hx (hVK (c.property.2 h)))
  rw [zero, zero_mul]

include core incView in
/-- The smooth pairing identity. -/
theorem regEmbedding_pairing (K : Set M) (hK : IsClosed K) (hVK : V ⊆ K)
    (c e : Core (E := E) V) :
    regEmbedding m a inc (coreLift m.qa c) (m.regularCore e) =
      ∫ x : K, functions V c x.val * functions V e x.val ∂(ν.comap Subtype.val) := by
  rw [regEmbedding_apply, core]
  simp_rw [incView, m.view_core]
  exact integral_on ν K hK hVK c (functions V e)

include core in
/-- The `smoothFull` identity. -/
theorem smoothFull (K : Set M) [CompactSpace K] (hK : IsClosed K) (hVK : V ⊆ K)
    (globalPhysical : Test →L[ℂ] (K →ᵇ ℂ)) (glob : ∀ t (x : K), globalPhysical t x = view t x.val)
    (c : Core (E := E) V) (t : Test) :
    a (coreLift m.qa c) t =
      ∫ x : K, physicalCore V K c x * globalPhysical t x ∂(ν.comap Subtype.val) := by
  rw [core]
  simp_rw [glob]
  exact integral_on ν K hK hVK c (view t)

end ConditionedStochasticStabilityHyperbolic.PhysicalModelNativeCoreData
