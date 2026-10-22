module

public import LeanShared.Geometry.RegularTestPairingFaithful
public import LeanShared.Analysis.DyadicCompletion
public import LeanShared.Analysis.CommonAmbientGlobalTests

/-! The regular tests on the retained open region are a constructed closed
subspace of the original regular space. Its inclusion has inherited norm;
its dual restriction is consequently bounded without an extra source. -/

@[expose] public noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped Manifold ContDiff BoundedContinuousFunction
namespace LeanShared.RetainedRegularTests
open SmoothSupportedManifoldCore DyadicCompletion
variable {E M Reg : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  (U : Opens M) (V K : Set M) [CompactSpace K]

 def retained : Set K := {x | x.val ∈ (U : Set M)}

def intoK (hUK : (U : Set M) ⊆ K) : C(U, K) :=
  ⟨fun x => ⟨x.val, hUK x.property⟩, by fun_prop⟩

def retainedHomeomorph (hUK : (U : Set M) ⊆ K) : U ≃ₜ retained U K where
  toFun x := ⟨⟨x.val, hUK x.property⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

omit [FiniteDimensional ℝ E] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [CompactSpace K] in
theorem intoK_openEmbedding (hUK : (U : Set M) ⊆ K) :
    Topology.IsOpenEmbedding (intoK U K hUK) := by
  have hret : IsOpen (retained U K) := U.isOpen.preimage continuous_subtype_val
  exact hret.isOpenEmbedding_subtypeVal.comp (retainedHomeomorph U K hUK).isOpenEmbedding

def coreInclusion (hUV : (U : Set M) ⊆ V) : core (E := E) (U : Set M) →ₗ[ℂ] core (E := E) V where
  toFun c := ⟨c.val, c.property.1, c.property.2.trans hUV⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coreMap (q : core (E := E) V →ₗ[ℂ] Reg) (hUV : (U : Set M) ⊆ V) :
    core (E := E) (U : Set M) →ₗ[ℂ] Reg := q.comp (coreInclusion (E := E) U V hUV)

def space (q : core (E := E) V →ₗ[ℂ] Reg) (hUV : (U : Set M) ⊆ V) : Submodule ℂ Reg :=
  closedCore (coreMap U V q hUV)

def restriction (q : core (E := E) V →ₗ[ℂ] Reg) (hUV : (U : Set M) ⊆ V) :
    (Reg →L[ℂ] ℂ) →L[ℂ] (space U V q hUV →L[ℂ] ℂ) :=
  CommonAmbientGlobalTests.restriction (space U V q hUV).subtypeL

def physical (q : core (E := E) V →ₗ[ℂ] Reg) (hUV : (U : Set M) ⊆ V)
    (hUK : (U : Set M) ⊆ K) (p : Reg →L[ℂ] (K →ᵇ ℂ)) :
    space U V q hUV →L[ℂ] (U →ᵇ ℂ) :=
  (BoundedContinuousFunction.compContinuousCLM ℂ ℂ (intoK U K hUK)).comp
    (p.comp (space U V q hUV).subtypeL)

variable (q : core (E := E) V →ₗ[ℂ] Reg) (hUV : (U : Set M) ⊆ V)
  (hUK : (U : Set M) ⊆ K) (p : Reg →L[ℂ] (K →ᵇ ℂ))
  (hp : ∀ c, p (q c) = physicalCore V K c)

omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
include hp in
theorem physical_core (c : core (E := E) (U : Set M)) (x : U) :
    physical U V K q hUV hUK p (coreLift (coreMap U V q hUV) c) x = c.val x.val := by
  change p (q (coreInclusion (E := E) U V hUV c)) (intoK U K hUK x) = _
  rw [hp]
  rfl

omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
include hp in
theorem zero_outside (v : space U V q hUV) (x : K) (hx : x.val ∉ (U : Set M)) :
    p v.val x = 0 := by
  apply (coreLift_dense (coreMap U V q hUV)).induction_on
    (p := fun z => p z.val x = 0) v
    (isClosed_eq (((BoundedContinuousFunction.evalCLM ℂ x).comp p).comp
      (space U V q hUV).subtypeL).continuous continuous_const)
  intro c
  change p (q (coreInclusion (E := E) U V hUV c)) x = 0
  rw [hp]
  exact SmoothSupportedManifoldCore.zero_outside (U : Set M) c x.val hx

omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
include hp in
theorem contains_smooth_compact_tests (g : U → ℝ)
    (smooth : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ)) ∞ g) (compact : HasCompactSupport g) :
    ∃ v : space U V q hUV, ∀ x, physical U V K q hUV hUK p v x = (g x : ℂ) := by
  let ext : M → ℝ := Subtype.val.extend g 0
  have extSmooth : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ)) ∞ ext := smooth.extend_zero compact
  have extSupport : tsupport ext ⊆ (U : Set M) :=
    (compact.tsupport_extend_zero_subset continuous_subtype_val).trans
      (Subtype.coe_image_subset _ _)
  let c : core (E := E) (U : Set M) := ⟨fun x => (ext x : ℂ),
    Complex.ofRealCLM.contMDiff.comp extSmooth, (closure_mono (by
      intro x hx
      exact fun hz => hx (by simp [hz]))).trans extSupport⟩
  refine ⟨coreLift (coreMap U V q hUV) c, ?_⟩
  intro x
  rw [physical_core U V K q hUV hUK p hp c x]
  change (ext x.val : ℂ) = (g x : ℂ)
  dsimp only [ext]
  rw [Subtype.val_injective.extend_apply]

end LeanShared.RetainedRegularTests
