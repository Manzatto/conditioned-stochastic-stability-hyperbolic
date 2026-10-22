module

public import ConditionedStochasticStabilityHyperbolic.Global.RestrictedLayerChain
public import Mathlib.Logic.Equiv.Basic

/-!
# Exact flattening of recursively killed filtration states

Successive restrictions to nested measurable levels give exactly the direct
restriction to the smaller level, after the canonical subtype identification.
This supplies actual kernel identities for the finite-layer recursion; no
coordinate/operator conjugacy is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.Global.NestedLayerKernel

variable {X : Type*} [MeasurableSpace X]
  (U V : Set X) (hUV : U ⊆ V)

/-- The smaller level inside the larger live-state subtype. -/
def innerLevel : Set V := Subtype.val ⁻¹' U

/-- Flatten the two actual subtype memberships using filtration nesting. -/
def flatten : innerLevel U V ≃ᵐ U where
  toEquiv := {
    toFun x := ⟨x.val.val, x.property⟩
    invFun x := ⟨⟨x.val, hUV x.property⟩, x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  measurable_toFun := (measurable_subtype_coe.comp measurable_subtype_coe).subtype_mk
  measurable_invFun := measurable_subtype_coe.subtype_mk.subtype_mk

@[simp] theorem flatten_val (x : innerLevel U V) : (flatten U V hUV x).val = x.val.val := rfl

/-- Successive killed kernel restrictions are the direct smaller killed
kernel under the literal source/destination subtype identification. -/
theorem map_nested_restriction (K : Kernel X X) (hU : MeasurableSet U) (hV : MeasurableSet V) :
    (LeanShared.SubtypeKernel.restrict (LeanShared.SubtypeKernel.restrict K V hV)
      (innerLevel U V) (hU.preimage measurable_subtype_coe)).map (flatten U V hUV) =
        (LeanShared.SubtypeKernel.restrict K U hU).comap (flatten U V hUV) (flatten U V hUV).measurable := by
  ext x A hA
  rw [Kernel.map_apply _ (flatten U V hUV).measurable,
    Measure.map_apply (flatten U V hUV).measurable hA,
    LeanShared.SubtypeKernel.restrict_apply_set _ (innerLevel U V)
      (hU.preimage measurable_subtype_coe) x _ (hA.preimage (flatten U V hUV).measurable)]
  have hAinner : MeasurableSet (Subtype.val '' ((flatten U V hUV) ⁻¹' A)) :=
    (MeasurableEmbedding.subtype_coe (hU.preimage measurable_subtype_coe)).measurableSet_image.2
      (hA.preimage (flatten U V hUV).measurable)
  rw [LeanShared.SubtypeKernel.restrict_apply_set _ V hV x.val _ hAinner,
    Kernel.comap_apply, LeanShared.SubtypeKernel.restrict_apply_set _ U hU _ A hA]
  congr 1
  ext y
  constructor
  · rintro ⟨v, ⟨z, hz, hzy⟩, rfl⟩
    subst v
    exact ⟨flatten U V hUV z, hz, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    let z := (flatten U V hUV).symm u
    refine ⟨z.val, ⟨z, ?_, rfl⟩, ?_⟩
    · simpa only [z, Set.mem_preimage, MeasurableEquiv.apply_symm_apply] using hu
    · rfl

/-- The same exact identity for the actual canonical chains used in the
finite-filtration proof. Only killed kernels enter spectral/path calculations. -/
theorem map_nested_killedTransition (C : AbsorbingMarkovChains.CanonicalChain X)
    (hU : MeasurableSet U) (hV : MeasurableSet V) :
    (RestrictedLayerChain.chain (RestrictedLayerChain.chain C V hV) (innerLevel U V)
      (hU.preimage measurable_subtype_coe)).killedTransition.map (flatten U V hUV) =
        (RestrictedLayerChain.chain C U hU).killedTransition.comap (flatten U V hUV)
          (flatten U V hUV).measurable := by
  have hn := RestrictedLayerChain.killedTransition (RestrictedLayerChain.chain C V hV)
    (innerLevel U V) (hU.preimage measurable_subtype_coe)
  have hi := RestrictedLayerChain.killedTransition C V hV
  have hd := RestrictedLayerChain.killedTransition C U hU
  calc
    _ = (LeanShared.SubtypeKernel.restrict (RestrictedLayerChain.chain C V hV).killedTransition
        (innerLevel U V) (hU.preimage measurable_subtype_coe)).map (flatten U V hUV) :=
      congrArg (fun K => K.map (flatten U V hUV)) hn
    _ = (LeanShared.SubtypeKernel.restrict (LeanShared.SubtypeKernel.restrict C.killedTransition V hV)
        (innerLevel U V) (hU.preimage measurable_subtype_coe)).map (flatten U V hUV) :=
      congrArg (fun K => (LeanShared.SubtypeKernel.restrict K (innerLevel U V)
        (hU.preimage measurable_subtype_coe)).map (flatten U V hUV)) hi
    _ = (LeanShared.SubtypeKernel.restrict C.killedTransition U hU).comap
        (flatten U V hUV) (flatten U V hUV).measurable := map_nested_restriction U V hUV _ hU hV
    _ = _ := congrArg (fun K => K.comap (flatten U V hUV) (flatten U V hUV).measurable) hd.symm

section Topology

variable [TopologicalSpace X]

def flattenHomeomorph : innerLevel U V ≃ₜ U where
  toEquiv := (flatten U V hUV).toEquiv
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk (fun x => x.property)
  continuous_invFun := (continuous_subtype_val.subtype_mk (fun x : U => hUV x.property)).subtype_mk
    (fun x => x.property)

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Actual bounded continuous coordinates under the canonical flattening. -/
def pullback : (U →ᵇ 𝕜) →L[𝕜] (innerLevel U V →ᵇ 𝕜) :=
  BoundedContinuousFunction.compContinuousCLM 𝕜 𝕜
    ⟨flattenHomeomorph U V hUV, (flattenHomeomorph U V hUV).continuous⟩

def pullbackInv : (innerLevel U V →ᵇ 𝕜) →L[𝕜] (U →ᵇ 𝕜) :=
  BoundedContinuousFunction.compContinuousCLM 𝕜 𝕜
    ⟨(flattenHomeomorph U V hUV).symm, (flattenHomeomorph U V hUV).symm.continuous⟩

theorem pullback_inv_apply (f : U →ᵇ 𝕜) : pullbackInv U V hUV (pullback U V hUV f) = f := by
  ext x
  rfl

theorem pullback_apply_inv (f : innerLevel U V →ᵇ 𝕜) : pullback U V hUV (pullbackInv U V hUV f) = f := by
  ext x
  rfl

theorem pullback_norm (f : U →ᵇ 𝕜) : ‖pullback U V hUV f‖ = ‖f‖ := by
  apply le_antisymm
  · exact BoundedContinuousFunction.norm_compContinuous_le _ _
  · apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
    intro x
    have hh := (pullback U V hUV f).norm_coe_le_norm ((flatten U V hUV).symm x)
    exact hh

theorem pullbackInv_norm (f : innerLevel U V →ᵇ 𝕜) : ‖pullbackInv U V hUV f‖ = ‖f‖ := by
  rw [← pullback_norm U V hUV (pullbackInv U V hUV f), pullback_apply_inv]

variable [OpensMeasurableSpace X]
  (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
  (hU : MeasurableSet U) (hV : MeasurableSet V)

local notation "Cinner" => RestrictedLayerChain.chain (RestrictedLayerChain.chain C V hV)
  (innerLevel U V) (hU.preimage measurable_subtype_coe)
local notation "SFinner" => RestrictedLayerChain.strongFeller (RestrictedLayerChain.chain C V hV)
  (RestrictedLayerChain.strongFeller C hSF V hV) (innerLevel U V) (hU.preimage measurable_subtype_coe)
local notation "Cdirect" => RestrictedLayerChain.chain C U hU
local notation "SFdirect" => RestrictedLayerChain.strongFeller C hSF U hU

/-- The actual nested and direct strong-Feller transfers intertwine under
isometric continuous coordinates. -/
theorem transfer_nested_pullback (f : U →ᵇ 𝕜) :
    ComplexStrongFeller.transferOperator (𝕜 := 𝕜) (Cinner) (SFinner) (pullback U V hUV f) =
      pullback U V hUV (ComplexStrongFeller.transferOperator (𝕜 := 𝕜) (Cdirect) (SFdirect) f) := by
  ext x
  change (∫ y, f (flatten U V hUV y) ∂(Cinner).killedTransition x) =
    ∫ y, f y ∂(Cdirect).killedTransition (flatten U V hUV x)
  have he := congrArg (fun K => K x) (map_nested_killedTransition U V hUV C hU hV)
  rw [Kernel.map_apply _ (flatten U V hUV).measurable, Kernel.comap_apply] at he
  rw [← integral_map_of_stronglyMeasurable (flatten U V hUV).measurable f.continuous.measurable.stronglyMeasurable,
    he]

/-- Every raw transfer power respects the same actual state identification. -/
theorem powers_nested_pullback (c : 𝕜) (n : ℕ) (f : U →ᵇ 𝕜) :
    ((c • ComplexStrongFeller.transferOperator (𝕜 := 𝕜) (Cinner) (SFinner)) ^ n) (pullback U V hUV f) =
      pullback U V hUV (((c • ComplexStrongFeller.transferOperator (𝕜 := 𝕜) (Cdirect) (SFdirect)) ^ n) f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', pow_succ', mul_apply_eq_comp, mul_apply_eq_comp, smul_apply, smul_apply,
        ih, transfer_nested_pullback U V hUV C hSF hU hV, map_smul]

include hUV in
/-- Nested-filtration terminal growth bounds can be copied directly from
the ambient smaller-level model, with no loss of rate or constant. -/
theorem nested_power_norm_eq (c : 𝕜) (n : ℕ) :
    ‖(c • ComplexStrongFeller.transferOperator (𝕜 := 𝕜) (Cinner) (SFinner)) ^ n‖ =
      ‖(c • ComplexStrongFeller.transferOperator (𝕜 := 𝕜) (Cdirect) (SFdirect)) ^ n‖ := by
  let P := c • ComplexStrongFeller.transferOperator (𝕜 := 𝕜) (Cinner) (SFinner)
  let Q := c • ComplexStrongFeller.transferOperator (𝕜 := 𝕜) (Cdirect) (SFdirect)
  apply le_antisymm
  · apply (P ^ n).opNorm_le_bound (norm_nonneg _)
    intro f
    calc
      ‖(P ^ n) f‖ = ‖(P ^ n) (pullback U V hUV (pullbackInv U V hUV f))‖ := by rw [pullback_apply_inv]
      _ = ‖pullback U V hUV ((Q ^ n) (pullbackInv U V hUV f))‖ := by
        rw [powers_nested_pullback U V hUV C hSF hU hV]
      _ = ‖(Q ^ n) (pullbackInv U V hUV f)‖ := pullback_norm U V hUV _
      _ ≤ ‖Q ^ n‖ * ‖pullbackInv U V hUV f‖ := (Q ^ n).le_opNorm _
      _ = ‖Q ^ n‖ * ‖f‖ := by rw [pullbackInv_norm]
  · apply (Q ^ n).opNorm_le_bound (norm_nonneg _)
    intro f
    calc
      ‖(Q ^ n) f‖ = ‖pullback U V hUV ((Q ^ n) f)‖ := (pullback_norm U V hUV _).symm
      _ = ‖(P ^ n) (pullback U V hUV f)‖ := by
        rw [powers_nested_pullback U V hUV C hSF hU hV]
      _ ≤ ‖P ^ n‖ * ‖pullback U V hUV f‖ := (P ^ n).le_opNorm _
      _ = ‖P ^ n‖ * ‖f‖ := by rw [pullback_norm]

end Topology

end ConditionedStochasticStabilityHyperbolic.Global.NestedLayerKernel
