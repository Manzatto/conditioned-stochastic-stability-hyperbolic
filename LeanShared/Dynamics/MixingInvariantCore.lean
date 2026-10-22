module

public import LeanShared.Dynamics.HyperbolicBasicSet
public import LeanShared.Dynamics.InvariantCoreHomeomorphism
public import LeanShared.Dynamics.PressureInvariantSubtype

/-! Literal ambient mixing on an invariant core gives mixing of its
actual subtype homeomorphism.  Relative open sets and orbit values are
transported explicitly.
-/

public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set Function
variable {X : Type*} [MetricSpace X]

theorem MixingOn.invariantCore {T : X ≃ₜ X} {K : Set X}
    (mixing : MixingOn T K) (invariant : T '' K = K) :
    MixingOn (LeanShared.invariantCoreHomeomorphism T K invariant) univ := by
  let S := LeanShared.invariantCoreHomeomorphism T K invariant
  have forward (x : K) : (S x).val = T x.val := rfl
  intro U V openU openV nonemptyU nonemptyV
  obtain ⟨U₀, openU₀, rfl⟩ := isOpen_induced_iff.mp openU
  obtain ⟨V₀, openV₀, rfl⟩ := isOpen_induced_iff.mp openV
  obtain ⟨x, hx⟩ := nonemptyU
  obtain ⟨y, hy⟩ := nonemptyV
  obtain ⟨N, hits⟩ := mixing U₀ V₀ openU₀ openV₀
    ⟨x.val, x.property, hx.2⟩ ⟨y.val, y.property, hy.2⟩
  refine ⟨N, fun n large => ?_⟩
  obtain ⟨z, ⟨inside, first⟩, last⟩ := hits n large
  refine ⟨⟨z, inside⟩, ⟨mem_univ _, first⟩, ?_⟩
  change (((S : K → K)^[n]) ⟨z, inside⟩).val ∈ V₀
  rw [ThermodynamicDefinitions.iterate_coe_restriction S forward]
  exact last

end LeanShared.HyperbolicBasicSet
