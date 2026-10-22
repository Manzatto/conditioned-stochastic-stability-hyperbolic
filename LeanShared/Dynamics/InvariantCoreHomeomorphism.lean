module
public import Mathlib.Topology.Homeomorph.Lemmas

/-! The actual restriction of a homeomorphism to an invariant set is a
homeomorphism, with literal ambient value and no extra inverse invariance. -/
public noncomputable section
namespace LeanShared
open Set
variable {X:Type*} [TopologicalSpace X]

@[expose] def invariantCoreHomeomorphism (T:X≃ₜX) (K:Set X) (invariant:T '' K=K) : K≃ₜK :=
  T.subtype (fun x=>by
    constructor
    · intro hx
      rw [←invariant]
      exact mem_image_of_mem T hx
    · intro hx
      rw [←invariant] at hx
      obtain ⟨y,hy,equal⟩ := hx
      exact T.injective equal ▸ hy)

theorem invariantCoreHomeomorphism_apply (T:X≃ₜX) (K:Set X) (invariant:T '' K=K) (x:K) :
    (invariantCoreHomeomorphism T K invariant x).val=T x.val := rfl

end LeanShared
