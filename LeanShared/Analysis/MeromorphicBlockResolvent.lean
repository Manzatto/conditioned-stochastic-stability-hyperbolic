module

public import LeanShared.Analysis.BlockResolvent
public import LeanShared.Analysis.MeromorphicLinearMap

/-! Meromorphic resolvents of diagonal blocks assemble to a meromorphic
resolvent of their actual direct sum. -/

public section
open Filter Topology ContinuousLinearMap
namespace LeanShared.MeromorphicBlockResolvent
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Pair two Banach-valued meromorphic germs. -/
theorem pair {f : ℂ → E} {g : ℂ → F} {z : ℂ}
    (hf : MeromorphicAt f z) (hg : MeromorphicAt g z) :
    MeromorphicAt (fun w => (f w, g w)) z := by
  have left := MeromorphicLinearMap.map (inl ℂ E F) hf
  have right := MeromorphicLinearMap.map (inr ℂ E F) hg
  have sum : MeromorphicAt (fun w => (f w, (0 : F)) + ((0 : E), g w)) z := left.add right
  simpa only [Pi.add_apply, inl_apply, inr_apply, Prod.mk_add_mk, add_zero, zero_add] using sum

/-- Actual diagonal resolvents are meromorphic whenever both actual block
resolvents are meromorphic and jointly defined on a punctured neighbourhood. -/
theorem meromorphicAt (A : E →L[ℂ] E) (B : F →L[ℂ] F) (z : ℂ)
    (hA : MeromorphicAt (resolvent A) z) (hB : MeromorphicAt (resolvent B) z)
    (hres : ∀ᶠ w in 𝓝[≠] z, w ∈ resolventSet ℂ A ∧ w ∈ resolventSet ℂ B) :
    MeromorphicAt (resolvent (A.prodMap B)) z := by
  have paired := pair hA hB
  have mapped := MeromorphicLinearMap.map (prodMapL ℂ E E F F) paired
  apply mapped.congr
  filter_upwards [hres] with w hw
  exact (BlockResolvent.formula A B w hw.1 hw.2).2.symm

end LeanShared.MeromorphicBlockResolvent
