module
public import Mathlib.Topology.Homeomorph.Lemmas

/-! A jointly continuous family of genuine equivalences on compact spaces
has jointly continuous inverses. The skew-product homeomorphism is constructed
from compactness; parameter regularity is not assumed for the inverses. -/
public noncomputable section
namespace LeanShared.CompactParametricInverse

 theorem continuous_inverse
    {A X : Type*} [TopologicalSpace A] [CompactSpace A] [T2Space A]
    [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (e : A → X ≃ X) (joint : Continuous (fun p : A × X => e p.1 p.2)) :
    Continuous (fun p : A × X => (e p.1).symm p.2) := by
  let skew : A × X ≃ A × X := {
    toFun := fun p => (p.1,e p.1 p.2)
    invFun := fun p => (p.1,(e p.1).symm p.2)
    left_inv := by intro p; exact Prod.ext rfl ((e p.1).symm_apply_apply p.2)
    right_inv := by intro p; exact Prod.ext rfl ((e p.1).apply_symm_apply p.2) }
  have continuousSkew : Continuous skew := continuous_fst.prodMk joint
  let h := continuousSkew.homeoOfEquivCompactToT2
  exact continuous_snd.comp h.symm.continuous

end LeanShared.CompactParametricInverse
