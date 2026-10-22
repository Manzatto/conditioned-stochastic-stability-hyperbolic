module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Complex.Basic

@[expose] public noncomputable section
namespace LeanShared.DualNormedSpaceParent

@[instance_reducible] def normedSpace {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] :
    letI : SeminormedAddCommGroup (H →L[ℂ] ℂ) :=
      (inferInstance : NormedAddCommGroup (H →L[ℂ] ℂ)).toSeminormedAddCommGroup
    NormedSpace ℂ (H →L[ℂ] ℂ) := by
  infer_instance

end LeanShared.DualNormedSpaceParent
