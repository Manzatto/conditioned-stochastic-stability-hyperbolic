module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Complex.Basic

@[expose] public noncomputable section
namespace LeanShared.SubmoduleNormedSpaceParent
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

@[instance_reducible] def seminormed (s : Submodule ℂ H) : SeminormedAddCommGroup s :=
  (inferInstance : NormedAddCommGroup s).toSeminormedAddCommGroup

@[instance_reducible] def normedSpace (s : Submodule ℂ H) :
    letI : SeminormedAddCommGroup s := seminormed s
    NormedSpace ℂ s := by
  infer_instance

end LeanShared.SubmoduleNormedSpaceParent
