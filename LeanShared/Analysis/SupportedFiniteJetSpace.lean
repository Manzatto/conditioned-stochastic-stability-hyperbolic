module
public import LeanShared.Analysis.BoundedFiniteJetEvaluation
public import LeanShared.Analysis.CompatibleJetMollification

/-! A fixed physical frequency support defines a closed Banach subspace
of the actual compatible finite jet graph. Integration and regularization
in this space preserve frequency support automatically. -/
public noncomputable section
open Set
open scoped ContDiff BoundedContinuousFunction
namespace LeanShared.SupportedFiniteJetSpace
variable {Z:Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

@[expose] def space (n:ℕ) (K:Set Z):Submodule ℂ (CompatibleJetMollification.Jet Z n) where
  carrier:={q|∀z,z∉K→(BoundedFiniteJetSpace.construct n (F:=ℂ)).physical q z=0}
  zero_mem':=by intro z _;rw [map_zero];rfl
  add_mem':=by
    intro q q' hq hq' z hz
    simp only [map_add,BoundedContinuousFunction.add_apply,hq z hz,hq' z hz,add_zero]
  smul_mem':=by
    intro c q hq z hz
    simp only [map_smul,BoundedContinuousFunction.smul_apply,hq z hz,smul_zero]

theorem closed (n:ℕ) (K:Set Z):IsClosed (space n K:Set (CompatibleJetMollification.Jet Z n)):=by
  change IsClosed {q|∀z,z∉K→(BoundedFiniteJetSpace.construct n (F:=ℂ)).physical q z=0}
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro z
  apply isClosed_iInter
  intro _
  exact isClosed_eq
    (((BoundedContinuousFunction.evalCLM ℂ z).comp
      (BoundedFiniteJetSpace.construct n (F:=ℂ)).physical).continuous) continuous_const

instance complete (n:ℕ) (K:Set Z):CompleteSpace (space n K):=(closed n K).completeSpace_coe

theorem tsupport_subset (n:ℕ) {K:Set Z} (closedK:IsClosed K) (q:space n K):
    tsupport (fun z=>(BoundedFiniteJetSpace.construct n (F:=ℂ)).physical q.val z)⊆K:=by
  apply closure_minimal _ closedK
  intro z hz
  by_contra outside
  exact hz (q.property z outside)

theorem compact_support (n:ℕ) {K:Set Z} (compact:IsCompact K) (q:space n K):
    HasCompactSupport (fun z=>(BoundedFiniteJetSpace.construct n (F:=ℂ)).physical q.val z):=
  compact.of_isClosed_subset (isClosed_tsupport _) (tsupport_subset n compact.isClosed q)
end LeanShared.SupportedFiniteJetSpace
