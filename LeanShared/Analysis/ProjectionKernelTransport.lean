module

public import LeanShared.Analysis.IntertwiningProjectionTransport
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Pi
public import Mathlib.Topology.Algebra.Module.Equiv.Prod
public import Mathlib.Topology.Algebra.Module.Equiv.Submodule

/-! Nearby continuous projections give actual local trivializations of their
kernels. No choice or continuity of moving bases is assumed. -/
public noncomputable section
namespace LeanShared.IntertwiningProjectionTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem map_kernel (P Q : E →L[ℝ] E)
    (hp : ∀ v, P (P v) = P v) (hq : ∀ v, Q (Q v) = Q v)
    (small : ‖P-Q‖ * (2*‖P‖+1) < 1) :
    P.ker.map (equivalence P Q hp small).toLinearMap = Q.ker := by
  have commute (v : E) : Q (equivalence P Q hp small v) =
      equivalence P Q hp small (P v) :=
    congrArg (fun A : E →L[ℝ] E => A v) (commutes P Q hp hq)
  ext v
  constructor
  · rintro ⟨u,hu,rfl⟩
    change Q (equivalence P Q hp small u)=0
    rw [commute, show P u=0 from hu, map_zero]
  · intro hv
    obtain ⟨u,rfl⟩ := (equivalence P Q hp small).surjective v
    refine ⟨u,?_,rfl⟩
    apply (equivalence P Q hp small).injective
    change equivalence P Q hp small (P u) = equivalence P Q hp small 0
    rw [map_zero,←commute]
    exact hv

@[expose] def kernelEquivalence (P Q : E →L[ℝ] E)
    (hp : ∀ v, P (P v) = P v) (hq : ∀ v, Q (Q v) = Q v)
    (small : ‖P-Q‖ * (2*‖P‖+1) < 1) : P.ker ≃L[ℝ] Q.ker :=
  (equivalence P Q hp small).ofSubmodules P.ker Q.ker (map_kernel P Q hp hq small)

theorem kernelEquivalence_apply (P Q : E →L[ℝ] E)
    (hp : ∀ v, P (P v) = P v) (hq : ∀ v, Q (Q v) = Q v)
    (small : ‖P-Q‖ * (2*‖P‖+1) < 1) (v : P.ker) :
    (kernelEquivalence P Q hp hq small v).val = transport P Q v.val := rfl

omit [CompleteSpace E] in
theorem continuous_kernel_frame {X : Type*} [TopologicalSpace X]
    (P : E →L[ℝ] E) {Q : X → E →L[ℝ] E} (continuousQ : Continuous Q) :
    Continuous (fun x => (transport P (Q x)).comp P.ker.subtypeL) := by
  exact ((continuousQ.clm_comp_const P).add
    ((continuous_const.sub continuousQ).clm_comp_const
      (ContinuousLinearMap.id ℝ E - P))).clm_comp_const P.ker.subtypeL

end LeanShared.IntertwiningProjectionTransport
