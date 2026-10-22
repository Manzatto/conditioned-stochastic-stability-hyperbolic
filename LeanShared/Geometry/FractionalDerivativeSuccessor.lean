module
public import LeanShared.Geometry.FractionalManifoldRegularity
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! Genuine higher fractional regularity is reconstructed recursively from
the derivative. Currying is an actual isometry of derivative tensors. -/
public noncomputable section
open Set
open scoped Manifold ContDiff
namespace LeanShared.FractionalManifoldRegularity
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_iterated_difference_succ (f : E → F) (n : ℕ) (x y : E) :
    ‖iteratedFDeriv ℝ (n+1) f x-iteratedFDeriv ℝ (n+1) f y‖ =
      ‖iteratedFDeriv ℝ n (fderiv ℝ f) x-iteratedFDeriv ℝ n (fderiv ℝ f) y‖ := by
  simp only [iteratedFDeriv_succ_eq_comp_right,Function.comp_apply]
  let e := (continuousMultilinearCurryRightEquiv' ℝ n E F).symm
  have equal := e.map_sub (iteratedFDeriv ℝ n (fderiv ℝ f) x) (iteratedFDeriv ℝ n (fderiv ℝ f) y)
  exact (congrArg (fun z => ‖z‖) equal).symm.trans (e.norm_map _)

theorem regular_of_regular_fderiv {f : E → F} {r : ℝ}
    (differentiable : Differentiable ℝ f)
    (derivativeRegular : Regular (E:=E) (F:=E →L[ℝ] F) r (fderiv ℝ f)) :
    Regular (E:=E) (F:=F) (r+1) f := by
  have floor : ⌊r+1⌋₊=⌊r⌋₊+1 := Nat.floor_add_one derivativeRegular.nonnegative
  refine ⟨by linarith [derivativeRegular.nonnegative],?_,?_⟩
  · rw [floor]
    apply ContDiff.contMDiff
    change ContDiff ℝ ((⌊r⌋₊:ℕ∞ω)+1) f
    exact contDiff_succ_iff_fderiv.mpr ⟨differentiable,by simp,derivativeRegular.differentiable.contDiff⟩
  · intro unequal x
    have unequalOld : r≠(⌊r⌋₊:ℝ) := by
      intro equal
      apply unequal
      rw [floor,Nat.cast_add,Nat.cast_one,←equal]
    obtain ⟨U,openU,inside,_,C,hC,bound⟩ := derivativeRegular.holder unequalOld x
    have chartF : chartMap (E:=E) (F:=F) f x=f := by simp [chartMap,chartAt_self_eq]
    have chartD : chartMap (E:=E) (F:=E →L[ℝ] F) (fderiv ℝ f) x=fderiv ℝ f := by
      simp [chartMap,chartAt_self_eq]
    have domain : chartDomain (E:=E) (F:=F) f x=univ := by simp [chartDomain,chartAt_self_eq]
    refine ⟨U,openU,inside,?_,C,hC,?_⟩
    · rw [domain]
      exact subset_univ _
    · intro y hy z hz
      rw [floor,chartF,norm_iterated_difference_succ]
      have exponent : r+1-((⌊r⌋₊+1:ℕ):ℝ)=r-(⌊r⌋₊:ℝ) := by
        rw [Nat.cast_add,Nat.cast_one]
        ring
      rw [exponent]
      simpa only [chartD] using bound y hy z hz
end LeanShared.FractionalManifoldRegularity
