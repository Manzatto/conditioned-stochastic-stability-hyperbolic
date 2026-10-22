module
public import LeanShared.Geometry.FractionalJetCharacterization
public import LeanShared.Geometry.LocalFractionalJetAddition

/-! Actual finite sums preserve every positive noninteger chart order. -/
public noncomputable section
open IsManifold
open scoped Manifold ContDiff
namespace LeanShared.FractionalManifoldRegularity
variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M]

theorem Regular.add_noninteger {a : ℝ} {n : ℕ} (ha : 0 < a) (ha1 : a < 1)
    {f g : M → F} (hf : Regular (E := E) (F := F) (a+n) f)
    (hg : Regular (E := E) (F := F) (a+n) g) :
    Regular (E := E) (F := F) (a+n) (fun x => f x + g x) := by
  apply regular_of_chart_jets ha ha1
  intro x
  have result := (hf.chart_jet ha ha1 x).add (hg.chart_jet ha ha1 x)
  simpa only [chartMap,extChartAt_model_space_eq_id,PartialEquiv.refl_coe,
    Function.comp_def,id_eq] using result

 theorem regular_finset_sum_noninteger {I : Type*} (s : Finset I)
    {a : ℝ} {n : ℕ} (ha : 0 < a) (ha1 : a < 1) (f : I → M → F)
    (regular : ∀ i ∈ s, Regular (E := E) (F := F) (a+n) (f i)) :
    Regular (E := E) (F := F) (a+n) (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using
      (regular_of_smooth (E := E) (F := F) (f := fun _ : M => (0 : F)) contMDiff_const
        (show 0 ≤ a+n by positivity))
  | @insert i s hi ih =>
    have hfi := regular i (Finset.mem_insert_self i s)
    have hfs := ih (fun j hj => regular j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using hfi.add_noninteger ha ha1 hfs

end LeanShared.FractionalManifoldRegularity
