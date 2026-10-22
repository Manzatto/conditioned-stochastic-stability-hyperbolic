module
public import LeanShared.Analysis.LocalJetCoordinateChanges
import all LeanShared.Analysis.FiniteJetComposition

/-! Fixed coordinate changes preserve moving-point jet convergence locally
at a point. Their domains need not be globally forward invariant. -/
public noncomputable section
namespace LeanShared.FiniteJetComposition
open Set Filter
open scoped Topology

theorem JetConvergesOn.fixed_coordinates_at
    {A E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : A → F → G} {g : F → G} {l : Filter A} {U : Set F}
    (jets : JetConvergesOn f g l U) (h : E → F) (k : G → H) (x : E)
    (inside : h x ∈ U) (first : ContDiffAt ℝ 1 h x)
    (last : ContDiffAt ℝ 1 k (g (h x))) :
    JetConvergesOn (fun a => k ∘ f a ∘ h) (k ∘ g ∘ h) l {x} := by
  have inner : JetConvergesOn (fun _ : A => h) h l {x} :=
    JetConvergesOn.constant h l {x} (fun _ hy => by simpa only [mem_singleton_iff.mp hy] using first)
  have middle := jets.comp inner (fun _ hy => by simpa only [mem_singleton_iff.mp hy] using inside)
  have outer : JetConvergesOn (fun _ : A => k) k l {g (h x)} :=
    JetConvergesOn.constant k l {g (h x)}
      (fun _ hy => by simpa only [mem_singleton_iff.mp hy] using last)
  exact outer.comp middle (fun _ hy => by
    simp only [mem_singleton_iff] at hy ⊢
    subst hy
    rfl)

end LeanShared.FiniteJetComposition
