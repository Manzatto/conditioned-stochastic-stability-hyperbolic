module
public import LeanShared.Geometry.FiniteSmoothCapturePartition
public import LeanShared.Geometry.FractionalScalarMultiplication
public import LeanShared.Geometry.FractionalRegularLinearIsometry
public import LeanShared.Geometry.FractionalSubunitRegularity
public import LeanShared.Geometry.SmoothFractionalRegularity

/-! The selected finite smooth capture cutoffs localize the actual weight
without losing its real regularity order. Their complex weights share an
internally chosen subunit order strictly above the ordinary exponent. -/
@[expose] public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff
namespace LeanShared.FiniteSmoothCapturePartition
variable {E M J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [Fintype J] {K : Set M} {v : J → Set M}
  (d : Data (E := E) K v)

def Data.localizedWeight (g : M → ℝ) (i : J) (x : M) : ℝ := g x * d.beta i x

theorem Data.localizedWeight_regular {g : M → ℝ} {r : ℝ}
    (hg : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) r g) (i : J) :
    FractionalManifoldRegularity.Regular (E := E) (F := ℝ) r (d.localizedWeight g i) :=
  hg.mul (FractionalManifoldRegularity.regular_of_smooth (d.smooth i) hg.nonnegative)

theorem Data.localizedWeight_complex_regular {g : M → ℝ} {r : ℝ}
    (hg : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) r g) (i : J) :
    FractionalManifoldRegularity.Regular (E := E) (F := ℂ) r
      (fun x => (g x : ℂ) * (d.beta i x : ℂ)) := by
  simpa only [Data.localizedWeight,Complex.ofReal_mul] using
    (d.localizedWeight_regular hg i).ofReal

omit [IsManifold (𝓘(ℝ,E)) ∞ M] in
theorem Data.localizedWeight_support (g : M → ℝ) (i : J) :
    tsupport (d.localizedWeight g i) ⊆ tsupport g ∩ v i := by
  intro x hx
  exact ⟨tsupport_mul_subset_left hx,d.support i (tsupport_mul_subset_right hx)⟩

omit [IsManifold (𝓘(ℝ,E)) ∞ M] in
theorem Data.localizedWeight_complex_support (g : M → ℝ) (i : J) :
    tsupport (fun x => (g x : ℂ) * (d.beta i x : ℂ)) ⊆ tsupport g ∩ v i := by
  have actual := (tsupport_comp_subset Complex.ofReal_zero (d.localizedWeight g i)).trans
    (d.localizedWeight_support g i)
  simpa only [Function.comp_def,Data.localizedWeight,Complex.ofReal_mul] using actual

omit [IsManifold (𝓘(ℝ,E)) ∞ M] in
theorem Data.localizedWeight_norm_le (g : M → ℝ) (i : J) (x : M) :
    ‖d.localizedWeight g i x‖ ≤ ‖g x‖ := by
  simp only [Data.localizedWeight,norm_mul,Real.norm_eq_abs]
  rw [abs_of_nonneg (d.bounds i x).1]
  exact mul_le_of_le_one_right (abs_nonneg _) (d.bounds i x).2

omit [IsManifold (𝓘(ℝ,E)) ∞ M] in
theorem Data.localizedWeight_complex_norm_le (g : M → ℝ) (i : J) (x : M) :
    ‖(g x : ℂ) * (d.beta i x : ℂ)‖ ≤ ‖g x‖ := by
  rw [← Complex.ofReal_mul,Complex.norm_real]
  exact d.localizedWeight_norm_le g i x

theorem Data.exists_common_localized_order {g : M → ℝ} {r b : ℝ}
    (hg : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) r g)
    (hb : 0 < b) (hb1 : b < 1) (hbr : b < r) :
    ∃ a : ℝ, b < a ∧ a < 1 ∧ a < r ∧
      ∀ i, FractionalManifoldRegularity.Regular (E := E) (F := ℂ) a
        (fun x => (g x : ℂ) * (d.beta i x : ℂ)) := by
  let a := (b + min r 1) / 2
  have above : b < a := by
    dsimp [a]
    have lower := lt_min hbr hb1
    linarith
  have belowOne : a < 1 := by
    dsimp [a]
    linarith [min_le_right r 1]
  have belowR : a < r := by
    dsimp [a]
    linarith [min_le_left r 1]
  exact ⟨a,above,belowOne,belowR,fun i =>
    FractionalManifoldRegularity.lower_subunit (hb.trans above) belowOne belowR
      (d.localizedWeight_complex_regular hg i)⟩

end LeanShared.FiniteSmoothCapturePartition
