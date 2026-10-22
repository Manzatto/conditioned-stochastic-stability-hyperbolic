module
public import LeanShared.Geometry.ChartTransitionGlobalization
public import LeanShared.Analysis.CompactSmoothCutoff
public import LeanShared.Analysis.HolderWeightedComposition
public import LeanShared.Geometry.ChartLocalization
public import LeanShared.Geometry.SupportedChartExtension

/-! A constructed bounded lower-Hölder chart transport agrees with the
literal cutoff/localization of every source supported in a fixed compact
chart region. All cutoffs and global transition maps are constructed. -/
public noncomputable section
set_option maxHeartbeats 800000
open Set IsManifold
open scoped Manifold ContDiff BoundedContinuousFunction
namespace LeanShared.ChartHolderTransport
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
  (e f : OpenPartialHomeomorph M E)
  (he : e∈maximalAtlas (𝓘(ℝ,E)) ∞ M) (hf : f∈maximalAtlas (𝓘(ℝ,E)) ∞ M)
  (θ : M → ℂ) (smoothθ : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ θ)
  (compactθ : HasCompactSupport θ) (supportθ : tsupport θ⊆e.source)
  {K : Set E} (compactK : IsCompact K) (targetK : K⊆f.target)
  {a : ℝ} (ha : 0≤a) (ha1 : a≤1)

include he hf smoothθ compactθ supportθ compactK targetK ha ha1 in
theorem exists_transport : ∃ T : BoundedHolderSpace.graph E a →L[ℂ] BoundedHolderSpace.graph E a,
    ∀ v : BoundedHolderSpace.graph E a,
    (∀z∉K, BoundedHolderSpace.physical E a v z=0) → ∀ y : E,
      BoundedHolderSpace.physical E a (T v) y =
        ChartLocalization.coordinate e θ
          (SupportedChartExtension.function f (BoundedHolderSpace.physical E a v)) y := by
  classical
  let C : Set M := tsupport θ ∩ f.symm '' K
  have compactImage : IsCompact (f.symm '' K) :=
    compactK.image_of_continuousOn (f.continuousOn_symm.mono targetK)
  have compactC : IsCompact C := compactθ.inter compactImage
  have sourceC : C⊆e.source := fun _ hx => supportθ hx.1
  let L : Set E := e '' C
  have compactL : IsCompact L := compactC.image_of_continuousOn (e.continuousOn.mono sourceC)
  have overlapL : L⊆(e.symm.trans f).source := by
    rintro _ ⟨x,hx,rfl⟩
    refine ⟨e.map_source (sourceC hx),?_⟩
    change e.symm (e x)∈f.source
    rw [e.left_inv (sourceC hx)]
    obtain ⟨z,hz,rfl⟩ := hx.2
    exact f.map_target (targetK hz)
  obtain ⟨ρ,smoothρ,compactρ,supportρ,_,oneρ⟩ := CompactSmoothCutoff.exists_cutoff
    compactL (e.symm.trans f).open_source overlapL
  obtain ⟨G,_,_,agree,Lg,lipg⟩ := ChartTransitionGlobalization.exists_extension e f he hf compactρ supportρ
  let θE := ChartLocalization.coordinate e θ (fun _ => (1:ℂ))
  have smoothE : ContDiff ℝ ∞ θE :=
    ChartLocalization.coordinate_contDiff e θ supportθ he smoothθ compactθ _ contMDiff_const
  have compactE : HasCompactSupport θE :=
    ChartLocalization.coordinate_hasCompactSupport e θ supportθ compactθ _
  let ψ : E → ℂ := fun y => (ρ y:ℂ)*θE y
  have smoothψ : ContDiff ℝ ∞ ψ :=
    (Complex.ofRealCLM.contDiff.comp smoothρ).mul smoothE
  have compactψ : HasCompactSupport ψ :=
    compactE.of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_right
  let ψb : E →ᵇ ℂ := ofCompactSupport ψ smoothψ.continuous compactψ
  obtain ⟨Lψ,lipψ⟩ := CompactC1Lipschitz.exists_lipschitz ψ (smoothψ.of_le (by simp)) compactψ
  let T := HolderWeightedComposition.operator ha ha1 ψb lipψ G lipg
  refine ⟨T,?_⟩
  intro v supported y
  let u := BoundedHolderSpace.physical E a v
  have exactT := HolderWeightedComposition.physical_operator ha ha1 ψb lipψ G lipg v y
  change BoundedHolderSpace.physical E a (T v) y = _
  rw [exactT]
  by_cases hy : y∈e.target
  · have original : ChartLocalization.coordinate e θ (SupportedChartExtension.function f u) y =
        θ (e.symm y) * (if e.symm y∈f.source then u (f (e.symm y)) else 0) := by
      rw [ChartLocalization.coordinate,ite_eq_left hy,SupportedChartExtension.function]
    have weightValue : ψb y=(ρ y:ℂ)*θ (e.symm y) := by
      change (ρ y:ℂ)*ChartLocalization.coordinate e θ (fun _ => (1:ℂ)) y = _
      rw [ChartLocalization.coordinate,ite_eq_left hy,mul_one]
    rw [weightValue,original]
    by_cases hsource : e.symm y∈f.source
    · rw [ite_eq_left hsource]
      have gated : (ρ y:ℂ)*(θ (e.symm y)*u (f (e.symm y))) =
          θ (e.symm y)*u (f (e.symm y)) := by
        by_cases nonzero : θ (e.symm y)*u (f (e.symm y))=0
        · rw [nonzero,mul_zero]
        have nonzeroθ : θ (e.symm y)≠0 := (mul_ne_zero_iff.mp nonzero).1
        have nonzerou : u (f (e.symm y))≠0 := (mul_ne_zero_iff.mp nonzero).2
        have inK : f (e.symm y)∈K := by
          by_contra outside
          exact nonzerou (supported _ outside)
        have inL : y∈L := by
          refine ⟨e.symm y,⟨subset_tsupport _ nonzeroθ,?_⟩,e.right_inv hy⟩
          exact ⟨f (e.symm y),inK,f.left_inv hsource⟩
        rw [oneρ inL,Complex.ofReal_one,one_mul]
      by_cases zeroρ : ρ y=0
      · simpa only [zeroρ,Complex.ofReal_zero,zero_mul] using gated
      · have inSupport : y∈tsupport ρ := subset_tsupport _ zeroρ
        have coordinate := agree inSupport
        rw [coordinate]
        exact (mul_assoc _ _ _).trans gated
    · have zeroρ : ρ y=0 := by
        by_contra nonzero
        exact hsource (supportρ (subset_tsupport _ nonzero)).2
      simp only [ite_eq_right hsource,zeroρ,Complex.ofReal_zero,zero_mul,mul_zero]
  · have zeroWeight : ψb y=0 := by
      change (ρ y:ℂ)*ChartLocalization.coordinate e θ (fun _ => (1:ℂ)) y=0
      rw [ChartLocalization.coordinate,ite_eq_right hy,mul_zero]
    rw [zeroWeight,zero_mul,ChartLocalization.coordinate,ite_eq_right hy]
end LeanShared.ChartHolderTransport
