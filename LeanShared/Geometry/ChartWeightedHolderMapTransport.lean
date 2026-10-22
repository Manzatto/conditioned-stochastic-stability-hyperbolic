module
public import LeanShared.Geometry.ChartMapC1Globalization
public import LeanShared.Geometry.ChartFractionalLocalization
public import LeanShared.Analysis.HolderWeightComposition
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
namespace LeanShared.ChartWeightedHolderMapTransport
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
  (e f : OpenPartialHomeomorph M E)
  (he : e∈maximalAtlas (𝓘(ℝ,E)) ∞ M) (hf : f∈maximalAtlas (𝓘(ℝ,E)) ∞ M)
  (θ : M → ℂ) (smoothθ : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ θ)
  (compactθ : HasCompactSupport θ) (supportθ : tsupport θ⊆e.source)
  {K : Set E} (compactK : IsCompact K) (targetK : K⊆f.target)
  (F:M→M) (hF:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 F)
  {w:M→ℂ} {u a:ℝ} (hu:0<u) (hu1:u<1)
  (hw:FractionalManifoldRegularity.Regular (E:=E) (F:=ℂ) u w)
  (ha : 0≤a) (hau:a<u)

include he hf smoothθ compactθ supportθ compactK targetK hF hu hu1 hw ha hau in
theorem exists_transport : ∃ T : BoundedHolderSpace.graph E a →L[ℂ] BoundedHolderSpace.graph E a,
    ∀ v : BoundedHolderSpace.graph E a,
    (∀z∉K, BoundedHolderSpace.physical E a v z=0) → ∀ y : E,
      BoundedHolderSpace.physical E a (T v) y =
        ChartLocalization.coordinate e θ
          (fun x=>w x*SupportedChartExtension.function f (BoundedHolderSpace.physical E a v) (F x)) y := by
  classical
  let C : Set M := tsupport θ ∩ F ⁻¹' (f.symm '' K)
  have compactImage : IsCompact (f.symm '' K) :=
    compactK.image_of_continuousOn (f.continuousOn_symm.mono targetK)
  have compactC : IsCompact C := compactθ.inter_right (compactImage.isClosed.preimage hF.continuous)
  have sourceC : C⊆e.source := fun _ hx => supportθ hx.1
  let L : Set E := e '' C
  have compactL : IsCompact L := compactC.image_of_continuousOn (e.continuousOn.mono sourceC)
  have overlapL : L⊆ChartMapC1Globalization.domain e f F := by
    rintro _ ⟨x,hx,rfl⟩
    refine ⟨e.map_source (sourceC hx),?_⟩
    change F (e.symm (e x))∈f.source
    rw [e.left_inv (sourceC hx)]
    obtain ⟨z,hz,eqn⟩ := hx.2
    rw [←eqn]
    exact f.map_target (targetK hz)
  obtain ⟨ρ,smoothρ,compactρ,supportρ,_,oneρ⟩ := CompactSmoothCutoff.exists_cutoff
    compactL (ChartMapC1Globalization.domain_open e f F hF) overlapL
  obtain ⟨G,_,_,agree,Lg,lipg⟩ := ChartMapC1Globalization.exists_extension e f he hf F hF compactρ supportρ
  let θE := ChartFractionalLocalization.bounded e θ supportθ compactθ smoothθ hw
  obtain ⟨C,hC,holder⟩ := ChartFractionalLocalization.global_holder
    e θ supportθ compactθ he smoothθ hu hu1 hw
  have lower (x y:E) : ‖θE x-θE y‖≤max C (2*‖θE‖)*dist x y^a := by
    simpa only [Real.one_rpow,mul_one,div_one] using
      HolderInterpolation.increment_bound θE ha hau hC zero_lt_one
        (fun x y=>by simpa only [dist_eq_norm] using holder x y) x y
  let amplitude := BoundedHolderSpace.ofBound E a θE (max C (2*‖θE‖)) lower
  have compactρb:HasCompactSupport (fun x=>(ρ x:ℂ)) :=
    compactρ.comp_left Complex.ofReal_zero
  let ρb:E→ᵇℂ := ofCompactSupport (fun x=>(ρ x:ℂ))
    (Complex.continuous_ofReal.comp smoothρ.continuous) compactρb
  obtain ⟨Lρ,lipρ⟩ := CompactC1Lipschitz.exists_lipschitz (fun x=>(ρ x:ℂ))
    (Complex.ofRealCLM.contDiff.comp smoothρ |>.of_le (by simp)) compactρb
  let ψgraph := HolderWeightedComposition.lifted ha (hau.trans hu1).le ρb lipρ
    (fun x:E=>x) LipschitzWith.id amplitude
  let ψb := BoundedHolderSpace.physical E a ψgraph
  let T := HolderWeightComposition.operator ha ψb (norm_nonneg ψgraph)
    (BoundedHolderSpace.increment_bound E a ψgraph) G lipg
  refine ⟨T,?_⟩
  intro v supported y
  let u := BoundedHolderSpace.physical E a v
  have exactT := HolderWeightComposition.physical_operator ha ψb (norm_nonneg ψgraph)
    (BoundedHolderSpace.increment_bound E a ψgraph) G lipg v y
  change BoundedHolderSpace.physical E a (T v) y = _
  rw [exactT]
  by_cases hy : y∈e.target
  · have original : ChartLocalization.coordinate e θ (fun x=>w x*SupportedChartExtension.function f u (F x)) y =
        (θ (e.symm y)*w (e.symm y)) * (if F (e.symm y)∈f.source then u (f (F (e.symm y))) else 0) := by
      rw [ChartLocalization.coordinate,ite_eq_left hy,SupportedChartExtension.function]
      ring
    have weightValue : ψb y=(ρ y:ℂ)*(θ (e.symm y)*w (e.symm y)) := by
      change (ρ y:ℂ)*ChartLocalization.coordinate e θ w y = _
      rw [ChartLocalization.coordinate,ite_eq_left hy]
    rw [weightValue,original]
    by_cases hsource : F (e.symm y)∈f.source
    · rw [ite_eq_left hsource]
      have gated : (ρ y:ℂ)*((θ (e.symm y)*w (e.symm y))*u (f (F (e.symm y)))) =
          (θ (e.symm y)*w (e.symm y))*u (f (F (e.symm y))) := by
        by_cases nonzero : (θ (e.symm y)*w (e.symm y))*u (f (F (e.symm y)))=0
        · rw [nonzero,mul_zero]
        have nonzeroθ : θ (e.symm y)≠0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp nonzero).1).1
        have nonzerou : u (f (F (e.symm y)))≠0 := (mul_ne_zero_iff.mp nonzero).2
        have inK : f (F (e.symm y))∈K := by
          by_contra outside
          exact nonzerou (supported _ outside)
        have inL : y∈L := by
          refine ⟨e.symm y,⟨subset_tsupport _ nonzeroθ,?_⟩,e.right_inv hy⟩
          exact ⟨f (F (e.symm y)),inK,f.left_inv hsource⟩
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
      change (ρ y:ℂ)*ChartLocalization.coordinate e θ w y=0
      rw [ChartLocalization.coordinate,ite_eq_right hy,mul_zero]
    rw [zeroWeight,zero_mul,ChartLocalization.coordinate,ite_eq_right hy]
end LeanShared.ChartWeightedHolderMapTransport
