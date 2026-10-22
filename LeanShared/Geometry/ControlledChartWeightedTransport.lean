module
public import LeanShared.Analysis.CompactC1UniformDomains
public import LeanShared.Geometry.ChartMapC1Globalization
public import LeanShared.Analysis.HolderWeightCompositionNorm
public import LeanShared.Geometry.ChartFractionalLocalization
public import LeanShared.Analysis.HolderWeightComposition
public import LeanShared.Analysis.CompactSmoothCutoff
public import LeanShared.Analysis.HolderWeightedComposition
public import LeanShared.Geometry.ChartLocalization
public import LeanShared.Geometry.SupportedChartExtension

/-! Quantitative value and derivative controls produce one bounded lower-Hölder chart transport agrees with the
literal cutoff/localization of every source supported in a fixed compact
chart region. All cutoffs and global transition maps are constructed. -/
public noncomputable section
set_option maxHeartbeats 800000
open Set IsManifold
open scoped Manifold ContDiff BoundedContinuousFunction
namespace LeanShared.ControlledChartWeightedTransport
variable {A E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
  (e f : OpenPartialHomeomorph M E)
  (he : e∈maximalAtlas (𝓘(ℝ,E)) ∞ M) (hf : f∈maximalAtlas (𝓘(ℝ,E)) ∞ M)
  (θ : M → ℂ) (smoothθ : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ θ)
  (compactθ : HasCompactSupport θ) (supportθ : tsupport θ⊆e.source)
  {K : Set E} (compactK : IsCompact K) (targetK : K⊆f.target)
  (F:A→M→M)
  (ρ σ:E→ℝ) (smoothρ:ContDiff ℝ ∞ ρ) (smoothσ:ContDiff ℝ ∞ σ)
  (compactρ:HasCompactSupport ρ) (compactσ:HasCompactSupport σ)
  (oneσ:EqOn σ (fun _=>1) (tsupport ρ))
  (valid:∀q,tsupport σ⊆ChartMapC1Globalization.domain e f (F q))
  (captureρ:∀q x,x∈tsupport θ→F q x∈f.symm '' K→ρ (e x)=1)
  (openDomain:∀q,IsOpen (ChartMapC1Globalization.domain e f (F q)))
  (regular:∀q,ContDiffOn ℝ 1 (fun y=>f (F q (e.symm y)))
    (ChartMapC1Globalization.domain e f (F q)))
  {B D:ℝ} (hB:0≤B) (hD:0≤D)
  (control:∀q x,x∈tsupport σ→‖f (F q (e.symm x))‖≤B ∧
    ‖fderiv ℝ (fun y=>f (F q (e.symm y))) x‖≤D)
  {w:M→ℂ} {u a:ℝ} (hu:0<u) (hu1:u<1)
  (hw:FractionalManifoldRegularity.Regular (E:=E) (F:=ℂ) u w)
  (ha : 0≤a) (hau:a<u)

include he smoothθ compactθ supportθ smoothρ smoothσ compactρ compactσ oneσ valid captureρ
  openDomain regular hB hD control hu hu1 hw ha hau in
omit [T2Space M] in
theorem exists_uniform_transport : ∃C:ℝ,0≤C ∧
    ∃T:A→(BoundedHolderSpace.graph E a →L[ℂ] BoundedHolderSpace.graph E a),
      (∀q,‖T q‖≤C) ∧ ∀q (v:BoundedHolderSpace.graph E a),
      (∀z∉K,BoundedHolderSpace.physical E a v z=0)→∀y:E,
        BoundedHolderSpace.physical E a (T q v) y=
          ChartLocalization.coordinate e θ
            (fun x=>w x*SupportedChartExtension.function f (BoundedHolderSpace.physical E a v) (F q x)) y := by
  classical
  obtain ⟨Lg,lipg⟩:=CompactC1UniformDomains.exists_uniform_lipschitz σ
    (smoothσ.of_le (by simp)) compactσ
    (fun q=>ChartMapC1Globalization.domain e f (F q)) openDomain valid
    (fun q y=>f (F q (e.symm y))) regular hB hD control
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
  let G (q:A) (y:E):=σ y • f (F q (e.symm y))
  let T(q:A):=HolderWeightComposition.operator ha ψb (norm_nonneg ψgraph)
    (BoundedHolderSpace.increment_bound E a ψgraph) (G q) (lipg q)
  refine ⟨max ‖ψb‖ (‖ψb‖*(Lg:ℝ)^a+‖ψgraph‖),
    le_trans (norm_nonneg ψb) (le_max_left _ _),T,?_,?_⟩
  · intro q
    exact HolderWeightComposition.operator_norm_le ha ψb (norm_nonneg ψgraph)
      (BoundedHolderSpace.increment_bound E a ψgraph) (G q) (lipg q)
  intro q v supported y
  let u := BoundedHolderSpace.physical E a v
  have exactT := HolderWeightComposition.physical_operator ha ψb (norm_nonneg ψgraph)
    (BoundedHolderSpace.increment_bound E a ψgraph) (G q) (lipg q) v y
  change BoundedHolderSpace.physical E a (T q v) y = _
  rw [exactT]
  by_cases hy : y∈e.target
  · have original : ChartLocalization.coordinate e θ (fun x=>w x*SupportedChartExtension.function f u (F q x)) y =
        (θ (e.symm y)*w (e.symm y)) * (if F q (e.symm y)∈f.source then u (f (F q (e.symm y))) else 0) := by
      rw [ChartLocalization.coordinate,ite_eq_left hy,SupportedChartExtension.function]
      ring
    have weightValue : ψb y=(ρ y:ℂ)*(θ (e.symm y)*w (e.symm y)) := by
      change (ρ y:ℂ)*ChartLocalization.coordinate e θ w y = _
      rw [ChartLocalization.coordinate,ite_eq_left hy]
    rw [weightValue,original]
    by_cases hsource : F q (e.symm y)∈f.source
    · rw [ite_eq_left hsource]
      have gated : (ρ y:ℂ)*((θ (e.symm y)*w (e.symm y))*u (f (F q (e.symm y)))) =
          (θ (e.symm y)*w (e.symm y))*u (f (F q (e.symm y))) := by
        by_cases nonzero : (θ (e.symm y)*w (e.symm y))*u (f (F q (e.symm y)))=0
        · rw [nonzero,mul_zero]
        have nonzeroθ : θ (e.symm y)≠0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp nonzero).1).1
        have nonzerou : u (f (F q (e.symm y)))≠0 := (mul_ne_zero_iff.mp nonzero).2
        have inK : f (F q (e.symm y))∈K := by
          by_contra outside
          exact nonzerou (supported _ outside)
        have captured : ρ y=1 := by
          have h:=captureρ q (e.symm y) (subset_tsupport _ nonzeroθ)
            ⟨f (F q (e.symm y)),inK,f.left_inv hsource⟩
          simpa only [e.right_inv hy] using h
        rw [captured,Complex.ofReal_one,one_mul]
      by_cases zeroρ : ρ y=0
      · simpa only [zeroρ,Complex.ofReal_zero,zero_mul] using gated
      · have inSupport : y∈tsupport ρ := subset_tsupport _ zeroρ
        have coordinate : G q y=f (F q (e.symm y)) := by
          change σ y • f (F q (e.symm y))=f (F q (e.symm y))
          rw [oneσ inSupport,one_smul]
        rw [coordinate]
        exact (mul_assoc _ _ _).trans gated
    · have zeroρ : ρ y=0 := by
        by_contra nonzero
        have inρ:y∈tsupport ρ:=subset_tsupport _ nonzero
        have inσ:y∈tsupport σ:=subset_tsupport _ (by change σ y≠0; rw [oneσ inρ];norm_num)
        exact hsource (valid q inσ).2
      simp only [ite_eq_right hsource,zeroρ,Complex.ofReal_zero,zero_mul,mul_zero]
  · have zeroWeight : ψb y=0 := by
      change (ρ y:ℂ)*ChartLocalization.coordinate e θ w y=0
      rw [ChartLocalization.coordinate,ite_eq_right hy,mul_zero]
    rw [zeroWeight,zero_mul,ChartLocalization.coordinate,ite_eq_right hy]
end LeanShared.ControlledChartWeightedTransport
