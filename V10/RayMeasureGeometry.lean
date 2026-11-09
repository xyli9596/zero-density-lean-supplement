import V10.RadialCutoffGeometry
import V10.SectorScaledNeighborhood
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic

/-! Actual length measure on positive rays and its finite weighted sums.
Angular membership is defined without an argument branch; thus periodic
representatives cannot silently change sector masses or boundary conditions. -/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
namespace V10.RayMeasureGeometry
open ZeroDensity ZeroDensity.SectorDivisorCount RadialCutoffGeometry
open SectorScaledNeighborhood
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def unitPoint (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

def rayLengthMeasure (θ : ℝ) : Measure ℂ :=
  Measure.map (fun r : ℝ => rayPoint r θ) (volume.restrict (Ioi 0))

def edgeMeasure (T : Finset ℝ) (w : ℝ → ℝ) : Measure ℂ :=
  ∑ θ ∈ T, ENNReal.ofReal (w θ) • rayLengthMeasure θ

def DirectionIn (θ a b : ℝ) : Prop :=
  ∃ α ∈ Ioo a b, unitPoint θ = unitPoint α

theorem continuous_rayPoint (θ : ℝ) : Continuous (fun r : ℝ => rayPoint r θ) := by
  fun_prop

theorem integral_rayLengthMeasure {φ : ℂ → ℝ} (hφ : Continuous φ) (θ : ℝ) :
    (∫ z, φ z ∂rayLengthMeasure θ) = ∫ r in Ioi (0 : ℝ), φ (rayPoint r θ) := by
  exact integral_map (continuous_rayPoint θ).measurable.aemeasurable
    hφ.aestronglyMeasurable

theorem rayLengthMeasure_closedBall (θ R : ℝ) :
    rayLengthMeasure θ (closedBall 0 R) = ENNReal.ofReal R := by
  rw [rayLengthMeasure, Measure.map_apply (continuous_rayPoint θ).measurable
    measurableSet_closedBall,
    Measure.restrict_apply (measurableSet_closedBall.preimage (continuous_rayPoint θ).measurable)]
  have he : (fun r : ℝ => rayPoint r θ) ⁻¹' closedBall 0 R ∩ Ioi 0 = Ioc 0 R := by
    ext r
    constructor
    · rintro ⟨hr, hp⟩
      refine ⟨hp, ?_⟩
      simpa only [mem_preimage, mem_closedBall, dist_zero_right, norm_polar hp.le] using hr
    · rintro ⟨hp, hr⟩
      refine ⟨?_, hp⟩
      simpa only [mem_preimage, mem_closedBall, dist_zero_right, norm_polar hp.le] using hr
  rw [he, Real.volume_Ioc]
  simp

instance rayLengthMeasure_finiteOnCompacts (θ : ℝ) :
    IsFiniteMeasureOnCompacts (rayLengthMeasure θ) where
  lt_top_of_isCompact := by
    intro K hK
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
    exact (measure_mono hR).trans_lt (by rw [rayLengthMeasure_closedBall]; exact ENNReal.ofReal_lt_top)

instance edgeMeasure_finiteOnCompacts (T : Finset ℝ) (w : ℝ → ℝ) :
    IsFiniteMeasureOnCompacts (edgeMeasure T w) where
  lt_top_of_isCompact := by
    intro K hK
    simp only [edgeMeasure, Measure.coe_finsetSum, Finset.sum_apply,
      Measure.smul_apply, smul_eq_mul]
    exact ENNReal.sum_lt_top.mpr fun θ _ =>
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

theorem rayLengthMeasure_sphere (θ R : ℝ) : rayLengthMeasure θ (sphere 0 R) = 0 := by
  rw [rayLengthMeasure, Measure.map_apply (continuous_rayPoint θ).measurable
    isClosed_sphere.measurableSet,
    Measure.restrict_apply (isClosed_sphere.measurableSet.preimage (continuous_rayPoint θ).measurable)]
  apply measure_mono_null (t := ({R} : Set ℝ)) _ (measure_singleton R)
  rintro r ⟨hr, hp⟩
  simpa only [mem_preimage, mem_sphere, dist_zero_right, norm_polar hp.le,
    mem_singleton_iff] using hr

theorem clippedSector_isMeasurable {S R a b : ℝ} (hS : 0 < S) :
    MeasurableSet (clippedSector S R a b) := by
  have he : CountGeometry.angularSector S a b = PerronSector.sector S (Ioo a b) := by
    ext z
    exact (PerronSector.mem_sector_iff hS).symm
  rw [clippedSector, he]
  exact (PerronSector.sector_isOpen S isOpen_Ioo).measurableSet.inter
    (polarCarrier_compact S R a b).measurableSet

theorem rayPoint_mem_clippedSector {S R a b r θ : ℝ} (hS : 0 ≤ S) (hr : 0 < r) :
    rayPoint r θ ∈ clippedSector S R a b ↔ r ∈ Ioc S R ∧ DirectionIn θ a b := by
  rw [clippedSector_eq_norm hS]
  constructor
  · rintro ⟨⟨ρ, hρ, α, hα, he⟩, hn⟩
    have hρr : ρ = r := by
      have hh := congrArg norm he
      rw [norm_polar hr.le, norm_polar (hS.trans hρ.le)] at hh
      exact hh.symm
    subst ρ
    refine ⟨⟨hρ, ?_⟩, α, hα, ?_⟩
    · simpa only [mem_ofPred_eq, norm_polar hr.le] using hn
    · exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne') he
  · rintro ⟨⟨hSr, hrR⟩, α, hα, he⟩
    refine ⟨⟨r, hSr, α, hα, ?_⟩, ?_⟩
    · exact congrArg (fun u : ℂ => (r : ℂ) * u) he
    · simpa only [mem_ofPred_eq, norm_polar hr.le] using hrR

theorem rayLengthMeasure_clippedSector {S R a b : ℝ} (hS : 0 < S) (θ : ℝ) :
    rayLengthMeasure θ (clippedSector S R a b) =
      if DirectionIn θ a b then ENNReal.ofReal (R - S) else 0 := by
  classical
  rw [rayLengthMeasure, Measure.map_apply (continuous_rayPoint θ).measurable
    (clippedSector_isMeasurable hS),
    Measure.restrict_apply ((clippedSector_isMeasurable hS).preimage
      (continuous_rayPoint θ).measurable)]
  by_cases hθ : DirectionIn θ a b
  · rw [if_pos hθ]
    have he : (fun r : ℝ => rayPoint r θ) ⁻¹' clippedSector S R a b ∩ Ioi 0 = Ioc S R := by
      ext r
      constructor
      · rintro ⟨hr, hp⟩
        exact ((rayPoint_mem_clippedSector hS.le hp).mp hr).1
      · intro hr
        have hp : 0 < r := hS.trans hr.1
        exact ⟨(rayPoint_mem_clippedSector hS.le hp).mpr ⟨hr, hθ⟩, hp⟩
    rw [he, Real.volume_Ioc]
  · rw [if_neg hθ]
    have he : (fun r : ℝ => rayPoint r θ) ⁻¹' clippedSector S R a b ∩ Ioi 0 = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro r ⟨hr, hp⟩
      exact hθ ((rayPoint_mem_clippedSector hS.le hp).mp hr).2
    rw [he, measure_empty]

theorem edgeMeasure_clippedSector {S R a b : ℝ} (hS : 0 < S)
    (T : Finset ℝ) (w : ℝ → ℝ) :
    edgeMeasure T w (clippedSector S R a b) =
      ENNReal.ofReal (R - S) *
        ∑ θ ∈ T, if DirectionIn θ a b then ENNReal.ofReal (w θ) else 0 := by
  simp only [edgeMeasure, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.smul_apply, smul_eq_mul, rayLengthMeasure_clippedSector hS,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro θ hθ
  split_ifs <;> simp [mul_comm]

/-- The closed positive ray, with the origin included. -/
def raySupport (θ : ℝ) : Set ℂ :=
  {z | z = (‖z‖ : ℂ) * unitPoint θ}

theorem raySupport_isClosed (θ : ℝ) : IsClosed (raySupport θ) := by
  apply isClosed_eq continuous_id
  fun_prop

theorem rayPoint_mem_raySupport {r θ α : ℝ} (hr : 0 < r) :
    rayPoint r θ ∈ raySupport α ↔ unitPoint θ = unitPoint α := by
  change (r : ℂ) * unitPoint θ = (‖rayPoint r θ‖ : ℂ) * unitPoint α ↔ _
  rw [norm_polar hr.le]
  constructor
  · exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne')
  · exact congrArg (fun u : ℂ => (r : ℂ) * u)

theorem rayLengthMeasure_raySupport_of_ne {θ α : ℝ} (h : unitPoint θ ≠ unitPoint α) :
    rayLengthMeasure θ (raySupport α) = 0 := by
  rw [rayLengthMeasure, Measure.map_apply (continuous_rayPoint θ).measurable
    (raySupport_isClosed α).measurableSet,
    Measure.restrict_apply ((raySupport_isClosed α).measurableSet.preimage
      (continuous_rayPoint θ).measurable)]
  have he : (fun r : ℝ => rayPoint r θ) ⁻¹' raySupport α ∩ Ioi 0 = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro r ⟨hr, hp⟩
    exact h ((rayPoint_mem_raySupport hp).mp hr)
  rw [he, measure_empty]

theorem clippedSector_closure_subset_carrier {S R a b : ℝ} :
    closure (clippedSector S R a b) ⊆ polarCarrier S R a b :=
  closure_minimal inter_subset_right (polarCarrier_compact S R a b).isClosed

theorem clippedSector_closure_compact (S R a b : ℝ) :
    IsCompact (closure (clippedSector S R a b)) :=
  (polarCarrier_compact S R a b).of_isClosed_subset isClosed_closure
    clippedSector_closure_subset_carrier

theorem clippedSector_closure_subset_fullCone {S R a b : ℝ} {J : Set ℝ}
    (hS : 0 < S) (hab : Icc a b ⊆ J) :
    closure (clippedSector S R a b) ⊆ fullCone J := by
  intro z hz
  obtain ⟨r, hr, θ, hθ, rfl⟩ := mem_polarCarrier.mp (clippedSector_closure_subset_carrier hz)
  have hr0 : 0 < r := hS.trans_le hr.1
  refine ⟨(Real.log r : ℂ) + (θ : ℂ) * Complex.I, ?_, ?_⟩
  · simpa using hab hθ
  · rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hr0]

theorem angularSector_isOpen {S a b : ℝ} (hS : 0 < S) :
    IsOpen (CountGeometry.angularSector S a b) := by
  have he : CountGeometry.angularSector S a b = PerronSector.sector S (Ioo a b) := by
    ext z
    exact (PerronSector.mem_sector_iff hS).symm
  rw [he]
  exact PerronSector.sector_isOpen S isOpen_Ioo

/-- Every boundary point lies on a radial circle or an angular side ray.
No injectivity of a global argument branch is used. -/
theorem clippedSector_frontier_subset {S R a b : ℝ} (hS : 0 < S) :
    frontier (clippedSector S R a b) ⊆
      sphere 0 S ∪ sphere 0 R ∪ raySupport a ∪ raySupport b := by
  intro z hz
  obtain ⟨r, hr, θ, hθ, he⟩ := mem_polarCarrier.mp
    (clippedSector_closure_subset_carrier (frontier_subset_closure hz))
  have hn : ‖z‖ = r := by rw [he, norm_polar (hS.le.trans hr.1)]
  by_cases hrS : r = S
  · have hm : z ∈ sphere 0 S := by simpa only [mem_sphere, dist_zero_right, hn] using hrS
    exact Or.inl (Or.inl (Or.inl hm))
  by_cases hrR : r = R
  · have hm : z ∈ sphere 0 R := by simpa only [mem_sphere, dist_zero_right, hn] using hrR
    exact Or.inl (Or.inl (Or.inr hm))
  by_cases hθa : θ = a
  · have hm : z ∈ raySupport a := by change z = _; rw [hn, he, hθa]; rfl
    exact Or.inl (Or.inr hm)
  by_cases hθb : θ = b
  · have hm : z ∈ raySupport b := by change z = _; rw [hn, he, hθb]; rfl
    exact Or.inr hm
  have hzr : z ∈ CountGeometry.angularSector S a b ∩ ball 0 R := by
    refine ⟨⟨r, lt_of_le_of_ne hr.1 (Ne.symm hrS), θ,
      ⟨lt_of_le_of_ne hθ.1 (Ne.symm hθa), lt_of_le_of_ne hθ.2 hθb⟩, he⟩, ?_⟩
    simpa only [mem_ball, dist_zero_right, hn] using lt_of_le_of_ne hr.2 hrR
  have hsub : CountGeometry.angularSector S a b ∩ ball (0 : ℂ) R ⊆
      clippedSector S R a b := by
    rw [clippedSector_eq_norm hS.le]
    intro x hx
    exact ⟨hx.1, (mem_ball_zero_iff.mp hx.2).le⟩
  have hi : z ∈ interior (clippedSector S R a b) :=
    interior_mono hsub (by simpa only [((angularSector_isOpen hS).inter isOpen_ball).interior_eq]
      using hzr)
  exact False.elim (hz.2 hi)

theorem edgeMeasure_sphere (T : Finset ℝ) (w : ℝ → ℝ) (R : ℝ) :
    edgeMeasure T w (sphere 0 R) = 0 := by
  simp [edgeMeasure, Measure.coe_finsetSum, Finset.sum_apply,
    rayLengthMeasure_sphere]

theorem edgeMeasure_raySupport (T : Finset ℝ) (w : ℝ → ℝ) (α : ℝ)
    (hw : ∀ θ ∈ T, unitPoint θ = unitPoint α → w θ = 0) :
    edgeMeasure T w (raySupport α) = 0 := by
  simp only [edgeMeasure, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply]
  apply Finset.sum_eq_zero
  intro θ hθ
  by_cases he : unitPoint θ = unitPoint α
  · simp [hw θ hθ he]
  · simp [rayLengthMeasure_raySupport_of_ne he]

theorem edgeMeasure_frontier_clippedSector {S R a b : ℝ} (hS : 0 < S)
    (T : Finset ℝ) (w : ℝ → ℝ)
    (ha : ∀ θ ∈ T, unitPoint θ = unitPoint a → w θ = 0)
    (hb : ∀ θ ∈ T, unitPoint θ = unitPoint b → w θ = 0) :
    edgeMeasure T w (frontier (clippedSector S R a b)) = 0 := by
  apply measure_mono_null (clippedSector_frontier_subset hS)
  apply measure_union_null
  · apply measure_union_null
    · exact measure_union_null (edgeMeasure_sphere T w S) (edgeMeasure_sphere T w R)
    · exact edgeMeasure_raySupport T w a ha
  · exact edgeMeasure_raySupport T w b hb

theorem integral_edgeMeasure {φ : ℂ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (T : Finset ℝ) (w : ℝ → ℝ)
    (hw : ∀ θ ∈ T, 0 ≤ w θ) :
    (∫ z, φ z ∂edgeMeasure T w) =
      ∑ θ ∈ T, w θ * ∫ r in Ioi (0 : ℝ), φ (rayPoint r θ) := by
  unfold edgeMeasure
  rw [integral_finsetSum_measure (fun θ _ =>
    (hφ.integrable_of_hasCompactSupport hφc (μ := rayLengthMeasure θ)).smul_measure
      ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro θ hθ
  rw [integral_smul_measure, ENNReal.toReal_ofReal (hw θ hθ),
    smul_eq_mul, integral_rayLengthMeasure hφ]

def sectorWeight (T : Finset ℝ) (w : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∑ θ ∈ T, if DirectionIn θ a b then w θ else 0

theorem sectorWeight_nonneg (T : Finset ℝ) (w : ℝ → ℝ) (a b : ℝ)
    (hw : ∀ θ ∈ T, 0 ≤ w θ) : 0 ≤ sectorWeight T w a b := by
  apply Finset.sum_nonneg
  intro θ hθ
  split_ifs
  · exact hw θ hθ
  · exact le_rfl

theorem edgeMeasure_clippedSector_eq_ofReal {S R a b : ℝ} (hS : 0 < S) (hSR : S ≤ R)
    (T : Finset ℝ) (w : ℝ → ℝ) (hw : ∀ θ ∈ T, 0 ≤ w θ) :
    edgeMeasure T w (clippedSector S R a b) =
      ENNReal.ofReal ((R - S) * sectorWeight T w a b) := by
  rw [edgeMeasure_clippedSector hS, ENNReal.ofReal_mul (sub_nonneg.mpr hSR)]
  congr 1
  rw [sectorWeight, ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro θ hθ
    split_ifs <;> simp
  · intro θ hθ
    split_ifs
    · exact hw θ hθ
    · exact le_rfl

/-- The divisor-limit normalization for a Laplacian edge measure. -/
def normalizedEdgeMeasure (T : Finset ℝ) (w : ℝ → ℝ) : Measure ℂ :=
  ENNReal.ofReal (1 / (2 * Real.pi)) • edgeMeasure T w

instance normalizedEdgeMeasure_finiteOnCompacts (T : Finset ℝ) (w : ℝ → ℝ) :
    IsFiniteMeasureOnCompacts (normalizedEdgeMeasure T w) :=
  IsFiniteMeasureOnCompacts.smul _ ENNReal.ofReal_ne_top

theorem normalizedEdgeMeasure_real_clippedSector {S R a b : ℝ}
    (hS : 0 < S) (hSR : S ≤ R) (T : Finset ℝ) (w : ℝ → ℝ)
    (hw : ∀ θ ∈ T, 0 ≤ w θ) :
    (normalizedEdgeMeasure T w).real (clippedSector S R a b) =
      (R - S) * sectorWeight T w a b / (2 * Real.pi) := by
  rw [Measure.real, normalizedEdgeMeasure, Measure.smul_apply, smul_eq_mul,
    edgeMeasure_clippedSector_eq_ofReal hS hSR T w hw, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / (2 * Real.pi)),
    ENNReal.toReal_ofReal (mul_nonneg (sub_nonneg.mpr hSR) (sectorWeight_nonneg T w a b hw))]
  ring

theorem normalizedEdgeMeasure_half_annulus (T : Finset ℝ) (w : ℝ → ℝ)
    (a b : ℝ) (hw : ∀ θ ∈ T, 0 ≤ w θ) :
    (normalizedEdgeMeasure T w).real (clippedSector (1 / 2) 1 a b) =
      sectorWeight T w a b / (4 * Real.pi) := by
  rw [normalizedEdgeMeasure_real_clippedSector (by norm_num) (by norm_num) T w hw]
  ring

theorem normalizedEdgeMeasure_frontier_clippedSector {S R a b : ℝ} (hS : 0 < S)
    (T : Finset ℝ) (w : ℝ → ℝ)
    (ha : ∀ θ ∈ T, unitPoint θ = unitPoint a → w θ = 0)
    (hb : ∀ θ ∈ T, unitPoint θ = unitPoint b → w θ = 0) :
    normalizedEdgeMeasure T w (frontier (clippedSector S R a b)) = 0 := by
  simp only [normalizedEdgeMeasure, Measure.smul_apply,
    edgeMeasure_frontier_clippedSector hS T w ha hb, smul_zero]

theorem unitPoint_injOn_Icc {l u : ℝ} (hshort : u - l < 2 * Real.pi) :
    InjOn unitPoint (Icc l u) := by
  intro θ hθ α hα he
  apply Circle.exp_injOn_Icc hshort hθ hα
  apply Subtype.ext
  exact he

theorem directionIn_iff_mem_of_branch {l u a b θ : ℝ}
    (hshort : u - l < 2 * Real.pi) (hθ : θ ∈ Icc l u)
    (hab : Ioo a b ⊆ Icc l u) :
    DirectionIn θ a b ↔ θ ∈ Ioo a b := by
  constructor
  · rintro ⟨α, hα, he⟩
    rwa [unitPoint_injOn_Icc hshort hθ (hab hα) he]
  · intro h
    exact ⟨θ, h, rfl⟩

theorem sectorWeight_eq_angle_sum {l u a b : ℝ}
    (hshort : u - l < 2 * Real.pi) (T : Finset ℝ) (w : ℝ → ℝ)
    (hT : ∀ θ ∈ T, θ ∈ Icc l u) (hab : Ioo a b ⊆ Icc l u) :
    sectorWeight T w a b = ∑ θ ∈ T, if θ ∈ Ioo a b then w θ else 0 := by
  apply Finset.sum_congr rfl
  intro θ hθ
  rw [directionIn_iff_mem_of_branch hshort (hT θ hθ) hab]
  split_ifs <;> rfl

theorem unitPoint_injOn_Ioc {l u : ℝ} (hshort : u - l ≤ 2 * Real.pi) :
    InjOn unitPoint (Ioc l u) := by
  intro θ hθ α hα he
  apply Circle.exp_injOn_Ioc hshort hθ hα
  apply Subtype.ext
  exact he

theorem directionIn_iff_mem_of_halfopen_branch {l u a b θ : ℝ}
    (hshort : u - l ≤ 2 * Real.pi) (hθ : θ ∈ Ioc l u)
    (hab : Ioo a b ⊆ Ioc l u) :
    DirectionIn θ a b ↔ θ ∈ Ioo a b := by
  constructor
  · rintro ⟨α, hα, he⟩
    rwa [unitPoint_injOn_Ioc hshort hθ (hab hα) he]
  · intro h
    exact ⟨θ, h, rfl⟩

theorem sectorWeight_eq_angle_sum_halfopen {l u a b : ℝ}
    (hshort : u - l ≤ 2 * Real.pi) (T : Finset ℝ) (w : ℝ → ℝ)
    (hT : ∀ θ ∈ T, θ ∈ Ioc l u) (hab : Ioo a b ⊆ Ioc l u) :
    sectorWeight T w a b = ∑ θ ∈ T, if θ ∈ Ioo a b then w θ else 0 := by
  apply Finset.sum_congr rfl
  intro θ hθ
  rw [directionIn_iff_mem_of_halfopen_branch hshort (hT θ hθ) hab]
  split_ifs <;> rfl

#print axioms integral_rayLengthMeasure
#print axioms rayLengthMeasure_clippedSector
#print axioms rayLengthMeasure_sphere
#print axioms edgeMeasure_frontier_clippedSector
#print axioms normalizedEdgeMeasure_half_annulus
#print axioms sectorWeight_eq_angle_sum
end V10.RayMeasureGeometry
