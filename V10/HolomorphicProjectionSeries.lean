import V10.ProjectionAverageDeficit
import V10.ProjectionDeficitGaussian

/-!
# A global potential from actual averaged holomorphic projections

The inputs are entire scalar projections of a continuous nonzero functional
family, nonnegative compactly supported parameter weights, and summable
positive weight masses. Finiteness somewhere, logarithmic homogeneity, and
genuine local plurisuperharmonic representations are conclusions about the
constructed extended series, not assumptions on that series.

The manuscript's particular window enumeration and its quantitative loss
estimate outside the pole cone are separate applications of this construction.
-/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal
namespace V10.HolomorphicProjectionSeries
open HolomorphicProjectionAverage ProjectionAverageDeficit
open LogHomogeneousSeries LogHomogeneousPluriSeries PluriPotentialSeries
open ProjectionDeficitGaussian
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The actual positive parameter measure associated to the cutoff. -/
def weightMeasure (φ : ℂ → ℝ) : Measure ℂ :=
  volume.withDensity (fun z => ENNReal.ofReal (φ z))

instance weightMeasure_sfinite (φ : ℂ → ℝ) : SFinite (weightMeasure φ) := by
  unfold weightMeasure
  infer_instance

theorem weightMeasure_mass {φ : ℂ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hφn : ∀ z, 0 ≤ φ z) :
    weightMeasure φ univ = ENNReal.ofReal (∫ z, φ z) := by
  rw [weightMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  exact (ofReal_integral_eq_lintegral_ofReal
    (hφ.integrable_of_hasCompactSupport hφc) (ae_of_all _ hφn)).symm

/-- The real and complex scalar normalizations are the same functional. -/
theorem normalized_eq (F : ℂ → E →L[ℂ] ℂ) (z : ℂ) :
    ProjectionGaussianLoss.normalized (F z) = normalizedProjection F z := by
  ext c
  simp [ProjectionGaussianLoss.normalized, normalizedProjection, Complex.real_smul]

theorem deficitAverage_eq {F : ℂ → E →L[ℂ] ℂ}
    (hF : Continuous F) (hFn : ∀ z, F z ≠ 0) {φ : ℂ → ℝ}
    (hφ : Continuous φ) (M : ℝ) (c : E) :
    deficitAverage (weightMeasure φ) F M c = averagedDeficit F φ M c := by
  have hNF := normalizedProjection_continuous hF hFn
  have hev : Measurable (fun z : ℂ => normalizedProjection F z c) :=
    (hNF.clm_apply continuous_const).measurable
  have hm : Measurable (fun z : ℂ =>
      ProjectionPlurisubharmonic.logDeficit (normalizedProjection F z) M c) := by
    unfold ProjectionPlurisubharmonic.logDeficit
    apply Measurable.ite (measurableSet_eq_fun hev measurable_const) measurable_const
    exact ENNReal.continuous_ofReal.measurable.comp (measurable_const.sub hev.norm.log)
  simp only [deficitAverage, normalized_eq, weightMeasure, averagedDeficit]
  exact lintegral_withDensity_eq_lintegral_mul volume
    (ENNReal.continuous_ofReal.measurable.comp hφ.measurable) hm

/-- The actual logarithmic integrand satisfies the operator-norm upper bound.
Its totalized value at a projection zero also satisfies the bound when B > 1. -/
theorem logProjection_le {F : ℂ → E →L[ℂ] ℂ} (hFn : ∀ z, F z ≠ 0)
    {B : ℝ} (hB : 1 < B) {c : E} (hc : c ∈ ball 0 B) (z : ℂ) :
    logProjection F c z ≤ Real.log B := by
  by_cases hz : F z c = 0
  · simpa [logProjection, hz] using Real.log_nonneg hB.le
  apply Real.log_le_log (div_pos (norm_pos_iff.mpr hz) (norm_pos_iff.mpr (hFn z)))
  exact (normalizedProjection_norm F z c ▸ normalizedProjection_bound hFn z c).trans
    (mem_ball_zero_iff.mp hc).le

theorem averagedLogProjection_le {F : ℂ → E →L[ℂ] ℂ}
    (hF : Continuous F) (hFn : ∀ z, F z ≠ 0) {c : E}
    (ha : AnalyticOnNhd ℂ (fun z => F z c) univ) (hn : ∃ z, F z c ≠ 0)
    {φ : ℂ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφn : ∀ z, 0 ≤ φ z) {B : ℝ} (hB : 1 < B) (hc : c ∈ ball 0 B) :
    averagedLogProjection F φ c ≤ (∫ z, φ z) * Real.log B := by
  unfold averagedLogProjection
  rw [← integral_mul_const]
  exact integral_mono (weighted_logProjection_integrable hF hFn ha hn hφ hφc)
    ((hφ.integrable_of_hasCompactSupport hφc).mul_const _) fun z =>
      mul_le_mul_of_nonneg_left (logProjection_le hFn hB hc z) (hφn z)

section Gaussian
variable [InnerProductSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Actual Gaussian logarithmic integrability supplies a nonzero coefficient
where the series of actual averaged projections converges. The origin is
excluded by its proved infinite deficit, not by an assumed exceptional set. -/
theorem exists_summable_average {F : ℕ → ℂ → E →L[ℂ] ℂ} {φ : ℕ → ℂ → ℝ}
    (hF : ∀ j, Continuous (F j)) (hFn : ∀ j z, F j z ≠ 0)
    (ha : ∀ j c, c ≠ 0 → AnalyticOnNhd ℂ (fun z => F j z c) univ)
    (hn : ∀ j c, c ≠ 0 → ∃ z, F j z c ≠ 0)
    (hφ : ∀ j, Continuous (φ j)) (hφc : ∀ j, HasCompactSupport (φ j))
    (hφn : ∀ j z, 0 ≤ φ j z) (hφpos : ∀ j, 0 < ∫ z, φ j z)
    (hsum : Summable (fun j => ∫ z, φ j z)) :
    ∃ c : E, c ≠ 0 ∧ Summable (fun j => averagedLogProjection (F j) (φ j) c) := by
  let σ : ℕ → Measure ℂ := fun j => weightMeasure (φ j)
  have hmass : (∑' j, ((1 : ℝ≥0) : ℝ≥0∞) * σ j univ) ≠ ∞ := by
    simp only [ENNReal.coe_one, one_mul]
    simp_rw [σ, weightMeasure_mass (hφ _) (hφc _) (hφn _)]
    exact hsum.tsum_ofReal_ne_top
  obtain ⟨c, hc, hf⟩ := exists_finite_potential_in_ball
    (σ := σ) hF hFn (fun _ => 1)
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) hmass (0 : E)
    (by norm_num : (0 : ℝ) < 2)
  have hfinite : deficitSeries σ F (fun _ => 1) (Real.log 2) c ≠ ∞ :=
    (negativePotential_eq_bot _ _).not.mp hf
  have he : deficitSeries σ F (fun _ => 1) (Real.log 2) c =
      ∑' j, averagedDeficit (F j) (φ j) (Real.log 2) c := by
    simp only [deficitSeries, ENNReal.coe_one, one_mul, σ,
      deficitAverage_eq (hF _) (hFn _) (hφ _)]
  have hc0 : c ≠ 0 := by
    intro hz
    subst c
    apply hfinite
    apply top_unique
    rw [he, ← averagedDeficit_zero (F := F 0) (hφ 0) (hφc 0) (hφn 0) (hφpos 0)]
    exact ENNReal.le_tsum 0
  refine ⟨c, hc0, ?_⟩
  apply (summable_iff_deficit_finite (hsum.mul_right (Real.log 2))
    (fun j => averagedLogProjection_le (hF j) (hFn j) (ha j c hc0) (hn j c hc0)
      (hφ j) (hφc j) (hφn j) (by norm_num : (1 : ℝ) < 2) hc)).mpr
  rw [he] at hfinite
  have hnorm : ‖c‖ ≤ Real.exp (Real.log 2) := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using
      (mem_ball_zero_iff.mp hc).le
  simpa only [averagedDeficit_eq_ofReal (hF _) (hFn _) (ha _ c hc0) (hn _ c hc0)
    (hφ _) (hφc _) (hφn _) hnorm, mul_comm] using hfinite

/-- Full assembly for an actual holomorphic projection family. The positive
homogeneity coefficient, a finite potential value, the pole cone, and genuine
local supermean representations all follow from the analytic input data.
No property of the final potential is assumed. -/
theorem constructed_potential {F : ℕ → ℂ → E →L[ℂ] ℂ} {φ : ℕ → ℂ → ℝ}
    (hF : ∀ j, Continuous (F j)) (hFn : ∀ j z, F j z ≠ 0)
    (ha : ∀ j c, c ≠ 0 → AnalyticOnNhd ℂ (fun z => F j z c) univ)
    (hn : ∀ j c, c ≠ 0 → ∃ z, F j z c ≠ 0)
    (hφ : ∀ j, Continuous (φ j)) (hφc : ∀ j, HasCompactSupport (φ j))
    (hφn : ∀ j z, 0 ≤ φ j z) (hφpos : ∀ j, 0 < ∫ z, φ j z)
    (hsum : Summable (fun j => ∫ z, φ j z)) :
    let v : ℕ → E → ℝ := fun j => averagedLogProjection (F j) (φ j)
    let κ : ℝ := ∑' j, ∫ z, φ j z
    0 < κ ∧
    ExceptionalCone.LogHomogeneous (seriesPotential v) κ ∧
    (∃ c : E, seriesPotential v c ≠ ⊥) ∧
    (∀ c : E, ∀ α : ℂ, seriesPotential v c = ⊥ → seriesPotential v (α • c) = ⊥) ∧
    (∀ B : ℝ, 1 < B → ∃ (C : ℝ) (D : E → ℝ≥0∞),
      PlurisuperharmonicOn D (ball (0 : E) B) ∧
      ∀ c ∈ ball (0 : E) B, seriesPotential v c = (C : EReal) - (D c : EReal)) := by
  dsimp only
  refine ⟨hsum.tsum_pos (fun j => (hφpos j).le) 0 (hφpos 0), ?_⟩
  apply LogHomogeneousPluriSeries.constructed_potential hsum
  · intro α hα c hc j
    simpa only [mul_comm] using averagedLogProjection_smul (hF j) (hFn j)
      (ha j c hc) (hn j c hc) (hφ j) (hφc j) hα
  · exact exists_summable_average hF hFn ha hn hφ hφc hφn hφpos hsum
  · intro B hB
    refine ⟨fun j => (∫ z, φ j z) * Real.log B, hsum.mul_right _, ?_, ?_⟩
    · intro c hc hc0 j
      exact averagedLogProjection_le (hF j) (hFn j) (ha j c hc0) (hn j c hc0)
        (hφ j) (hφc j) (hφn j) hB hc
    · intro j
      exact puncturedDeficit_on_ball j B hB (hF j) (hFn j) (ha j) (hn j)
        (hφ j) (hφc j) (hφn j) (hφpos j)

end Gaussian

#print axioms exists_summable_average
#print axioms constructed_potential

end V10.HolomorphicProjectionSeries
