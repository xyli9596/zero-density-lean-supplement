import V10.ProjectionAffineWindow
import V10.HolomorphicProjectionSeries

/-! Transporting a real-affine physical window into its actual compact weight.
The row remains holomorphic in the original physical variable. The determinant
factor is carried by the weight, with exactly preserved total mass. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace V10.ProjectionWindowTransport
open ProjectionAffineWindow HolomorphicProjectionAverage
set_option backward.isDefEq.respectTransparency false

def transportedWeight (A : ℂ ≃L[ℝ] ℂ) (b : ℂ) (φ : ℂ → ℝ) (z : ℂ) : ℝ :=
  (inverseJacobian A).toReal * φ ((window A b).symm z)

theorem transportedWeight_continuous (A : ℂ ≃L[ℝ] ℂ) (b : ℂ) {φ : ℂ → ℝ}
    (hφ : Continuous φ) : Continuous (transportedWeight A b φ) :=
  (hφ.comp (window A b).symm.continuous).const_mul _

theorem transportedWeight_compact (A : ℂ ≃L[ℝ] ℂ) (b : ℂ) {φ : ℂ → ℝ}
    (hφc : HasCompactSupport φ) : HasCompactSupport (transportedWeight A b φ) :=
  (hφc.comp_homeomorph (window A b).symm).mul_left

theorem transportedWeight_nonneg (A : ℂ ≃L[ℝ] ℂ) (b : ℂ) {φ : ℂ → ℝ}
    (hφn : ∀ z, 0 ≤ φ z) : ∀ z, 0 ≤ transportedWeight A b φ z :=
  fun _z => mul_nonneg ENNReal.toReal_nonneg (hφn _)

/-- Actual change of variables for a measurable scalar integrand. The real
affine map is not required to be holomorphic. -/
theorem integral_transport (A : ℂ ≃L[ℝ] ℂ) (b : ℂ) {φ f : ℂ → ℝ}
    (hφ : Measurable φ) (hf : Measurable f) :
    (∫ z, transportedWeight A b φ z * f z) =
      ∫ z, φ z * f (window A b z) := by
  have hm : Measurable (fun z => φ ((window A b).symm z) * f z) :=
    (hφ.comp (window A b).symm.continuous.measurable).mul hf
  have h := integral_map (μ := (volume : Measure ℂ))
    (window A b).continuous.measurable.aemeasurable
    hm.aestronglyMeasurable
  rw [map_window_volume, integral_smul_measure] at h
  simp only [Homeomorph.symm_apply_apply, smul_eq_mul] at h
  rw [← h, ← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun z => by unfold transportedWeight; ring

theorem transportedWeight_mass (A : ℂ ≃L[ℝ] ℂ) (b : ℂ) {φ : ℂ → ℝ}
    (hφ : Measurable φ) : (∫ z, transportedWeight A b φ z) = ∫ z, φ z := by
  simpa only [mul_one] using integral_transport A b hφ (measurable_const (a := (1 : ℝ)))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem measurable_logProjection {F : ℂ → E →L[ℂ] ℂ}
    (hF : Continuous F) (c : E) : Measurable (logProjection F c) :=
  ((hF.clm_apply continuous_const).measurable.norm.div hF.measurable.norm).log

/-- The actual average on a real-affine window is exactly an average of the
original holomorphic row against its transported compact weight. -/
theorem averagedLogProjection_transport {F : ℂ → E →L[ℂ] ℂ}
    (hF : Continuous F) (A : ℂ ≃L[ℝ] ℂ) (b : ℂ) {φ : ℂ → ℝ}
    (hφ : Measurable φ) (c : E) :
    averagedLogProjection F (transportedWeight A b φ) c =
      averagedLogProjection (fun z => F (window A b z)) φ c := by
  exact integral_transport A b hφ (measurable_logProjection hF c)

theorem averagedLogProjection_const_mul (F : ℂ → E →L[ℂ] ℂ)
    (φ : ℂ → ℝ) (a : ℝ) (c : E) :
    averagedLogProjection F (fun z => a * φ z) c =
      a * averagedLogProjection F φ c := by
  unfold averagedLogProjection
  simp_rw [mul_assoc]
  exact integral_const_mul _ _

#print axioms integral_transport
#print axioms transportedWeight_mass
#print axioms averagedLogProjection_transport
end V10.ProjectionWindowTransport
