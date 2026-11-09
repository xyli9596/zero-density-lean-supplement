import V10.HolomorphicProjectionAverage
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic

/-!
# Actual invertible real affine parameter windows

An invertible real affine map of the physical plane need not be holomorphic.
The pullback null-set and weighted-log integrability statements below are
proved by its actual Lebesgue pushforward, with the real determinant factor.
Analyticity is required only of the original scalar projection.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace V10.ProjectionAffineWindow
open HolomorphicProjectionAverage
set_option backward.isDefEq.respectTransparency false

/-- Every invertible real affine self-map of the physical complex plane has
this form; no complex linearity is required of A. -/
def window (A : ℂ ≃L[ℝ] ℂ) (b : ℂ) : ℂ ≃ₜ ℂ :=
  A.toHomeomorph.trans (Homeomorph.addRight b)

@[simp] theorem window_apply (A : ℂ ≃L[ℝ] ℂ) (b z : ℂ) :
    window A b z = A z + b := rfl

/-- The true two-dimensional Jacobian factor for the pushforward measure. -/
def inverseJacobian (A : ℂ ≃L[ℝ] ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal |(LinearMap.det (A : ℂ →ₗ[ℝ] ℂ))⁻¹|

theorem inverseJacobian_ne_zero (A : ℂ ≃L[ℝ] ℂ) : inverseJacobian A ≠ 0 := by
  apply ne_of_gt
  apply ENNReal.ofReal_pos.mpr
  exact abs_pos.mpr (inv_ne_zero A.toLinearEquiv.isUnit_det'.ne_zero)

theorem inverseJacobian_ne_top (A : ℂ ≃L[ℝ] ℂ) : inverseJacobian A ≠ ∞ :=
  ENNReal.ofReal_ne_top

/-- The actual planar volume law, including translation and the determinant
of an arbitrary invertible real linear map. -/
theorem map_window_volume (A : ℂ ≃L[ℝ] ℂ) (b : ℂ) :
    Measure.map (window A b) volume = inverseJacobian A • volume := by
  have hA : Measure.map A volume = inverseJacobian A • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume A.toLinearEquiv.isUnit_det'.ne_zero
  change Measure.map ((fun z : ℂ => z + b) ∘ A) volume = _
  rw [← Measure.map_map (g := fun z : ℂ => z + b)
      (by fun_prop) A.continuous.measurable,
    hA, Measure.map_smul, (measurePreserving_add_right volume b).map_eq]

/-- The actual null zero set of a nonzero entire function stays null under
every invertible real affine parameter window. -/
theorem ae_ne_zero_window {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ)
    (hn : ∃ z, f z ≠ 0) (A : ℂ ≃L[ℝ] ℂ) (b : ℂ) :
    ∀ᵐ z ∂volume, f (window A b z) ≠ 0 := by
  apply ae_of_ae_map (p := fun w => f w ≠ 0)
    (window A b).continuous.measurable.aemeasurable
  rw [map_window_volume]
  exact Measure.ae_smul_measure (ae_ne_zero_of_entire hf hn) _

/-- Compactly weighted local integrability pulls back through the actual
affine map, using a transported compact weight and the proved Jacobian law. -/
theorem weighted_integrable_window {f : ℂ → ℝ} (hf : LocallyIntegrable f volume)
    {φ : ℂ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (A : ℂ ≃L[ℝ] ℂ) (b : ℂ) :
    Integrable (fun z => φ z * f (window A b z)) volume := by
  let e := window A b
  have hi : Integrable (fun z => φ (e.symm z) * f z) volume := by
    exact hf.integrable_smul_left_of_hasCompactSupport
      (hφ.comp e.symm.continuous) (hφc.comp_homeomorph e.symm)
  have himap : Integrable (fun z => φ (e.symm z) * f z) (Measure.map e volume) := by
    rw [map_window_volume]
    exact hi.smul_measure (inverseJacobian_ne_top A)
  simpa only [Function.comp_def, e.symm_apply_apply] using
    himap.comp_measurable e.continuous.measurable

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Weighted logarithmic integrability for the true composed row F(Az+b).
The composition is not assumed holomorphic: only the original scalar
projection is entire and nonzero. -/
theorem weighted_logProjection_integrable_window {F : ℂ → E →L[ℂ] ℂ}
    (hF : Continuous F) (hFn : ∀ z, F z ≠ 0) {c : E}
    (ha : AnalyticOnNhd ℂ (fun z => F z c) univ) (hn : ∃ z, F z c ≠ 0)
    {φ : ℂ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (A : ℂ ≃L[ℝ] ℂ) (b : ℂ) :
    Integrable (fun z => φ z * logProjection (fun w => F (window A b w)) c z) volume := by
  have hi := weighted_integrable_window (locallyIntegrable_log_of_entire ha hn) hφ hφc A b
  have hden : Continuous (fun z => Real.log ‖F (window A b z)‖) :=
    ((hF.comp (window A b).continuous).norm).log
      (fun z => norm_ne_zero_iff.mpr (hFn (window A b z)))
  have hj : Integrable (fun z => φ z * Real.log ‖F (window A b z)‖) volume :=
    (hφ.mul hden).integrable_of_hasCompactSupport hφc.mul_right
  apply (hi.sub hj).congr
  filter_upwards [ae_ne_zero_window ha hn A b] with z hz
  change φ z * Real.log ‖F (window A b z) c‖ -
    φ z * Real.log ‖F (window A b z)‖ = _
  rw [logProjection, Real.log_div (norm_ne_zero_iff.mpr hz)
    (norm_ne_zero_iff.mpr (hFn (window A b z)))]
  ring

/-- True logarithmic homogeneity of the finite average on an arbitrary
invertible real affine physical window. -/
theorem averagedLogProjection_window_smul {F : ℂ → E →L[ℂ] ℂ}
    (hF : Continuous F) (hFn : ∀ z, F z ≠ 0) {c : E}
    (ha : AnalyticOnNhd ℂ (fun z => F z c) univ) (hn : ∃ z, F z c ≠ 0)
    {φ : ℂ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (A : ℂ ≃L[ℝ] ℂ) (b : ℂ) {κ : ℂ} (hκ : κ ≠ 0) :
    averagedLogProjection (fun z => F (window A b z)) φ (κ • c) =
      averagedLogProjection (fun z => F (window A b z)) φ c +
        Real.log ‖κ‖ * ∫ z, φ z := by
  have he : (fun z => φ z * logProjection (fun w => F (window A b w)) (κ • c) z)
      =ᵐ[volume] (fun z => φ z * logProjection (fun w => F (window A b w)) c z +
        Real.log ‖κ‖ * φ z) := by
    filter_upwards [ae_ne_zero_window ha hn A b] with z hz
    unfold logProjection
    rw [map_smul, norm_smul, mul_div_assoc,
      Real.log_mul (norm_ne_zero_iff.mpr hκ)
        (div_ne_zero (norm_ne_zero_iff.mpr hz)
          (norm_ne_zero_iff.mpr (hFn (window A b z))))]
    ring
  unfold averagedLogProjection
  rw [integral_congr_ae he,
    integral_add (weighted_logProjection_integrable_window hF hFn ha hn hφ hφc A b)
      ((hφ.integrable_of_hasCompactSupport hφc).const_mul _), integral_const_mul]

#print axioms map_window_volume
#print axioms ae_ne_zero_window
#print axioms weighted_integrable_window
#print axioms weighted_logProjection_integrable_window
#print axioms averagedLogProjection_window_smul
end V10.ProjectionAffineWindow
