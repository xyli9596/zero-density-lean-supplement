import V10.ScalarAnalytic
import V10.PluriPotentialIntegral
import Mathlib.Tactic

/-!
# Finite averaged logarithmic projections and actual logarithmic homogeneity

For every nonzero analytic projection, its true zero set is null and its
logarithmic modulus is locally integrable. A compactly supported continuous
weight therefore gives a finite real integral, including when the scalar
projection has zeros inside the integration region. No nonvanishing
projection or assumed logarithmic integrability is required.

The real integral below is used away from the zero coefficient. Its totalized
value at the zero coefficient is not claimed to represent a pluripotential
pole; the extended potential and its value −∞ at zero are handled separately.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace V10.HolomorphicProjectionAverage
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def logProjection (F : ℂ → E →L[ℂ] ℂ) (c : E) (z : ℂ) : ℝ :=
  Real.log (‖F z c‖ / ‖F z‖)

def averagedLogProjection (F : ℂ → E →L[ℂ] ℂ) (φ : ℂ → ℝ) (c : E) : ℝ :=
  ∫ z, φ z * logProjection F c z

/-- A nonzero entire analytic function has no zero analytic germ. -/
theorem germs_ne_zero_of_entire {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ)
    (hn : ∃ z, f z ≠ 0) : ∀ z, ¬f =ᶠ[𝓝 z] 0 := by
  obtain ⟨w, hw⟩ := hn
  intro z hz
  exact hw ((hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (mem_univ z) hz) (mem_univ w))

/-- Nullness of the actual scalar zero set, with no assumed a.e. nonvanishing. -/
theorem ae_ne_zero_of_entire {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ)
    (hn : ∃ z, f z ≠ 0) : ∀ᵐ z ∂volume, f z ≠ 0 := by
  simpa only [Measure.restrict_univ] using ScalarAnalytic.ae_ne_zero_of_germs
    MeasurableSet.univ hf (fun z _ => germs_ne_zero_of_entire hf hn z)

theorem locallyIntegrable_log_of_entire {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (hn : ∃ z, f z ≠ 0) :
    LocallyIntegrable (fun z => Real.log ‖f z‖) volume :=
  locallyIntegrableOn_univ.mp
    (ZeroDensity.AnalyticLogIntegrability.locallyIntegrableOn_log_norm hf
      (fun z _ => germs_ne_zero_of_entire hf hn z))

/-- The actual normalized logarithmic projection is integrable against any
continuous compactly supported weight, despite isolated projection zeros. -/
theorem weighted_logProjection_integrable {F : ℂ → E →L[ℂ] ℂ}
    (hF : Continuous F) (hFn : ∀ z, F z ≠ 0) {c : E}
    (ha : AnalyticOnNhd ℂ (fun z => F z c) univ) (hn : ∃ z, F z c ≠ 0)
    {φ : ℂ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Integrable (fun z => φ z * logProjection F c z) volume := by
  have hi := (locallyIntegrable_log_of_entire ha hn).integrable_smul_left_of_hasCompactSupport
    hφ hφc
  have hden : Continuous (fun z => Real.log ‖F z‖) :=
    hF.norm.log (fun z => norm_ne_zero_iff.mpr (hFn z))
  have hj : Integrable (fun z => φ z * Real.log ‖F z‖) volume :=
    (hφ.mul hden).integrable_of_hasCompactSupport hφc.mul_right
  apply (hi.sub hj).congr
  filter_upwards [ae_ne_zero_of_entire ha hn] with z hz
  change φ z * Real.log ‖F z c‖ - φ z * Real.log ‖F z‖ = _
  rw [logProjection, Real.log_div (norm_ne_zero_iff.mpr hz) (norm_ne_zero_iff.mpr (hFn z))]
  ring

/-- At almost every actual projection point, scaling the coefficient adds
the true logarithm of the scalar norm. The exceptional set is proved null. -/
theorem logProjection_smul_ae {F : ℂ → E →L[ℂ] ℂ} (hFn : ∀ z, F z ≠ 0)
    {c : E} (ha : AnalyticOnNhd ℂ (fun z => F z c) univ) (hn : ∃ z, F z c ≠ 0)
    {κ : ℂ} (hκ : κ ≠ 0) :
    logProjection F (κ • c) =ᵐ[volume] (fun z => logProjection F c z + Real.log ‖κ‖) := by
  filter_upwards [ae_ne_zero_of_entire ha hn] with z hz
  unfold logProjection
  rw [map_smul, norm_smul, mul_div_assoc,
    Real.log_mul (norm_ne_zero_iff.mpr hκ)
      (div_ne_zero (norm_ne_zero_iff.mpr hz) (norm_ne_zero_iff.mpr (hFn z)))]
  ring

/-- Exact logarithmic homogeneity of the finite averaged projection. The
weight need not be normalized: its integral is the coefficient of log|κ|. -/
theorem averagedLogProjection_smul {F : ℂ → E →L[ℂ] ℂ}
    (hF : Continuous F) (hFn : ∀ z, F z ≠ 0) {c : E}
    (ha : AnalyticOnNhd ℂ (fun z => F z c) univ) (hn : ∃ z, F z c ≠ 0)
    {φ : ℂ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    {κ : ℂ} (hκ : κ ≠ 0) :
    averagedLogProjection F φ (κ • c) = averagedLogProjection F φ c +
      Real.log ‖κ‖ * ∫ z, φ z := by
  unfold averagedLogProjection
  have he : (fun z => φ z * logProjection F (κ • c) z) =ᵐ[volume]
      (fun z => φ z * logProjection F c z + Real.log ‖κ‖ * φ z) := by
    filter_upwards [logProjection_smul_ae hFn ha hn hκ] with z hz
    rw [hz]
    ring
  rw [integral_congr_ae he, integral_add (weighted_logProjection_integrable hF hFn ha hn hφ hφc)
    ((hφ.integrable_of_hasCompactSupport hφc).const_mul _), integral_const_mul]

/-- A continuous entire projection family which separates every nonzero
coefficient supplies finite averages and exact homogeneity at every nonzero
coefficient. Nonnegativity and smoothness of the manuscript's weight are
stronger than the continuity and compact support needed for this step. -/
theorem averagedLogProjection_family {F : ℂ → E →L[ℂ] ℂ}
    (hF : Continuous F) (hFn : ∀ z, F z ≠ 0)
    (ha : ∀ c : E, c ≠ 0 → AnalyticOnNhd ℂ (fun z => F z c) univ)
    (hn : ∀ c : E, c ≠ 0 → ∃ z, F z c ≠ 0)
    {φ : ℂ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    ∀ c : E, c ≠ 0 →
      Integrable (fun z => φ z * logProjection F c z) volume ∧
      ∀ κ : ℂ, κ ≠ 0 → averagedLogProjection F φ (κ • c) =
        averagedLogProjection F φ c + Real.log ‖κ‖ * ∫ z, φ z := by
  intro c hc
  refine ⟨weighted_logProjection_integrable hF hFn (ha c hc) (hn c hc) hφ hφc, ?_⟩
  intro κ hκ
  exact averagedLogProjection_smul hF hFn (ha c hc) (hn c hc) hφ hφc hκ

#print axioms weighted_logProjection_integrable
#print axioms averagedLogProjection_smul
#print axioms averagedLogProjection_family
end V10.HolomorphicProjectionAverage
