import ZeroDensity.AnalyticLogIntegrability
import ZeroDensity.ScalarLimit
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Topology

/-!
# Actual scalar logarithms on the phase domain

A nonzero actual derivative jet at one point of a connected open analytic domain
implies nonzero analytic germs everywhere. We derive this input, rather than
assuming it in the local integrability theorem. Isolated zeros then give a
null zero set. The conclusions persist under nonzero complex dilations, on any
measurable subset whose dilation lies in the original domain.

The real logarithm is only the almost-everywhere representative for integration.
No subharmonic pointwise value at a scalar zero is inferred from `Real.log 0`.
These results provide inputs to scalar L¹ compactness; they do not assert it.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace V10.ScalarAnalytic

set_option backward.isDefEq.respectTransparency false

/-- An actual nonzero derivative jet rules out the zero analytic germ, even
when its zeroth component vanishes at the base point. -/
theorem germ_ne_zero_of_jet_ne_zero {n : ℕ} {v : ℂ → ℂ} {z : ℂ}
    (hn : ZeroDensity.ScalarLimit.jet n v z ≠ 0) : ¬v =ᶠ[𝓝 z] 0 := by
  intro hz
  apply hn
  funext j
  change iteratedDeriv j.val v z = 0
  simpa using hz.iteratedDeriv_eq j.val

/-- Identity continuation propagates a nonzero jet to nonzero scalar germs
throughout the original connected open phase domain. -/
theorem germs_ne_zero_of_jet {n : ℕ} {v : ℂ → ℂ} {S : Set ℂ}
    (hS : IsOpen S) (hconn : IsPreconnected S) (hv : AnalyticOnNhd ℂ v S)
    {z₀ : ℂ} (hz₀ : z₀ ∈ S) (hn : ZeroDensity.ScalarLimit.jet n v z₀ ≠ 0) :
    ∀ z ∈ S, ¬v =ᶠ[𝓝 z] 0 := by
  intro z hz hzero
  have hvan := hv.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hz hzero
  apply germ_ne_zero_of_jet_ne_zero hn
  filter_upwards [hS.mem_nhds hz₀] with w hw
  exact hvan hw

/-- Isolated zeros yield an almost-everywhere nonvanishing statement without
requiring the working set itself to be connected. -/
theorem ae_ne_zero_of_germs {v : ℂ → ℂ} {S : Set ℂ} (hS : MeasurableSet S)
    (hv : AnalyticOnNhd ℂ v S) (hn : ∀ z ∈ S, ¬v =ᶠ[𝓝 z] 0) :
    ∀ᵐ z ∂volume.restrict S, v z ≠ 0 := by
  apply ae_restrict_le_codiscreteWithin hS
  rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  intro z hz
  have h := (hv z hz).eventually_eq_zero_or_eventually_ne_zero.resolve_left (hn z hz)
  filter_upwards [h] with w hw
  exact Or.inl hw

theorem ae_ne_zero_of_jet {n : ℕ} {v : ℂ → ℂ} {S : Set ℂ}
    (hS : IsOpen S) (hconn : IsPreconnected S) (hv : AnalyticOnNhd ℂ v S)
    {z₀ : ℂ} (hz₀ : z₀ ∈ S) (hn : ZeroDensity.ScalarLimit.jet n v z₀ ≠ 0) :
    ∀ᵐ z ∂volume.restrict S, v z ≠ 0 :=
  ae_ne_zero_of_germs hS.measurableSet hv (germs_ne_zero_of_jet hS hconn hv hz₀ hn)

/-- The zero set of the actual scalar function has planar measure zero. -/
theorem zero_set_null_of_jet {n : ℕ} {v : ℂ → ℂ} {S : Set ℂ}
    (hS : IsOpen S) (hconn : IsPreconnected S) (hv : AnalyticOnNhd ℂ v S)
    {z₀ : ℂ} (hz₀ : z₀ ∈ S) (hn : ZeroDensity.ScalarLimit.jet n v z₀ ≠ 0) :
    volume.restrict S {z | v z = 0} = 0 := by
  simpa only [ae_iff, not_not] using ae_ne_zero_of_jet hS hconn hv hz₀ hn

/-- The existing local logarithmic factorization now applies from a single
nonzero jet, with no separate nonzero-germ assumptions. -/
theorem locallyIntegrableOn_log_of_jet {n : ℕ} {v : ℂ → ℂ} {S : Set ℂ}
    (hS : IsOpen S) (hconn : IsPreconnected S) (hv : AnalyticOnNhd ℂ v S)
    {z₀ : ℂ} (hz₀ : z₀ ∈ S) (hn : ZeroDensity.ScalarLimit.jet n v z₀ ≠ 0) :
    LocallyIntegrableOn (fun z => Real.log ‖v z‖) S :=
  ZeroDensity.AnalyticLogIntegrability.locallyIntegrableOn_log_norm hv
    (germs_ne_zero_of_jet hS hconn hv hz₀ hn)

/-- Nonzero complex dilation preserves a nonzero analytic germ. -/
theorem dilated_germ_ne_zero {v : ℂ → ℂ} {c z : ℂ} (hc : c ≠ 0)
    (hn : ¬v =ᶠ[𝓝 (c * z)] 0) : ¬(fun w => v (c * w)) =ᶠ[𝓝 z] 0 := by
  intro hzero
  apply hn
  have hcont : Continuous (fun w : ℂ => c⁻¹ * w) := continuous_const.mul continuous_id
  have ht : Tendsto (fun w : ℂ => c⁻¹ * w) (𝓝 (c * z)) (𝓝 z) := by
    simpa [← mul_assoc, hc] using hcont.tendsto (c * z)
  have h := hzero.comp_tendsto ht
  filter_upwards [h] with w hw
  simpa only [Function.comp_def, ← mul_assoc, mul_inv_cancel₀ hc, one_mul, Pi.zero_apply] using hw

/-- Analyticity under the actual rescaling used in the scalar potential. -/
theorem dilated_analyticOnNhd {v : ℂ → ℂ} {S D : Set ℂ} {c : ℂ}
    (hv : AnalyticOnNhd ℂ v S) (hDS : ∀ z ∈ D, c * z ∈ S) :
    AnalyticOnNhd ℂ (fun z => v (c * z)) D := by
  intro z hz
  exact (hv (c * z) (hDS z hz)).comp (analyticAt_const.mul analyticAt_id)

/-- The manuscript's scalar potential as a real-valued integration
representative. Its point values at zeros are not the subharmonic representative. -/
def potential (v : ℂ → ℂ) (R : ℝ) (z : ℂ) : ℝ :=
  Real.log ‖v ((R : ℂ) * z)‖ / R

/-- All scalar scaled logarithms are locally integrable, derived from actual
analyticity, an initial jet, and the scaled-domain inclusion. -/
theorem potential_locallyIntegrableOn {n : ℕ} {v : ℂ → ℂ} {S D : Set ℂ}
    (hS : IsOpen S) (hconn : IsPreconnected S) (hv : AnalyticOnNhd ℂ v S)
    {z₀ : ℂ} (hz₀ : z₀ ∈ S) (hn : ZeroDensity.ScalarLimit.jet n v z₀ ≠ 0)
    {R : ℝ} (hR : R ≠ 0) (hDS : ∀ z ∈ D, (R : ℂ) * z ∈ S) :
    LocallyIntegrableOn (potential v R) D := by
  have hg := germs_ne_zero_of_jet hS hconn hv hz₀ hn
  have hi := ZeroDensity.AnalyticLogIntegrability.locallyIntegrableOn_log_norm
    (dilated_analyticOnNhd hv hDS)
    (fun z hz => dilated_germ_ne_zero (Complex.ofReal_ne_zero.mpr hR) (hg _ (hDS z hz)))
  convert hi.smul R⁻¹ using 1
  funext z
  simp only [potential, div_eq_inv_mul, Pi.smul_apply, smul_eq_mul]

/-- Compact L¹ membership, including compact sets meeting actual scalar zeros. -/
theorem potential_integrableOn_compact {n : ℕ} {v : ℂ → ℂ} {S D K : Set ℂ}
    (hS : IsOpen S) (hconn : IsPreconnected S) (hv : AnalyticOnNhd ℂ v S)
    {z₀ : ℂ} (hz₀ : z₀ ∈ S) (hn : ZeroDensity.ScalarLimit.jet n v z₀ ≠ 0)
    {R : ℝ} (hR : R ≠ 0) (hDS : ∀ z ∈ D, (R : ℂ) * z ∈ S)
    (hKD : K ⊆ D) (hK : IsCompact K) : IntegrableOn (potential v R) K :=
  (potential_locallyIntegrableOn hS hconn hv hz₀ hn hR hDS).integrableOn_compact_subset hKD hK

/-- The scalar versus jet logarithmic comparison holds almost everywhere,
including on working domains which contain scalar zeros. -/
theorem potential_le_jet_ae {n : ℕ} (hnpos : 0 < n) {v : ℂ → ℂ} {S D : Set ℂ}
    (hS : IsOpen S) (hconn : IsPreconnected S) (hv : AnalyticOnNhd ℂ v S)
    {z₀ : ℂ} (hz₀ : z₀ ∈ S) (hn : ZeroDensity.ScalarLimit.jet n v z₀ ≠ 0)
    {R : ℝ} (hR : 0 < R) (hD : MeasurableSet D)
    (hDS : ∀ z ∈ D, (R : ℂ) * z ∈ S) :
    ∀ᵐ z ∂volume.restrict D, potential v R z ≤
      Real.log ‖ZeroDensity.ScalarLimit.jet n v ((R : ℂ) * z)‖ / R := by
  have hg := germs_ne_zero_of_jet hS hconn hv hz₀ hn
  have hae := ae_ne_zero_of_germs hD (dilated_analyticOnNhd hv hDS)
    (fun z hz => dilated_germ_ne_zero (Complex.ofReal_ne_zero.mpr hR.ne') (hg _ (hDS z hz)))
  filter_upwards [hae] with z hz
  exact div_le_div_of_nonneg_right (ZeroDensity.ScalarLimit.log_scalar_le_jet hnpos hz) hR.le

/-- The actual complex jet ODE itself supplies scalar analyticity. No
analyticity of the coefficient matrix is needed for this implication. -/
theorem analyticOnNhd_of_jet_ode {n : ℕ} (hnpos : 0 < n) {v : ℂ → ℂ}
    {S : Set ℂ} (hS : IsOpen S)
    {A : ℂ → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)}
    (hode : ∀ z ∈ S, HasDerivAt (ZeroDensity.ScalarLimit.jet n v)
      (A z (ZeroDensity.ScalarLimit.jet n v z)) z) : AnalyticOnNhd ℂ v S := by
  apply DifferentiableOn.analyticOnNhd _ hS
  intro z hz
  have h := (hasDerivAt_pi.mp (hode z hz)) (⟨0, hnpos⟩ : Fin n)
  simpa only [ZeroDensity.ScalarLimit.jet, iteratedDeriv_zero] using
    h.differentiableAt.differentiableWithinAt

/-- Complete integration inputs for the actual scalar potential, directly
from a jet ODE and one nonzero initial jet. The domain may contain scalar zeros.
This establishes L¹ membership and almost-everywhere comparison, not L¹ compactness. -/
theorem scalar_inputs_of_jet_ode {n : ℕ} (hnpos : 0 < n) {v : ℂ → ℂ}
    {S D : Set ℂ} (hS : IsOpen S) (hconn : IsPreconnected S)
    {A : ℂ → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)}
    (hode : ∀ z ∈ S, HasDerivAt (ZeroDensity.ScalarLimit.jet n v)
      (A z (ZeroDensity.ScalarLimit.jet n v z)) z)
    {z₀ : ℂ} (hz₀ : z₀ ∈ S) (hn : ZeroDensity.ScalarLimit.jet n v z₀ ≠ 0)
    {R : ℝ} (hR : 0 < R) (hD : MeasurableSet D)
    (hDS : ∀ z ∈ D, (R : ℂ) * z ∈ S) :
    AnalyticOnNhd ℂ (fun z => v ((R : ℂ) * z)) D ∧
    (∀ᵐ z ∂volume.restrict D, v ((R : ℂ) * z) ≠ 0) ∧
    LocallyIntegrableOn (potential v R) D ∧
    (∀ᵐ z ∂volume.restrict D, potential v R z ≤
      Real.log ‖ZeroDensity.ScalarLimit.jet n v ((R : ℂ) * z)‖ / R) := by
  have hv := analyticOnNhd_of_jet_ode hnpos hS hode
  have hg := germs_ne_zero_of_jet hS hconn hv hz₀ hn
  exact ⟨dilated_analyticOnNhd hv hDS,
    ae_ne_zero_of_germs hD (dilated_analyticOnNhd hv hDS)
      (fun z hz => dilated_germ_ne_zero (Complex.ofReal_ne_zero.mpr hR.ne') (hg _ (hDS z hz))),
    potential_locallyIntegrableOn hS hconn hv hz₀ hn hR.ne' hDS,
    potential_le_jet_ae hnpos hS hconn hv hz₀ hn hR hD hDS⟩

#print axioms germs_ne_zero_of_jet
#print axioms zero_set_null_of_jet
#print axioms potential_locallyIntegrableOn
#print axioms potential_integrableOn_compact
#print axioms potential_le_jet_ae
#print axioms scalar_inputs_of_jet_ode

end V10.ScalarAnalytic
