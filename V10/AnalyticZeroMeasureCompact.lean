import V10.ZeroMeasureTestConvergence

/-!
# Poincaré–Lelong and zero measures on arbitrary compact carriers

A compact carrier need not be connected or convex. The correct nontriviality
condition is a nonzero analytic germ at every point of the carrier. This is
supplied by the actual nonzero jet ODE on the original connected analytic domain.
-/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory Metric InnerProductSpace
open scoped Topology ContDiff ENNReal
namespace V10.AnalyticZeroMeasureCompact
open LogLaplacianLocal

def divisorSupport (f : ℂ → ℂ) {K : Set ℂ} (hK : IsCompact K) : Finset ℂ :=
  ((MeromorphicOn.divisor f K).finiteSupport hK).toFinset

theorem mem_divisorSupport {f : ℂ → ℂ} {K : Set ℂ} (hK : IsCompact K) {z : ℂ} :
    z ∈ divisorSupport f hK ↔ MeromorphicOn.divisor f K z ≠ 0 := by
  simp [divisorSupport, Function.mem_support]

theorem analytic_log_divisor_decomposition {f : ℂ → ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hf : AnalyticOnNhd ℂ f K)
    (hn : ∀ z ∈ K, ¬f =ᶠ[𝓝 z] 0) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g K ∧ (∀ z ∈ K, g z ≠ 0) ∧
      (fun z => Real.log ‖f z‖) =ᵐ[volume.restrict K]
        ((∑ᶠ u, (fun z => (MeromorphicOn.divisor f K u : ℝ) * Real.log ‖z - u‖)) +
          fun z => Real.log ‖g z‖) := by
  have ho : ∀ z : K, meromorphicOrderAt f z ≠ ⊤ := by
    intro z
    rw [(hf z z.property).meromorphicOrderAt_eq, ne_eq, ENat.map_eq_top_iff]
    exact fun h => hn z z.property (analyticOrderAt_eq_top.mp h)
  obtain ⟨g, hg, hgn, he⟩ := hf.meromorphicOn.extract_zeros_poles ho
    ((MeromorphicOn.divisor f K).finiteSupport hK)
  exact ⟨g, hg, fun z hz => hgn ⟨z, hz⟩,
    ae_restrict_le_codiscreteWithin hK.measurableSet
      (MeromorphicOn.extract_zeros_poles_log hgn he)⟩

theorem analytic_log_laplacian {f : ℂ → ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hf : AnalyticOnNhd ℂ f K)
    (hn : ∀ z ∈ K, ¬f =ᶠ[𝓝 z] 0)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ K) :
    (∫ z, Laplacian.laplacian φ z * Real.log ‖f z‖) =
      2 * Real.pi * ∑ u ∈ divisorSupport f hK,
        (MeromorphicOn.divisor f K u : ℝ) * φ u := by
  classical
  obtain ⟨g, hg, hgn, he⟩ := analytic_log_divisor_decomposition hK hf hn
  have hhg : HarmonicOnNhd (fun z => Real.log ‖g z‖) K :=
    fun z hz => (hg z hz).harmonicAt_log_norm (hgn z hz)
  have hsup : Function.support (fun u => (fun z =>
      (MeromorphicOn.divisor f K u : ℝ) * Real.log ‖z - u‖)) ⊆
      (divisorSupport f hK : Set ℂ) := by
    intro u hu
    apply (mem_divisorSupport hK).mpr
    intro hzero
    apply hu
    ext z
    simp [hzero]
  rw [finsum_eq_sum_of_support_subset _ hsup] at he
  have he' : (fun z => Real.log ‖f z‖) =ᵐ[volume.restrict K]
      (fun z => (∑ u ∈ divisorSupport f hK,
        (MeromorphicOn.divisor f K u : ℝ) * Real.log ‖z - u‖) +
          Real.log ‖g z‖) := by
    filter_upwards [he] with z hz
    simpa only [Pi.add_apply, Finset.sum_apply] using hz
  rw [laplacian_pairing_congr_local hK.measurableSet hs he']
  simp_rw [mul_add]
  have hi1 : Integrable (fun z => Laplacian.laplacian φ z *
      ∑ u ∈ divisorSupport f hK,
        (MeromorphicOn.divisor f K u : ℝ) * Real.log ‖z - u‖) := by
    simp_rw [Finset.mul_sum]
    apply integrable_finsetSum
    intro u hu
    simpa only [mul_left_comm] using
      (integrable_laplacian_mul_log u hφ hφc).const_mul
        (MeromorphicOn.divisor f K u : ℝ)
  have hi2 : Integrable (fun z => Laplacian.laplacian φ z * Real.log ‖g z‖) := by
    have hi := HarmonicWeakLaplacian.integrable_mul_of_local
      (continuous_laplacian hφ hφc) (hasCompactSupport_laplacian hφc)
      (fun z hz => (hhg z (hs (tsupport_laplacian_subset φ hz))).1.continuousAt)
    simpa only [mul_comm] using hi
  have hpot := finite_log_potential_laplacian (divisorSupport f hK)
    (fun u : ℂ => u) (fun u => (MeromorphicOn.divisor f K u : ℝ)) hφ hφc
  rw [integral_add hi1 hi2, hpot,
    HarmonicWeakLaplacian.harmonic_laplacian_test hhg hφ hφc hs, add_zero]

/-- The actual analytic divisor on a compact carrier, as a finite positive atomic measure.
The positive-part convention is immaterial under analyticity, where every divisor
multiplicity is nonnegative. -/
def divisorMeasure (f : ℂ → ℂ) {K : Set ℂ} (hK : IsCompact K) : Measure ℂ :=
  ∑ u ∈ divisorSupport f hK,
    ((MeromorphicOn.divisor f K u).toNat : ℝ≥0∞) • Measure.dirac u

instance divisorMeasure_finite (f : ℂ → ℂ) {K : Set ℂ} (hK : IsCompact K) :
    IsFiniteMeasure (divisorMeasure f hK) := by
  constructor
  simp only [divisorMeasure, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  simp

theorem integrable_divisorMeasure (f : ℂ → ℂ) {K : Set ℂ} (hK : IsCompact K) (φ : ℂ → ℝ) :
    Integrable φ (divisorMeasure f hK) := by
  apply integrable_finsetSum_measure.mpr
  intro u hu
  exact (integrable_dirac (by finiteness)).smul_measure (by finiteness)

/-- Integration against this measure is the actual multiplicity-weighted sum. -/
theorem integral_divisorMeasure {f : ℂ → ℂ} {K : Set ℂ} (hK : IsCompact K)
    (hf : AnalyticOnNhd ℂ f K) (φ : ℂ → ℝ) :
    (∫ z, φ z ∂divisorMeasure f hK) =
      ∑ u ∈ divisorSupport f hK, (MeromorphicOn.divisor f K u : ℝ) * φ u := by
  unfold divisorMeasure
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro u hu
    rw [integral_smul_measure, integral_dirac]
    simp only [ENNReal.toReal_natCast, smul_eq_mul]
    congr 1
    exact_mod_cast Int.toNat_of_nonneg (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf u)
  · intro u hu
    exact (integrable_dirac (by finiteness)).smul_measure (by finiteness)

/-- Local Poincaré–Lelong with the actual positive zero-counting measure. -/
theorem analytic_log_laplacian_measure {f : ℂ → ℂ} {K : Set ℂ} (hK : IsCompact K)
    (hf : AnalyticOnNhd ℂ f K) (hn : ∀ z ∈ K, ¬f =ᶠ[𝓝 z] 0)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ K) :
    (∫ z, Laplacian.laplacian φ z * Real.log ‖f z‖) =
      2 * Real.pi * ∫ z, φ z ∂divisorMeasure f hK := by
  rw [integral_divisorMeasure hK hf]
  exact analytic_log_laplacian hK hf hn hφ hφc hs

/-- The zero measure normalized by the positive logarithmic scale. -/
def normalizedDivisorMeasure (f : ℂ → ℂ) {K : Set ℂ} (hK : IsCompact K) (q : ℝ) : Measure ℂ :=
  ENNReal.ofReal q⁻¹ • divisorMeasure f hK

instance normalizedDivisorMeasure_finite (f : ℂ → ℂ) {K : Set ℂ} (hK : IsCompact K) (q : ℝ) :
    IsFiniteMeasure (normalizedDivisorMeasure f hK q) := by
  exact (divisorMeasure f hK).smul_finite ENNReal.ofReal_ne_top

theorem normalized_log_laplacian_measure {f : ℂ → ℂ} {K : Set ℂ} (hK : IsCompact K) {q : ℝ}
    (hq : 0 < q) (hf : AnalyticOnNhd ℂ f K)
    (hn : ∀ z ∈ K, ¬f =ᶠ[𝓝 z] 0)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ K) :
    (∫ z, Laplacian.laplacian φ z * (Real.log ‖f z‖ / q)) =
      2 * Real.pi * ∫ z, φ z ∂normalizedDivisorMeasure f hK q := by
  simp_rw [← mul_div_assoc]
  rw [integral_div, analytic_log_laplacian_measure hK hf hn hφ hφc hs,
    normalizedDivisorMeasure, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr hq.le), smul_eq_mul]
  ring

theorem normalized_divisor_measure_tendsto_test
    {ι : Type*} {l : Filter ι} {f : ι → ℂ → ℂ} {q : ι → ℝ}
    {K : Set ℂ} (hK : IsCompact K) {H φ : ℂ → ℝ}
    (hinputs : ∀ᶠ i in l, 0 < q i ∧
      AnalyticOnNhd ℂ (f i) K ∧
      ∀ z ∈ K, ¬(f i) =ᶠ[𝓝 z] 0)
    (hH : IntegrableOn H K)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ K)
    (hL1 : Tendsto (fun i => ∫ z in K,
      ‖Real.log ‖f i z‖ / q i - H z‖) l (𝓝 0)) :
    Tendsto (fun i => ∫ z, φ z ∂normalizedDivisorMeasure (f i) hK (q i)) l
      (𝓝 ((∫ z, Laplacian.laplacian φ z * H z) / (2 * Real.pi))) := by
  have hu : ∀ᶠ i in l, IntegrableOn (fun z => Real.log ‖f i z‖ / q i)
      K := by
    filter_upwards [hinputs] with i hi
    exact ((ZeroDensity.AnalyticLogIntegrability.locallyIntegrableOn_log_norm
      hi.2.1 hi.2.2).integrableOn_isCompact hK).div_const _
  have ht := ScalarWeakLaplacian.weakLaplacianPairing_tendsto_on_compact_eventually
    hK hu hH (continuous_laplacian hφ hφc) hL1
  have he (u : ℂ → ℝ) : ZeroDensity.L1TestPairing.weakLaplacianPairing
      (volume.restrict K) u φ =
      ∫ z, Laplacian.laplacian φ z * u z := ZeroMeasureTestConvergence.setIntegral_laplacian_mul hs
  simp_rw [he] at ht
  apply (ht.div_const (2 * Real.pi)).congr'
  filter_upwards [hinputs] with i hi
  rw [normalized_log_laplacian_measure hK hi.1 hi.2.1 hi.2.2 hφ hφc hs]
  field_simp

#print axioms analytic_log_laplacian
#print axioms normalized_log_laplacian_measure
#print axioms normalized_divisor_measure_tendsto_test
end V10.AnalyticZeroMeasureCompact
