import V10.SmoothMeasureMass

/-!
# From smooth tests to continuous compactly supported tests

For locally finite positive measures, convergence on smooth compactly supported
tests in an open domain implies convergence on all continuous compactly supported
tests there. Uniform local mass bounds are derived from smooth cutoffs. The
candidate limiting measure is explicit; this module does not identify a
particular indicator's Laplacian measure or assume any sector counting law.
-/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
namespace V10.ContinuousMeasureTests

/-- Uniform approximation on a common compact carrier controls test integrals
by the actual mass of that carrier. -/
theorem integral_difference_le_mass (μ : Measure ℂ) [IsFiniteMeasureOnCompacts μ]
    {K : Set ℂ} (hK : IsCompact K) {f g : ℂ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hfs : tsupport f ⊆ K)
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ K)
    {δ : ℝ} (hbound : ∀ z, ‖f z - g z‖ ≤ δ) :
    ‖(∫ z, f z ∂μ) - ∫ z, g z ∂μ‖ ≤ δ * μ.real K := by
  rw [← integral_sub (hf.integrable_of_hasCompactSupport hfc)
    (hg.integrable_of_hasCompactSupport hgc)]
  have he : (∫ z in K, f z - g z ∂μ) = ∫ z, f z - g z ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hfs h)),
      image_eq_zero_of_notMem_tsupport (fun h => hz (hgs h)), sub_self]
  rw [← he]
  exact norm_setIntegral_le_of_norm_le_const hK.measure_lt_top (fun z _ => hbound z)

/-- The smooth-test criterion for vague convergence inside an open domain.
No local mass bounds or uniform-integrability hypotheses are supplied: the
required bounds follow from the asserted smooth-test convergence itself. -/
theorem continuous_test_tendsto_of_smooth
    {ι : Type*} {l : Filter ι} {μ : ι → Measure ℂ} {ν : Measure ℂ}
    [∀ i, IsFiniteMeasureOnCompacts (μ i)] [IsFiniteMeasureOnCompacts ν]
    {U : Set ℂ} (hU : IsOpen U)
    (htest : ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      Tendsto (fun i => ∫ z, ψ z ∂μ i) l (𝓝 (∫ z, ψ z ∂ν)))
    {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ U) :
    Tendsto (fun i => ∫ z, f z ∂μ i) l (𝓝 (∫ z, f z ∂ν)) := by
  obtain ⟨K, hK, hKU, hfK, happrox⟩ :=
    SmoothTestApproximation.exists_fixed_compact_smooth_approximation hf hfc hU hfs
  obtain ⟨M, hM, hmass⟩ := SmoothMeasureMass.eventually_bounded_mass_on_compact
    hU htest hK hKU
  rw [Metric.tendsto_nhds]
  intro ε hε
  let C := M + ν.real K + 1
  have hC : 0 < C := by dsimp [C]; positivity
  let δ := ε / (3 * C)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hC)
  obtain ⟨g, hg, hgc, hgK, hgf⟩ := happrox δ hδ
  have heν : ‖(∫ z, g z ∂ν) - ∫ z, f z ∂ν‖ ≤ δ * ν.real K :=
    integral_difference_le_mass ν hK hg.continuous hgc hgK hf hfc hfK
      (fun z => (hgf z).le)
  have heg : ∀ᶠ i in l, ‖(∫ z, g z ∂μ i) - ∫ z, g z ∂ν‖ < ε / 3 := by
    simpa only [dist_eq_norm] using Metric.tendsto_nhds.mp
      (htest g hg hgc (hgK.trans hKU)) (ε / 3) (by positivity)
  filter_upwards [hmass, heg] with i hi hgi
  have hei : ‖(∫ z, f z ∂μ i) - ∫ z, g z ∂μ i‖ ≤ δ * M := by
    apply (integral_difference_le_mass (μ i) hK hf hfc hfK hg.continuous hgc hgK
      (fun z => by simpa only [norm_sub_rev] using (hgf z).le)).trans
    exact mul_le_mul_of_nonneg_left hi hδ.le
  have htri : ‖(∫ z, f z ∂μ i) - ∫ z, f z ∂ν‖ ≤
      ‖(∫ z, f z ∂μ i) - ∫ z, g z ∂μ i‖ +
        (‖(∫ z, g z ∂μ i) - ∫ z, g z ∂ν‖ +
          ‖(∫ z, g z ∂ν) - ∫ z, f z ∂ν‖) := by
    exact (norm_sub_le_norm_sub_add_norm_sub
      (∫ z, f z ∂μ i) (∫ z, g z ∂μ i) (∫ z, f z ∂ν)).trans
      (add_le_add le_rfl (norm_sub_le_norm_sub_add_norm_sub
        (∫ z, g z ∂μ i) (∫ z, g z ∂ν) (∫ z, f z ∂ν)))
  have hδC : δ * C = ε / 3 := by dsimp [δ]; field_simp
  rw [dist_eq_norm]
  dsimp [C] at hδC
  nlinarith [mul_pos hδ hM]

#print axioms integral_difference_le_mass
#print axioms continuous_test_tendsto_of_smooth
end V10.ContinuousMeasureTests
