import V10.LocalPortmanteau
import V10.ScalarZeroMeasureCompact

/-!
# Actual scalar zero measures on local continuity sets

The compact carrier K is fixed before quantifying over tests. The explicit
candidate measure must be identified with the actual indicator's distributional
Laplacian; no zero-measure convergence is assumed in the scalar-ODE endpoint.
-/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff
namespace V10.ScalarZeroMeasureSets
open AnalyticZeroMeasureCompact

/-- L¹ convergence of actual analytic logarithms gives continuity-set convergence
once the candidate measure's actual Laplacian pairing has been identified. -/
theorem normalized_divisor_measure_tendsto_set
    {ι : Type*} {l : Filter ι} {f : ι → ℂ → ℂ} {q : ι → ℝ}
    {K : Set ℂ} (hK : IsCompact K) {H : ℂ → ℝ}
    (hinputs : ∀ᶠ i in l, 0 < q i ∧ AnalyticOnNhd ℂ (f i) K ∧
      ∀ z ∈ K, ¬(f i) =ᶠ[𝓝 z] 0)
    (hH : IntegrableOn H K)
    (hL1 : Tendsto (fun i => ∫ z in K, ‖Real.log ‖f i z‖ / q i - H z‖) l (𝓝 0))
    {ν : Measure ℂ} [IsFiniteMeasureOnCompacts ν]
    {U : Set ℂ} (hU : IsOpen U) (hUK : U ⊆ K)
    (hpair : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ z, Laplacian.laplacian φ z * H z) / (2 * Real.pi) = ∫ z, φ z ∂ν)
    {A : Set ℂ} (hA : MeasurableSet A) (hAc : IsCompact (closure A))
    (hAU : closure A ⊆ U) (hfront : ν (frontier A) = 0) :
    Tendsto (fun i => normalizedDivisorMeasure (f i) hK (q i) A) l (𝓝 (ν A)) := by
  apply LocalPortmanteau.tendsto_measure_of_smooth_compact_tests hU _ hA hAc hAU hfront
  intro φ hφ hφc hφU
  rw [← hpair φ hφ hφc hφU]
  exact AnalyticZeroMeasureCompact.normalized_divisor_measure_tendsto_test hK
    hinputs hH hφ hφc (hφU.trans hUK) hL1

/-- Original scalar ODE and sector hypotheses give convergence of actual
normalized zero masses on relatively compact continuity sets. -/
theorem sector_scalar_zero_measure_tendsto_set
    {n : ℕ} {v : ℂ → ℂ} {b : ℂ → Fin (n + 1) → ℂ}
    {a : Fin (n + 1) → ℂ} {R₀ : ℝ} {J : Set ℝ}
    (hR₀ : 0 < R₀) (hJo : IsOpen J) (hJc : IsPreconnected J)
    (hv : AnalyticOnNhd ℂ v (PerronSector.sector R₀ J))
    (hb : ContinuousOn b (PerronSector.sector R₀ J))
    (hscalar : ∀ z ∈ PerronSector.sector R₀ J, iteratedDeriv (n + 1) v z +
      ∑ j : Fin (n + 1), b z j * iteratedDeriv j.val v z = 0)
    (hnontrivial : ∃ z ∈ PerronSector.sector R₀ J, v z ≠ 0)
    (hlim : ∀ j (K : Set ℝ), K ⊆ J → IsCompact K →
      TendstoUniformlyOn
        (fun t : ℝ => fun θ : ℝ => b ((t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) j)
        (fun _ => a j) atTop K)
    {K : Set ℂ} (hK : IsCompact K)
    (hKD : K ⊆ SectorScaledNeighborhood.fullCone J)
    {ν : Measure ℂ} [IsFiniteMeasureOnCompacts ν]
    {U : Set ℂ} (hU : IsOpen U) (hUK : U ⊆ K)
    (hpair : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ z, Laplacian.laplacian φ z * ScalarIndicatorLimit.homogeneousIndicator v z) /
        (2 * Real.pi) = ∫ z, φ z ∂ν)
    {A : Set ℂ} (hA : MeasurableSet A) (hAc : IsCompact (closure A))
    (hAU : closure A ⊆ U) (hfront : ν (frontier A) = 0) :
    Tendsto (fun R : ℝ => (normalizedDivisorMeasure
      (fun z => v ((R : ℂ) * z)) hK R) A) atTop (𝓝 (ν A)) := by
  apply LocalPortmanteau.tendsto_measure_of_smooth_compact_tests hU _ hA hAc hAU hfront
  intro φ hφ hφc hφU
  rw [← hpair φ hφ hφc hφU]
  exact ScalarZeroMeasureCompact.sector_scalar_zero_measure_tendsto_test
    hR₀ hJo hJc hv hb hscalar hnontrivial hlim hK hKD hφ hφc (hφU.trans hUK)

#print axioms normalized_divisor_measure_tendsto_set
#print axioms sector_scalar_zero_measure_tendsto_set
end V10.ScalarZeroMeasureSets
