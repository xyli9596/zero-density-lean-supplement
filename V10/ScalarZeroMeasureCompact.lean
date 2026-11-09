import V10.AnalyticZeroMeasureCompact
import V10.ScalarIndicatorLimit
import Mathlib.Tactic

/-! Actual ODE and sector endpoints for zero-measure convergence on arbitrary
compact carriers. No convexity or connectedness of the compact carrier is
required; every scaled scalar germ is derived nonzero on the original domain.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ContDiff
namespace V10.ScalarZeroMeasureCompact
open AnalyticZeroMeasureCompact PerronVectorLimit
set_option backward.isDefEq.respectTransparency false

theorem eventually_scaled_inputs {n : ℕ} {v : ℂ → ℂ} {S K : Set ℂ}
    (hS : IsOpen S) (hconn : IsPreconnected S) (hv : AnalyticOnNhd ℂ v S)
    {z₀ : ℂ} (hz₀ : z₀ ∈ S) (hn₀ : ZeroDensity.ScalarLimit.jet n v z₀ ≠ 0)
    (hDS : ∀ᶠ R : ℝ in atTop, ∀ z ∈ K, (R : ℂ) * z ∈ S) :
    ∀ᶠ R : ℝ in atTop, 0 < R ∧
      AnalyticOnNhd ℂ (fun z => v ((R : ℂ) * z)) K ∧
      ∀ z ∈ K, ¬(fun w => v ((R : ℂ) * w)) =ᶠ[𝓝 z] 0 := by
  have hg := ScalarAnalytic.germs_ne_zero_of_jet hS hconn hv hz₀ hn₀
  filter_upwards [hDS, eventually_gt_atTop (0 : ℝ)] with R hmap hR
  refine ⟨hR, ScalarAnalytic.dilated_analyticOnNhd hv hmap, ?_⟩
  intro z hz
  exact ScalarAnalytic.dilated_germ_ne_zero (Complex.ofReal_ne_zero.mpr hR.ne')
    (hg _ (hmap z hz))

/-- The actual jet ODE endpoint on any compact subset of the phase domain. The right-hand
limit is the genuine distributional Laplacian of its actual Perron indicator. -/
theorem actual_ode_zero_measure_tendsto_test
    {n : ℕ} (hn : 0 < n) {v : ℂ → ℂ} {S D : Set ℂ}
    (hS : IsOpen S) (hconn : IsPreconnected S)
    {A : ℂ → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)}
    {A₀ : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)}
    (hA : ContinuousOn A S)
    (hode : ∀ z ∈ S, HasDerivAt (ZeroDensity.ScalarLimit.jet n v)
      (A z (ZeroDensity.ScalarLimit.jet n v z)) z)
    (hnonzero : ∃ z ∈ S, ZeroDensity.ScalarLimit.jet n v z ≠ 0)
    (hlocal : ∀ x ∈ D, ∃ N : Set ℂ, IsOpen N ∧ x ∈ N ∧ N ⊆ D ∧
      Convex ℝ N ∧ (∀ z ∈ N, z ≠ 0) ∧ ∃ M : ℝ≥0,
        (∀ᶠ R : ℝ in atTop, ∀ z ∈ N, (R : ℂ) * z ∈ S) ∧
        (∀ᶠ R : ℝ in atTop, ∀ z ∈ N, ‖A ((R : ℂ) * z)‖ ≤ M) ∧
        (∀ z ∈ N, Tendsto (fun R : ℝ => A ((R : ℂ) * z)) atTop (𝓝 A₀)))
    {K : Set ℂ} (hK : IsCompact K) (hKD : K ⊆ D)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ K) :
    Tendsto (fun R : ℝ => ∫ z, φ z ∂normalizedDivisorMeasure
      (fun z => v ((R : ℂ) * z)) hK R) atTop
      (𝓝 ((∫ z, Laplacian.laplacian φ z *
        indicator (ZeroDensity.ScalarLimit.jet n v) z) / (2 * Real.pi))) := by
  have hv := ScalarAnalytic.analyticOnNhd_of_jet_ode hn hS hode
  have hne := PerronNonvanishing.nowhere_zero hS hconn hA hode hnonzero
  have hmap : ∀ᶠ R : ℝ in atTop, ∀ z ∈ K, (R : ℂ) * z ∈ S := by
    apply ScalarWeakLaplacian.eventually_on_compact_of_locally hK
    intro x hx
    obtain ⟨N, hNo, hxN, _, _, _, M, hm, _, _⟩ := hlocal x (hKD hx)
    exact ⟨N, hNo, hxN, hm⟩
  have hH : ContinuousOn (indicator (ZeroDensity.ScalarLimit.jet n v)) (K) := by
    intro x hx
    obtain ⟨N, hNo, hxN, _, hNc, hNz, M, hm, hb, hl⟩ := hlocal x (hKD hx)
    have hsN : ({x} : Set ℂ) ⊆ N := singleton_subset_iff.mpr hxN
    obtain ⟨_, _, hc, _⟩ := actual_vector_compact_limit hNc isCompact_singleton hsN hNz
      hA hode hne hm hb hl
    exact (hc.continuousAt (hNo.mem_nhds hxN)).continuousWithinAt
  obtain ⟨z₀, hz₀, hn₀⟩ := hnonzero
  exact AnalyticZeroMeasureCompact.normalized_divisor_measure_tendsto_test hK
    (eventually_scaled_inputs hS hconn hv hz₀ hn₀ hmap) (hH.integrableOn_compact hK)
    hφ hφc hs
    (ScalarL1GlobalLimit.actual_scalar_L1_on_compacts hn hS hconn hA hode
      ⟨z₀, hz₀, hn₀⟩ hlocal _ hK hKD)

/-- The original scalar equation and its sector coefficient limits imply
smooth-test convergence of actual scaled zeros. This uses the completed
Lemma 3.2 internally and has no convergence premise. -/
theorem sector_scalar_zero_measure_tendsto_test
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
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ K) :
    Tendsto (fun R : ℝ => ∫ z, φ z ∂normalizedDivisorMeasure
      (fun z => v ((R : ℂ) * z)) hK R) atTop
      (𝓝 ((∫ z, Laplacian.laplacian φ z * ScalarIndicatorLimit.homogeneousIndicator v z) /
        (2 * Real.pi))) := by
  have hS := PerronSector.sector_isOpen R₀ hJo
  have hSc := PerronSector.sector_isPreconnected R₀ hJc
  have hne := ScalarCompanionODE.jet_nowhere_zero_of_scalar_nontrivial
    hS hSc hv hb hscalar hnontrivial
  have hAlim : ∀ K : Set ℝ, K ⊆ J → IsCompact K →
      TendstoUniformlyOn
        (fun t : ℝ => fun θ : ℝ => CompanionObservation.companion
          (b ((t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))))
        (fun _ => CompanionObservation.companion a) atTop K :=
    fun K hKJ hK => ScalarCoefficientLimits.companion_uniform_limit (fun j => hlim j K hKJ hK)
  have hlocal := SectorScaledNeighborhood.exists_scaled_neighborhood
    (A := fun z => CompanionObservation.companion (b z))
    (A₀ := CompanionObservation.companion a) hR₀ hJo hAlim
  have hmap : ∀ᶠ R : ℝ in atTop, ∀ z ∈ K,
      (R : ℂ) * z ∈ PerronSector.sector R₀ J := by
    apply ScalarWeakLaplacian.eventually_on_compact_of_locally hK
    intro x hx
    obtain ⟨N, hNo, hxN, _, _, _, M, hm, _, _⟩ := hlocal x (hKD hx)
    exact ⟨N, hNo, hxN, hm⟩
  obtain ⟨hH, _, hL1, _⟩ := ScalarIndicatorLimit.lemma_3_2
    hR₀ hJo hJc hv hb hscalar hnontrivial hlim
  obtain ⟨z₀, hz₀, _⟩ := hnontrivial
  exact AnalyticZeroMeasureCompact.normalized_divisor_measure_tendsto_test hK
    (eventually_scaled_inputs hS hSc hv hz₀ (hne z₀ hz₀) hmap)
    ((hH.mono hKD).integrableOn_compact hK) hφ hφc hs (hL1 _ hK hKD)

#print axioms eventually_scaled_inputs
#print axioms actual_ode_zero_measure_tendsto_test
#print axioms sector_scalar_zero_measure_tendsto_test
end V10.ScalarZeroMeasureCompact
