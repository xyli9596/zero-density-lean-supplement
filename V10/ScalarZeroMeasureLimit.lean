import V10.ZeroMeasureTestConvergence
import V10.ScalarIndicatorLimit
import Mathlib.Tactic

/-! Actual scalar ODE solutions give smooth-test convergence of their
normalized zero measures. The zeros are those of the actual scaled function
`z ↦ v (R*z)` and carry normalization `1/R`. Neither scalar L¹ convergence
nor the Poincaré–Lelong identity is an input to either ODE endpoint below.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ContDiff
namespace V10.ScalarZeroMeasureLimit
open AnalyticZeroMeasure PerronVectorLimit
set_option backward.isDefEq.respectTransparency false

theorem exists_nonzero_on_closedBall_of_germ {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hg : ¬f =ᶠ[𝓝 c] 0) :
    ∃ w ∈ closedBall c r, f w ≠ 0 := by
  by_contra! h
  apply hg
  filter_upwards [Metric.ball_mem_nhds c hr] with z hz
  exact h z (ball_subset_closedBall hz)

/-- Eventual analytic/nontrivial inputs for the genuine scaled divisor,
derived from a nonzero actual derivative jet and eventual domain inclusion. -/
theorem eventually_scaled_inputs {n : ℕ} {v : ℂ → ℂ} {S : Set ℂ}
    (hS : IsOpen S) (hconn : IsPreconnected S) (hv : AnalyticOnNhd ℂ v S)
    {z₀ c : ℂ} {r : ℝ} (hz₀ : z₀ ∈ S)
    (hn₀ : ZeroDensity.ScalarLimit.jet n v z₀ ≠ 0) (hr : 0 < r)
    (hDS : ∀ᶠ R : ℝ in atTop, ∀ z ∈ closedBall c r, (R : ℂ) * z ∈ S) :
    ∀ᶠ R : ℝ in atTop, 0 < R ∧
      AnalyticOnNhd ℂ (fun z => v ((R : ℂ) * z)) (closedBall c r) ∧
      ∃ w ∈ closedBall c r, v ((R : ℂ) * w) ≠ 0 := by
  have hg := ScalarAnalytic.germs_ne_zero_of_jet hS hconn hv hz₀ hn₀
  filter_upwards [hDS, eventually_gt_atTop (0 : ℝ)] with R hmap hR
  refine ⟨hR, ScalarAnalytic.dilated_analyticOnNhd hv hmap, ?_⟩
  apply exists_nonzero_on_closedBall_of_germ hr
  exact ScalarAnalytic.dilated_germ_ne_zero (Complex.ofReal_ne_zero.mpr hR.ne')
    (hg _ (hmap c (mem_closedBall_self hr.le)))

/-- The actual jet ODE endpoint on a fixed interior disk. The right-hand
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
    {c : ℂ} {r : ℝ} (hr : 0 < r) (hKD : closedBall c r ⊆ D)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ closedBall c r) :
    Tendsto (fun R : ℝ => ∫ z, φ z ∂normalizedDivisorMeasure
      (fun z => v ((R : ℂ) * z)) c r R) atTop
      (𝓝 ((∫ z, Laplacian.laplacian φ z *
        indicator (ZeroDensity.ScalarLimit.jet n v) z) / (2 * Real.pi))) := by
  have hv := ScalarAnalytic.analyticOnNhd_of_jet_ode hn hS hode
  have hne := PerronNonvanishing.nowhere_zero hS hconn hA hode hnonzero
  have hK : IsCompact (closedBall c r) := isCompact_closedBall c r
  have hmap : ∀ᶠ R : ℝ in atTop, ∀ z ∈ closedBall c r, (R : ℂ) * z ∈ S := by
    apply ScalarWeakLaplacian.eventually_on_compact_of_locally hK
    intro x hx
    obtain ⟨N, hNo, hxN, _, _, _, M, hm, _, _⟩ := hlocal x (hKD hx)
    exact ⟨N, hNo, hxN, hm⟩
  have hH : ContinuousOn (indicator (ZeroDensity.ScalarLimit.jet n v)) (closedBall c r) := by
    intro x hx
    obtain ⟨N, hNo, hxN, _, hNc, hNz, M, hm, hb, hl⟩ := hlocal x (hKD hx)
    have hsN : ({x} : Set ℂ) ⊆ N := singleton_subset_iff.mpr hxN
    obtain ⟨_, _, hc, _⟩ := actual_vector_compact_limit hNc isCompact_singleton hsN hNz
      hA hode hne hm hb hl
    exact (hc.continuousAt (hNo.mem_nhds hxN)).continuousWithinAt
  obtain ⟨z₀, hz₀, hn₀⟩ := hnonzero
  exact ZeroMeasureTestConvergence.normalized_divisor_measure_tendsto_test
    (eventually_scaled_inputs hS hconn hv hz₀ hn₀ hr hmap) (hH.integrableOn_compact hK)
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
    {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hKD : closedBall c r ⊆ SectorScaledNeighborhood.fullCone J)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ closedBall c r) :
    Tendsto (fun R : ℝ => ∫ z, φ z ∂normalizedDivisorMeasure
      (fun z => v ((R : ℂ) * z)) c r R) atTop
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
  have hK : IsCompact (closedBall c r) := isCompact_closedBall c r
  have hmap : ∀ᶠ R : ℝ in atTop, ∀ z ∈ closedBall c r,
      (R : ℂ) * z ∈ PerronSector.sector R₀ J := by
    apply ScalarWeakLaplacian.eventually_on_compact_of_locally hK
    intro x hx
    obtain ⟨N, hNo, hxN, _, _, _, M, hm, _, _⟩ := hlocal x (hKD hx)
    exact ⟨N, hNo, hxN, hm⟩
  obtain ⟨hH, _, hL1, _⟩ := ScalarIndicatorLimit.lemma_3_2
    hR₀ hJo hJc hv hb hscalar hnontrivial hlim
  obtain ⟨z₀, hz₀, _⟩ := hnontrivial
  exact ZeroMeasureTestConvergence.normalized_divisor_measure_tendsto_test
    (eventually_scaled_inputs hS hSc hv hz₀ (hne z₀ hz₀) hr hmap)
    ((hH.mono hKD).integrableOn_compact hK) hφ hφc hs (hL1 _ hK hKD)

#print axioms eventually_scaled_inputs
#print axioms actual_ode_zero_measure_tendsto_test
#print axioms sector_scalar_zero_measure_tendsto_test
end V10.ScalarZeroMeasureLimit
