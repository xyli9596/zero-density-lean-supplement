import V10.ScalarCompactnessAssembly
import V10.ScalarCompactnessInputs

/-!
# Actual scaled scalar potentials have local L¹-convergent subsequences

Vector-potential convergence and the actual derivative jet imply the analytic
upper bounds and the moving scalar lower samples. The compactness theorem for
analytic logarithms then applies to every sequence of scales tending to infinity.
An initial finite segment is removed internally, rather than imposing eventual
estimates as hypotheses at every index.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology

namespace V10.ScalarCompactnessActual

/-- For every sequence of scales tending to infinity, the actual scalar
potentials have an L¹-convergent subsequence on the smaller disk. Neither
scalar convergence nor scalar subsequential compactness is an input. -/
theorem actual_scalar_local_L1_subsequence {n : ℕ} (hn : 0 < n)
    {v : ℂ → ℂ} {S : Set ℂ} {H : ℂ → ℝ} {x : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hv : AnalyticOnNhd ℂ v S)
    (hDS : ∀ᶠ R : ℝ in atTop, ∀ z ∈ closedBall x (5 * δ), (R : ℂ) * z ∈ S)
    (hH : ContinuousOn H (closedBall x (5 * δ)))
    (hlim : TendstoUniformlyOn (PerronVectorLimit.potential (ZeroDensity.ScalarLimit.jet n v))
      H atTop (closedBall x (5 * δ)))
    (hjet : ∀ᶠ R : ℝ in atTop, ∀ z ∈ closedBall x (5 * δ),
      ZeroDensity.ScalarLimit.jet n v ((R : ℂ) * z) ≠ 0)
    {R : ℕ → ℝ} (hR : Tendsto R atTop atTop) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ U : ℂ → ℝ,
      IntegrableOn U (closedBall x δ) ∧
      Tendsto (fun k => ∫ z in closedBall x δ,
        ‖ScalarAnalytic.potential v (R (σ k)) z - U z‖) atTop (𝓝 0) := by
  obtain ⟨B, C, hB, _, hb⟩ := ScalarCompactnessInputs.eventual_local_analytic_bounds
    hn hδ hv hDS hH hlim hjet
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hR.eventually hb)
  have htail : ∀ k, 1 ≤ R (k + N) ∧
      AnalyticOnNhd ℂ (fun z => v ((R (k + N) : ℂ) * z)) (closedBall x (5 * δ)) ∧
      (∀ z ∈ closedBall x (5 * δ), ‖v ((R (k + N) : ℂ) * z)‖ ≤ Real.exp (R (k + N) * B)) ∧
      ∃ a ∈ closedBall x δ, Real.exp (-R (k + N) * C) ≤ ‖v ((R (k + N) : ℂ) * a)‖ := by
    intro k
    exact hN (k + N) (by omega)
  obtain ⟨σ, hσ, U, hUi, hU⟩ :=
    ScalarCompactnessAssembly.analytic_log_L1_subsequence_moving_center
      (f := fun k z => v ((R (k + N) : ℂ) * z)) (q := fun k => R (k + N))
      hδ (fun k => lt_of_lt_of_le zero_lt_one (htail k).1) hB
      (fun k => (htail k).2.1) (fun k => (htail k).2.2.1) (fun k => (htail k).2.2.2)
  refine ⟨fun k => σ k + N, fun i j hij => Nat.add_lt_add_right (hσ hij) N, U, hUi, ?_⟩
  simpa only [ScalarAnalytic.potential] using hU

#print axioms actual_scalar_local_L1_subsequence
end V10.ScalarCompactnessActual
