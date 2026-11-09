import V10.ScalarIndicator
import V10.CompanionRoots
import V10.PerronNonvanishing
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# The original scalar equation supplies the companion system

The derivative jet is the actual jet of the scalar analytic function. Its
companion ODE is derived from the scalar differential equation, not supplied
as an independent assumption. Pointwise coefficient convergence also gives
operator convergence of the actual companion matrices.
-/

noncomputable section
open Set Filter
open scoped Topology
namespace V10.ScalarCompanionODE
open V10.CompanionObservation V10.CompanionShortFlow V10.ScalarIndicator
set_option backward.isDefEq.respectTransparency false

theorem iteratedDeriv_hasDerivAt {v : ℂ → ℂ} {z : ℂ} (hv : AnalyticAt ℂ v z) (j : ℕ) :
    HasDerivAt (iteratedDeriv j v) (iteratedDeriv (j + 1) v z) z := by
  rw [iteratedDeriv_succ]
  apply DifferentiableAt.hasDerivAt
  simpa only [iteratedDeriv_eq_iterate] using (hv.iterated_deriv j).differentiableAt

/-- The actual derivative jet satisfies the actual companion ODE at every
analytic point where the original scalar differential equation holds. -/
theorem jet_hasDerivAt_companion {n : ℕ} {v : ℂ → ℂ} {z : ℂ}
    (hv : AnalyticAt ℂ v z) (b : Fin (n + 1) → ℂ)
    (hscalar : iteratedDeriv (n + 1) v z +
      ∑ j : Fin (n + 1), b j * iteratedDeriv j.val v z = 0) :
    HasDerivAt (ZeroDensity.ScalarLimit.jet (n + 1) v)
      (companion b (ZeroDensity.ScalarLimit.jet (n + 1) v z)) z := by
  apply hasDerivAt_pi.mpr
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · have hd := iteratedDeriv_hasDerivAt hv n
    have he : companion b (ZeroDensity.ScalarLimit.jet (n + 1) v z) (Fin.last n) =
        iteratedDeriv (n + 1) v z := by
      rw [companion_last]
      change -(∑ j : Fin (n + 1), b j * iteratedDeriv j.val v z) = _
      linear_combination -hscalar
    rw [he]
    exact hd
  · have hd := iteratedDeriv_hasDerivAt hv i.val
    simpa [companion, ZeroDensity.ScalarLimit.jet] using hd

/-- Dependence of the actual companion operator on its coefficient row is
continuous in operator norm; finite dimensionality supplies the topology. -/
theorem companion_continuous {n : ℕ} : Continuous (companion (n := n)) := by
  apply continuous_clm_apply.mpr
  intro w
  apply continuous_pi
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · have he : (fun b : Fin (n + 1) → ℂ => companion b w (Fin.last n)) =
        (fun b => -∑ j : Fin (n + 1), b j * w j) := funext fun b => companion_last b w
    rw [he]
    fun_prop
  · have he : (fun b : Fin (n + 1) → ℂ => companion b w i.castSucc) =
        (fun _ => w i.succ) := by funext b; simp [companion]
    rw [he]
    exact continuous_const

/-- A nontrivial scalar solution has a nowhere-zero derivative jet. This
derives the initial nonvanishing used by Perron from scalar nontriviality. -/
theorem jet_nowhere_zero_of_scalar_nontrivial {n : ℕ} {v : ℂ → ℂ}
    {b : ℂ → Fin (n + 1) → ℂ} {S : Set ℂ} (hS : IsOpen S) (hconn : IsPreconnected S)
    (hv : AnalyticOnNhd ℂ v S) (hb : ContinuousOn b S)
    (hscalar : ∀ z ∈ S, iteratedDeriv (n + 1) v z +
      ∑ j : Fin (n + 1), b z j * iteratedDeriv j.val v z = 0)
    (hnontrivial : ∃ z ∈ S, v z ≠ 0) :
    ∀ z ∈ S, ZeroDensity.ScalarLimit.jet (n + 1) v z ≠ 0 := by
  apply V10.PerronNonvanishing.nowhere_zero hS hconn
    (companion_continuous.comp_continuousOn hb)
    (fun z hz => jet_hasDerivAt_companion (hv z hz) (b z) (hscalar z hz))
  obtain ⟨z, hz, hn⟩ := hnontrivial
  refine ⟨z, hz, ?_⟩
  intro hzero
  apply hn
  have hh := congrFun hzero (0 : Fin (n + 1))
  simpa only [ZeroDensity.ScalarLimit.jet, Fin.val_zero, iteratedDeriv_zero, Pi.zero_apply] using hh

/-- The scalar spectral classification from the original analytic scalar ODE
on a complex phase-domain ray. Every stated root is an actual root of the
scalar characteristic equation. -/
theorem scalar_equation_ray_classification {n : ℕ} {v : ℂ → ℂ}
    {b : ℂ → Fin (n + 1) → ℂ} {b₀ : Fin (n + 1) → ℂ}
    {S : Set ℂ} {ζ : ℂ} {T : ℝ} (hζ : ζ ≠ 0)
    (hv : AnalyticOnNhd ℂ v S) (hb : ContinuousOn b S)
    (hray : ∀ r ≥ T, (r : ℂ) * ζ ∈ S)
    (hlim : ∀ j, Tendsto (fun r : ℝ => b ((r : ℂ) * ζ) j) atTop (𝓝 (b₀ j)))
    (hscalar : ∀ z ∈ S, iteratedDeriv (n + 1) v z +
      ∑ j : Fin (n + 1), b z j * iteratedDeriv j.val v z = 0)
    (hY : ZeroDensity.ScalarLimit.jet (n + 1) v ((T : ℂ) * ζ) ≠ 0) :
    ∃ μ : ℂ, μ ^ (n + 1) + ∑ j : Fin (n + 1), b₀ j * μ ^ j.val = 0 ∧
      Tendsto (fun r : ℝ => Real.log
        ‖ZeroDensity.ScalarLimit.jet (n + 1) v ((r : ℂ) * ζ)‖ / r)
        atTop (𝓝 (μ * ζ).re) ∧ rayIndicator v ζ = ((μ * ζ).re : EReal) := by
  have hc : ContinuousOn (fun z => companion (b z)) S := companion_continuous.comp_continuousOn hb
  have hl : Tendsto (fun r : ℝ => companion (b ((r : ℂ) * ζ))) atTop (𝓝 (companion b₀)) :=
    (companion_continuous.tendsto b₀).comp (tendsto_pi_nhds.mpr hlim)
  obtain ⟨μ, hμ, hs⟩ := actual_jet_ray_classification b₀ hζ hc hray hl
    (fun z hz => jet_hasDerivAt_companion (hv z hz) (b z) (hscalar z hz)) hY
  exact ⟨μ.val, V10.CompanionRoots.eigenvalue_root_equation b₀ μ.property, hμ, hs⟩

/-- Scalar spectral classification with all jet-system and nonvanishing
inputs derived from the original nontrivial analytic scalar equation. -/
theorem nontrivial_scalar_ray_classification {n : ℕ} {v : ℂ → ℂ}
    {b : ℂ → Fin (n + 1) → ℂ} {b₀ : Fin (n + 1) → ℂ}
    {S : Set ℂ} {ζ : ℂ} {T : ℝ} (hζ : ζ ≠ 0)
    (hS : IsOpen S) (hconn : IsPreconnected S)
    (hv : AnalyticOnNhd ℂ v S) (hb : ContinuousOn b S)
    (hray : ∀ r ≥ T, (r : ℂ) * ζ ∈ S)
    (hlim : ∀ j, Tendsto (fun r : ℝ => b ((r : ℂ) * ζ) j) atTop (𝓝 (b₀ j)))
    (hscalar : ∀ z ∈ S, iteratedDeriv (n + 1) v z +
      ∑ j : Fin (n + 1), b z j * iteratedDeriv j.val v z = 0)
    (hnontrivial : ∃ z ∈ S, v z ≠ 0) :
    ∃ μ : ℂ, μ ^ (n + 1) + ∑ j : Fin (n + 1), b₀ j * μ ^ j.val = 0 ∧
      Tendsto (fun r : ℝ => Real.log
        ‖ZeroDensity.ScalarLimit.jet (n + 1) v ((r : ℂ) * ζ)‖ / r)
        atTop (𝓝 (μ * ζ).re) ∧ rayIndicator v ζ = ((μ * ζ).re : EReal) :=
  scalar_equation_ray_classification hζ hv hb hray hlim hscalar
    (jet_nowhere_zero_of_scalar_nontrivial hS hconn hv hb hscalar hnontrivial _ (hray T le_rfl))

#print axioms jet_hasDerivAt_companion
#print axioms scalar_equation_ray_classification
#print axioms nontrivial_scalar_ray_classification

end V10.ScalarCompanionODE
