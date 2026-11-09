import V10.PerronVectorLimit
import V10.SubharmonicLimit
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The actual Perron vector indicator is subharmonic

On an open convex scaled neighborhood, actual complex ODE derivatives give
analyticity of the scaled vector functions. The proved Perron theorem and
ODE Lipschitz bounds give compact uniform convergence to the actual limsup
indicator, which is therefore continuous real-valued subharmonic.

No convergence of potentials or subharmonicity is a hypothesis. Nonvanishing
of the vector is essential here: scalar zeros and their extended-real/L1
potential theory remain separate from this vector conclusion.
-/

noncomputable section
open Set Filter Module
open scoped Topology NNReal
namespace V10.PerronVectorSubharmonic
open V10.PerronVectorLimit

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Analyticity of the scaled vector functions follows from the actual
complex ODE on the scaled image of the open neighborhood. -/
theorem eventually_analytic_scaled_vector {Ω D : Set ℂ} (hDopen : IsOpen D)
    {A : ℂ → E →L[ℂ] E} {Y : ℂ → E}
    (hode : ∀ z ∈ Ω, HasDerivAt Y (A z (Y z)) z)
    (hmap : ∀ᶠ R : ℝ in atTop, ∀ ζ ∈ D, (R : ℂ) * ζ ∈ Ω) :
    ∀ᶠ R : ℝ in atTop, AnalyticOnNhd ℂ (fun ζ => Y ((R : ℂ) * ζ)) D := by
  apply hmap.mono
  intro R hR
  apply DifferentiableOn.analyticOnNhd _ hDopen
  intro ζ hζ
  have hs : Differentiable ℂ (fun w : ℂ => (R : ℂ) * w) :=
    fun w => ((hasDerivAt_id w).const_mul (R : ℂ)).differentiableAt
  exact ((hode _ (hR ζ hζ)).differentiableAt.comp ζ hs.differentiableAt).differentiableWithinAt

/-- The actual limsup vector indicator is subharmonic. All pointwise Perron
limits, compact uniform convergence and scaled analyticity are derived from
the real hypotheses on the complex ODE, not supplied as conclusions. -/
theorem actual_indicator_subharmonic {Ω D : Set ℂ}
    (hDopen : IsOpen D) (hD : Convex ℝ D) (hDzero : ∀ ζ ∈ D, ζ ≠ 0)
    {A : ℂ → E →L[ℂ] E} {A₀ : E →L[ℂ] E} {Y : ℂ → E} {M : ℝ≥0}
    (hcont : ContinuousOn A Ω)
    (hode : ∀ z ∈ Ω, HasDerivAt Y (A z (Y z)) z)
    (hne : ∀ z ∈ Ω, Y z ≠ 0)
    (hmap : ∀ᶠ R : ℝ in atTop, ∀ ζ ∈ D, (R : ℂ) * ζ ∈ Ω)
    (hbound : ∀ᶠ R : ℝ in atTop, ∀ ζ ∈ D, ‖A ((R : ℂ) * ζ)‖ ≤ M)
    (hlim : ∀ ζ ∈ D, Tendsto (fun R : ℝ => A ((R : ℂ) * ζ)) atTop (𝓝 A₀)) :
    SubharmonicOn (indicator Y) D := by
  apply V10.SubharmonicLimit.normalized_logNorm_limit_subharmonic
    (l := atTop) (F := fun (R : ℝ) ζ => Y ((R : ℂ) * ζ)) (q := fun R : ℝ => R) hDopen
  · filter_upwards [eventually_analytic_scaled_vector hDopen hode hmap,
      hmap, eventually_gt_atTop (0 : ℝ)] with R ha hm hR
    exact ⟨hR, ha, fun ζ hζ => hne _ (hm ζ hζ)⟩
  · intro K hKD hK
    exact (actual_vector_compact_limit hD hK hKD hDzero
      hcont hode hne hmap hbound hlim).1

#print axioms eventually_analytic_scaled_vector
#print axioms actual_indicator_subharmonic
end V10.PerronVectorSubharmonic
