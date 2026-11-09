import V10.ProjectionPhysicalWindows
import V10.SamplingScale

/-! The actual square-root sample and phase normalization in Theorem 1.5
consume Lemma 4.3 without a remaining summability hypothesis. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace V10.ProjectionSampledPhysicalWindows
open ProjectionRowFamily ProjectionLemma43 SamplingScale
set_option backward.isDefEq.respectTransparency false

variable {ι Ω : Type*} [Fintype ι] [Fintype Ω] [Nonempty Ω]

/-- One actual complete pluripolar cone controls every sampled physical
window at `r_m = sqrt(m+1)` and `Q_m=(a*r_m)^β exp(a*r_m)`.
Positivity and reciprocal summability of this exact Q are derived, not
assumed. All compact parameter sets are covered simultaneously. -/
theorem sampled_physical_window_projection {f : ι → ℂ → ℂ}
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) univ) (hi : LinearIndependent ℂ f)
    (hn : ∀ z, ∃ j, f j z ≠ 0)
    (ω : Ω → ℂ) (hω : ∀ dir, ω dir ≠ 0)
    {a β : ℝ} (ha : 0 < a) (hβ : 0 ≤ β) :
    ∃ (Ψ : EuclideanSpace ℂ ι → EReal) (κ : ℝ),
      ERealPlurisubharmonic.Plurisubharmonic Ψ ∧ 0 < κ ∧
      ExceptionalCone.LogHomogeneous Ψ κ ∧ (∃ c, Ψ c ≠ ⊥) ∧
      IsCompletePluripolar {c | Ψ c = ⊥} ∧
      (∀ c, ∀ α : ℂ, Ψ c = ⊥ → Ψ (α • c) = ⊥) ∧
      (∀ c, Ψ c ≠ ⊥ → ∀ dir : Ω, ∀ K : Set (ℝ × ℝ), IsCompact K →
        Tendsto (fun m => (phaseScale a β m)⁻¹ * ∫ z in K,
          |Real.log (‖∑ j, f j ((ω dir)⁻¹ * (((a * radius m : ℝ) : ℂ) +
              (z.1 : ℂ) + Complex.I * (Real.sqrt (a * radius m) : ℂ) *
              (z.2 : ℂ))) * c j‖ /
            ‖rowVector f ((ω dir)⁻¹ * (((a * radius m : ℝ) : ℂ) +
              (z.1 : ℂ) + Complex.I * (Real.sqrt (a * radius m) : ℂ) *
              (z.2 : ℂ)))‖)|)
          atTop (𝓝 0)) := by
  exact ProjectionPhysicalWindows.physical_window_projection hf hi hn ω hω
    (fun m => a * radius m) (fun m => mul_pos ha (radius_pos m))
    (phaseScale_pos ha β) (summable_reciprocal_phaseScale ha hβ)

#print axioms sampled_physical_window_projection
end V10.ProjectionSampledPhysicalWindows
