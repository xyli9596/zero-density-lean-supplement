import V10.ProjectionWindowPotential
import V10.ProjectionWindowLoss
import V10.ProjectionWindowSubsequence
import V10.ProjectionWindowCompactLoss

/-! The same actual exceptional pole cone controls every prescribed direction,
every scale, and every compact parameter window. -/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
namespace V10.ProjectionExceptionalCone
open ProjectionWindowPotential ProjectionWindowWeights ProjectionWindowSubsequence
open HolomorphicProjectionAverage ProjectionAffineWindow ProjectionWindowLoss
open LogHomogeneousSeries PluriPotentialSeries
set_option backward.isDefEq.respectTransparency false

variable {Ω E : Type*} [Fintype Ω] [Nonempty Ω]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Outside the pole set of the one constructed global potential, the actual
weighted absolute losses tend to zero for every direction and cutoff size.
The signed-average convergence is derived from the enumerated potential. -/
theorem weighted_loss_outside_pole {F : ℂ → E →L[ℂ] ℂ}
    (hF : Continuous F) (hFn : ∀ z, F z ≠ 0)
    (ha : ∀ c : E, c ≠ 0 → AnalyticOnNhd ℂ (fun z => F z c) univ)
    (hn : ∀ c : E, c ≠ 0 → ∃ z, F z c ≠ 0)
    (A : Ω → ℕ → ℂ ≃L[ℝ] ℂ) (b : Ω → ℕ → ℂ)
    {Q : ℕ → ℝ} (hQ : ∀ m, 0 < Q m) (hQs : Summable (fun m => (Q m)⁻¹))
    {c : E} (hc : potential F A b Q c ≠ ⊥) (dir : Ω) (L : ℕ) :
    Tendsto (fun m => (Q m)⁻¹ * ∫ z, cutoff L z *
      |logProjection (fun w => F (window (A dir m) (b dir m) w)) c z|)
      atTop (𝓝 0) := by
  have hc0 : c ≠ 0 := coefficient_ne_zero hc
  apply weighted_absolute_tendsto hF hFn (ha c hc0) (hn c hc0)
    (cutoff_smooth L).continuous (cutoff_compact L) (cutoff_nonneg L)
    (A dir) (b dir) hQ hQs
  exact window_tendsto_zero_of_ne_bot hc dir L
    (fun m => windowSummand_eq hF A b Q (dir, L, m) c)

/-- The same pole cone works for every compact parameter set, in particular
every compact rectangle. The cutoff is constructed and chosen internally. -/
theorem compact_loss_outside_pole {F : ℂ → E →L[ℂ] ℂ}
    (hF : Continuous F) (hFn : ∀ z, F z ≠ 0)
    (ha : ∀ c : E, c ≠ 0 → AnalyticOnNhd ℂ (fun z => F z c) univ)
    (hn : ∀ c : E, c ≠ 0 → ∃ z, F z c ≠ 0)
    (A : Ω → ℕ → ℂ ≃L[ℝ] ℂ) (b : Ω → ℕ → ℂ)
    {Q : ℕ → ℝ} (hQ : ∀ m, 0 < Q m) (hQs : Summable (fun m => (Q m)⁻¹))
    {c : E} (hc : potential F A b Q c ≠ ⊥) (dir : Ω)
    {K : Set ℂ} (hK : IsCompact K) :
    Tendsto (fun m => (Q m)⁻¹ * ∫ z in K,
      |logProjection (fun w => F (window (A dir m) (b dir m) w)) c z|)
      atTop (𝓝 0) := by
  have hc0 : c ≠ 0 := coefficient_ne_zero hc
  obtain ⟨L, hL⟩ := exists_cutoff_eq_one_on hK
  exact ProjectionWindowCompactLoss.compact_absolute_tendsto_of_weighted
    hF hFn (ha c hc0) (hn c hc0) (cutoff_smooth L).continuous
    (cutoff_compact L) (cutoff_nonneg L) hK (fun z hz => (hL z hz).ge)
    (A dir) (b dir) hQ (weighted_loss_outside_pole hF hFn ha hn A b hQ hQs hc dir L)

section Construction
variable [InnerProductSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Actual-window form of the pluripolar projection construction. The single
potential is built from the prescribed real-affine windows, has positive
logarithmic degree and genuine local pluripotential representations, and
controls the absolute logarithmic loss on every compact set outside its pole
cone. No convergence, exceptional set, or potential property is an input. -/
theorem actual_window_exceptional_potential {F : ℂ → E →L[ℂ] ℂ}
    (hF : Continuous F) (hFn : ∀ z, F z ≠ 0)
    (ha : ∀ c : E, c ≠ 0 → AnalyticOnNhd ℂ (fun z => F z c) univ)
    (hn : ∀ c : E, c ≠ 0 → ∃ z, F z c ≠ 0)
    (A : Ω → ℕ → ℂ ≃L[ℝ] ℂ) (b : Ω → ℕ → ℂ)
    {Q : ℕ → ℝ} (hQ : ∀ m, 0 < Q m) (hQs : Summable (fun m => (Q m)⁻¹)) :
    ∃ (Ψ : E → EReal) (κ : ℝ),
      0 < κ ∧ ExceptionalCone.LogHomogeneous Ψ κ ∧
      (∃ c : E, Ψ c ≠ ⊥) ∧ (∀ c : E, Ψ c ≠ ⊤) ∧ Ψ 0 = ⊥ ∧
      (∀ c : E, ∀ α : ℂ, Ψ c = ⊥ → Ψ (α • c) = ⊥) ∧
      (∀ B : ℝ, 1 < B → ∃ (C : ℝ) (D : E → ℝ≥0∞),
        PlurisuperharmonicOn D (ball (0 : E) B) ∧
        ∀ c ∈ ball (0 : E) B, Ψ c = (C : EReal) - (D c : EReal)) ∧
      (∀ c : E, Ψ c ≠ ⊥ → ∀ dir : Ω, ∀ K : Set ℂ, IsCompact K →
        Tendsto (fun m => (Q m)⁻¹ * ∫ z in K,
          |logProjection (fun w => F (window (A dir m) (b dir m) w)) c z|)
          atTop (𝓝 0)) := by
  obtain ⟨hk, hhom, hgood, hcone, hlocal⟩ := constructed_window_potential hF hFn ha hn A b hQ hQs
  refine ⟨potential F A b Q, ∑' j, windowMass Q (enumerate Ω j), hk, hhom,
    hgood, fun c => seriesPotential_ne_top _ c, ?_, hcone, hlocal, ?_⟩
  · simp [potential, seriesPotential]
  · intro c hc dir K hK
    exact compact_loss_outside_pole hF hFn ha hn A b hQ hQs hc dir hK

end Construction

#print axioms weighted_loss_outside_pole
#print axioms compact_loss_outside_pole
#print axioms actual_window_exceptional_potential
end V10.ProjectionExceptionalCone
