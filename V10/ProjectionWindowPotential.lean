import V10.ProjectionWindowTransport
import V10.ProjectionWindowWeights

/-! A single genuine extended logarithmically homogeneous potential for all
finite-direction real-affine windows, scales, and compact cutoff sizes. -/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
namespace V10.ProjectionWindowPotential
open ProjectionWindowWeights ProjectionWindowTransport HolomorphicProjectionAverage
open LogHomogeneousSeries PluriPotentialSeries
set_option backward.isDefEq.respectTransparency false

variable {Ω E : Type*} [Fintype Ω] [Nonempty Ω]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

def windowCutoff (A : Ω → ℕ → ℂ ≃L[ℝ] ℂ) (b : Ω → ℕ → ℂ)
    (Q : ℕ → ℝ) (i : WindowIndex Ω) : ℂ → ℝ :=
  transportedWeight (A i.1 i.2.2) (b i.1 i.2.2)
    (fun z => windowWeight Q i * cutoff i.2.1 z)

def windowSummand (F : ℂ → E →L[ℂ] ℂ) (A : Ω → ℕ → ℂ ≃L[ℝ] ℂ)
    (b : Ω → ℕ → ℂ) (Q : ℕ → ℝ) (i : WindowIndex Ω) : E → ℝ :=
  averagedLogProjection F (windowCutoff A b Q i)

def potential (F : ℂ → E →L[ℂ] ℂ) (A : Ω → ℕ → ℂ ≃L[ℝ] ℂ)
    (b : Ω → ℕ → ℂ) (Q : ℕ → ℝ) : E → EReal :=
  seriesPotential (fun j => windowSummand F A b Q (enumerate Ω j))

omit [Fintype Ω] [Nonempty Ω] in
theorem windowCutoff_continuous (A : Ω → ℕ → ℂ ≃L[ℝ] ℂ) (b : Ω → ℕ → ℂ)
    (Q : ℕ → ℝ) (i : WindowIndex Ω) : Continuous (windowCutoff A b Q i) :=
  transportedWeight_continuous _ _ ((cutoff_smooth _).continuous.const_mul _)

omit [Fintype Ω] [Nonempty Ω] in
theorem windowCutoff_compact (A : Ω → ℕ → ℂ ≃L[ℝ] ℂ) (b : Ω → ℕ → ℂ)
    (Q : ℕ → ℝ) (i : WindowIndex Ω) : HasCompactSupport (windowCutoff A b Q i) :=
  transportedWeight_compact _ _ (cutoff_compact _).mul_left

omit [Fintype Ω] [Nonempty Ω] in
theorem windowCutoff_nonneg (A : Ω → ℕ → ℂ ≃L[ℝ] ℂ) (b : Ω → ℕ → ℂ)
    {Q : ℕ → ℝ} (hQ : ∀ m, 0 < Q m) (i : WindowIndex Ω) :
    ∀ z, 0 ≤ windowCutoff A b Q i z :=
  transportedWeight_nonneg _ _ fun z =>
    mul_nonneg (windowWeight_pos hQ i).le (cutoff_nonneg _ z)

omit [Fintype Ω] [Nonempty Ω] in
theorem windowCutoff_mass (A : Ω → ℕ → ℂ ≃L[ℝ] ℂ) (b : Ω → ℕ → ℂ)
    (Q : ℕ → ℝ) (i : WindowIndex Ω) :
    (∫ z, windowCutoff A b Q i z) = windowMass Q i := by
  rw [windowCutoff, transportedWeight_mass _ _
    (((cutoff_smooth _).continuous.const_mul _).measurable), integral_const_mul]
  rfl

omit [Fintype Ω] [Nonempty Ω] in
/-- Exact equality with the signed averages in the manuscript, including
both the cutoff factor and the reciprocal scale. -/
theorem windowSummand_eq {F : ℂ → E →L[ℂ] ℂ} (hF : Continuous F)
    (A : Ω → ℕ → ℂ ≃L[ℝ] ℂ) (b : Ω → ℕ → ℂ) (Q : ℕ → ℝ)
    (i : WindowIndex Ω) (c : E) :
    windowSummand F A b Q i c = cutoffWeight i.2.1 * ((Q i.2.2)⁻¹ *
      averagedLogProjection
        (fun z => F (ProjectionAffineWindow.window (A i.1 i.2.2) (b i.1 i.2.2) z))
        (cutoff i.2.1) c) := by
  rw [windowSummand, windowCutoff, averagedLogProjection_transport hF _ _
    (((cutoff_smooth _).continuous.const_mul _).measurable), averagedLogProjection_const_mul]
  simp only [windowWeight, div_eq_mul_inv, mul_assoc]

section Construction
variable [InnerProductSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The actual common potential has positive logarithmic degree and genuine
local plurisuperharmonic deficit representations. All real-affine changes,
cutoffs, mass summability, and Gaussian finiteness are proved internally. -/
theorem constructed_window_potential {F : ℂ → E →L[ℂ] ℂ}
    (hF : Continuous F) (hFn : ∀ z, F z ≠ 0)
    (ha : ∀ c : E, c ≠ 0 → AnalyticOnNhd ℂ (fun z => F z c) univ)
    (hn : ∀ c : E, c ≠ 0 → ∃ z, F z c ≠ 0)
    (A : Ω → ℕ → ℂ ≃L[ℝ] ℂ) (b : Ω → ℕ → ℂ)
    {Q : ℕ → ℝ} (hQ : ∀ m, 0 < Q m) (hQs : Summable (fun m => (Q m)⁻¹)) :
    let κ : ℝ := ∑' j, windowMass Q (enumerate Ω j)
    0 < κ ∧
    ExceptionalCone.LogHomogeneous (potential F A b Q) κ ∧
    (∃ c : E, potential F A b Q c ≠ ⊥) ∧
    (∀ c : E, ∀ α : ℂ, potential F A b Q c = ⊥ → potential F A b Q (α • c) = ⊥) ∧
    (∀ B : ℝ, 1 < B → ∃ (C : ℝ) (D : E → ℝ≥0∞),
      PlurisuperharmonicOn D (ball (0 : E) B) ∧
      ∀ c ∈ ball (0 : E) B, potential F A b Q c = (C : EReal) - (D c : EReal)) := by
  have hsum : Summable (fun j => ∫ z, windowCutoff A b Q (enumerate Ω j) z) := by
    simp only [windowCutoff_mass]
    exact summable_enumerated_mass hQ hQs
  have h := HolomorphicProjectionSeries.constructed_potential
    (F := fun _ : ℕ => F) (φ := fun j => windowCutoff A b Q (enumerate Ω j))
    (fun _ => hF) (fun _ => hFn) (fun _ => ha) (fun _ => hn)
    (fun j => windowCutoff_continuous A b Q (enumerate Ω j))
    (fun j => windowCutoff_compact A b Q (enumerate Ω j))
    (fun j => windowCutoff_nonneg A b hQ (enumerate Ω j))
    (fun j => by rw [windowCutoff_mass]; exact windowMass_pos hQ _) hsum
  simpa only [windowCutoff_mass, potential, windowSummand] using h

end Construction

#print axioms windowSummand_eq
#print axioms constructed_window_potential
end V10.ProjectionWindowPotential
