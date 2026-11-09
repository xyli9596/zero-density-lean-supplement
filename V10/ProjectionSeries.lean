import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

/-!
# The measure-theoretic summation step in v10 Lemma 4.3

This module proves the Tonelli / almost-everywhere summability mechanism
for nonnegative measurable losses. In particular, an integral bound
uniform in `m`, combined with summable reciprocal normalizations, gives
almost-everywhere summability and convergence to zero. Countably many
families can share one exceptional null set.

These results do **not** prove the full pluripolar projection lemma:
the holomorphic logarithmic losses, their Gaussian integral bound,
plurisubharmonicity of the potential, and complete pluripolarity must
still be constructed and verified separately. Integral estimates below
are explicit hypotheses, not conclusions about the manuscript's row.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace V10.ProjectionSeries

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Tonelli bounds the integral of the complete weighted loss series.
No probability, finite-measure, or sigma-finiteness assumption is needed. -/
theorem lintegral_weighted_tsum_le
    (loss : ℕ → α → ℝ≥0∞) (weight : ℕ → ℝ≥0∞) (C : ℝ≥0∞)
    (hmeas : ∀ m, AEMeasurable (loss m) μ)
    (hbound : ∀ m, ∫⁻ c, loss m c ∂μ ≤ C) :
    ∫⁻ c, ∑' m, weight m * loss m c ∂μ ≤ (∑' m, weight m) * C := by
  rw [lintegral_tsum (fun m => (hmeas m).const_mul (weight m))]
  calc
    (∑' m, ∫⁻ c, weight m * loss m c ∂μ) =
        ∑' m, weight m * ∫⁻ c, loss m c ∂μ := by
          congr 1
          funext m
          exact lintegral_const_mul'' (weight m) (hmeas m)
    _ ≤ ∑' m, weight m * C :=
      ENNReal.tsum_le_tsum fun m => by gcongr; exact hbound m
    _ = (∑' m, weight m) * C := ENNReal.tsum_mul_right

/-- A finite total integral makes the weighted loss series finite almost
    everywhere. ENNReal is used so that no value at a logarithmic pole is
    silently replaced by a finite real number. -/
theorem ae_weighted_tsum_ne_top
    (loss : ℕ → α → ℝ≥0∞) (weight : ℕ → ℝ≥0∞) (C : ℝ≥0∞)
    (hmeas : ∀ m, AEMeasurable (loss m) μ)
    (hbound : ∀ m, ∫⁻ c, loss m c ∂μ ≤ C)
    (hweight : (∑' m, weight m) ≠ ∞) (hC : C ≠ ∞) :
    ∀ᵐ c ∂μ, (∑' m, weight m * loss m c) ≠ ∞ := by
  have hfinite : (∫⁻ c, ∑' m, weight m * loss m c ∂μ) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hweight hC)
      (lintegral_weighted_tsum_le loss weight C hmeas hbound)
  exact (ae_lt_top' (AEMeasurable.tsum fun m =>
    (hmeas m).const_mul (weight m)) hfinite).mono fun _ hc => hc.ne

/-- The same almost-everywhere set gives a summable finite-valued sequence
    and convergence of the original extended-valued losses to zero. -/
theorem ae_weighted_summable_and_tendsto
    (loss : ℕ → α → ℝ≥0∞) (weight : ℕ → ℝ≥0∞) (C : ℝ≥0∞)
    (hmeas : ∀ m, AEMeasurable (loss m) μ)
    (hbound : ∀ m, ∫⁻ c, loss m c ∂μ ≤ C)
    (hweight : (∑' m, weight m) ≠ ∞) (hC : C ≠ ∞) :
    ∀ᵐ c ∂μ,
      (∀ m, weight m * loss m c ≠ ∞) ∧
      Summable (fun m => (weight m * loss m c).toNNReal) ∧
      Tendsto (fun m => weight m * loss m c) atTop (𝓝 0) := by
  filter_upwards [ae_weighted_tsum_ne_top loss weight C hmeas hbound hweight hC]
    with c hc
  exact ⟨ENNReal.ne_top_of_tsum_ne_top hc,
    ENNReal.summable_toNNReal_of_tsum_ne_top hc,
    ENNReal.tendsto_atTop_zero_of_tsum_ne_top hc⟩

/-- Countable families (in particular finitely many directions times
countably many rectangles) satisfy the conclusions simultaneously. -/
theorem ae_all_weighted_tsum_ne_top
    {ι : Type*} [Countable ι]
    (loss : ι → ℕ → α → ℝ≥0∞) (weight : ℕ → ℝ≥0∞) (C : ι → ℝ≥0∞)
    (hmeas : ∀ i m, AEMeasurable (loss i m) μ)
    (hbound : ∀ i m, ∫⁻ c, loss i m c ∂μ ≤ C i)
    (hweight : (∑' m, weight m) ≠ ∞) (hC : ∀ i, C i ≠ ∞) :
    ∀ᵐ c ∂μ, ∀ i, (∑' m, weight m * loss i m c) ≠ ∞ := by
  exact ae_all_iff.mpr fun i =>
    ae_weighted_tsum_ne_top (loss i) weight (C i) (hmeas i) (hbound i) hweight (hC i)

/-- The manuscript-shaped interface: `Q m > 0`, reciprocal normalizations
summable, and a uniform integral bound imply summability of `loss / Q`
and convergence to zero, outside one null set. -/
theorem ae_normalized_loss_summable_and_tendsto
    (loss : ℕ → α → ℝ≥0) (Q : ℕ → ℝ≥0) (C : ℝ≥0)
    (hQ : ∀ m, 0 < Q m)
    (hreciprocal : Summable (fun m => (Q m)⁻¹))
    (hmeas : ∀ m, AEMeasurable (loss m) μ)
    (hbound : ∀ m, ∫⁻ c, (loss m c : ℝ≥0∞) ∂μ ≤ C) :
    ∀ᵐ c ∂μ, Summable (fun m => loss m c / Q m) ∧
      Tendsto (fun m => loss m c / Q m) atTop (𝓝 0) := by
  have hweight : (∑' m, (Q m : ℝ≥0∞)⁻¹) ≠ ∞ := by
    simp_rw [← ENNReal.coe_inv (ne_of_gt (hQ _))]
    exact ENNReal.tsum_coe_ne_top_iff_summable.mpr hreciprocal
  filter_upwards [ae_weighted_tsum_ne_top
    (fun m c => (loss m c : ℝ≥0∞)) (fun m => (Q m : ℝ≥0∞)⁻¹) C
    (fun m => (hmeas m).coe_nnreal_ennreal) hbound hweight ENNReal.coe_ne_top]
    with c hc
  have hfinite : (∑' m, ((loss m c / Q m : ℝ≥0) : ℝ≥0∞)) ≠ ∞ := by
    convert hc using 1
    congr 1
    funext m
    rw [ENNReal.coe_div (ne_of_gt (hQ m)), div_eq_mul_inv, mul_comm]
  have hs : Summable (fun m => loss m c / Q m) :=
    ENNReal.tsum_coe_ne_top_iff_summable.mp hfinite
  refine ⟨hs, ?_⟩
  simpa only [Nat.cofinite_eq_atTop] using NNReal.tendsto_cofinite_zero_of_summable hs

/-- The exceptional set is defined by divergence in at least one of the
countably many families. This is only a null set, not yet a pluripolar set. -/
def divergenceSet {ι : Type*}
    (loss : ι → ℕ → α → ℝ≥0∞) (weight : ℕ → ℝ≥0∞) : Set α :=
  {c | ∃ i, (∑' m, weight m * loss i m c) = ∞}

theorem measure_divergenceSet_eq_zero
    {ι : Type*} [Countable ι]
    (loss : ι → ℕ → α → ℝ≥0∞) (weight : ℕ → ℝ≥0∞) (C : ι → ℝ≥0∞)
    (hmeas : ∀ i m, AEMeasurable (loss i m) μ)
    (hbound : ∀ i m, ∫⁻ c, loss i m c ∂μ ≤ C i)
    (hweight : (∑' m, weight m) ≠ ∞) (hC : ∀ i, C i ≠ ∞) :
    μ (divergenceSet loss weight) = 0 := by
  have h := ae_all_weighted_tsum_ne_top loss weight C hmeas hbound hweight hC
  simpa only [ae_iff, not_forall, not_not, divergenceSet] using h

omit [MeasurableSpace α] in
/-- A countable family has finite values and convergence on the complement
of the single explicitly defined null set. -/
theorem tendsto_outside_divergenceSet
    {ι : Type*} (loss : ι → ℕ → α → ℝ≥0∞) (weight : ℕ → ℝ≥0∞)
    {c : α} (hc : c ∉ divergenceSet loss weight) (i : ι) :
    Tendsto (fun m => weight m * loss i m c) atTop (𝓝 0) := by
  apply ENNReal.tendsto_atTop_zero_of_tsum_ne_top
  intro hi
  exact hc ⟨i, hi⟩

/-- A summable additive error preserves summability. This is the interface
needed after bounding the change of an absolute logarithmic loss under
scaling by `|log |λ|| / Q m`. -/
theorem summable_of_summable_add_error
    {u v error : ℕ → ℝ≥0}
    (hcontrol : ∀ m, v m ≤ u m + error m)
    (hu : Summable u) (herror : Summable error) : Summable v :=
  NNReal.summable_of_le hcontrol (hu.add herror)

/-- Under a group action and a summable error for each group element,
loss summability is invariant. For complex scaling the group can be
`ℂˣ`, avoiding any assertion about scaling by zero. -/
theorem summable_smul_iff
    {G X : Type*} [Group G] [MulAction G X]
    (loss : ℕ → X → ℝ≥0) (error : G → ℕ → ℝ≥0)
    (herror : ∀ g, Summable (error g))
    (hcontrol : ∀ g m c, loss m (g • c) ≤ loss m c + error g m)
    (g : G) (c : X) :
    Summable (fun m => loss m (g • c)) ↔ Summable (fun m => loss m c) := by
  constructor
  · intro h
    have hinv := summable_of_summable_add_error
      (fun m => hcontrol g⁻¹ m (g • c)) h (herror g⁻¹)
    simpa only [inv_smul_smul] using hinv
  · intro h
    exact summable_of_summable_add_error (fun m => hcontrol g m c) h (herror g)

/-- The union of divergence sets is invariant under nonzero scaling once
the preceding summable-error hypothesis has been checked. This geometric
conclusion alone does not give plurisubharmonicity or pluripolarity. -/
theorem divergent_family_smul_iff
    {G X ι : Type*} [Group G] [MulAction G X]
    (loss : ι → ℕ → X → ℝ≥0) (error : G → ι → ℕ → ℝ≥0)
    (herror : ∀ g i, Summable (error g i))
    (hcontrol : ∀ g i m c, loss i m (g • c) ≤ loss i m c + error g i m)
    (g : G) (c : X) :
    (∃ i, ¬Summable (fun m => loss i m (g • c))) ↔
      (∃ i, ¬Summable (fun m => loss i m c)) := by
  apply exists_congr
  intro i
  exact not_congr (summable_smul_iff (loss i) (fun g => error g i)
    (fun g => herror g i) (fun g m c => hcontrol g i m c) g c)

/-- A uniform logarithmic shift changes its weighted absolute value by
at most the same weight times the absolute shift. This elementary step
is stated for finite real potentials; logarithmic poles require a separate
domain or extended-valued treatment. -/
theorem weighted_absolute_shift_le (u b : ℝ) (w : ℝ≥0) :
    ‖u + b‖₊ * w ≤ ‖u‖₊ * w + ‖b‖₊ * w := by
  calc
    ‖u + b‖₊ * w ≤ (‖u‖₊ + ‖b‖₊) * w := by
      gcongr
      exact nnnorm_add_le u b
    _ = ‖u‖₊ * w + ‖b‖₊ * w := add_mul _ _ _

/-- Finite logarithmic averages with an additive scaling law give an
invariant summability condition for their weighted absolute values.
For the manuscript this applies on the punctured parameter space, after
local integrability and the actual scaling law have been established.
It makes no assertion about a real logarithm at zero. -/
theorem summable_weighted_absolute_smul_iff
    {G X : Type*} [Group G] [MulAction G X]
    (potential : ℕ → X → ℝ) (shift : G → ℝ) (weight : ℕ → ℝ≥0)
    (hweight : Summable weight)
    (hshift : ∀ g m c, potential m (g • c) = potential m c + shift g)
    (g : G) (c : X) :
    Summable (fun m => ‖potential m (g • c)‖₊ * weight m) ↔
      Summable (fun m => ‖potential m c‖₊ * weight m) := by
  apply summable_smul_iff
    (fun m c => ‖potential m c‖₊ * weight m)
    (fun g m => ‖shift g‖₊ * weight m)
  · intro g
    exact hweight.mul_left ‖shift g‖₊
  · intro g m c
    rw [hshift g m c]
    exact weighted_absolute_shift_le _ _ _

/-- The finite-direction, countable-rectangle setting is an instance of
this countable family theorem; the family constants need not be bounded
uniformly in the rectangle. -/
theorem ae_all_normalized_loss_summable_and_tendsto
    {ι : Type*} [Countable ι]
    (loss : ι → ℕ → α → ℝ≥0) (Q : ℕ → ℝ≥0) (C : ι → ℝ≥0)
    (hQ : ∀ m, 0 < Q m)
    (hreciprocal : Summable (fun m => (Q m)⁻¹))
    (hmeas : ∀ i m, AEMeasurable (loss i m) μ)
    (hbound : ∀ i m, ∫⁻ c, (loss i m c : ℝ≥0∞) ∂μ ≤ C i) :
    ∀ᵐ c ∂μ, ∀ i,
      Summable (fun m => loss i m c / Q m) ∧
      Tendsto (fun m => loss i m c / Q m) atTop (𝓝 0) := by
  exact ae_all_iff.mpr fun i => ae_normalized_loss_summable_and_tendsto
    (loss i) Q (C i) hQ hreciprocal (hmeas i) (hbound i)

#print axioms ae_normalized_loss_summable_and_tendsto
#print axioms measure_divergenceSet_eq_zero
#print axioms summable_weighted_absolute_smul_iff

end V10.ProjectionSeries
