module
public import Ray.Hartogs.Subharmonic
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
import all Ray.Hartogs.Subharmonic
import Mathlib.Tactic

/-!
# Nonpositive plurisubharmonic series with genuine poles

On each coefficient ball the upper constants in Lemma 4.3 can be subtracted
from the summands. Their negatives are nonnegative plurisuperharmonic
functions. This module proves closure under countable sums, including infinite
values, using the actual disk supermean inequality and monotone convergence.
Lower semicontinuity is included explicitly: Ray's auxiliary measurable
superharmonic predicate alone is not treated as the standard notion.

This is the series step, not a construction of the manuscript's holomorphic
projection summands or a proof of their Gaussian bound.
-/

public section
noncomputable section
open MeasureTheory Set Metric
open scoped Topology NNReal ENNReal

namespace V10.PluriPotentialSeries

/-- The genuine normalized disk supermean inequality for an extended
nonnegative function. Semicontinuity is imposed separately below. -/
structure SupermeanOn (f : ℂ → ℝ≥0∞) (S : Set ℂ) : Prop where
  aemeasurable : AEMeasurable f (volume.restrict S)
  supermean : ∀ (c : ℂ) (r : ℝ), 0 < r → closedBall c r ⊆ S →
    ENNReal.ofReal (Real.pi * r ^ 2)⁻¹ * ∫⁻ z in closedBall c r, f z ≤ f c

/-- The real-valued subharmonic theory supplies the actual extended-valued
supermean statement after changing the sign of a nonpositive function. -/
theorem supermean_of_nonpositive {f : ℂ → ℝ} {S : Set ℂ}
    (hf : SubharmonicOn f S) (hn : ∀ z ∈ S, f z ≤ 0) (hS : MeasurableSet S) :
    SupermeanOn (fun z => ENNReal.ofReal (-f z)) S := by
  have h := hf.neg hn hS
  exact ⟨h.AEMeasurable, h.supmean⟩

theorem superharmonic_tsum {f : ℕ → ℂ → ℝ≥0∞} {S : Set ℂ}
    (hf : ∀ n, SupermeanOn (f n) S) :
    SupermeanOn (fun z => ∑' n, f n z) S := by
  refine ⟨?_, ?_⟩
  · exact AEMeasurable.tsum fun n => (hf n).aemeasurable
  · intro c r hr hs
    have hmeas (n : ℕ) : AEMeasurable (f n) (volume.restrict (closedBall c r)) :=
      (hf n).aemeasurable.mono_measure (Measure.restrict_mono hs le_rfl)
    rw [lintegral_tsum hmeas, ← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun n => (hf n).supermean c r hr hs

theorem lowerSemicontinuousOn_tsum {X : Type*} [TopologicalSpace X]
    {f : ℕ → X → ℝ≥0∞} {S : Set X}
    (hf : ∀ n, LowerSemicontinuousOn (f n) S) :
    LowerSemicontinuousOn (fun z => ∑' n, f n z) S := by
  simp_rw [ENNReal.tsum_eq_iSup_nat]
  exact lowerSemicontinuousOn_iSup fun n =>
    lowerSemicontinuousOn_sum fun i _ => hf i

/-- Monotone convergence retains the extended supermean inequality, even
when the limit is infinite. -/
theorem supermean_iSup {f : ℕ → ℂ → ℝ≥0∞} {S : Set ℂ}
    (hf : ∀ n, SupermeanOn (f n) S) (hm : Monotone f) :
    SupermeanOn (fun z => ⨆ n, f n z) S := by
  refine ⟨AEMeasurable.iSup fun n => (hf n).aemeasurable, ?_⟩
  intro c r hr hs
  have hmeas (n : ℕ) : AEMeasurable (f n) (volume.restrict (closedBall c r)) :=
    (hf n).aemeasurable.mono_measure (Measure.restrict_mono hs le_rfl)
  rw [lintegral_iSup' hmeas (ae_of_all _ fun z n m hnm => hm hnm z), ENNReal.mul_iSup]
  exact iSup_le fun n => ((hf n).supermean c r hr hs).trans (le_iSup (fun n => f n c) n)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Standard nonnegative plurisuperharmonic data: lower semicontinuity and
the disk supermean inequality on every complex affine line. Infinity is
allowed, so the negative extended-real potential retains its actual poles. -/
structure PlurisuperharmonicOn (f : E → ℝ≥0∞) (U : Set E) : Prop where
  lowerSemicontinuousOn : LowerSemicontinuousOn f U
  onLine : ∀ a b : E, SupermeanOn (fun z : ℂ => f (a + z • b))
    {z : ℂ | a + z • b ∈ U}

/-- A nonnegative series preserves the actual line supermean inequality and
lower semicontinuity. No finite-valued limit assumption is required. -/
theorem PlurisuperharmonicOn.tsum {f : ℕ → E → ℝ≥0∞} {U : Set E}
    (hf : ∀ n, PlurisuperharmonicOn (f n) U) :
    PlurisuperharmonicOn (fun c => ∑' n, f n c) U := by
  refine ⟨lowerSemicontinuousOn_tsum fun n => (hf n).lowerSemicontinuousOn, ?_⟩
  intro a b
  exact superharmonic_tsum fun n => (hf n).onLine a b

theorem PlurisuperharmonicOn.iSup {f : ℕ → E → ℝ≥0∞} {U : Set E}
    (hf : ∀ n, PlurisuperharmonicOn (f n) U) (hm : Monotone f) :
    PlurisuperharmonicOn (fun c => ⨆ n, f n c) U := by
  refine ⟨lowerSemicontinuousOn_iSup fun n => (hf n).lowerSemicontinuousOn, ?_⟩
  intro a b
  exact supermean_iSup (fun n => (hf n).onLine a b) (fun n m hnm z => hm hnm _)

/-- Actual continuous nonpositive plurisubharmonic functions embed into the
extended theory through their negatives. -/
theorem of_nonpositive {f : E → ℝ} {U : Set E} (hU : IsOpen U)
    (hc : ContinuousOn f U)
    (hline : ∀ a b : E, SubharmonicOn (fun z : ℂ => f (a + z • b))
      {z : ℂ | a + z • b ∈ U})
    (hn : ∀ c ∈ U, f c ≤ 0) :
    PlurisuperharmonicOn (fun c => ENNReal.ofReal (-f c)) U := by
  refine ⟨(ENNReal.continuous_ofReal.comp_continuousOn hc.neg).lowerSemicontinuousOn, ?_⟩
  intro a b
  apply supermean_of_nonpositive (hline a b) (fun z hz => hn _ hz)
  exact (hU.preimage (continuous_const.add (continuous_id.smul continuous_const))).measurableSet

/-- A truncated actual complex-linear logarithm, after subtraction of its
upper bound, supplies genuine nonnegative plurisuperharmonic data. -/
theorem truncated_linear_log (F : E →L[ℂ] ℂ) {U : Set E} (hU : IsOpen U)
    {b M : ℝ} (hb : b ≤ M) (hbound : ∀ c ∈ U, ‖F c‖ ≤ Real.exp M) :
    PlurisuperharmonicOn (fun c => ENNReal.ofReal (M - maxLog b ‖F c‖)) U := by
  have hc : ContinuousOn (fun c => maxLog b ‖F c‖ - M) U :=
    ((continuous_maxLog b).comp F.continuous.norm).continuousOn.sub continuousOn_const
  have hl : ∀ a d : E, SubharmonicOn (fun z : ℂ => maxLog b ‖F (a + z • d)‖ - M)
      {z : ℂ | a + z • d ∈ U} := by
    intro a d
    have ha : AnalyticOnNhd ℂ (fun z : ℂ => F (a + z • d))
        {z : ℂ | a + z • d ∈ U} := by
      intro z hz
      simp only [map_add, map_smul, smul_eq_mul]
      fun_prop
    exact (ha.maxLog_norm_subharmonicOn b).add (HarmonicOn.const (-M)).subharmonicOn
  have h := of_nonpositive hU hc hl
    (fun c hc => sub_nonpos.mpr (maxLog_le hb (hbound c hc)))
  convert h using 1
  ext c
  congr 1
  ring

def negativePotential (f : E → ℝ≥0∞) (c : E) : EReal := -(f c : EReal)

omit [NormedSpace ℂ E] in
theorem negativePotential_upperSemicontinuous {f : E → ℝ≥0∞} {U : Set E}
    (hf : LowerSemicontinuousOn f U) :
    UpperSemicontinuousOn (negativePotential f) U := by
  apply (continuous_coe_ennreal_ereal.neg).comp_lowerSemicontinuousOn_antitone hf
  intro x y hxy
  exact EReal.neg_le_neg_iff.mpr (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hxy)

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem negativePotential_ne_top (f : E → ℝ≥0∞) (c : E) :
    negativePotential f c ≠ ⊤ := by
  simp [negativePotential]

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem negativePotential_eq_bot (f : E → ℝ≥0∞) (c : E) :
    negativePotential f c = ⊥ ↔ f c = ⊤ := by
  simp [negativePotential]

#print axioms PlurisuperharmonicOn.tsum
#print axioms PlurisuperharmonicOn.iSup
#print axioms truncated_linear_log
#print axioms negativePotential_upperSemicontinuous

end V10.PluriPotentialSeries
