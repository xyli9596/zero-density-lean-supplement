import ZeroDensity.CountGeometry
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-!
# The shrinking-tube diagonal step in v10 Proposition 3.5

From convergence for each fixed positive tube width, this module constructs
an everywhere positive, nonincreasing width tending to zero, with the same
normalized convergence for the moving tube. The selection is proved here:
neither a preselected width nor uniform convergence is assumed.

The actual zero-count specialization uses `CountGeometry.count` and the
set `{z ∈ U | ε < Metric.infDist z Γ}`. The preceding sectorial
concentration and inverse-map distance estimates of Proposition 3.5 remain
inputs to its fixed-width hypothesis; they are not proved in this module.
-/

noncomputable section
open Filter Set Metric
open scoped Topology

namespace V10.ShrinkingTubes

/-- The last index whose threshold has been reached, capped by the natural
floor of the radius. The cap makes this finite even if thresholds are not
monotone. No regularity of the chosen thresholds is required. -/
def stage (threshold : ℕ → ℝ) (r : ℝ) : ℕ :=
  Nat.findGreatest (fun n => threshold n ≤ r) ⌊r⌋₊

lemma stage_monotone (threshold : ℕ → ℝ) : Monotone (stage threshold) := by
  intro r s hrs
  exact Nat.findGreatest_mono (fun n hn => hn.trans hrs) (Nat.floor_mono hrs)

lemma stage_tendsto (threshold : ℕ → ℝ) :
    Tendsto (stage threshold) atTop atTop := by
  apply Filter.tendsto_atTop.mpr
  intro n
  apply eventually_atTop.mpr
  refine ⟨max (threshold n) (n : ℝ), ?_⟩
  intro r hr
  exact Nat.le_findGreatest
    (Nat.le_floor ((le_max_right (threshold n) (n : ℝ)).trans hr))
    ((le_max_left (threshold n) (n : ℝ)).trans hr)

lemma threshold_stage_le (threshold : ℕ → ℝ) {r : ℝ} (hr : threshold 0 ≤ r) :
    threshold (stage threshold r) ≤ r := by
  unfold stage
  exact Nat.findGreatest_spec (P := fun n => threshold n ≤ r) (Nat.zero_le ⌊r⌋₊) hr

/-- A diagonal through a countable family of real limits can be selected
with a nondecreasing index tending to infinity. -/
theorem exists_monotone_diagonal
    (F : ℝ → ℕ → ℝ)
    (hF : ∀ n, Tendsto (fun r => F r n) atTop (𝓝 0)) :
    ∃ k : ℝ → ℕ, Monotone k ∧ Tendsto k atTop atTop ∧
      Tendsto (fun r => F r (k r)) atTop (𝓝 0) := by
  have hcut : ∀ n : ℕ, ∃ R : ℝ, ∀ r ≥ R, |F r n| ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    have he : ∀ᶠ r in atTop, |F r n| < 1 / ((n : ℝ) + 1) := by
      have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      simpa only [Real.dist_eq, sub_zero] using
        (Metric.tendsto_nhds.mp (hF n) _ hp)
    obtain ⟨R, hR⟩ := eventually_atTop.mp he
    exact ⟨R, fun r hr => (hR r hr).le⟩
  choose threshold hthreshold using hcut
  refine ⟨stage threshold, stage_monotone threshold, stage_tendsto threshold, ?_⟩
  have hsmall : Tendsto (fun r => 1 / ((stage threshold r : ℝ) + 1))
      atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp (stage_tendsto threshold)
  have hbound : ∀ᶠ r in atTop,
      |F r (stage threshold r)| ≤ 1 / ((stage threshold r : ℝ) + 1) := by
    filter_upwards [eventually_ge_atTop (threshold 0)] with r hr
    exact hthreshold (stage threshold r) r (threshold_stage_le threshold hr)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using
    squeeze_zero' (Eventually.of_forall fun r => abs_nonneg (F r (stage threshold r)))
      hbound hsmall

/-- The fixed-width hypotheses alone imply a shrinking width. Monotonicity
of `N` in its width is not needed, since the diagonal samples the fixed
widths exactly; this is stronger than the monotone-count special case. -/
theorem exists_antitone_width
    (N : ℝ → ℝ → ℝ)
    (hfixed : ∀ ε : ℝ, 0 < ε → Tendsto (fun r => N r ε) atTop (𝓝 0)) :
    ∃ ε : ℝ → ℝ, (∀ r, 0 < ε r) ∧ Antitone ε ∧
      Tendsto ε atTop (𝓝 0) ∧ Tendsto (fun r => N r (ε r)) atTop (𝓝 0) := by
  obtain ⟨k, hkmono, hktop, hkdiag⟩ := exists_monotone_diagonal
    (fun r n => N r (1 / ((n : ℝ) + 1)))
    (fun n => hfixed _ (by positivity))
  refine ⟨fun r => 1 / ((k r : ℝ) + 1), ?_, ?_, ?_, hkdiag⟩
  · intro r
    positivity
  · intro r s hrs
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
    exact hkmono hrs
  · exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hktop

/-- The part of `U` outside the open-width tube, with the strict distance
convention used in the manuscript. No measurability of this set is needed
by the finite divisor-count definition. -/
def outsideTube (U Γ : Set ℂ) (ε : ℝ) : Set ℂ :=
  {z | z ∈ U ∧ ε < Metric.infDist z Γ}

lemma outsideTube_antitone (U Γ : Set ℂ) : Antitone (outsideTube U Γ) := by
  intro ε δ hεδ z hz
  exact ⟨hz.1, hεδ.trans_lt hz.2⟩

/-- For an entire function the actual zero count is nonincreasing in tube
width, independently of the diagonal-selection argument. -/
theorem count_outsideTube_antitone {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (U Γ : Set ℂ) (r : ℝ) :
    Antitone (fun ε => ZeroDensity.CountGeometry.count f (outsideTube U Γ ε) r) := by
  intro ε δ hεδ
  exact ZeroDensity.CountGeometry.count_mono r hf (outsideTube_antitone U Γ hεδ)

/-- Actual zero-count version of the diagonal step in Proposition 3.5.
Analyticity/concentration are required to establish `hfixed` upstream;
this theorem constructs the moving width rather than assuming it. -/
theorem exists_shrinking_tube
    (f : ℂ → ℂ) (U Γ : Set ℂ) (Q : ℝ → ℝ)
    (hfixed : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun r => ZeroDensity.CountGeometry.count f (outsideTube U Γ ε) r / Q r)
        atTop (𝓝 0)) :
    ∃ ε : ℝ → ℝ, (∀ r, 0 < ε r) ∧ Antitone ε ∧ Tendsto ε atTop (𝓝 0) ∧
      Tendsto (fun r => ZeroDensity.CountGeometry.count f (outsideTube U Γ (ε r)) r / Q r)
        atTop (𝓝 0) :=
  exists_antitone_width
    (fun r ε => ZeroDensity.CountGeometry.count f (outsideTube U Γ ε) r / Q r) hfixed

/-- The same moving-tube conclusion in little-o notation, when the scale
is eventually nonzero. No positivity of the limiting zero density is used. -/
theorem exists_shrinking_tube_littleO
    (f : ℂ → ℂ) (U Γ : Set ℂ) (Q : ℝ → ℝ)
    (hQ : ∀ᶠ r in atTop, Q r ≠ 0)
    (hfixed : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun r => ZeroDensity.CountGeometry.count f (outsideTube U Γ ε) r / Q r)
        atTop (𝓝 0)) :
    ∃ ε : ℝ → ℝ, (∀ r, 0 < ε r) ∧ Antitone ε ∧ Tendsto ε atTop (𝓝 0) ∧
      (fun r => ZeroDensity.CountGeometry.count f (outsideTube U Γ (ε r)) r) =o[atTop] Q := by
  obtain ⟨ε, hpos, hanti, hzero, hcount⟩ := exists_shrinking_tube f U Γ Q hfixed
  refine ⟨ε, hpos, hanti, hzero, ?_⟩
  rw [Asymptotics.isLittleO_iff_tendsto' (hQ.mono fun r hr hz => (hr hz).elim)]
  exact hcount

#print axioms exists_monotone_diagonal
#print axioms exists_shrinking_tube
#print axioms exists_shrinking_tube_littleO

end V10.ShrinkingTubes
