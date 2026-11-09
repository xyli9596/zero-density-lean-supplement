module
public import Ray.Hartogs.Subharmonic
public import Ray.Hartogs.MaxLog
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import all Ray.Hartogs.Subharmonic
import Mathlib.Tactic

/-!
# Nonvanishing analytic vector log norms and their compact uniform limits

Ray's subharmonic predicate is real-valued and continuous. For a nowhere-zero
analytic vector function, the genuine log norm fits that predicate: locally
it equals a suitable truncated log norm. Compact uniform limits then retain
the circle submean inequality and continuity. No totalized log-at-zero,
scalar zero-set argument, or extended-real L1 compactness is used.
-/

public section
noncomputable section
open Set Filter MeasureTheory
open Metric (closedBall ball)
open scoped Topology
namespace V10.SubharmonicLimit

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
  [SecondCountableTopology H]

/-- The actual log norm of a nowhere-zero analytic vector function is
subharmonic. The proof uses a locally inactive truncation. -/
theorem analytic_logNorm_subharmonic {f : ℂ → H} {s : Set ℂ}
    (hf : AnalyticOnNhd ℂ f s) (hne : ∀ z ∈ s, f z ≠ 0) :
    SubharmonicOn (fun z => Real.log ‖f z‖) s := by
  refine ⟨hf.continuousOn.norm.log (fun z hz => norm_ne_zero_iff.mpr (hne z hz)), ?_⟩
  intro c hc
  have hcs : c ∈ s := interior_subset hc
  have hpos : 0 < ‖f c‖ / 2 := half_pos (norm_pos_iff.mpr (hne c hcs))
  let b := Real.log (‖f c‖ / 2)
  have hb : Real.exp b = ‖f c‖ / 2 := Real.exp_log hpos
  have hnear : ∀ᶠ z in 𝓝 c, ‖f c‖ / 2 < ‖f z‖ :=
    (hf c hcs).continuousAt.norm.eventually_const_lt (by linarith [hpos])
  obtain ⟨d, hd, hdb⟩ := Metric.eventually_nhds_iff.mp hnear
  obtain ⟨r, hr, hmean⟩ := (hf.maxLog_norm_subharmonicOn b).submean' c hc
  refine ⟨min r d, lt_min hr hd, ?_⟩
  intro t ht htr
  have hcEq : maxLog b ‖f c‖ = Real.log ‖f c‖ :=
    maxLog_eq_log (by rw [hb]; linarith [hpos])
  have hcircle : ∀ u : ℝ, maxLog b ‖f (circleMap c t u)‖ = Real.log ‖f (circleMap c t u)‖ := by
    intro u
    apply maxLog_eq_log
    rw [hb]
    apply (hdb ?_).le
    simpa only [dist_eq_norm, circleMap_sub_center, norm_circleMap_zero, abs_of_pos ht] using
      lt_of_lt_of_le htr (min_le_right r d)
  have hh := hmean t ht (lt_of_lt_of_le htr (min_le_left r d))
  simpa only [hcEq, hcircle] using hh

/-- Positive normalization preserves actual nonvanishing vector lognorm
subharmonicity; no truncation remains in the conclusion. -/
theorem analytic_normalized_logNorm_subharmonic {f : ℂ → H} {s : Set ℂ} {q : ℝ}
    (hq : 0 < q) (hf : AnalyticOnNhd ℂ f s) (hne : ∀ z ∈ s, f z ≠ 0) :
    SubharmonicOn (fun z => Real.log ‖f z‖ / q) s := by
  simpa only [div_eq_mul_inv, mul_comm] using
    (analytic_logNorm_subharmonic hf hne).const_mul (inv_nonneg.mpr hq.le)

section Limits
variable {α : Type*} {l : Filter α} [NeBot l] [l.IsCountablyGenerated]
  {F : α → ℂ → ℝ} {g : ℂ → ℝ} {s : Set ℂ}

/-- Locally uniform convergence of real continuous subharmonic functions
preserves subharmonicity, including its continuity requirement. Eventual
subharmonicity suffices. Countably generated filters include real atTop. -/
theorem subharmonic_of_compact_uniform_limit (hs : IsOpen s)
    (hF : ∀ᶠ n in l, SubharmonicOn (F n) s)
    (hlim : ∀ K, K ⊆ s → IsCompact K → TendstoUniformlyOn F g l K) :
    SubharmonicOn g s := by
  have hlocal := (tendstoLocallyUniformlyOn_iff_forall_isCompact hs).mpr hlim
  have gc : ContinuousOn g s := hlocal.continuousOn
    (hF.mono (fun _ hf => hf.cont)).frequently
  rw [subharmonicOn_iff_submean gc]
  intro c r hr hball
  have hct : ∀ t : ℝ, circleMap c r t ∈ closedBall c r :=
    fun t => circleMap_mem_closedBall c hr.le t
  have hpoint : ∀ z ∈ closedBall c r, Tendsto (fun n => F n z) l (𝓝 (g z)) :=
    fun z hz => (hlim _ hball (isCompact_closedBall c r)).tendsto_at hz
  have hclose : ∀ᶠ n in l, ∀ z ∈ closedBall c r, dist (g z) (F n z) < 1 :=
    (Metric.tendstoUniformlyOn_iff.mp (hlim _ hball (isCompact_closedBall c r))) 1 zero_lt_one
  have havg : Tendsto (fun n => ⨍ t in itau, F n (circleMap c r t)) l
      (𝓝 (⨍ t in itau, g (circleMap c r t))) := by
    simp_rw [average_eq]
    apply Filter.Tendsto.const_smul
    apply tendsto_integral_filter_of_dominated_convergence
      (fun t => 1 + |g (circleMap c r t)|)
    · apply hF.mono
      intro n hn
      exact ((hn.cont.mono hball).comp_continuous (continuous_circleMap c r) hct).aestronglyMeasurable
    · apply hclose.mono
      intro n hn
      apply ae_of_all
      intro t
      have hd := (hn _ (hct t)).le
      calc
        ‖F n (circleMap c r t)‖ ≤ ‖g (circleMap c r t)‖ +
            ‖g (circleMap c r t) - F n (circleMap c r t)‖ := norm_le_insert _ _
        _ ≤ ‖g (circleMap c r t)‖ + 1 :=
          add_le_add le_rfl (by simpa only [dist_eq_norm] using hd)
        _ = 1 + |g (circleMap c r t)| := by rw [Real.norm_eq_abs]; ring
    · exact (continuousOn_const.add (gc.mono hball).abs).integrableOn_sphere hr
    · exact ae_of_all _ fun t => hpoint _ (hct t)
  exact le_of_tendsto_of_tendsto (hpoint c (Metric.mem_closedBall_self hr.le)) havg
    (hF.mono fun _ hn => (hn.mono hball).submean hr)

end Limits

/-- Actual nonzero analytic vector normalized log norms converging uniformly
on every compact subset have a continuous subharmonic limit. This is the
vector half of the manuscript limit argument; scalar zeros require more. -/
theorem normalized_logNorm_limit_subharmonic {α : Type*} {l : Filter α}
    [NeBot l] [l.IsCountablyGenerated] {F : α → ℂ → H} {q : α → ℝ}
    {g : ℂ → ℝ} {s : Set ℂ} (hs : IsOpen s)
    (hgood : ∀ᶠ n in l, 0 < q n ∧ AnalyticOnNhd ℂ (F n) s ∧ ∀ z ∈ s, F n z ≠ 0)
    (hlim : ∀ K, K ⊆ s → IsCompact K →
      TendstoUniformlyOn (fun n z => Real.log ‖F n z‖ / q n) g l K) :
    SubharmonicOn g s :=
  subharmonic_of_compact_uniform_limit hs
    (hgood.mono fun _ hn => analytic_normalized_logNorm_subharmonic hn.1 hn.2.1 hn.2.2) hlim

#print axioms analytic_logNorm_subharmonic
#print axioms subharmonic_of_compact_uniform_limit
#print axioms normalized_logNorm_limit_subharmonic
end V10.SubharmonicLimit
