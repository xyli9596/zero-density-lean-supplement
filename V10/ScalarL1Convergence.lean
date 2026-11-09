import ZeroDensity.L1TestPairing
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Tactic

/-!+# Closure and full-family steps for the scalar L¹ argument

These are the measure-theoretic closing steps, with their compactness and
identification inputs explicitly stated. They are not a substitute for deriving
those inputs from the actual analytic differential equation.
-/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace V10.ScalarL1Convergence
set_option backward.isDefEq.respectTransparency false

/-- Order is closed under genuine L¹ convergence, with only almost-everywhere
comparison of the approximants. In particular scalar zeros cause no exception. -/
theorem ae_le_of_L1_limits {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} {l : Filter ι} [l.NeBot]
    {u v : ι → α → ℝ} {U V : α → ℝ}
    (hu : ∀ i, Integrable (u i) μ) (hv : ∀ i, Integrable (v i) μ)
    (hU : Integrable U μ) (hV : Integrable V μ)
    (hle : ∀ᶠ i in l, ∀ᵐ z ∂μ, u i z ≤ v i z)
    (hlimu : Tendsto (fun i => ∫ z, ‖u i z - U z‖ ∂μ) l (𝓝 0))
    (hlimv : Tendsto (fun i => ∫ z, ‖v i z - V z‖ ∂μ) l (𝓝 0)) :
    ∀ᵐ z ∂μ, U z ≤ V z := by
  let g : α → ℝ := fun z => max (U z - V z) 0
  have hg : Integrable g μ := (hU.sub hV).sup (integrable_zero _ _ _)
  have herr : ∀ᶠ i in l, (∫ z, g z ∂μ) ≤
      (∫ z, ‖u i z - U z‖ ∂μ) + ∫ z, ‖v i z - V z‖ ∂μ := by
    filter_upwards [hle] with i hi
    have h1 : Integrable (fun z => ‖u i z - U z‖) μ := ((hu i).sub hU).norm
    have h2 : Integrable (fun z => ‖v i z - V z‖) μ := ((hv i).sub hV).norm
    rw [← integral_add h1 h2]
    apply integral_mono_ae hg (h1.add h2)
    filter_upwards [hi] with z hz
    change max (U z - V z) 0 ≤ ‖u i z - U z‖ + ‖v i z - V z‖
    simp only [Real.norm_eq_abs]
    apply max_le
    · have h1 := neg_le_abs (u i z - U z)
      have h2 := le_abs_self (v i z - V z)
      linarith
    · positivity
  have hlim : Tendsto (fun i => (∫ z, ‖u i z - U z‖ ∂μ) +
      ∫ z, ‖v i z - V z‖ ∂μ) l (𝓝 0) := by
    simpa only [add_zero] using hlimu.add hlimv
  have hz : ∫ z, g z ∂μ = 0 := le_antisymm (ge_of_tendsto hlim herr)
    (integral_nonneg fun _ => le_max_right _ _)
  have hgz := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun _ => le_max_right _ _) hg).mp hz
  filter_upwards [hgz] with z hz
  have h : U z - V z ≤ 0 := (le_max_left _ _).trans_eq hz
  linarith

/-- An L¹ limit lies below an eventual arbitrarily sharp upper bound.
No integrability of an intermediate vector-potential family is required. -/
theorem ae_le_of_L1_limit_of_eventual_upper {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {l : Filter ι} [l.NeBot]
    {u : ι → α → ℝ} {U H : α → ℝ}
    (hu : ∀ i, Integrable (u i) μ) (hU : Integrable U μ) (hH : Integrable H μ)
    (hlim : Tendsto (fun i => ∫ z, ‖u i z - U z‖ ∂μ) l (𝓝 0))
    (hupper : ∀ ε > 0, ∀ᶠ i in l, ∀ᵐ z ∂μ, u i z ≤ H z + ε) :
    ∀ᵐ z ∂μ, U z ≤ H z := by
  have happrox : ∀ n : ℕ, ∀ᵐ z ∂μ, U z ≤ H z + 1 / ((n : ℝ) + 1) := by
    intro n
    let ε : ℝ := 1 / ((n : ℝ) + 1)
    have hε : 0 < ε := by dsimp [ε]; positivity
    apply ae_le_of_L1_limits hu (fun _ => hH.add (integrable_const ε)) hU
      (hH.add (integrable_const ε)) (hupper ε hε) hlim
    simp
  filter_upwards [ae_all_iff.mpr happrox] with z hz
  have hlim' : Tendsto (fun n : ℕ => H z + 1 / ((n : ℝ) + 1)) atTop (𝓝 (H z)) := by
    simpa only [add_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_add (H z)
  exact ge_of_tendsto' hlim' hz

/-- The scalar/vector upper comparison passes to an L¹ scalar limit and a
uniform vector limit, including scalar zeros as null-set representatives. -/
theorem ae_le_of_L1_and_uniform_limits {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} {K : Set α} [IsFiniteMeasure (μ.restrict K)]
    {l : Filter ι} [l.NeBot] {u V : ι → α → ℝ} {U H : α → ℝ}
    (hK : MeasurableSet K) (hu : ∀ i, IntegrableOn (u i) K μ)
    (hU : IntegrableOn U K μ) (hH : IntegrableOn H K μ)
    (hlim : Tendsto (fun i => ∫ z in K, ‖u i z - U z‖ ∂μ) l (𝓝 0))
    (hV : TendstoUniformlyOn V H l K)
    (hle : ∀ᶠ i in l, ∀ᵐ z ∂μ.restrict K, u i z ≤ V i z) :
    ∀ᵐ z ∂μ.restrict K, U z ≤ H z := by
  apply ae_le_of_L1_limit_of_eventual_upper hu hU hH hlim
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hV) ε hε, hle] with i hi hi'
  filter_upwards [ae_restrict_mem hK, hi'] with z hz hle'
  have hd : |H z - V i z| < ε := by simpa only [Real.dist_eq] using hi z hz
  have := neg_le_abs (H z - V i z)
  linarith

/-- The final sequence criterion applies to arbitrary countably generated
scaling filters, including the full real parameter R → ∞. -/
theorem L1_tendsto_of_subsequence_identification {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} {l : Filter ι} [l.IsCountablyGenerated]
    {u : ι → α → ℝ} {H : α → ℝ}
    (hsub : ∀ R : ℕ → ι, Tendsto R atTop l →
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        Tendsto (fun k => ∫ z, ‖u (R (σ k)) z - H z‖ ∂μ) atTop (𝓝 0)) :
    Tendsto (fun R => ∫ z, ‖u R z - H z‖ ∂μ) l (𝓝 0) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro R hR
  obtain ⟨σ, _, hσ⟩ := hsub R hR
  exact ⟨σ, hσ⟩

/-- L¹ compactness plus identification up to null sets suffices: representatives
at zeros never need to be forced to agree pointwise. -/
theorem L1_tendsto_of_subsequence_limits_ae {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} {l : Filter ι} [l.IsCountablyGenerated]
    {u : ι → α → ℝ} {H : α → ℝ}
    (hsub : ∀ R : ℕ → ι, Tendsto R atTop l →
      ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ G : α → ℝ,
        Tendsto (fun k => ∫ z, ‖u (R (σ k)) z - G z‖ ∂μ) atTop (𝓝 0) ∧ G =ᵐ[μ] H) :
    Tendsto (fun R => ∫ z, ‖u R z - H z‖ ∂μ) l (𝓝 0) := by
  apply L1_tendsto_of_subsequence_identification
  intro R hR
  obtain ⟨σ, hσ, G, hG, heq⟩ := hsub R hR
  refine ⟨σ, hσ, ?_⟩
  have he : (fun k => ∫ z, ‖u (R (σ k)) z - G z‖ ∂μ) =
      fun k => ∫ z, ‖u (R (σ k)) z - H z‖ ∂μ := by
    funext k
    apply integral_congr_ae
    filter_upwards [heq] with z hz
    rw [hz]
  rwa [he] at hG

#print axioms ae_le_of_L1_limits
#print axioms ae_le_of_L1_limit_of_eventual_upper
#print axioms ae_le_of_L1_and_uniform_limits
#print axioms L1_tendsto_of_subsequence_identification
#print axioms L1_tendsto_of_subsequence_limits_ae
end V10.ScalarL1Convergence
