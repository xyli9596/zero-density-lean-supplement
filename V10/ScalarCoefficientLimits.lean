import V10.ScalarCompanionODE
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Tactic

/-! The manuscript's finitely many coefficient limits imply the actual
companion-operator limit, uniformly on each compact angular interval. -/

noncomputable section
open Set Filter
open scoped Topology
namespace V10.ScalarCoefficientLimits

theorem uniform_const_limit_pi {ι α κ : Type*} [Fintype κ]
    {l : Filter ι} {K : Set α} {f : ι → α → κ → ℂ} {c : κ → ℂ}
    (h : ∀ j, TendstoUniformlyOn (fun i x => f i x j) (fun _ => c j) l K) :
    TendstoUniformlyOn f (fun _ => c) l K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hh : ∀ᶠ i in l, ∀ j, ∀ x ∈ K, dist (c j) (f i x j) < ε :=
    eventually_all.mpr (fun j => (Metric.tendstoUniformlyOn_iff.mp (h j)) ε hε)
  filter_upwards [hh] with i hi x hx
  exact (dist_pi_lt_iff hε).mpr (fun j => hi j x hx)

theorem continuous_comp_uniform_const_limit {ι α E F : Type*}
    [PseudoMetricSpace E] [PseudoMetricSpace F]
    {l : Filter ι} {K : Set α} {f : ι → α → E} {c : E} {g : E → F}
    (hg : ContinuousAt g c) (hf : TendstoUniformlyOn f (fun _ => c) l K) :
    TendstoUniformlyOn (fun i x => g (f i x)) (fun _ => g c) l K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hmap⟩ := Metric.continuousAt_iff.mp hg ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hf) δ hδ] with i hi x hx
  have hd : dist (f i x) c < δ := by simpa only [dist_comm] using hi x hx
  simpa only [dist_comm] using hmap hd

theorem companion_uniform_limit {n : ℕ} {b : ℂ → Fin (n + 1) → ℂ}
    {c : Fin (n + 1) → ℂ} {K : Set ℝ}
    (h : ∀ j, TendstoUniformlyOn
      (fun r : ℝ => fun θ : ℝ => b ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) j)
      (fun _ => c j) atTop K) :
    TendstoUniformlyOn
      (fun r : ℝ => fun θ : ℝ => CompanionObservation.companion
        (b ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))))
      (fun _ => CompanionObservation.companion c) atTop K :=
  continuous_comp_uniform_const_limit ScalarCompanionODE.companion_continuous.continuousAt
    (uniform_const_limit_pi h)

#print axioms companion_uniform_limit
end V10.ScalarCoefficientLimits
