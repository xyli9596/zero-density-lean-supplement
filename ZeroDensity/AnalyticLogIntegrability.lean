import ZeroDensity.PlanarLogIntegrability
import ZeroDensity.LogZeroGerm

namespace ZeroDensity.AnalyticLogIntegrability
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The actual scalar log modulus is locally integrable at every analytic point
with a nonzero analytic germ, including actual zeros of finite multiplicity. -/
theorem integrableAt_log_norm {v : ℂ → ℂ} {z₀ : ℂ}
    (hv : AnalyticAt ℂ v z₀) (hn : ¬v =ᶠ[𝓝 z₀] 0) :
    IntegrableAtFilter (fun z => Real.log ‖v z‖) (𝓝 z₀) volume := by
  obtain ⟨g, hg, hgn, hharm, hlog⟩ := LogZeroGerm.log_norm_local_factorization hv hn
  have hall := hlog.and (hg.eventually_analyticAt.and (hg.continuousAt.eventually_ne hgn))
  obtain ⟨U, hU, hUopen, hzU⟩ := eventually_nhds_iff.mp hall
  have hgc : ContinuousOn (fun z => Real.log ‖g z‖) U := by
    intro z hz
    exact ((Real.continuousAt_log (x := ‖g z‖) (norm_ne_zero_iff.mpr (hU z hz).2.2)).comp (f := fun t : ℂ => ‖g t‖)
      (hU z hz).2.1.continuousAt.norm).continuousWithinAt
  have hkernel := (PlanarLogIntegrability.locallyIntegrable_log_norm_sub z₀).smul
    (analyticOrderNatAt v z₀ : ℝ)
  have hsum : LocallyIntegrableOn
      (fun z => (analyticOrderNatAt v z₀ : ℝ) * Real.log ‖z - z₀‖ + Real.log ‖g z‖) U := by
    intro z hz
    have hi := (hkernel z).filter_mono (nhdsWithin_le_nhds (s := U))
    have hj := hgc.integrableAt_nhdsWithin (μ := volume) hUopen.measurableSet hz
    have hadd := hi.add hj
    have he : ((analyticOrderNatAt v z₀ : ℝ) • (fun z => Real.log ‖z - z₀‖)) +
        (fun z => Real.log ‖g z‖) =
        (fun z => (analyticOrderNatAt v z₀ : ℝ) * Real.log ‖z - z₀‖ + Real.log ‖g z‖) := by
      funext z
      rfl
    unfold IntegrableAtFilter at hadd ⊢
    rw [he] at hadd
    exact hadd

  have heq : (fun z => (analyticOrderNatAt v z₀ : ℝ) * Real.log ‖z - z₀‖ + Real.log ‖g z‖)
      =ᵐ[volume.restrict U] (fun z => Real.log ‖v z‖) := by
    filter_upwards [ae_restrict_mem hUopen.measurableSet,
      ae_restrict_of_ae (volume.ae_ne z₀)] with z hz hne
    exact ((hU z hz).1 hne).symm
  have hi := (hsum.congr heq) z₀ hzU
  simpa only [nhdsWithin_eq_nhds.mpr (hUopen.mem_nhds hzU)] using hi

/-- This applies on the actual analytic phase domain; entire analyticity is not
required. Nonzero germ is an explicit local condition, not a logarithmic bound. -/
theorem locallyIntegrableOn_log_norm {v : ℂ → ℂ} {U : Set ℂ}
    (hv : AnalyticOnNhd ℂ v U) (hn : ∀ z ∈ U, ¬v =ᶠ[𝓝 z] 0) :
    LocallyIntegrableOn (fun z => Real.log ‖v z‖) U := by
  intro z hz
  exact (integrableAt_log_norm (hv z hz) (hn z hz)).filter_mono nhdsWithin_le_nhds

#print axioms integrableAt_log_norm
#print axioms locallyIntegrableOn_log_norm
end
end ZeroDensity.AnalyticLogIntegrability
