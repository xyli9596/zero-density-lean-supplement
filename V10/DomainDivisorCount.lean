import V10.RadialTransfer

/-!
# Radial transfer without phase analyticity at the inner boundary

The divisor is taken on the open analytic phase domain U and then filtered
by the truncated sector. Neither v nor G is required to extend across the
inner boundary. Finite support follows instead from actual multiplicity
transport, injectivity of χ, and the compact image of the closed carrier.
-/

namespace V10.DomainDivisorCount
open Set Filter Metric MeromorphicOn
open ZeroDensity.CountGeometry ZeroDensity.SectorDivisorCount
open V10.RadialTransfer V10.RadialCutoffGeometry
open scoped Topology
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

/-- The phase divisor is evaluated on its analytic domain, not on a carrier
whose inner boundary may fail to be a domain of analyticity for v. -/
def domainPhaseCount (v : ℂ → ℂ) (U : Set ℂ) (S a b R : ℝ) : ℝ :=
  regionCount v U (clippedSector S R a b)

/-- Actual multiplicity transport requires no analyticity of the target
factor on the target carrier boundary: only its germ at each counted point. -/
theorem divisor_eq_entire_target {f G χ v : ℂ → ℂ} {U V L : Set ℂ}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f univ)
    (hG : AnalyticOnNhd ℂ G V) (hχ : AnalyticOnNhd ℂ χ U)
    (hv : AnalyticOnNhd ℂ v U) (hmap : MapsTo χ U V)
    (heq : EqOn (f ∘ χ) ((G ∘ χ) * v) U) (hG0 : ∀ z ∈ V, G z ≠ 0)
    {s : ℂ} (hs : s ∈ U) (hL : χ s ∈ L) (hd : deriv χ s ≠ 0) :
    divisor v U s = divisor f L (χ s) := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hv hs,
    MeromorphicOn.AnalyticOnNhd.divisor_apply (hf.mono (subset_univ L)) hL,
    order_eq_on_open hU (hf.mono (subset_univ V)) hG hχ hv hmap heq hG0 hs hd]

/-- The open-domain filtered divisor count is exactly the actual divisor
count on its physical image. -/
theorem domain_region_image {f G χ v : ℂ → ℂ} {U V L A : Set ℂ}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f univ)
    (hG : AnalyticOnNhd ℂ G V) (hχ : AnalyticOnNhd ℂ χ U)
    (hv : AnalyticOnNhd ℂ v U) (hmap : MapsTo χ U V)
    (heq : EqOn (f ∘ χ) ((G ∘ χ) * v) U) (hG0 : ∀ z ∈ V, G z ≠ 0)
    (hAU : A ⊆ U) (hinj : InjOn χ U) (hAL : MapsTo χ A L)
    (hd : ∀ s ∈ U, deriv χ s ≠ 0) :
    regionCount f L (χ '' A) = regionCount v U A := by
  rw [regionCount_eq_mem_sum, regionCount_eq_mem_sum]
  congr 1
  rw [finsum_mem_image (hinj.mono hAU)]
  apply finsum_mem_congr rfl
  intro s hs
  exact (divisor_eq_entire_target hU hf hG hχ hv hmap heq hG0
    (hAU hs) (hAL hs) (hd s (hAU hs))).symm

/-- Finite support is pulled back from a compact physical carrier. This is
why no extension of the phase solution across its inner boundary is needed. -/
theorem domain_region_support_finite {f G χ v : ℂ → ℂ} {U V L A : Set ℂ}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f univ)
    (hG : AnalyticOnNhd ℂ G V) (hχ : AnalyticOnNhd ℂ χ U)
    (hv : AnalyticOnNhd ℂ v U) (hmap : MapsTo χ U V)
    (heq : EqOn (f ∘ χ) ((G ∘ χ) * v) U) (hG0 : ∀ z ∈ V, G z ≠ 0)
    (hAU : A ⊆ U) (hinj : InjOn χ U) (hAL : MapsTo χ A L)
    (hd : ∀ s ∈ U, deriv χ s ≠ 0) (hL : IsCompact L) :
    (Function.support (fun s => if s ∈ A then divisor v U s else 0)).Finite := by
  have hsub : Function.support (fun s => if s ∈ A then divisor v U s else 0) ⊆ A := by
    intro s hs
    by_contra hn
    simp [Function.mem_support, hn] at hs
  apply Set.Finite.of_injOn (f := χ) (t := Function.support (divisor f L))
    ?_ (hinj.mono (hsub.trans hAU)) ((divisor f L).finiteSupport hL)
  intro s hs
  have hA := hsub hs
  have hn : divisor v U s ≠ 0 := by simpa [Function.mem_support, hA] using hs
  change divisor f L (χ s) ≠ 0
  rw [← divisor_eq_entire_target hU hf hG hχ hv hmap heq hG0
    (hAU hA) (hAL hA) (hd s (hAU hA))]
  exact hn

/-- Away from the original inner boundary this open-domain count agrees
with the legacy compact-carrier phase count. -/
theorem domainPhaseCount_eq_phaseCount {v : ℂ → ℂ} {U : Set ℂ} {S R a b : ℝ}
    (hv : AnalyticOnNhd ℂ v U) (hcarrier : polarCarrier S R a b ⊆ U) :
    domainPhaseCount v U S a b R = phaseCount v S a b R := by
  rw [phaseCount_eq_domain hv hcarrier]
  simp only [domainPhaseCount, regionCount, clippedSector, mem_inter_iff]

/-- Exact splitting of a domain-divisor count, including the new inner
radial boundary in the fixed inner part. The finite-support hypotheses are
proved geometrically by domain_region_support_finite in the application. -/
theorem domainPhaseCount_inner_split {v : ℂ → ℂ} {U : Set ℂ} {S₀ S₁ R a b : ℝ}
    (hS₀ : 0 ≤ S₀) (hS : S₀ ≤ S₁) (hR : S₁ ≤ R)
    (hfin1 : (Function.support (fun s => if s ∈ clippedSector S₁ R a b
      then divisor v U s else 0)).Finite)
    (hfin0 : (Function.support (fun s => if s ∈ clippedSector S₀ S₁ a b
      then divisor v U s else 0)).Finite) :
    domainPhaseCount v U S₀ a b R =
      domainPhaseCount v U S₁ a b R + domainPhaseCount v U S₀ a b S₁ := by
  have heq : (fun s => if s ∈ clippedSector S₀ R a b then divisor v U s else 0) =
      (fun s => if s ∈ clippedSector S₁ R a b then divisor v U s else 0) +
      (fun s => if s ∈ clippedSector S₀ S₁ a b then divisor v U s else 0) := by
    funext s
    simp only [Pi.add_apply, clippedSector_eq_norm hS₀,
      clippedSector_eq_norm (hS₀.trans hS), mem_inter_iff, mem_ofPred_eq]
    by_cases hs : s ∈ angularSector S₀ a b
    · by_cases hn : S₁ < ‖s‖
      · have hs1 := sector_of_norm_gt hS₀ hs hn
        have hn0 : ¬ ‖s‖ ≤ S₁ := not_le_of_gt hn
        simp [hs, hs1, hn0]
      · have hn' : ‖s‖ ≤ S₁ := le_of_not_gt hn
        have hs1 : s ∉ angularSector S₁ a b := by
          intro hm
          exact (not_lt_of_ge hn') (sector_norm_gt (hS₀.trans hS) hm)
        simp [hs, hs1, hn', hn'.trans hR]
    · have hs1 : s ∉ angularSector S₁ a b := fun hm => hs (angularSector_mono_inner hS hm)
      simp [hs, hs1]
  have hi := congrArg (fun w : ℂ → ℤ => ∑ᶠ s, w s) heq
  simp only [Pi.add_apply] at hi
  rw [finsum_add_distrib hfin1 hfin0] at hi
  unfold domainPhaseCount regionCount
  exact_mod_cast hi

/-- The original open-domain phase law passes to a tail law. The only
boundary regularity used is continuity of χ on the fixed inner carrier;
v and G need not extend across that boundary. -/
theorem domain_phase_law_after_inner_cutoff {f G χ v : ℂ → ℂ} {U V : Set ℂ}
    {S₀ S₁ a b c : ℝ}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f univ)
    (hG : AnalyticOnNhd ℂ G V) (hχ : AnalyticOnNhd ℂ χ U)
    (hv : AnalyticOnNhd ℂ v U) (hmap : MapsTo χ U V)
    (heq : EqOn (f ∘ χ) ((G ∘ χ) * v) U) (hG0 : ∀ z ∈ V, G z ≠ 0)
    (hinj : InjOn χ U) (hd : ∀ s ∈ U, deriv χ s ≠ 0)
    (hS₀ : 0 ≤ S₀) (hS : S₀ ≤ S₁)
    (hsector : angularSector S₀ a b ⊆ U)
    (hχinner : ContinuousOn χ (polarCarrier S₀ S₁ a b))
    (hcarrier : ∀ R ≥ S₁, polarCarrier S₁ R a b ⊆ U)
    (hn : Tendsto (fun R => domainPhaseCount v U S₀ a b R / R) atTop (𝓝 c)) :
    Tendsto (fun R => phaseCount v S₁ a b R / R) atTop (𝓝 c) := by
  have hfin0 : (Function.support (fun s => if s ∈ clippedSector S₀ S₁ a b
      then divisor v U s else 0)).Finite := by
    apply domain_region_support_finite hU hf hG hχ hv hmap heq hG0
      (inter_subset_left.trans hsector) hinj
      (L := χ '' polarCarrier S₀ S₁ a b)
      (fun s hs => mem_image_of_mem χ hs.2) hd
    exact (polarCarrier_compact S₀ S₁ a b).image_of_continuousOn hχinner
  have hsplit : ∀ R ≥ S₁, domainPhaseCount v U S₀ a b R =
      phaseCount v S₁ a b R + domainPhaseCount v U S₀ a b S₁ := by
    intro R hR
    have hfin1 : (Function.support (fun s => if s ∈ clippedSector S₁ R a b
        then divisor v U s else 0)).Finite := by
      apply domain_region_support_finite hU hf hG hχ hv hmap heq hG0
        (inter_subset_right.trans (hcarrier R hR)) hinj
        (L := χ '' polarCarrier S₁ R a b)
        (fun s hs => mem_image_of_mem χ hs.2) hd
      exact (polarCarrier_compact S₁ R a b).image_of_continuousOn
        (hχ.continuousOn.mono (hcarrier R hR))
    rw [domainPhaseCount_inner_split hS₀ hS hR hfin1 hfin0,
      domainPhaseCount_eq_phaseCount hv (hcarrier R hR)]
  have hconstant : Tendsto (fun R : ℝ => domainPhaseCount v U S₀ a b S₁ / R)
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have ht : Tendsto (fun R => domainPhaseCount v U S₀ a b R / R -
      domainPhaseCount v U S₀ a b S₁ / R) atTop (𝓝 c) := by
    simpa using hn.sub hconstant
  refine ht.congr' ?_
  filter_upwards [eventually_ge_atTop S₁] with R hR
  rw [hsplit R hR, add_div]
  ring

/-- Lemma 3.4 with the original open-domain phase divisor count. Every
counting equality, finite-inner-error bound and radial sandwich is derived
from the analytic hypotheses. In particular, no analyticity of v or G at
the inner boundary is assumed. -/
theorem radial_transfer_open_domain {f G χ v : ℂ → ℂ} {U V : Set ℂ}
    {S₀ S₁ α a b c : ℝ} {q : ℝ → ℝ} {E : ℝ → ℝ → ℝ}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f univ)
    (hG : AnalyticOnNhd ℂ G V) (hχ : AnalyticOnNhd ℂ χ U)
    (hv : AnalyticOnNhd ℂ v U) (hmap : MapsTo χ U V)
    (heq : EqOn (f ∘ χ) ((G ∘ χ) * v) U) (hG0 : ∀ z ∈ V, G z ≠ 0)
    (hinj : InjOn χ U) (hd : ∀ s ∈ U, deriv χ s ≠ 0)
    (hS₀ : 0 ≤ S₀) (hS : S₀ ≤ S₁)
    (hsector : angularSector S₀ a b ⊆ U)
    (hχinner : ContinuousOn χ (polarCarrier S₀ S₁ a b))
    (hcarrier : ∀ R ≥ S₁, polarCarrier S₁ R a b ⊆ U)
    (hmono : ∀ θ ∈ Ioo a b, MonotoneOn
      (fun ρ => ‖χ (rayPoint ρ θ)‖) (Ici S₁))
    (hq : Tendsto q atTop atTop)
    (hn : Tendsto (fun R => domainPhaseCount v U S₀ a b R / R) atTop (𝓝 c))
    (hα : 0 < α) (hE : ∀ k > 0, Tendsto (E k) atTop (𝓝 0))
    (herr : ∀ k > 0, ∀ᶠ r in atTop, ∀ θ ∈ Ioo a b,
      |‖χ (rayPoint (k * q r) θ)‖ - r - Real.log k / α| ≤ E k r) :
    Tendsto (fun r => count f (pullback χ S₀ a b) r / q r) atTop (𝓝 c) ∧
      (fun r => count f (pullback χ S₀ a b) r - c * q r) =o[atTop] q := by
  have htail := domain_phase_law_after_inner_cutoff hU hf hG hχ hv hmap heq hG0
    hinj hd hS₀ hS hsector hχinner hcarrier hn
  have ht := radial_transfer_of_uniform_log_shift hU hf hG hχ hv hmap heq hG0
    hinj hd hS₀ hS hχinner hcarrier hmono hq htail hα hE herr
  exact ⟨ht, (count_law_iff_littleO hq).mp ht⟩

#print axioms divisor_eq_entire_target
#print axioms domain_region_image
#print axioms domain_region_support_finite
#print axioms domainPhaseCount_inner_split
#print axioms domain_phase_law_after_inner_cutoff
#print axioms radial_transfer_open_domain
end
end V10.DomainDivisorCount
