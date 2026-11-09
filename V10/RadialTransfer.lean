import ZeroDensity.ConformalMultiplicity
import ZeroDensity.SectorDivisorCount
import ZeroDensity.CountingTransfer
import V10.RadialCutoffGeometry
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Topology.Instances.RealVectorSpace

/-!
# Actual divisor transport for radial transfer

The hypotheses concern actual holomorphic functions on open domains:
f ∘ χ = (G ∘ χ) * v, a nonvanishing factor G, and an injective coordinate
map χ with nonzero derivative. No multiplicity equality is assumed.

regionCount uses the actual meromorphic divisor on a carrier K,
filtered by a possibly nonclosed region A. Compactness of the carrier makes
the support finite. Applications must separately exclude the zero function:
mathlib's total divisor assigns zero to an identically-zero germ.

This module closes actual divisor transport, geometric radial cutoffs,
a uniform logarithmic shift, and the fixed physical inner error. It provides
both a tail-count interface and an original compact-carrier-count interface.
The companion module V10.DomainDivisorCount removes the latter interface's
inner-boundary analyticity requirement by taking the divisor on the open
phase domain; its radial_transfer_open_domain is the full Lemma 3.4 entry
point, with the original phase count and no extra phase boundary regularity.
-/

namespace V10.RadialTransfer
open Set Filter Metric MeromorphicOn
open scoped Topology
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Actual divisor count, filtered by a region. -/
def regionCount (f : ℂ → ℂ) (K A : Set ℂ) : ℝ :=
  ((∑ᶠ z, if z ∈ A then divisor f K z else 0 : ℤ) : ℝ)

lemma regionCount_eq_mem_sum (f : ℂ → ℂ) (K A : Set ℂ) :
    regionCount f K A = ((∑ᶠ z ∈ A, divisor f K z : ℤ) : ℝ) := by
  simp only [regionCount, finsum_mem_def, Set.indicator]

/-- A compact carrier gives finite support even for an open counting region. -/
theorem regionCount_support_finite (f : ℂ → ℂ) {K : Set ℂ}
    (hK : IsCompact K) (A : Set ℂ) :
    (Function.support (fun z => if z ∈ A then divisor f K z else 0)).Finite := by
  apply ((divisor f K).finiteSupport hK).subset
  intro z hz
  by_cases h : z ∈ A
  · simpa [h, Function.mem_support] using hz
  · simp [h, Function.mem_support] at hz

/-- Zero-order preservation is derived from the analytic germ factorization. -/
theorem order_eq_of_conformal_factor {f G χ v : ℂ → ℂ} {s : ℂ}
    (hf : AnalyticAt ℂ f (χ s)) (hG : AnalyticAt ℂ G (χ s))
    (hχ : AnalyticAt ℂ χ s) (hv : AnalyticAt ℂ v s)
    (hd : deriv χ s ≠ 0) (hG0 : G (χ s) ≠ 0)
    (heq : (f ∘ χ) =ᶠ[𝓝 s] ((G ∘ χ) * v)) :
    analyticOrderAt v s = analyticOrderAt f (χ s) := by
  have hzero : analyticOrderAt (G ∘ χ) s = 0 :=
    (hG.comp hχ).analyticOrderAt_eq_zero.mpr hG0
  have h := ZeroDensity.ConformalMultiplicity.order_comp hf hχ hd
  rw [analyticOrderAt_congr heq, analyticOrderAt_mul (hG.comp hχ) hv,
    hzero, zero_add] at h
  exact h

/-- Open-domain equality supplies equality of germs. -/
theorem order_eq_on_open {f G χ v : ℂ → ℂ} {U V : Set ℂ}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f V) (hG : AnalyticOnNhd ℂ G V)
    (hχ : AnalyticOnNhd ℂ χ U) (hv : AnalyticOnNhd ℂ v U)
    (hmap : MapsTo χ U V)
    (heq : EqOn (f ∘ χ) ((G ∘ χ) * v) U)
    (hG0 : ∀ z ∈ V, G z ≠ 0) {s : ℂ} (hs : s ∈ U)
    (hd : deriv χ s ≠ 0) :
    analyticOrderAt v s = analyticOrderAt f (χ s) := by
  apply order_eq_of_conformal_factor
    (hf _ (hmap hs)) (hG _ (hmap hs)) (hχ _ hs) (hv _ hs) hd (hG0 _ (hmap hs))
  exact Filter.eventually_of_mem (hU.mem_nhds hs) (fun z hz => heq hz)

/-- Actual divisor weights agree independently of the shapes of the carriers. -/
theorem divisor_eq_on_carriers {f G χ v : ℂ → ℂ} {U V K L : Set ℂ}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f V) (hG : AnalyticOnNhd ℂ G V)
    (hχ : AnalyticOnNhd ℂ χ U) (hv : AnalyticOnNhd ℂ v U)
    (hmap : MapsTo χ U V)
    (heq : EqOn (f ∘ χ) ((G ∘ χ) * v) U)
    (hG0 : ∀ z ∈ V, G z ≠ 0)
    (hKU : K ⊆ U) (hLV : L ⊆ V)
    {s : ℂ} (hs : s ∈ K) (himage : χ s ∈ L) (hd : deriv χ s ≠ 0) :
    divisor v K s = divisor f L (χ s) := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (hv.mono hKU) hs,
    MeromorphicOn.AnalyticOnNhd.divisor_apply (hf.mono hLV) himage,
    order_eq_on_open hU hf hG hχ hv hmap heq hG0 (hKU hs) hd]

/-- An analytic injection with nonzero derivative and a zero-free factor
preserve actual divisor counts. Regions may have open angular sides and
closed radial sides, with different compact carriers in the two planes. -/
theorem regionCount_image {f G χ v : ℂ → ℂ} {U V K L A : Set ℂ}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f V) (hG : AnalyticOnNhd ℂ G V)
    (hχ : AnalyticOnNhd ℂ χ U) (hv : AnalyticOnNhd ℂ v U)
    (hmap : MapsTo χ U V)
    (heq : EqOn (f ∘ χ) ((G ∘ χ) * v) U)
    (hG0 : ∀ z ∈ V, G z ≠ 0)
    (hKU : K ⊆ U) (hLV : L ⊆ V) (hAK : A ⊆ K)
    (hinj : InjOn χ A) (hAL : MapsTo χ A L)
    (hd : ∀ s ∈ A, deriv χ s ≠ 0) :
    regionCount f L (χ '' A) = regionCount v K A := by
  rw [regionCount_eq_mem_sum, regionCount_eq_mem_sum]
  congr 1
  rw [finsum_mem_image hinj]
  apply finsum_mem_congr rfl
  intro s hs
  exact (divisor_eq_on_carriers hU hf hG hχ hv hmap heq hG0
    hKU hLV (hAK hs) (hAL hs) (hd s hs)).symm

/-- The transport equality and finite supports on both sides, so these are
ordinary finite weighted counts, rather than an infinite-support fallback. -/
theorem compact_region_transport {f G χ v : ℂ → ℂ} {U V K L A : Set ℂ}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f V) (hG : AnalyticOnNhd ℂ G V)
    (hχ : AnalyticOnNhd ℂ χ U) (hv : AnalyticOnNhd ℂ v U)
    (hmap : MapsTo χ U V)
    (heq : EqOn (f ∘ χ) ((G ∘ χ) * v) U)
    (hG0 : ∀ z ∈ V, G z ≠ 0)
    (hK : IsCompact K) (hL : IsCompact L)
    (hKU : K ⊆ U) (hLV : L ⊆ V) (hAK : A ⊆ K)
    (hinj : InjOn χ A) (hAL : MapsTo χ A L)
    (hd : ∀ s ∈ A, deriv χ s ≠ 0) :
    regionCount f L (χ '' A) = regionCount v K A ∧
    (Function.support (fun z => if z ∈ χ '' A then divisor f L z else 0)).Finite ∧
    (Function.support (fun s => if s ∈ A then divisor v K s else 0)).Finite := by
  exact ⟨regionCount_image hU hf hG hχ hv hmap heq hG0 hKU hLV hAK hinj hAL hd,
    regionCount_support_finite f hL (χ '' A), regionCount_support_finite v hK A⟩

/-- Count comparison only requires containment after both carrier cutoffs.
The weights are actual analytic divisor weights, not arbitrary input masses. -/
theorem regionCount_mono_carriers {f : ℂ → ℂ} {K L A B : Set ℂ}
    (hK : IsCompact K) (hL : IsCompact L)
    (hfK : AnalyticOnNhd ℂ f K) (hfL : AnalyticOnNhd ℂ f L)
    (hsub : A ∩ K ⊆ B ∩ L) :
    regionCount f K A ≤ regionCount f L B := by
  have hle : ∀ z, (if z ∈ A then divisor f K z else 0) ≤
      (if z ∈ B then divisor f L z else 0) := by
    intro z
    by_cases hA : z ∈ A
    · by_cases hzK : z ∈ K
      · obtain ⟨hB, hzL⟩ := hsub ⟨hA, hzK⟩
        simp only [if_pos hA, if_pos hB]
        rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hfK hzK,
          MeromorphicOn.AnalyticOnNhd.divisor_apply hfL hzL]
      · simp only [if_pos hA, ZeroDensity.SectorDivisorCount.divisor_zero_outside hzK]
        split_ifs
        · exact hfL.divisor_nonneg z
        · exact le_rfl
    · simp only [if_neg hA]
      split_ifs
      · exact hfL.divisor_nonneg z
      · exact le_rfl
  unfold regionCount
  exact_mod_cast finsum_le_finsum' (regionCount_support_finite f hK A)
    (regionCount_support_finite f hL B) hle

/-- Restricting the counting region to its carrier changes no count. -/
theorem regionCount_inter_carrier (f : ℂ → ℂ) (K A : Set ℂ) :
    regionCount f K (A ∩ K) = regionCount f K A := by
  unfold regionCount
  congr 1
  apply finsum_congr
  intro z
  by_cases hA : z ∈ A <;> by_cases hK : z ∈ K <;> simp [hA, hK]

/-- The generic count specializes definitionally to the legacy disk count. -/
theorem regionCount_disk (f : ℂ → ℂ) (A : Set ℂ) (r : ℝ) :
    regionCount f (closedBall 0 r) A = ZeroDensity.CountGeometry.count f A r := rfl

open ZeroDensity.SectorDivisorCount ZeroDensity.CountGeometry

/-- An actual truncated phase-sector divisor count equals the count on its
compact conformal image. No multiplicity or counting equality is assumed. -/
theorem phaseCount_image {f G χ v : ℂ → ℂ} {U V : Set ℂ} {S R a b : ℝ}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f V) (hG : AnalyticOnNhd ℂ G V)
    (hχ : AnalyticOnNhd ℂ χ U) (hv : AnalyticOnNhd ℂ v U)
    (hmap : MapsTo χ U V)
    (heq : EqOn (f ∘ χ) ((G ∘ χ) * v) U)
    (hG0 : ∀ z ∈ V, G z ≠ 0)
    (hKU : polarCarrier S R a b ⊆ U)
    (hinj : InjOn χ U) (hd : ∀ s ∈ U, deriv χ s ≠ 0) :
    regionCount f (χ '' polarCarrier S R a b)
      (χ '' (angularSector S a b ∩ polarCarrier S R a b)) =
      phaseCount v S a b R := by
  have h := regionCount_image hU hf hG hχ hv hmap heq hG0 hKU
    (image_subset_iff.mpr (fun s hs => hmap (hKU hs)))
    (inter_subset_right : angularSector S a b ∩ polarCarrier S R a b ⊆ _)
    (hinj.mono (inter_subset_right.trans hKU))
    (fun s hs => mem_image_of_mem χ hs.2)
    (fun s hs => hd s (hKU hs.2))
  rw [regionCount_inter_carrier] at h
  exact h

/-- Actual disk counts are trapped by actual phase counts once the geometric
inner/outer inclusions have been established. This derives, rather than
assumes, the zero-count sandwich used by the asymptotic transfer theorem. -/
theorem actual_count_sandwich {f G χ v : ℂ → ℂ} {U V : Set ℂ}
    {S R T a b r : ℝ}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f univ)
    (hG : AnalyticOnNhd ℂ G V)
    (hχ : AnalyticOnNhd ℂ χ U) (hv : AnalyticOnNhd ℂ v U)
    (hmap : MapsTo χ U V)
    (heq : EqOn (f ∘ χ) ((G ∘ χ) * v) U)
    (hG0 : ∀ z ∈ V, G z ≠ 0)
    (hRU : polarCarrier S R a b ⊆ U) (hTU : polarCarrier S T a b ⊆ U)
    (hinj : InjOn χ U) (hd : ∀ s ∈ U, deriv χ s ≠ 0)
    (hlo : χ '' (angularSector S a b ∩ polarCarrier S R a b) ⊆ closedBall 0 r)
    (hhi : (χ '' angularSector S a b) ∩ closedBall 0 r ⊆
      χ '' (angularSector S a b ∩ polarCarrier S T a b)) :
    phaseCount v S a b R ≤ count f (χ '' angularSector S a b) r ∧
    count f (χ '' angularSector S a b) r ≤ phaseCount v S a b T := by
  have hRc : IsCompact (χ '' polarCarrier S R a b) :=
    (polarCarrier_compact S R a b).image_of_continuousOn
      (hχ.continuousOn.mono hRU)
  have hTc : IsCompact (χ '' polarCarrier S T a b) :=
    (polarCarrier_compact S T a b).image_of_continuousOn
      (hχ.continuousOn.mono hTU)
  have hfV := hf.mono (subset_univ V)
  have hR := phaseCount_image hU hfV hG hχ hv hmap heq hG0 hRU hinj hd
  have hT := phaseCount_image hU hfV hG hχ hv hmap heq hG0 hTU hinj hd
  constructor
  · rw [← hR, ← regionCount_disk]
    apply regionCount_mono_carriers hRc (isCompact_closedBall 0 r)
      (hf.mono (subset_univ _)) (hf.mono (subset_univ _))
    intro z hz
    exact ⟨image_mono inter_subset_left hz.1, hlo hz.1⟩
  · rw [← hT, ← regionCount_disk]
    apply regionCount_mono_carriers (isCompact_closedBall 0 r) hTc
      (hf.mono (subset_univ _)) (hf.mono (subset_univ _))
    intro z hz
    have hm := hhi hz
    exact ⟨hm, image_mono inter_subset_right hm⟩

/-- A fixed compact exceptional region contributes at most its actual
finite divisor count, uniformly in the physical disk radius. -/
theorem count_le_count_add_compact {f : ℂ → ℂ} {W A B : Set ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (hB : IsCompact B)
    (hcover : W ⊆ A ∪ B) (r : ℝ) :
    count f W r ≤ count f A r + regionCount f B univ := by
  have hfD := hf.mono (subset_univ (closedBall (0 : ℂ) r))
  have hle : ∀ z, (if z ∈ W then divisor f (closedBall 0 r) z else 0) ≤
      (if z ∈ A then divisor f (closedBall 0 r) z else 0) +
      (if z ∈ B then divisor f (closedBall 0 r) z else 0) := by
    intro z
    have hn : (0 : ℤ) ≤ divisor f (closedBall 0 r) z := hfD.divisor_nonneg z
    by_cases hzW : z ∈ W
    · rcases hcover hzW with hzA | hzB
      · simp only [if_pos hzW, if_pos hzA]
        split_ifs <;> omega
      · simp only [if_pos hzW, if_pos hzB]
        split_ifs <;> omega
    · simp only [if_neg hzW]
      split_ifs <;> omega
  have hsumfin : (Function.support (fun z =>
      (if z ∈ A then divisor f (closedBall 0 r) z else 0) +
      (if z ∈ B then divisor f (closedBall 0 r) z else 0))).Finite := by
    apply ((divisor f (closedBall 0 r)).finiteSupport (isCompact_closedBall 0 r)).subset
    intro z hz
    by_contra hz0
    have hd : divisor f (closedBall 0 r) z = 0 := by
      simpa only [Function.mem_support, not_not] using hz0
    simp [Function.mem_support, hd] at hz
  have hi := finsum_le_finsum' (ZeroDensity.CountGeometry.filtered_support_finite f W r)
    hsumfin hle
  rw [finsum_add_distrib
    (ZeroDensity.CountGeometry.filtered_support_finite f A r)
    (ZeroDensity.CountGeometry.filtered_support_finite f B r)] at hi
  have hi' : count f W r ≤ count f A r + count f B r := by
    unfold count
    exact_mod_cast hi
  have hbound : count f B r ≤ regionCount f B univ := by
    rw [← regionCount_disk]
    exact regionCount_mono_carriers (isCompact_closedBall 0 r) hB hfD
      (hf.mono (subset_univ _)) (fun _ hz => ⟨mem_univ _, hz.1⟩)
  linarith

/-- The actual physical count has a uniformly bounded inner-cutoff error.
Only continuity of the coordinate map on the fixed inner carrier is needed;
the phase equation need not extend analytically to that carrier. -/
theorem physical_inner_error {f χ : ℂ → ℂ} {S₀ S₁ a b : ℝ}
    (hf : AnalyticOnNhd ℂ f univ) (hS₀ : 0 ≤ S₀) (hS : S₀ ≤ S₁)
    (hχinner : ContinuousOn χ (polarCarrier S₀ S₁ a b)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r,
      count f (pullback χ S₁ a b) r ≤ count f (pullback χ S₀ a b) r ∧
      count f (pullback χ S₀ a b) r ≤ count f (pullback χ S₁ a b) r + C := by
  let B := χ '' polarCarrier S₀ S₁ a b
  have hB : IsCompact B := (polarCarrier_compact S₀ S₁ a b).image_of_continuousOn hχinner
  refine ⟨regionCount f B univ, ?_, fun r => ⟨?_, ?_⟩⟩
  · unfold regionCount
    exact_mod_cast finsum_nonneg (fun z => by
      simp only [mem_univ, ite_true]
      exact (hf.mono (subset_univ B)).divisor_nonneg z)
  · exact count_mono r (Complex.analyticOnNhd_univ_iff_differentiable.mp hf)
      (image_mono (angularSector_mono_inner hS))
  · exact count_le_count_add_compact hf hB
      (V10.RadialCutoffGeometry.pullback_subset_tail_union_inner χ hS₀) r

/-- A genuine analytic radial-transfer theorem: the conclusion concerns the
actual disk divisor count of the conformal-image sector. Uniform cutoff
inequalities and radial monotonicity produce the geometric inclusions;
analytic factorization produces the multiplicities; compactness controls the
inner error. No zero-count sandwich is supplied as a hypothesis. -/
theorem radial_transfer_actual {f G χ v : ℂ → ℂ} {U V : Set ℂ}
    {S₀ S₁ a b c : ℝ} {q : ℝ → ℝ}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f univ)
    (hG : AnalyticOnNhd ℂ G V) (hχ : AnalyticOnNhd ℂ χ U)
    (hv : AnalyticOnNhd ℂ v U) (hmap : MapsTo χ U V)
    (heq : EqOn (f ∘ χ) ((G ∘ χ) * v) U) (hG0 : ∀ z ∈ V, G z ≠ 0)
    (hinj : InjOn χ U) (hd : ∀ s ∈ U, deriv χ s ≠ 0)
    (hS₀ : 0 ≤ S₀) (hS : S₀ ≤ S₁)
    (hχinner : ContinuousOn χ (polarCarrier S₀ S₁ a b))
    (hcarrier : ∀ R ≥ S₁, polarCarrier S₁ R a b ⊆ U)
    (hmono : ∀ θ ∈ Ioo a b, MonotoneOn
      (fun ρ => ‖χ (V10.RadialCutoffGeometry.rayPoint ρ θ)‖) (Ici S₁))
    (hq : Tendsto q atTop atTop)
    (hn : Tendsto (fun R => phaseCount v S₁ a b R / R) atTop (𝓝 c))
    (hcut : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ r in atTop,
      (∀ θ ∈ Ioo a b,
        ‖χ (V10.RadialCutoffGeometry.rayPoint ((1 - ε) * q r) θ)‖ ≤ r) ∧
      (∀ θ ∈ Ioo a b,
        r < ‖χ (V10.RadialCutoffGeometry.rayPoint ((1 + ε) * q r) θ)‖)) :
    Tendsto (fun r => count f (pullback χ S₀ a b) r / q r) atTop (𝓝 c) := by
  obtain ⟨C, hC, hinner⟩ := physical_inner_error hf hS₀ hS hχinner
  apply ZeroDensity.CountingTransfer.count_law_transfer hq hn (C := C)
  intro ε hε hε1
  have hloR := ((hq.const_mul_atTop (by linarith : 0 < 1 - ε))).eventually_ge_atTop S₁
  have hhiR := ((hq.const_mul_atTop (by linarith : 0 < 1 + ε))).eventually_ge_atTop S₁
  filter_upwards [hcut ε hε hε1, hloR, hhiR] with r hc hlR hhR
  have hlo := V10.RadialCutoffGeometry.clipped_image_subset_closedBall χ
    (hS₀.trans hS) hlR hmono hc.1
  have hhi := V10.RadialCutoffGeometry.imageDisk_subset_clipped_image χ
    (hS₀.trans hS) hhR hmono hc.2
  have hs := actual_count_sandwich hU hf hG hχ hv hmap heq hG0
    (hcarrier _ hlR) (hcarrier _ hhR) hinj hd hlo hhi
  have hinnerR := hinner r
  change phaseCount v S₁ a b ((1 - ε) * q r) - C ≤ _ ∧
    _ ≤ phaseCount v S₁ a b ((1 + ε) * q r) + C
  constructor <;> dsimp [pullback] at hinnerR ⊢ <;> linarith

/-- Moving the phase counting law past a fixed inner cutoff preserves its
coefficient. This uses the existing exact actual-divisor inner split and the
vanishing of the fixed inner count divided by the outer radius. -/
theorem phase_law_after_inner_cutoff {v : ℂ → ℂ} {S₀ S₁ a b c : ℝ}
    (hS₀ : 0 ≤ S₀) (hS : S₀ ≤ S₁)
    (hv : ∀ R ≥ S₁, AnalyticOnNhd ℂ v (polarCarrier S₀ R a b))
    (hn : Tendsto (fun R => phaseCount v S₀ a b R / R) atTop (𝓝 c)) :
    Tendsto (fun R => phaseCount v S₁ a b R / R) atTop (𝓝 c) := by
  have hconstant : Tendsto (fun R : ℝ => phaseCount v S₀ a b S₁ / R)
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have ht := hn.sub hconstant
  have ht' : Tendsto (fun R => phaseCount v S₀ a b R / R -
      phaseCount v S₀ a b S₁ / R) atTop (𝓝 c) := by simpa using ht
  refine ht'.congr' ?_
  filter_upwards [eventually_ge_atTop S₁] with R hR
  have hs := phaseCount_inner_split hS₀ hS hR (hv R hR)
  rw [hs, add_div]
  ring

/-- The manuscript's angularly uniform logarithmic shift gives both actual
radial cutoff inequalities. Uniformity is encoded by a vanishing real error
majorant for each fixed positive multiplier. -/
theorem cutoffs_of_uniform_log_shift {χ : ℂ → ℂ} {q : ℝ → ℝ}
    {α a b : ℝ} (hα : 0 < α) {E : ℝ → ℝ → ℝ}
    (hE : ∀ k > 0, Tendsto (E k) atTop (𝓝 0))
    (herr : ∀ k > 0, ∀ᶠ r in atTop, ∀ θ ∈ Ioo a b,
      |‖χ (V10.RadialCutoffGeometry.rayPoint (k * q r) θ)‖ - r -
        Real.log k / α| ≤ E k r)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ r in atTop,
      (∀ θ ∈ Ioo a b,
        ‖χ (V10.RadialCutoffGeometry.rayPoint ((1 - ε) * q r) θ)‖ ≤ r) ∧
      (∀ θ ∈ Ioo a b,
        r < ‖χ (V10.RadialCutoffGeometry.rayPoint ((1 + ε) * q r) θ)‖) := by
  have hm : 0 < 1 - ε := by linarith
  have hp : 0 < 1 + ε := by linarith
  have hneg := ZeroDensity.RadiusComparison.lower_shift_neg hα hε hε1
  have hpos := ZeroDensity.RadiusComparison.upper_shift_pos hα hε
  have heminus := (hE (1 - ε) hm).eventually
    (eventually_lt_nhds (neg_pos.mpr hneg))
  have heplus := (hE (1 + ε) hp).eventually (eventually_lt_nhds hpos)
  filter_upwards [herr (1 - ε) hm, herr (1 + ε) hp, heminus, heplus]
    with r hminus hplus eminus eplus
  constructor
  · intro θ hθ
    have hh := (abs_le.mp (hminus θ hθ)).2
    linarith
  · intro θ hθ
    have hh := (abs_le.mp (hplus θ hθ)).1
    linarith

/-- The analytic radial-transfer conclusion from the uniform shift appearing
in manuscript Lemma 3.4. The phase law is stated after a fixed inner cutoff;
the physical sector retains its original inner cutoff. -/
theorem radial_transfer_of_uniform_log_shift {f G χ v : ℂ → ℂ} {U V : Set ℂ}
    {S₀ S₁ α a b c : ℝ} {q : ℝ → ℝ} {E : ℝ → ℝ → ℝ}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f univ)
    (hG : AnalyticOnNhd ℂ G V) (hχ : AnalyticOnNhd ℂ χ U)
    (hv : AnalyticOnNhd ℂ v U) (hmap : MapsTo χ U V)
    (heq : EqOn (f ∘ χ) ((G ∘ χ) * v) U) (hG0 : ∀ z ∈ V, G z ≠ 0)
    (hinj : InjOn χ U) (hd : ∀ s ∈ U, deriv χ s ≠ 0)
    (hS₀ : 0 ≤ S₀) (hS : S₀ ≤ S₁)
    (hχinner : ContinuousOn χ (polarCarrier S₀ S₁ a b))
    (hcarrier : ∀ R ≥ S₁, polarCarrier S₁ R a b ⊆ U)
    (hmono : ∀ θ ∈ Ioo a b, MonotoneOn
      (fun ρ => ‖χ (V10.RadialCutoffGeometry.rayPoint ρ θ)‖) (Ici S₁))
    (hq : Tendsto q atTop atTop)
    (hn : Tendsto (fun R => phaseCount v S₁ a b R / R) atTop (𝓝 c))
    (hα : 0 < α) (hE : ∀ k > 0, Tendsto (E k) atTop (𝓝 0))
    (herr : ∀ k > 0, ∀ᶠ r in atTop, ∀ θ ∈ Ioo a b,
      |‖χ (V10.RadialCutoffGeometry.rayPoint (k * q r) θ)‖ - r -
        Real.log k / α| ≤ E k r) :
    Tendsto (fun r => count f (pullback χ S₀ a b) r / q r) atTop (𝓝 c) := by
  apply radial_transfer_actual hU hf hG hχ hv hmap heq hG0 hinj hd hS₀ hS
    hχinner hcarrier hmono hq hn
  intro ε hε hε1
  exact cutoffs_of_uniform_log_shift hα hE herr hε hε1

/-- Radial transfer with the original phase cutoff and the original
physical cutoff, using an analytic phase carrier. In the sectorial-counting
setup R₀ > R_* this carrier condition follows from the larger phase domain.
The separate local-setting lemma only assumes analyticity on the open
exterior sector, so using this interface there requires that identification. -/
theorem radial_transfer_original_phase_count {f G χ v : ℂ → ℂ} {U V : Set ℂ}
    {S₀ S₁ α a b c : ℝ} {q : ℝ → ℝ} {E : ℝ → ℝ → ℝ}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f univ)
    (hG : AnalyticOnNhd ℂ G V) (hχ : AnalyticOnNhd ℂ χ U)
    (hv : AnalyticOnNhd ℂ v U) (hmap : MapsTo χ U V)
    (heq : EqOn (f ∘ χ) ((G ∘ χ) * v) U) (hG0 : ∀ z ∈ V, G z ≠ 0)
    (hinj : InjOn χ U) (hd : ∀ s ∈ U, deriv χ s ≠ 0)
    (hS₀ : 0 ≤ S₀) (hS : S₀ ≤ S₁)
    (hχinner : ContinuousOn χ (polarCarrier S₀ S₁ a b))
    (hcarrier : ∀ R ≥ S₁, polarCarrier S₁ R a b ⊆ U)
    (hvcarrier : ∀ R ≥ S₁, AnalyticOnNhd ℂ v (polarCarrier S₀ R a b))
    (hmono : ∀ θ ∈ Ioo a b, MonotoneOn
      (fun ρ => ‖χ (V10.RadialCutoffGeometry.rayPoint ρ θ)‖) (Ici S₁))
    (hq : Tendsto q atTop atTop)
    (hn : Tendsto (fun R => phaseCount v S₀ a b R / R) atTop (𝓝 c))
    (hα : 0 < α) (hE : ∀ k > 0, Tendsto (E k) atTop (𝓝 0))
    (herr : ∀ k > 0, ∀ᶠ r in atTop, ∀ θ ∈ Ioo a b,
      |‖χ (V10.RadialCutoffGeometry.rayPoint (k * q r) θ)‖ - r -
        Real.log k / α| ≤ E k r) :
    Tendsto (fun r => count f (pullback χ S₀ a b) r / q r) atTop (𝓝 c) := by
  exact radial_transfer_of_uniform_log_shift hU hf hG hχ hv hmap heq hG0 hinj hd
    hS₀ hS hχinner hcarrier hmono hq
    (phase_law_after_inner_cutoff hS₀ hS hvcarrier hn) hα hE herr

/-- For a scale tending to infinity, normalized count convergence has exactly
the little-o form printed in Lemma 3.4. -/
theorem count_law_iff_littleO {N q : ℝ → ℝ} {c : ℝ}
    (hq : Tendsto q atTop atTop) :
    Tendsto (fun r => N r / q r) atTop (𝓝 c) ↔
      (fun r => N r - c * q r) =o[atTop] q := by
  have hnz : ∀ᶠ r in atTop, q r ≠ 0 :=
    (hq.eventually_gt_atTop 0).mono (fun _ hr => ne_of_gt hr)
  have heq : ∀ᶠ r in atTop,
      (N r - c * q r) / q r = N r / q r - c := by
    filter_upwards [hnz] with r hr
    field_simp
  rw [Asymptotics.isLittleO_iff_tendsto' (hnz.mono fun _ hr hz => (hr hz).elim)]
  constructor
  · intro ht
    have ht' : Tendsto (fun r => N r / q r - c) atTop (𝓝 0) := by
      simpa using ht.sub_const c
    exact ht'.congr' (heq.mono fun _ h => h.symm)
  · intro ht
    have ht' : Tendsto (fun r => N r / q r - c) atTop (𝓝 0) := ht.congr' heq
    simpa using ht'.add_const c

#print axioms order_eq_of_conformal_factor
#print axioms order_eq_on_open
#print axioms divisor_eq_on_carriers
#print axioms regionCount_image
#print axioms compact_region_transport
#print axioms regionCount_mono_carriers
#print axioms phaseCount_image
#print axioms actual_count_sandwich
#print axioms count_le_count_add_compact
#print axioms physical_inner_error
#print axioms radial_transfer_actual
#print axioms phase_law_after_inner_cutoff
#print axioms cutoffs_of_uniform_log_shift
#print axioms radial_transfer_of_uniform_log_shift
#print axioms radial_transfer_original_phase_count
#print axioms count_law_iff_littleO

end
end V10.RadialTransfer
