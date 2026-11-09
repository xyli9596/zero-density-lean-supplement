import ZeroDensity.PlanarLogIntegrability
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.Convex.TotallyBounded
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.Sequences
import Mathlib.Tactic

/-!
# Compactness of logarithmic potentials with bounded positive mass

The singular logarithmic kernel is first cut off outside a large disk, without
truncating its singularity. Its translates form a continuous family in actual
`L¹(ℂ)`, by the continuity of translation on `Lp`. Consequently normalized
positive finite combinations over a compact set of centers have compact closure
in `L¹`. This is the logarithmic-potential part of scalar compactness, not by
itself the full compactness theorem for analytic logarithms.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace V10.ScalarCompactnessLogPotential

local instance : Fact ((1 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

abbrev L1 := MeasureTheory.Lp ℝ 1 (volume : Measure ℂ)

/-- A spatial cutoff of the true logarithmic kernel. At its single singular
point the totalized real representative is harmless for the L¹ class. -/
def cutoffLog (R : ℝ) (z : ℂ) : ℝ :=
  (ball (0 : ℂ) R).indicator (fun w => Real.log ‖w‖) z

theorem integrable_cutoffLog (R : ℝ) : Integrable (cutoffLog R) := by
  exact (integrable_indicator_iff measurableSet_ball).mpr
    (ZeroDensity.PlanarLogIntegrability.integrableOn_log_norm_ball R)

def cutoffLogL1 (R : ℝ) : L1 :=
  (memLp_one_iff_integrable.mpr (integrable_cutoffLog R)).toLp (cutoffLog R)

theorem cutoffLogL1_ae_eq (R : ℝ) :
    (cutoffLogL1 R : ℂ → ℝ) =ᵐ[volume] cutoffLog R :=
  MemLp.coeFn_toLp _

/-- The center `a` is translated with the sign required for `log |z-a|`. -/
def logKernelL1 (R : ℝ) (a : ℂ) : L1 :=
  DomAddAct.mk (-a) +ᵥ cutoffLogL1 R

theorem continuous_logKernelL1 (R : ℝ) : Continuous (logKernelL1 R) := by
  exact (DomAddAct.continuous_mk.comp continuous_neg).vadd continuous_const

theorem logKernelL1_ae_eq (R : ℝ) (a : ℂ) :
    (logKernelL1 R a : ℂ → ℝ) =ᵐ[volume] fun z => cutoffLog R (z - a) := by
  have ht := DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk (-a)) (cutoffLogL1 R)
  have he := (measurePreserving_add_left volume (-a)).quasiMeasurePreserving.ae_eq_comp
    (cutoffLogL1_ae_eq R)
  exact ht.trans (by simpa only [Equiv.symm_apply_apply, vadd_eq_add, add_comm,
    Function.comp_def, ← sub_eq_add_neg] using he)

/-- On an observation set whose distance to the center is below the cutoff,
the L¹ element represents the original logarithmic singularity exactly a.e. -/
theorem logKernelL1_ae_eq_on {K : Set ℂ} (hKm : MeasurableSet K) {R : ℝ} {a : ℂ}
    (hK : ∀ z ∈ K, ‖z - a‖ < R) :
    (logKernelL1 R a : ℂ → ℝ) =ᵐ[volume.restrict K] fun z => Real.log ‖z - a‖ := by
  filter_upwards [ae_restrict_of_ae (logKernelL1_ae_eq R a), ae_restrict_mem hKm] with z hz hzK
  rw [hz, cutoffLog, indicator_of_mem (mem_ball_zero_iff.mpr (hK z hzK))]

theorem isCompact_logKernelL1_image {K : Set ℂ} (hK : IsCompact K) (R : ℝ) :
    IsCompact (logKernelL1 R '' K) :=
  hK.image (continuous_logKernelL1 R)

/-- Compactness in L¹ is derived here, including the singular kernels. -/
theorem isCompact_closed_convex_logKernel {K : Set ℂ} (hK : IsCompact K) (R : ℝ) :
    IsCompact (closure (convexHull ℝ (insert 0 (logKernelL1 R '' K)))) := by
  apply TotallyBounded.isCompact_of_isClosed
  · exact ((isCompact_logKernelL1_image hK R).insert 0).totallyBounded.convexHull.closure
  · exact isClosed_closure

/-- Positive finite combinations of total mass at most one belong to the
convex hull after adding the zero potential. -/
theorem sum_smul_mem_convexHull_insert_zero {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι] {S : Set E} {w : ι → ℝ} {v : ι → E}
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i ≤ 1) (hv : ∀ i, v i ∈ S) :
    ∑ i, w i • v i ∈ convexHull ℝ (insert 0 S) := by
  classical
  let w' : Option ι → ℝ := fun i => i.elim (1 - ∑ j, w j) w
  let v' : Option ι → E := fun i => i.elim 0 v
  have hp : ∀ i, 0 ≤ w' i := by
    intro i
    cases i with
    | none => exact sub_nonneg.mpr hs
    | some i => exact hw i
  have ht : ∑ i, w' i = 1 := by simp [w', Fintype.sum_option]
  have hm : ∀ i, v' i ∈ convexHull ℝ (insert 0 S) := by
    intro i
    apply subset_convexHull
    cases i with
    | none => exact mem_insert _ _
    | some i => exact mem_insert_of_mem _ (hv i)
  have h := (convex_convexHull ℝ (insert 0 S)).sum_mem
    (t := Finset.univ) (fun i _ => hp i) ht (fun i _ => hm i)
  simpa [w', v', Fintype.sum_option] using h

/-- The compact set containing all positive log potentials of mass at most `M`.
No bound on the number of atoms is required. -/
def potentialCompactSet (R : ℝ) (K : Set ℂ) (M : ℝ) : Set L1 :=
  (fun u : L1 => M • u) '' closure (convexHull ℝ (insert 0 (logKernelL1 R '' K)))

theorem isCompact_potentialCompactSet {K : Set ℂ} (hK : IsCompact K) (R M : ℝ) :
    IsCompact (potentialCompactSet R K M) :=
  (isCompact_closed_convex_logKernel hK R).image (continuous_const_smul M)

theorem sum_logKernel_mem_potentialCompactSet {ι : Type*} [Fintype ι]
    {R M : ℝ} {K : Set ℂ} {w : ι → ℝ} {a : ι → ℂ}
    (hM : 0 < M) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i ≤ M)
    (ha : ∀ i, a i ∈ K) :
    ∑ i, w i • logKernelL1 R (a i) ∈ potentialCompactSet R K M := by
  classical
  have hc : ∑ i, (w i / M) • logKernelL1 R (a i) ∈
      convexHull ℝ (insert 0 (logKernelL1 R '' K)) := by
    apply sum_smul_mem_convexHull_insert_zero
    · exact fun i => div_nonneg (hw i) hM.le
    · rw [← Finset.sum_div]
      exact (div_le_one hM).mpr hs
    · exact fun i => mem_image_of_mem _ (ha i)
  refine ⟨_, subset_closure hc, ?_⟩
  change M • (∑ i, (w i / M) • logKernelL1 R (a i)) = _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul]
  congr 1
  field_simp

/-- Genuine L¹ subsequential compactness for finite logarithmic potentials
whose atom locations stay in a compact set and whose positive masses are
uniformly bounded. The finite index set may vary with the sequence index. -/
theorem logPotential_tendsto_subseq {κ : ℕ → Type*} [∀ n, Fintype (κ n)]
    {R M : ℝ} {K : Set ℂ} {w : ∀ n, κ n → ℝ} {a : ∀ n, κ n → ℂ}
    (hK : IsCompact K) (hM : 0 < M)
    (hw : ∀ n i, 0 ≤ w n i) (hs : ∀ n, ∑ i, w n i ≤ M)
    (ha : ∀ n i, a n i ∈ K) :
    ∃ u : L1, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (fun n => ∑ i, w (σ n) i • logKernelL1 R (a (σ n) i)) atTop (𝓝 u) := by
  obtain ⟨u, _, σ, hσ, hu⟩ := (isCompact_potentialCompactSet hK R M).tendsto_subseq
    (fun n => sum_logKernel_mem_potentialCompactSet hM (hw n) (hs n) (ha n))
  exact ⟨u, σ, hσ, hu⟩

theorem norm_logKernelL1 (R : ℝ) (a : ℂ) :
    ‖logKernelL1 R a‖ = ‖cutoffLogL1 R‖ := by
  exact DomAddAct.norm_vadd_Lp _ _

theorem norm_sum_logKernel_le {ι : Type*} (s : Finset ι) {w : ι → ℝ}
    (a : ι → ℂ) (R : ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    ‖∑ i ∈ s, w i • logKernelL1 R (a i)‖ ≤ (∑ i ∈ s, w i) * ‖cutoffLogL1 R‖ := by
  calc
    _ ≤ ∑ i ∈ s, ‖w i • logKernelL1 R (a i)‖ := norm_sum_le _ _
    _ = ∑ i ∈ s, w i * ‖cutoffLogL1 R‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_smul, norm_logKernelL1, Real.norm_eq_abs, abs_of_nonneg (hw i hi)]
    _ = _ := (Finset.sum_mul ..).symm

theorem coeFn_finset_sum_ae {ι : Type*} (s : Finset ι) (g : ι → L1) :
    ((∑ i ∈ s, g i : L1) : ℂ → ℝ) =ᵐ[volume] fun z => ∑ i ∈ s, g i z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℝ 1 (volume : Measure ℂ)] with z hz
    simpa only [Finset.sum_empty, Pi.zero_apply] using hz
  | @insert i s his ih =>
    simp only [Finset.sum_insert his]
    filter_upwards [Lp.coeFn_add (g i) (∑ j ∈ s, g j), ih] with z hz hz'
    simpa only [Pi.add_apply, hz'] using hz

theorem sum_logKernel_ae_eq_on {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (a : ι → ℂ) {K : Set ℂ} (hKm : MeasurableSet K) {R : ℝ}
    (hcut : ∀ i ∈ s, ∀ z ∈ K, ‖z - a i‖ < R) :
    ((∑ i ∈ s, w i • logKernelL1 R (a i) : L1) : ℂ → ℝ) =ᵐ[volume.restrict K]
      fun z => ∑ i ∈ s, w i * Real.log ‖z - a i‖ := by
  have ht : ∀ i ∈ s, ((w i • logKernelL1 R (a i) : L1) : ℂ → ℝ) =ᵐ[volume.restrict K]
      fun z => w i * Real.log ‖z - a i‖ := by
    intro i hi
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul (w i) (logKernelL1 R (a i))),
      logKernelL1_ae_eq_on hKm (hcut i hi)] with z hz hz'
    simpa only [Pi.smul_apply, smul_eq_mul, hz'] using hz
  filter_upwards [ae_restrict_of_ae (coeFn_finset_sum_ae s
      (fun i => w i • logKernelL1 R (a i))), (eventually_all_finset s).mpr ht] with z hz ht'
  rw [hz]
  exact Finset.sum_congr rfl fun i hi => ht' i hi

end V10.ScalarCompactnessLogPotential
