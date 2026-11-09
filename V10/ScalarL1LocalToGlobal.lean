import V10.ScalarL1Convergence
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! Local disk L¹ convergence implies L¹ convergence on every compact subset.
This finite-cover step avoids an unnecessary global diagonal subsequence when
the local limit has already been uniquely identified. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology
namespace V10.ScalarL1LocalToGlobal
set_option backward.isDefEq.respectTransparency false

theorem integral_finset_union_le {α κ : Type*} [MeasurableSpace α]
    {μ : Measure α} (t : Finset κ) {D : κ → Set α} {f : α → ℝ}
    (hf : ∀ z, 0 ≤ f z) (hi : ∀ k ∈ t, IntegrableOn f (D k) μ) :
    (∫ z in ⋃ k ∈ t, D k, f z ∂μ) ≤ ∑ k ∈ t, ∫ z in D k, f z ∂μ := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert a t hat ih =>
    have hia := hi a (Finset.mem_insert_self a t)
    have hit : ∀ k ∈ t, IntegrableOn f (D k) μ := fun k hk => hi k (Finset.mem_insert_of_mem hk)
    have hiU : IntegrableOn f (⋃ k ∈ t, D k) μ := integrableOn_finset_iUnion.mpr hit
    have hm := integral_mono_measure (μ.restrict_union_le (D a) (⋃ k ∈ t, D k))
      (ae_of_all _ hf) (integrable_add_measure.mpr ⟨hia, hiU⟩)
    rw [integral_add_measure hia hiU] at hm
    simpa only [Finset.set_biUnion_insert, Finset.sum_insert hat] using
      hm.trans (add_le_add_right (ih hit) _)

theorem L1_on_compacts_of_eventual_local_disks {ι : Type*} {l : Filter ι}
    {u : ι → ℂ → ℝ} {H : ℂ → ℝ} {S : Set ℂ}
    (hlocal : ∀ x ∈ S, ∃ r > 0, closedBall x r ⊆ S ∧
      (∀ᶠ i in l, IntegrableOn (fun z => ‖u i z - H z‖) (closedBall x r)) ∧
      Tendsto (fun i => ∫ z in closedBall x r, ‖u i z - H z‖) l (𝓝 0)) :
    ∀ K, IsCompact K → K ⊆ S →
      Tendsto (fun i => ∫ z in K, ‖u i z - H z‖) l (𝓝 0) := by
  intro K hK hKS
  classical
  choose r hr hball hi hconv using (fun x : K => hlocal x (hKS x.property))
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => ball (x : ℂ) (r x))
    (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr ⟨x, hx⟩)⟩)
  let D : Set ℂ := ⋃ x ∈ t, closedBall (x : ℂ) (r x)
  have hKD : K ⊆ D := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_iUnion₂.mpr ⟨y, hy, ball_subset_closedBall hxy⟩
  have hie : ∀ᶠ i in l, ∀ x ∈ t,
      IntegrableOn (fun z => ‖u i z - H z‖) (closedBall (x : ℂ) (r x)) :=
    (eventually_all_finset t).mpr (fun x _ => hi x)
  have hb : ∀ᶠ i in l, (∫ z in K, ‖u i z - H z‖) ≤
      ∑ x ∈ t, ∫ z in closedBall (x : ℂ) (r x), ‖u i z - H z‖ := by
    filter_upwards [hie] with i hi'
    have hib : IntegrableOn (fun z => ‖u i z - H z‖) D := integrableOn_finset_iUnion.mpr hi'
    have hm := setIntegral_mono_set hib (ae_of_all _ fun _ => norm_nonneg _)
      (ae_of_all _ fun _ hz => hKD hz)
    exact hm.trans (integral_finset_union_le t (fun _ => norm_nonneg _) hi')
  have htend : Tendsto (fun i => ∑ x ∈ t, ∫ z in closedBall (x : ℂ) (r x), ‖u i z - H z‖)
      l (𝓝 0) := by
    simpa using tendsto_finsetSum t (fun x _ => hconv x)
  exact squeeze_zero' (Eventually.of_forall (fun i => integral_nonneg (fun _ => norm_nonneg _))) hb htend

theorem L1_on_compacts_of_local_disks {ι : Type*} {l : Filter ι}
    {u : ι → ℂ → ℝ} {H : ℂ → ℝ} {S : Set ℂ}
    (hu : ∀ i, LocallyIntegrableOn (u i) S) (hH : LocallyIntegrableOn H S)
    (hlocal : ∀ x ∈ S, ∃ r > 0, closedBall x r ⊆ S ∧
      Tendsto (fun i => ∫ z in closedBall x r, ‖u i z - H z‖) l (𝓝 0)) :
    ∀ K, IsCompact K → K ⊆ S →
      Tendsto (fun i => ∫ z in K, ‖u i z - H z‖) l (𝓝 0) := by
  apply L1_on_compacts_of_eventual_local_disks
  intro x hx
  obtain ⟨r, hr, hsub, ht⟩ := hlocal x hx
  refine ⟨r, hr, hsub, Eventually.of_forall (fun i => ?_), ht⟩
  exact (((hu i).sub hH).norm).integrableOn_compact_subset hsub (isCompact_closedBall _ _)

#print axioms integral_finset_union_le
#print axioms L1_on_compacts_of_eventual_local_disks
#print axioms L1_on_compacts_of_local_disks
end V10.ScalarL1LocalToGlobal
