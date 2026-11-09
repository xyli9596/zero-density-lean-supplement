import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic

/-! A finite smooth decomposition of an actual compact test subordinate to
an arbitrary open cover. This supplies the local-to-global step for weak
Laplacian identities without assuming a decomposition of the test. -/
noncomputable section
set_option autoImplicit false
open Set
open scoped Topology ContDiff Manifold
namespace V10.SmoothTestLocalization

theorem finite_decomposition {ι : Type*} {U : ι → Set ℂ}
    (hU : ∀ i, IsOpen (U i)) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hcover : tsupport φ ⊆ ⋃ i, U i) :
    ∃ (t : Finset ι) (ψ : t → ℂ → ℝ),
      (∀ i, ContDiff ℝ ∞ (ψ i) ∧ HasCompactSupport (ψ i) ∧
        tsupport (ψ i) ⊆ U i ∧ tsupport (ψ i) ⊆ tsupport φ) ∧
      φ = ∑ i, ψ i := by
  classical
  obtain ⟨t, ht⟩ := hφc.elim_finite_subcover U hU hcover
  have htcover : tsupport φ ⊆ ⋃ i : t, U i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ℂ)
    (isClosed_tsupport φ) (fun i : t => U i) (fun i => hU i) htcover
  let ψ : t → ℂ → ℝ := fun i z => ρ i z * φ z
  have hψ (i : t) : ContDiff ℝ ∞ (ψ i) ∧ HasCompactSupport (ψ i) ∧
      tsupport (ψ i) ⊆ U i ∧ tsupport (ψ i) ⊆ tsupport φ := by
    have hr : ContDiff ℝ ∞ (ρ i) := contMDiff_iff_contDiff.mp (ρ i).contMDiff
    exact ⟨hr.mul hφ, hφc.mul_left,
      tsupport_mul_subset_left.trans (hρ i), tsupport_mul_subset_right⟩
  refine ⟨t, ψ, hψ, ?_⟩
  funext z
  simp only [Finset.sum_apply, ψ, ← Finset.sum_mul]
  by_cases hz : z ∈ tsupport φ
  · have he := ρ.sum_eq_one hz
    rw [finsum_eq_sum_of_fintype] at he
    rw [he, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]

/-- A property of smooth compact tests that is preserved under finite addition
can be verified on arbitrary pointwise neighborhoods of their support. -/
theorem of_local {P : (ℂ → ℝ) → Prop}
    (hzero : P 0)
    (hadd : ∀ f g : ℂ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      ContDiff ℝ ∞ g → HasCompactSupport g → P f → P g → P (f + g))
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hlocal : ∀ x ∈ tsupport φ, ∃ V : Set ℂ, IsOpen V ∧ x ∈ V ∧
      ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ V → P ψ) :
    P φ := by
  classical
  choose V hVo hxV hVP using fun x : tsupport φ => hlocal x x.property
  have hcover : tsupport φ ⊆ ⋃ x : tsupport φ, V x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxV _⟩
  obtain ⟨t, ψ, hψ, he⟩ := finite_decomposition hVo hφ hφc hcover
  rw [he]
  have hsum : ∀ s : Finset t,
      ContDiff ℝ ∞ (∑ i ∈ s, ψ i) ∧ HasCompactSupport (∑ i ∈ s, ψ i) ∧
      P (∑ i ∈ s, ψ i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (show ContDiff ℝ ∞ (0 : ℂ → ℝ) ∧
        HasCompactSupport (0 : ℂ → ℝ) ∧ P 0 from
        ⟨contDiff_const, HasCompactSupport.zero, hzero⟩)
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact ⟨(hψ i).1.add ih.1, (hψ i).2.1.add ih.2.1,
        hadd _ _ (hψ i).1 (hψ i).2.1 ih.1 ih.2.1
          (hVP i.val (ψ i) (hψ i).1 (hψ i).2.1 (hψ i).2.2.1) ih.2.2⟩
  exact (hsum Finset.univ).2.2

#print axioms finite_decomposition
#print axioms of_local
end V10.SmoothTestLocalization
