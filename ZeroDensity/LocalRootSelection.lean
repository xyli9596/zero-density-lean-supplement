import CRGIndicatorPartition
import Mathlib.Order.Interval.Set.Infinite

/-! The root selection used in manuscript Theorem 3.1.

The selection is defined by equality on nonempty open intervals. Continuity
and the finite root alternatives prove that it is nonempty and still covers
every direction, including collision directions. The analytic assertion
that a solution's indicator has these alternatives is not assumed proved.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology

namespace ZeroDensity.LocalRootSelection
open CRGIndicatorPartition CRGPhaseDirections
attribute [local instance] Classical.propDecidable

def projection (μ : ℂ) (θ : ℝ) : ℝ := leadingReal μ 1 θ

theorem projection_eq (μ : ℂ) (θ : ℝ) :
    projection μ θ = (μ * Complex.exp ((θ : ℂ) * Complex.I)).re := by
  simp [projection, leadingReal]

def selected (roots : Finset ℂ) (h : ℝ → ℝ) (l u : ℝ) : Finset ℂ :=
  roots.filter fun μ => ∃ a b : ℝ, a < b ∧ Ioo a b ⊆ Ioo l u ∧
    ∀ θ ∈ Ioo a b, h θ = projection μ θ

theorem selected_subset (roots : Finset ℂ) (h : ℝ → ℝ) (l u : ℝ) :
    selected roots h l u ⊆ roots := by
  exact Finset.filter_subset _ _

theorem local_selection (roots : Finset ℂ) {h : ℝ → ℝ} {l u θ : ℝ}
    (hh : ContinuousOn h (Ioo l u))
    (halt : ∀ x ∈ Ioo l u, ∃ μ ∈ roots, h x = projection μ x)
    (hθ : θ ∈ Ioo l u)
    (hnot : θ ∉ collisionDirections roots 1 l u) :
    ∃ μ ∈ selected roots h l u, ∃ a b : ℝ,
      θ ∈ Ioo a b ∧ Ioo a b ⊆ Ioo l u ∧
        ∀ x ∈ Ioo a b, h x = projection μ x := by
  have hf : (collisionDirections roots 1 l u).Finite :=
    collisionDirections_finite roots (by norm_num)
  have hn : Ioo l u ∩ (collisionDirections roots 1 l u)ᶜ ∈ 𝓝 θ :=
    (isOpen_Ioo.inter hf.isClosed.isOpen_compl).mem_nhds ⟨hθ, hnot⟩
  obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhds_iff.mp hn
  let a := θ - δ / 2
  let b := θ + δ / 2
  have hab : a < b := by dsimp [a, b]; linarith
  have hsub : Ioo a b ⊆ Ioo l u ∩ (collisionDirections roots 1 l u)ᶜ := by
    intro x hx
    apply hd
    rw [mem_ball, Real.dist_eq, abs_lt]
    dsimp [a, b] at hx
    constructor <;> linarith [hx.1, hx.2]
  obtain ⟨μ, hμ⟩ := one_alternative_on_preconnected isPreconnected_Ioo
    (nonempty_Ioo.mpr hab) h (fun μ : roots => projection μ.val)
    (hh.mono fun x hx => (hsub hx).1)
    (fun μ => (CRGIndicatorAlternatives.continuous_leadingReal μ.val 1).continuousOn)
    (fun x hx => by
      obtain ⟨μ, hm, he⟩ := halt x (hsub hx).1
      exact ⟨⟨μ, hm⟩, he⟩)
    (by
      intro x hx μ ν he
      apply Subtype.ext
      by_contra hne
      exact (hsub hx).2 ⟨⟨(hsub hx).1.1.le, (hsub hx).1.2.le⟩,
        μ.val, μ.property, ν.val, ν.property, hne, he⟩)
  refine ⟨μ.val, Finset.mem_filter.mpr ⟨μ.property, a, b, hab,
    (fun x hx => (hsub hx).1), hμ⟩, a, b, ?_,
    (fun x hx => (hsub hx).1), hμ⟩
  dsimp [a, b]
  constructor <;> linarith

/-- All directions are represented by an actually selected root. Roots that
only fit an isolated direction need not be inserted into the selection. -/
theorem selected_covers (roots : Finset ℂ) {h : ℝ → ℝ} {l u : ℝ}
    (hh : ContinuousOn h (Ioo l u))
    (halt : ∀ x ∈ Ioo l u, ∃ μ ∈ roots, h x = projection μ x)
    {θ : ℝ} (hθ : θ ∈ Ioo l u) :
    ∃ μ ∈ selected roots h l u, h θ = projection μ θ := by
  classical
  by_contra hnone
  have hne : ∀ μ ∈ selected roots h l u, h θ - projection μ θ ≠ 0 := by
    intro μ hμ he
    exact hnone ⟨μ, hμ, sub_eq_zero.mp he⟩
  have hc : ContinuousAt h θ := hh.continuousAt (isOpen_Ioo.mem_nhds hθ)
  have he : ∀ᶠ x in 𝓝 θ, ∀ μ ∈ selected roots h l u,
      h x - projection μ x ≠ 0 := by
    rw [Filter.eventually_all_finset]
    intro μ hμ
    have ht := hc.sub (CRGIndicatorAlternatives.continuous_leadingReal μ 1).continuousAt
    exact ht.eventually_ne (hne μ hμ)
  have hn : {x | x ∈ Ioo l u ∧ ∀ μ ∈ selected roots h l u,
      h x - projection μ x ≠ 0} ∈ 𝓝 θ := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ, he] with x hx he
    exact ⟨hx, he⟩
  obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhds_iff.mp hn
  have hf : (collisionDirections roots 1 l u).Finite :=
    collisionDirections_finite roots (by norm_num)
  obtain ⟨x, hx, hnx⟩ := ((Ioo_infinite (show θ - δ < θ + δ by linarith)).sdiff hf).nonempty
  have hxd : x ∈ ball θ δ := by
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  have hv := hd hxd
  obtain ⟨μ, hm, a, b, hxI, _hsub, hform⟩ := local_selection roots hh halt hv.1 hnx
  exact hv.2 μ hm (sub_eq_zero.mpr (hform x hxI))

theorem selected_nonempty (roots : Finset ℂ) {h : ℝ → ℝ} {l u : ℝ}
    (hlu : l < u) (hh : ContinuousOn h (Ioo l u))
    (halt : ∀ x ∈ Ioo l u, ∃ μ ∈ roots, h x = projection μ x) :
    (selected roots h l u).Nonempty := by
  obtain ⟨θ, hθ⟩ := nonempty_Ioo.mpr hlu
  obtain ⟨μ, hμ, _⟩ := selected_covers roots hh halt hθ
  exact ⟨μ, hμ⟩

#print axioms local_selection
#print axioms selected_covers
#print axioms selected_nonempty
end ZeroDensity.LocalRootSelection
