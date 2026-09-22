import AKS7ExactWeightedFamilyUniqueness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators
namespace Grad.PuncturedRetainedEnergy
open Grad.AnnularIncomingIntegrability

/-- The canonical countable gluing also works for actual L2 representatives:
only equality almost everywhere on each overlap is needed. -/
theorem cofinalSquare_same_ae (upper : ℝ) (collars : ℕ → ℝ)
    (squares : ℕ → ℝ → ℝ≥0∞)
    (compatible : ∀ first second, squares first =ᵐ[volume.restrict (Icc (max (collars first) (collars second)) upper)] squares second)
    (index : ℕ) :
    cofinalIncomingSquare upper collars squares =ᵐ[volume.restrict (Icc (collars index) upper)] squares index := by
  have overlap : ∀ other, ∀ᵐ radius ∂volume.restrict (Icc (collars index) upper),
      radius ∈ Icc (collars other) upper → squares other radius = squares index radius := by
    intro other
    have same := (ae_restrict_iff' measurableSet_Icc).mp (compatible other index)
    filter_upwards [same.filter_mono (ae_mono Measure.restrict_le_self), ae_restrict_mem measurableSet_Icc]
      with radius same inside member
    exact same ⟨max_le member.1 inside.1,inside.2⟩
  filter_upwards [ae_all_iff.mpr overlap, ae_restrict_mem measurableSet_Icc] with radius same inside
  apply le_antisymm
  · apply iSup_le
    intro other
    by_cases member : radius ∈ Icc (collars other) upper
    · rw [indicator_of_mem member]
      exact (same other member).le
    · rw [indicator_of_notMem member]
      exact zero_le
  · exact le_iSup_of_le index (by rw [indicator_of_mem inside])

/-- The outer scalar coordinate is included exactly once in the monotone
cofinal energy, rather than being counted once for every collar. -/
theorem cofinalEnergy_eq_iSup (upper : ℝ) (collars : ℕ → ℝ)
    (positive : ∀ index, 0 < collars index) (decreasing : Antitone collars)
    (cofinal : Tendsto collars atTop (𝓝 0)) (density : ℝ → ℝ≥0∞) (outer : ℝ≥0∞) :
    (∫⁻ radius, density radius ∂volume.restrict (Ioc 0 upper)) + outer =
      ⨆ index, (∫⁻ radius, density radius ∂volume.restrict (Icc (collars index) upper)) + outer := by
  have cover : (⋃ index, Icc (collars index) upper) = Ioc 0 upper := by
    ext radius
    constructor
    · rintro ⟨_,⟨index,rfl⟩,inside⟩
      exact ⟨(positive index).trans_le inside.1,inside.2⟩
    · intro inside
      obtain ⟨index,small⟩ := (cofinal.eventually (gt_mem_nhds inside.1)).exists
      exact mem_iUnion.mpr ⟨index,small.le,inside.2⟩
  have directed : Directed (· ⊆ ·) (fun index => Icc (collars index) upper) := by
    intro first second
    refine ⟨max first second,?_,?_⟩
    · exact fun _ inside => ⟨(decreasing (le_max_left _ _)).trans inside.1,inside.2⟩
    · exact fun _ inside => ⟨(decreasing (le_max_right _ _)).trans inside.1,inside.2⟩
  rw [← cover,setLIntegral_iUnion_of_directed _ directed,ENNReal.iSup_add]

/-- The unchanged uniform fixed-collar constant bounds the global energy. -/
theorem cofinalEnergy_bound (upper : ℝ) (collars : ℕ → ℝ)
    (positive : ∀ index, 0 < collars index) (decreasing : Antitone collars)
    (cofinal : Tendsto collars atTop (𝓝 0)) (density : ℝ → ℝ≥0∞) (outer bound : ℝ≥0∞)
    (fixed : ∀ index, (∫⁻ radius, density radius ∂volume.restrict (Icc (collars index) upper)) + outer ≤ bound) :
    (∫⁻ radius, density radius ∂volume.restrict (Ioc 0 upper)) + outer ≤ bound := by
  rw [cofinalEnergy_eq_iSup upper collars positive decreasing cofinal density outer]
  exact iSup_le fixed

end Grad.PuncturedRetainedEnergy
