import AKO10CofinalCollarLogIntegral
import AKO12SameIncomingDensityLocality

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace Grad.AnnularIncomingIntegrability

/-- Canonical countable gluing of the actual nonnegative local densities. -/
def cofinalIncomingSquare (upper : ℝ) (collars : ℕ → ℝ) (localSquares : ℕ → ℝ → ℝ≥0∞) (radius : ℝ) : ℝ≥0∞ :=
  ⨆ index, (Icc (collars index) upper).indicator (localSquares index) radius

theorem cofinalIncomingSquare_measurable (upper : ℝ) (collars : ℕ → ℝ)
    (localSquares : ℕ → ℝ → ℝ≥0∞) (measurable : ∀ index, Measurable (localSquares index)) :
    Measurable (cofinalIncomingSquare upper collars localSquares) :=
  Measurable.iSup (fun index => (measurable index).indicator measurableSet_Icc)

theorem cofinalIncomingSquare_same (upper : ℝ) (collars : ℕ → ℝ)
    (localSquares : ℕ → ℝ → ℝ≥0∞)
    (compatible : ∀ first second radius, radius ∈ Icc (collars first) upper → radius ∈ Icc (collars second) upper →
      localSquares first radius = localSquares second radius)
    (index : ℕ) (radius : ℝ) (inside : radius ∈ Icc (collars index) upper) :
    cofinalIncomingSquare upper collars localSquares radius = localSquares index radius := by
  apply le_antisymm
  · apply iSup_le
    intro other
    by_cases member : radius ∈ Icc (collars other) upper
    · rw [indicator_of_mem member]
      exact (compatible other index radius member inside).le
    · rw [indicator_of_notMem member]
      exact zero_le
  · apply le_iSup_of_le index
    rw [indicator_of_mem inside]

theorem cofinalIncomingSquare_zero_outside (upper : ℝ) (collars : ℕ → ℝ)
    (positive : ∀ index, 0 < collars index) (localSquares : ℕ → ℝ → ℝ≥0∞)
    (radius : ℝ) (outside : radius ∉ Ioc 0 upper) :
    cofinalIncomingSquare upper collars localSquares radius = 0 := by
  apply le_antisymm _ zero_le
  apply iSup_le
  intro index
  have absent : radius ∉ Icc (collars index) upper := fun member => outside ⟨(positive index).trans_le member.1,member.2⟩
  rw [indicator_of_notMem absent]

theorem cofinalIncomingSquare_ne_top (upper : ℝ) (collars : ℕ → ℝ)
    (positive : ∀ index, 0 < collars index) (cofinal : Tendsto collars atTop (𝓝 0))
    (localSquares : ℕ → ℝ → ℝ≥0∞)
    (compatible : ∀ first second radius, radius ∈ Icc (collars first) upper → radius ∈ Icc (collars second) upper →
      localSquares first radius = localSquares second radius)
    (finite : ∀ index radius, radius ∈ Icc (collars index) upper → localSquares index radius ≠ ⊤)
    (radius : ℝ) : cofinalIncomingSquare upper collars localSquares radius ≠ ⊤ := by
  by_cases inside : radius ∈ Ioc 0 upper
  · obtain ⟨index,small⟩ := (cofinal.eventually (gt_mem_nhds inside.1)).exists
    rw [cofinalIncomingSquare_same upper collars localSquares compatible index radius ⟨small.le,inside.2⟩]
    exact finite index radius ⟨small.le,inside.2⟩
  · rw [cofinalIncomingSquare_zero_outside upper collars positive localSquares radius inside]
    exact ENNReal.zero_ne_top

/-- A genuine real incoming norm, determined by the full high-plus-low square. -/
def cofinalIncomingNorm (upper : ℝ) (collars : ℕ → ℝ) (localSquares : ℕ → ℝ → ℝ≥0∞) (radius : ℝ) : ℝ :=
  Real.sqrt (cofinalIncomingSquare upper collars localSquares radius).toReal

theorem cofinalIncomingNorm_measurable (upper : ℝ) (collars : ℕ → ℝ)
    (localSquares : ℕ → ℝ → ℝ≥0∞) (measurable : ∀ index, Measurable (localSquares index)) :
    Measurable (cofinalIncomingNorm upper collars localSquares) :=
  (cofinalIncomingSquare_measurable upper collars localSquares measurable).ennreal_toReal.sqrt

theorem cofinalIncomingNorm_nonnegative (upper : ℝ) (collars : ℕ → ℝ)
    (localSquares : ℕ → ℝ → ℝ≥0∞) (radius : ℝ) : 0 ≤ cofinalIncomingNorm upper collars localSquares radius :=
  Real.sqrt_nonneg _

theorem cofinalIncomingNorm_square (upper : ℝ) (collars : ℕ → ℝ)
    (localSquares : ℕ → ℝ → ℝ≥0∞) (radius : ℝ)
    (finite : cofinalIncomingSquare upper collars localSquares radius ≠ ⊤) :
    ENNReal.ofReal (cofinalIncomingNorm upper collars localSquares radius ^ 2) = cofinalIncomingSquare upper collars localSquares radius := by
  rw [cofinalIncomingNorm,Real.sq_sqrt ENNReal.toReal_nonneg,ENNReal.ofReal_toReal finite]

end Grad.AnnularIncomingIntegrability
