import ARC1HalfInverseChart

noncomputable section
open Set Filter
open scoped BigOperators ContDiff Topology
namespace Grad.CollarCartesian
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints Grad.BoundaryLift

theorem reverseCollar_axis_derivative_bound {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] (field : SpatialPlane → Value) (smooth : ContDiff ℝ ∞ field)
    (grade order : ℕ) (upper : order ≤ grade) (radius : ℝ) (inside : radius ∈ Icc (1 / 2 : ℝ) 1) :
    ‖iteratedFDeriv ℝ order field (collarAxis radius)‖ ≤
      order.factorial * polarJetEnvelope (field ∘ collarPlane) grade (1 - radius, 0) *
        inverseChartBound grade ^ order := by
  have positive : 0 < radius := by linarith [inside.1]
  have chartMember : collarAxis radius ∈ rightHalfPlane := positive
  have inverseSmooth : ContDiffOn ℝ ∞ inverseCollarChart rightHalfPlane :=
    fun point pointIn => (inverseCollarChart_smoothAt point pointIn).contDiffWithinAt
  have outerBounds : ∀ index, index ≤ order →
      ‖iteratedFDerivWithin ℝ index (field ∘ collarPlane) univ
        (inverseCollarChart (collarAxis radius))‖ ≤
          polarJetEnvelope (field ∘ collarPlane) grade (1 - radius, 0) := by
    intro index indexBound
    rw [iteratedFDerivWithin_univ, inverseCollarChart_axis radius positive]
    exact polarJetEnvelope_bound _ grade index (indexBound.trans upper) _
  have innerBounds : ∀ index, 1 ≤ index → index ≤ order →
      ‖iteratedFDerivWithin ℝ index inverseCollarChart rightHalfPlane (collarAxis radius)‖ ≤
        inverseChartBound grade ^ index := by
    intro index indexPositive indexBound
    rw [iteratedFDerivWithin_of_isOpen index rightHalfPlane_open chartMember]
    apply (inverseChart_derivative_bound grade index (indexBound.trans upper) radius inside).trans
    simpa only [pow_one] using pow_le_pow_right₀ (inverseChartBound_one_le grade) indexPositive
  have composite := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (n := order) (N := ∞)
    (s := rightHalfPlane) (t := univ) (smooth.comp collarPlane_smooth).contDiffOn inverseSmooth
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤)) uniqueDiffOn_univ
    rightHalfPlane_open.uniqueDiffOn (mapsTo_univ _ _) chartMember outerBounds innerBounds
  rw [iteratedFDerivWithin_of_isOpen order rightHalfPlane_open chartMember] at composite
  have agreement : ((field ∘ collarPlane) ∘ inverseCollarChart) =ᶠ[𝓝 (collarAxis radius)] field := by
    filter_upwards [rightHalfPlane_open.mem_nhds chartMember] with point pointIn
    change field (collarPlane (inverseCollarChart point)) = field point
    rw [collarPlane_inverseCollarChart point pointIn]
  rw [(agreement.iteratedFDeriv (𝕜 := ℝ) order).eq_of_nhds] at composite
  exact composite

end Grad.CollarCartesian
