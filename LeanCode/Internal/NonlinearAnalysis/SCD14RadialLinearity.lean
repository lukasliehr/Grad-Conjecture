import SCD13LinearJetMaps

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators

namespace Grad.SourceCollarDivision

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRadial Grad.BoundaryTrace

def polarOpenStrip : Set (ℝ × ℝ) := {point | point.1 ∈ Ioo (0 : ℝ) 1}

theorem polarOpenStrip_isOpen : IsOpen polarOpenStrip :=
  isOpen_Ioo.preimage continuous_fst

theorem radialIter_congr {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (order : ℕ) (first second : ℝ × ℝ → Value) (agree : EqOn first second polarOpenStrip) :
    EqOn (radialIter order first) (radialIter order second) polarOpenStrip := by
  induction order with
  | zero => exact agree
  | succ order inductionHypothesis =>
    intro point inside
    have localEquality : radialIter order first =ᶠ[𝓝 point] radialIter order second :=
      Filter.eventually_of_mem (polarOpenStrip_isOpen.mem_nhds inside) inductionHypothesis
    change (fderiv ℝ (radialIter order first) point) (1, 0) =
      (fderiv ℝ (radialIter order second) point) (1, 0)
    rw [localEquality.fderiv_eq]

theorem radialIter_add {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (order : ℕ) (first second : ℝ × ℝ → Value)
    (firstSmooth : ContDiff ℝ ∞ first) (secondSmooth : ContDiff ℝ ∞ second) :
    radialIter order (first + second) = radialIter order first + radialIter order second := by
  induction order with
  | zero => rfl
  | succ order inductionHypothesis =>
    funext point
    simp only [radialIter_succ, inductionHypothesis, radialField, Pi.add_apply]
    rw [fderiv_add ((radialIter_smooth order first firstSmooth).differentiable (by simp) point)
      ((radialIter_smooth order second secondSmooth).differentiable (by simp) point)]
    rfl

theorem radialIter_smul {dimension : ℕ} (order : ℕ) (scalar : ℂ)
    (field : ℝ × ℝ → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ field) :
    radialIter order (scalar • field) = scalar • radialIter order field := by
  induction order with
  | zero => rfl
  | succ order inductionHypothesis =>
    funext point
    simp only [radialIter_succ, inductionHypothesis, radialField, Pi.smul_apply]
    have derivative := (((radialIter_smooth order field smooth).differentiable (by simp) point).hasFDerivAt.const_smul scalar).fderiv
    rw [derivative]
    rfl

theorem divided_radial_add {dimension : ℕ} (first second : ClosedJet dimension)
    (order : ℕ) (radius angle : ℝ) (inside : radius ∈ Ioo (0 : ℝ) 1) :
    radialIter order (dividedPolarValue (first + second)) (radius, angle) =
      radialIter order (dividedPolarValue first) (radius, angle) +
        radialIter order (dividedPolarValue second) (radius, angle) := by
  have agree : EqOn (dividedPolarValue (first + second))
      (dividedPolarValue first + dividedPolarValue second) polarOpenStrip := by
    intro point member
    exact dividedPolarValue_add_closed first second point.1 point.2 member.1.le member.2.le
  rw [radialIter_congr order _ _ agree (show (radius, angle) ∈ polarOpenStrip from inside),
    radialIter_add _ _ _ (dividedPolarValue_smooth _) (dividedPolarValue_smooth _)]
  rfl

theorem divided_radial_smul {dimension : ℕ} (scalar : ℂ) (field : ClosedJet dimension)
    (order : ℕ) (radius angle : ℝ) (inside : radius ∈ Ioo (0 : ℝ) 1) :
    radialIter order (dividedPolarValue (scalar • field)) (radius, angle) =
      scalar • radialIter order (dividedPolarValue field) (radius, angle) := by
  have agree : EqOn (dividedPolarValue (scalar • field))
      (scalar • dividedPolarValue field) polarOpenStrip := by
    intro point member
    exact dividedPolarValue_smul_closed scalar field point.1 point.2 member.1.le member.2.le
  rw [radialIter_congr order _ _ agree (show (radius, angle) ∈ polarOpenStrip from inside),
    radialIter_smul _ _ _ (dividedPolarValue_smooth _)]
  rfl

end Grad.SourceCollarDivision
