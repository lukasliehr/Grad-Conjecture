import RSC4AllCellEnergy

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators
namespace Grad.SourceCollarRestriction
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.BoundaryTrace
open Grad.SourceCollarDivision

theorem originalPolarValue_add_closed {dimension : ℕ} (first second : ClosedJet dimension)
    (radius angle : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    originalPolarValue (first + second) (radius, angle) =
      originalPolarValue first (radius, angle) + originalPolarValue second (radius, angle) := by
  rw [originalPolarValue_closed _ _ _ nonnegative bounded,
    originalPolarValue_closed _ _ _ nonnegative bounded, originalPolarValue_closed _ _ _ nonnegative bounded]
  rfl

theorem originalPolarValue_smul_closed {dimension : ℕ} (scalar : ℂ) (field : ClosedJet dimension)
    (radius angle : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    originalPolarValue (scalar • field) (radius, angle) = scalar • originalPolarValue field (radius, angle) := by
  rw [originalPolarValue_closed _ _ _ nonnegative bounded, originalPolarValue_closed _ _ _ nonnegative bounded]
  rfl

theorem polar_radial_add {dimension : ℕ} (first second : ClosedJet dimension)
    (order : ℕ) (radius angle : ℝ) (inside : radius ∈ Ioo (0 : ℝ) 1) :
    radialIter order (originalPolarValue (first + second)) (radius, angle) =
      radialIter order (originalPolarValue first) (radius, angle) +
        radialIter order (originalPolarValue second) (radius, angle) := by
  have agree : EqOn (originalPolarValue (first + second))
      (originalPolarValue first + originalPolarValue second) polarOpenStrip := by
    intro point member
    exact originalPolarValue_add_closed first second point.1 point.2 member.1.le member.2.le
  rw [radialIter_congr order _ _ agree (show (radius, angle) ∈ polarOpenStrip from inside),
    radialIter_add _ _ _ (originalPolarValue_smooth _) (originalPolarValue_smooth _)]
  rfl

theorem polar_radial_smul {dimension : ℕ} (scalar : ℂ) (field : ClosedJet dimension)
    (order : ℕ) (radius angle : ℝ) (inside : radius ∈ Ioo (0 : ℝ) 1) :
    radialIter order (originalPolarValue (scalar • field)) (radius, angle) =
      scalar • radialIter order (originalPolarValue field) (radius, angle) := by
  have agree : EqOn (originalPolarValue (scalar • field))
      (scalar • originalPolarValue field) polarOpenStrip := by
    intro point member
    exact originalPolarValue_smul_closed scalar field point.1 point.2 member.1.le member.2.le
  rw [radialIter_congr order _ _ agree (show (radius, angle) ∈ polarOpenStrip from inside),
    radialIter_smul _ _ _ (originalPolarValue_smooth _)]
  rfl

theorem polarCoefficient_add {dimension : ℕ} (first second : ClosedJet dimension)
    (mode : ℤ) (order : ℕ) (radius : ℝ) (inside : radius ∈ Ioo (0 : ℝ) 1) :
    radialCoefficientJet (originalPolarValue (first + second)) mode order radius =
      radialCoefficientJet (originalPolarValue first) mode order radius +
        radialCoefficientJet (originalPolarValue second) mode order radius := by
  have functionEquality : (fun angle => radialIter order (originalPolarValue (first + second)) (radius, angle)) =
      (fun angle => radialIter order (originalPolarValue first) (radius, angle)) +
        (fun angle => radialIter order (originalPolarValue second) (radius, angle)) := by
    funext angle
    exact polar_radial_add first second order radius angle inside
  rw [radialCoefficientJet, functionEquality]
  exact angularCoefficient_add_continuous _ _
    ((radialIter_smooth order _ (originalPolarValue_smooth _)).continuous.comp (continuous_const.prodMk continuous_id))
    ((radialIter_smooth order _ (originalPolarValue_smooth _)).continuous.comp (continuous_const.prodMk continuous_id)) mode

theorem polarCoefficient_smul {dimension : ℕ} (scalar : ℂ) (field : ClosedJet dimension)
    (mode : ℤ) (order : ℕ) (radius : ℝ) (inside : radius ∈ Ioo (0 : ℝ) 1) :
    radialCoefficientJet (originalPolarValue (scalar • field)) mode order radius =
      scalar • radialCoefficientJet (originalPolarValue field) mode order radius := by
  have functionEquality : (fun angle => radialIter order (originalPolarValue (scalar • field)) (radius, angle)) =
      scalar • (fun angle => radialIter order (originalPolarValue field) (radius, angle)) := by
    funext angle
    exact polar_radial_smul scalar field order radius angle inside
  rw [radialCoefficientJet, functionEquality]
  exact angularCoefficient_smul_continuous scalar _ mode

theorem weightedPolarCoefficient_add {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (first second : ClosedJet dimension) (mode : ℤ) (order : ℕ)
    (radius : ℝ) (inside : radius ∈ Ioo (0 : ℝ) 1) :
    radialCoefficientJet (originalPolarValue (phaseWeightedJet parameters cell (first + second))) mode order radius =
      radialCoefficientJet (originalPolarValue (phaseWeightedJet parameters cell first)) mode order radius +
        radialCoefficientJet (originalPolarValue (phaseWeightedJet parameters cell second)) mode order radius := by
  rw [show phaseWeightedJet parameters cell (first + second) =
    phaseWeightedJet parameters cell first + phaseWeightedJet parameters cell second from
      (phaseWeightedJetLinear parameters cell).map_add first second]
  exact polarCoefficient_add _ _ mode order radius inside

theorem weightedPolarCoefficient_smul {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (scalar : ℂ) (field : ClosedJet dimension) (mode : ℤ) (order : ℕ)
    (radius : ℝ) (inside : radius ∈ Ioo (0 : ℝ) 1) :
    radialCoefficientJet (originalPolarValue (phaseWeightedJet parameters cell (scalar • field))) mode order radius =
      scalar • radialCoefficientJet (originalPolarValue (phaseWeightedJet parameters cell field)) mode order radius := by
  rw [show phaseWeightedJet parameters cell (scalar • field) =
    scalar • phaseWeightedJet parameters cell field from (phaseWeightedJetLinear parameters cell).map_smul scalar field]
  exact polarCoefficient_smul scalar _ mode order radius inside


end Grad.SourceCollarRestriction
