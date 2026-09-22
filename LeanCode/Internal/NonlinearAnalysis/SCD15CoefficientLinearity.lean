import SCD14RadialLinearity

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators

namespace Grad.SourceCollarDivision

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRadial Grad.BoundaryTrace

theorem angularCoefficient_add_continuous {dimension : ℕ}
    (first second : ℝ → ComplexEuclidean dimension)
    (firstContinuous : Continuous first) (secondContinuous : Continuous second) (mode : ℤ) :
    angularCoefficient (first + second) mode = angularCoefficient first mode + angularCoefficient second mode := by
  simp only [angularCoefficient_compact, Pi.add_apply, smul_add]
  rw [integral_add]
  · exact smul_add _ _ _
  · exact ((cellExponential_smooth (-mode)).continuous.smul firstContinuous).continuousOn.integrableOn_Icc
  · exact ((cellExponential_smooth (-mode)).continuous.smul secondContinuous).continuousOn.integrableOn_Icc

theorem angularCoefficient_smul_continuous {dimension : ℕ}
    (scalar : ℂ) (field : ℝ → ComplexEuclidean dimension) (mode : ℤ) :
    angularCoefficient (scalar • field) mode = scalar • angularCoefficient field mode := by
  simp only [angularCoefficient_compact, Pi.smul_apply]
  calc
    _ = (2 * Real.pi)⁻¹ •
        (∫ angle in Icc (-Real.pi) Real.pi, scalar • (cellExponential (-mode) angle • field angle)) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with angle
      exact smul_comm _ _ _
    _ = _ := by rw [integral_smul]; exact smul_comm _ _ _

theorem dividedCoefficient_add {dimension : ℕ} (first second : ClosedJet dimension)
    (mode : ℤ) (order : ℕ) (radius : ℝ) (inside : radius ∈ Ioo (0 : ℝ) 1) :
    radialCoefficientJet (dividedPolarValue (first + second)) mode order radius =
      radialCoefficientJet (dividedPolarValue first) mode order radius +
        radialCoefficientJet (dividedPolarValue second) mode order radius := by
  have functionEquality : (fun angle => radialIter order (dividedPolarValue (first + second)) (radius, angle)) =
      (fun angle => radialIter order (dividedPolarValue first) (radius, angle)) +
        (fun angle => radialIter order (dividedPolarValue second) (radius, angle)) := by
    funext angle
    exact divided_radial_add first second order radius angle inside
  rw [radialCoefficientJet, functionEquality]
  exact angularCoefficient_add_continuous _ _
    ((radialIter_smooth order _ (dividedPolarValue_smooth _)).continuous.comp (continuous_const.prodMk continuous_id))
    ((radialIter_smooth order _ (dividedPolarValue_smooth _)).continuous.comp (continuous_const.prodMk continuous_id)) mode

theorem dividedCoefficient_smul {dimension : ℕ} (scalar : ℂ) (field : ClosedJet dimension)
    (mode : ℤ) (order : ℕ) (radius : ℝ) (inside : radius ∈ Ioo (0 : ℝ) 1) :
    radialCoefficientJet (dividedPolarValue (scalar • field)) mode order radius =
      scalar • radialCoefficientJet (dividedPolarValue field) mode order radius := by
  have functionEquality : (fun angle => radialIter order (dividedPolarValue (scalar • field)) (radius, angle)) =
      scalar • (fun angle => radialIter order (dividedPolarValue field) (radius, angle)) := by
    funext angle
    exact divided_radial_smul scalar field order radius angle inside
  rw [radialCoefficientJet, functionEquality]
  exact angularCoefficient_smul_continuous scalar _ mode

theorem weightedDividedCoefficient_add {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (first second : ClosedJet dimension) (mode : ℤ) (order : ℕ)
    (radius : ℝ) (inside : radius ∈ Ioo (0 : ℝ) 1) :
    radialCoefficientJet (dividedPolarValue (phaseWeightedJet parameters cell (first + second))) mode order radius =
      radialCoefficientJet (dividedPolarValue (phaseWeightedJet parameters cell first)) mode order radius +
        radialCoefficientJet (dividedPolarValue (phaseWeightedJet parameters cell second)) mode order radius := by
  rw [show phaseWeightedJet parameters cell (first + second) =
    phaseWeightedJet parameters cell first + phaseWeightedJet parameters cell second from
      (phaseWeightedJetLinear parameters cell).map_add first second]
  exact dividedCoefficient_add _ _ mode order radius inside

theorem weightedDividedCoefficient_smul {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (scalar : ℂ) (field : ClosedJet dimension) (mode : ℤ) (order : ℕ)
    (radius : ℝ) (inside : radius ∈ Ioo (0 : ℝ) 1) :
    radialCoefficientJet (dividedPolarValue (phaseWeightedJet parameters cell (scalar • field))) mode order radius =
      scalar • radialCoefficientJet (dividedPolarValue (phaseWeightedJet parameters cell field)) mode order radius := by
  rw [show phaseWeightedJet parameters cell (scalar • field) =
    scalar • phaseWeightedJet parameters cell field from (phaseWeightedJetLinear parameters cell).map_smul scalar field]
  exact dividedCoefficient_smul scalar _ mode order radius inside

end Grad.SourceCollarDivision
