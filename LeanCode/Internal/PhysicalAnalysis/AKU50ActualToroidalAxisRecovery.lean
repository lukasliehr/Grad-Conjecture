import AKU49ActualAxialCorrectionOrder

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearProduct Grad.NonlinearDivision
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.SourceCollar Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Ledger

theorem axisDot_smul_right {parameters : PhaseParameters}
    (first second : Grad.AxisCore.AxisSmoothCore parameters 3) (scalar : ℂ) :
    axisDot first (scalar • second) = scalar • axisDot first second := by
  simp only [axisDot,axisConstantCore,map_smul]

theorem axisDot_eT {parameters : PhaseParameters} (data : Grad.AxisCore.AxisSmoothCore parameters 3) :
    axisDot data (traceZero (eTConstantCore parameters)) = axisComponent 1 data := by
  apply axisPhysicalValue_ext
  intro angle
  apply PiLp.ext
  intro component
  have only : component = 0 := Subsingleton.elim _ _
  subst component
  rw [axisDot_physical,traceZero_physical,axisComponent_physical,componentValue_apply]
  simp [eTConstantCore,coreValue_constant,Grad.NonlinearQuotient.complexDot]

theorem originalLiftPhysicalUAxis_toroidal (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3) (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (index : Fin 3) :
    axisComponent 1 (originalLiftPhysicalUAxis parameters length rho epsilon field low source index) =
      originalC2Axis length source index := by
  apply axisPhysicalValue_ext
  intro angle
  apply PiLp.ext
  intro component
  have only : component = 0 := Subsingleton.elim _ _
  subst component
  rw [axisComponent_physical,componentValue_apply,originalLiftPhysicalUAxis_physical]
  have margin := originalCoefficient_low_margin parameters length rho epsilon field
    (originalCubic_low_margin parameters length rho epsilon field low).1
  have inverse := fullColumn_dot_inverseTranspose
    (originalPhysicalFrameMatrix parameters length epsilon field angle closedOrigin)
    (familyMatrix (originalInverseFamily parameters length epsilon field) 0 angle closedOrigin)
    (originalInverseFamily_matrix_identity parameters length epsilon field margin.2.2 0 angle closedOrigin).2
    (axisCovectorValue
      (axisPhysicalValue (originalLiftPlanarAxis parameters length rho epsilon field low source index) angle)
      (axisPhysicalValue (originalC2Axis length source index) angle 0)) 2
  simpa [originalAxis_thirdColumn parameters length epsilon field vanishes angle,
    Grad.NonlinearQuotient.complexDot,Fin.sum_univ_three,axisCovectorValue] using inverse

theorem secondTaylorAxis_rotation_lift_dot {parameters : PhaseParameters}
    (data : Fin 3 → Grad.AxisCore.AxisSmoothCore parameters 3) (field : ACore parameters 3) :
    secondTaylorAxis (dotOperation parameters (rotationCore parameters (localizedQuadraticVectorAxisCore data)) field) =
      ![axisDot (data 1) (traceZero field),
        (2 : ℂ) • axisDot (data 2) (traceZero field) - (2 : ℂ) • axisDot (data 0) (traceZero field),
        -(axisDot (data 1) (traceZero field))] := by
  rw [localizedQuadraticVectorAxisCore_coordinates]
  funext index
  fin_cases index
  all_goals simp [rotationCore,partialCore_coordinateCore,secondTaylorAxis,map_add,map_sub,
    dot_coordinate_first,secondAxisTrace_two_coordinates,traceZero_coordinateCore,
    traceZero_dot_eq_axisDot,traceZero_localizedAxisConstantCore]
  all_goals module

end Grad.FinitePhysicalJetLift
