import AKBJ21ProjectedScalarAxisRemoval
import AKBD2ProjectedParameterCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 950000
open Set MeasureTheory
open scoped ContDiff Interval
namespace Grad.ActualScalarWeakEquations
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.SourceCollarFullSource Grad.BoundaryTrace

/-- Scalar P0 commutes with the genuine axial Fourier coefficient by double-coefficient Fubini. -/
theorem scalarProjection_axialCell (field : ℝ × ℝ → ℂ) (continuousField : Continuous field) (cell : ℤ) (polar : ℝ) :
    angularCoefficient (fun axial => removePolarMean field (polar,axial)) cell =
      angularCoefficient (fun axial => field (polar,axial)) cell -
        angularCoefficient (fun angle => angularCoefficient (fun axial => field (angle,axial)) cell) 0 := by
  have meanContinuous : Continuous (fun axial => angularCoefficient (fun angle => field (angle,axial)) 0) :=
    angularCoefficient_continuous_parameter (fun angles => field (angles.2,angles.1))
      (continuousField.comp (continuous_snd.prodMk continuous_fst)) 0
  have meanSame := (doubleCoefficient_swap field continuousField 0 cell).symm
  have subtraction := angularCoefficient_sub_general (fun axial => field (polar,axial))
    (fun axial => angularCoefficient (fun angle => field (angle,axial)) 0)
    (continuousField.comp (continuous_const.prodMk continuous_id)) meanContinuous cell
  exact subtraction.trans (congrArg (angularCoefficient (fun axial => field (polar,axial)) cell - ·) meanSame)

/-- The scalar Cartesian mean is the actual angular zero coefficient on every complete circle. -/
theorem scalarMean_polar (field : ClosedDisk → ComplexEuclidean 1)
    (radius : ℝ) (bounded : |radius| ≤ 1) (angle : ℝ) :
    closedAngularMean field (Grad.Constraints.polarClosedPoint radius bounded angle) =
      angularCoefficient (fun polar => field (Grad.Constraints.polarClosedPoint radius bounded polar)) 0 := by
  have periodic : Function.Periodic (fun polar => field (Grad.Constraints.polarClosedPoint radius bounded polar)) (2*Real.pi) := by
    intro polar
    exact congrArg field (Grad.Constraints.polarClosedPoint_periodic radius bounded polar)
  have invariant := closedAngularMean_rotation field angle (axisClosedPoint radius bounded)
  change closedAngularMean field (Grad.Constraints.polarClosedPoint radius bounded angle) = _ at invariant
  rw [invariant,closedAngularMean_interval,Grad.ActualCartesianWeakEquations.originalAngularMean_interval _ periodic]
  congr 1

end Grad.ActualScalarWeakEquations
