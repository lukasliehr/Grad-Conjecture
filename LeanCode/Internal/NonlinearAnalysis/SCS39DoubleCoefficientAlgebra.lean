import SCS38PhysicalCorrection

noncomputable section
open Set MeasureTheory

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace

variable {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]

def doubleCoefficient (field : ℝ × ℝ → Value) (mode : ℤ × ℤ) : Value :=
  angularCoefficient (fun polar => angularCoefficient (fun axial => field (polar, axial)) mode.2) mode.1

theorem angularCoefficient_add_general (first second : ℝ → Value)
    (firstContinuous : Continuous first) (secondContinuous : Continuous second) (mode : ℤ) :
    angularCoefficient (fun angle => first angle + second angle) mode =
      angularCoefficient first mode + angularCoefficient second mode := by
  simp_rw [angularCoefficient_compact_general, smul_add]
  have firstIntegrable : IntegrableOn (fun angle => cellExponential (-mode) angle • first angle)
      (Icc (-Real.pi) Real.pi) :=
    (((cellExponential_smooth (-mode)).continuous.smul firstContinuous).continuousOn.integrableOn_Icc)
  have secondIntegrable : IntegrableOn (fun angle => cellExponential (-mode) angle • second angle)
      (Icc (-Real.pi) Real.pi) :=
    (((cellExponential_smooth (-mode)).continuous.smul secondContinuous).continuousOn.integrableOn_Icc)
  rw [integral_add firstIntegrable secondIntegrable, smul_add]

theorem doubleCoefficient_add (first second : ℝ × ℝ → Value)
    (firstContinuous : Continuous first) (secondContinuous : Continuous second) (mode : ℤ × ℤ) :
    doubleCoefficient (fun angles => first angles + second angles) mode =
      doubleCoefficient first mode + doubleCoefficient second mode := by
  have inner (polar : ℝ) := angularCoefficient_add_general (fun axial => first (polar, axial))
    (fun axial => second (polar, axial)) (firstContinuous.comp (continuous_const.prodMk continuous_id))
    (secondContinuous.comp (continuous_const.prodMk continuous_id)) mode.2
  unfold doubleCoefficient
  simp_rw [inner]
  exact angularCoefficient_add_general _ _
    (angularCoefficient_continuous_parameter first firstContinuous mode.2)
    (angularCoefficient_continuous_parameter second secondContinuous mode.2) mode.1

theorem doubleCoefficient_sub (first second : ℝ × ℝ → Value)
    (firstContinuous : Continuous first) (secondContinuous : Continuous second) (mode : ℤ × ℤ) :
    doubleCoefficient (fun angles => first angles - second angles) mode =
      doubleCoefficient first mode - doubleCoefficient second mode := by
  have inner (polar : ℝ) := angularCoefficient_sub_general (fun axial => first (polar, axial))
    (fun axial => second (polar, axial)) (firstContinuous.comp (continuous_const.prodMk continuous_id))
    (secondContinuous.comp (continuous_const.prodMk continuous_id)) mode.2
  unfold doubleCoefficient
  simp_rw [inner]
  exact angularCoefficient_sub_general _ _
    (angularCoefficient_continuous_parameter first firstContinuous mode.2)
    (angularCoefficient_continuous_parameter second secondContinuous mode.2) mode.1

end Grad.SourceCollarFullSource
