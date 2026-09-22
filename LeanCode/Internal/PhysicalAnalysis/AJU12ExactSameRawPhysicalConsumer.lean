import AJU11SamePhysicalSmoothResponse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval ENNReal BigOperators
namespace Grad.AnnularPhysicalFourier
open Grad.BoundaryTrace Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.SourceCollarCoefficients Grad.AnnularSmoothCore
open Grad.AnnularReconstruction Grad.AnnularStrongOrbit Grad.AnnularCoupledInverse
open Grad.AnnularHighGenerators
open Grad.AnnularClosedJointRegularity Grad.SourceCollarFullSource Grad.SourceCollarAngular
open Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (core : OriginalSmoothSourceCore parameters)

/-- The actual normalized Fourier integrals recover the SAME original
physical X coefficient, including exact high/low representative storage. -/
theorem originalSmoothResponsePhysicalX_raw_coefficient (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    angularCoefficient (fun axial => angularCoefficient
      (fun polar => originalSmoothResponsePhysicalX parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core (radius.val, polar, axial)) mode.1) mode.2 =
      sameCoupledXCoefficient parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
        (originalSmoothSourceResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core) 0 radius mode := by
  rw [originalSmoothResponsePhysicalX_coefficient parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core radius.val radius.property mode]
  change sameCoupledPhysicalXSection parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 0
    (originalSmoothSourceResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core)
    (radialClamp lower (lowerHalf.trans (by norm_num)) radius.val) mode = _
  rw [radialClamp_eq lower (lowerHalf.trans (by norm_num)) radius.val radius.property]
  exact sameCoupledPhysicalXSection_coefficient parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
    (originalSmoothSourceResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core)
    (originalSmoothSourceResponse_allGrades parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core) 0 radius mode

theorem originalSmoothResponsePhysicalX_zeroAngularCoefficient (radius : Icc lower (1 : ℝ)) (cell : ℤ) :
    angularCoefficient (fun axial => angularCoefficient
      (fun polar => originalSmoothResponsePhysicalX parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core (radius.val, polar, axial)) 0) cell = 0 := by
  rw [originalSmoothResponsePhysicalX_raw_coefficient parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core radius (0, cell)]
  exact sameCoupledXCoefficient_meanZero parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
    (originalSmoothSourceResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core) 0 radius cell

/-- The actual normalized Fourier integrals recover the SAME original
physical Xi coefficient, including exact high/low representative storage. -/
theorem originalSmoothResponsePhysicalXi_raw_coefficient (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    angularCoefficient (fun axial => angularCoefficient
      (fun polar => originalSmoothResponsePhysicalXi parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core (radius.val, polar, axial)) mode.1) mode.2 =
      sameCoupledXiCoefficient parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
        (originalSmoothSourceResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core) 0 radius mode := by
  rw [originalSmoothResponsePhysicalXi_coefficient parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core radius.val radius.property mode]
  change sameCoupledPhysicalXiSection parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 0
    (originalSmoothSourceResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core)
    (radialClamp lower (lowerHalf.trans (by norm_num)) radius.val) mode = _
  rw [radialClamp_eq lower (lowerHalf.trans (by norm_num)) radius.val radius.property]
  exact sameCoupledPhysicalXiSection_coefficient parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
    (originalSmoothSourceResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core)
    (originalSmoothSourceResponse_allGrades parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core) 0 radius mode

theorem originalSmoothResponsePhysicalXi_zeroAngularCoefficient (radius : Icc lower (1 : ℝ)) (cell : ℤ) :
    angularCoefficient (fun axial => angularCoefficient
      (fun polar => originalSmoothResponsePhysicalXi parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core (radius.val, polar, axial)) 0) cell = 0 := by
  rw [originalSmoothResponsePhysicalXi_raw_coefficient parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core radius (0, cell)]
  exact sameCoupledXiCoefficient_meanZero parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
    (originalSmoothSourceResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core) 0 radius cell

end Grad.AnnularPhysicalFourier
