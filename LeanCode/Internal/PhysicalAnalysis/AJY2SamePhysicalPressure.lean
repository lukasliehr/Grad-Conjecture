import AJY1ExactAngularPrimitiveCurve

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval ENNReal BigOperators
namespace Grad.AnnularPhysicalFourier
open Grad.BoundaryTrace Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.SourceCollarCoefficients Grad.AnnularSmoothCore
open Grad.AnnularReconstruction Grad.AnnularStrongOrbit Grad.AnnularCoupledInverse
open Grad.AnnularClosedJointRegularity Grad.SourceCollarFullSource Grad.SourceCollarAngular
open Grad.GaugeCoefficients.Physical.Allocation Grad.BoundaryKernelAction

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (core : OriginalSmoothSourceCore parameters)

/-- The actual original physical p = R⁻¹ X field of the SAME shared smooth-source
response, reconstructed with every original Fourier mode exactly once. -/
def originalSmoothResponsePhysicalP : (ℝ × (ℝ × ℝ)) → ComplexEuclidean 1 :=
  hilbertPhysicalField lower (lowerHalf.trans_lt (by norm_num))
    (fun grade radius => (physicalAngularPrimitive parameters (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade radius).1))

private theorem originalSmoothResponseP_same (grade : ℕ) (radius : ℝ) (mode : ℤ × ℤ) :
    (physicalAngularPrimitive parameters (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade radius).1) mode =
      ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        (physicalAngularPrimitive parameters (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core 0 radius).1) mode :=
by
  rw [physicalAngularPrimitive_apply,physicalAngularPrimitive_apply]
  have same :
      (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade radius).1 mode =
        ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
          (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core 0 radius).1 mode := congrArg Prod.fst
    (originalSmoothResponsePairCurve_coefficient_grade parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade radius mode)
  rw [same,smul_comm]

theorem originalSmoothResponsePhysicalP_smooth_closed :
    ContDiffOn ℝ ∞ (originalSmoothResponsePhysicalP parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core) (annularJointClosed lower) :=
  hilbertPhysicalField_smooth_closed lower positive (lowerHalf.trans_lt (by norm_num))
    (fun grade radius => (physicalAngularPrimitive parameters (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade radius).1))
    (fun grade => physicalAngularPrimitive_smooth parameters lower _ (originalSmoothResponseXCurve_smooth parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade))
    (fun grade radius _ mode => originalSmoothResponseP_same parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade radius mode)

theorem originalSmoothResponsePhysicalP_coefficient (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    angularCoefficient (fun axial => angularCoefficient
      (fun polar => originalSmoothResponsePhysicalP parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core (radius, polar, axial)) mode.1) mode.2 =
      (physicalAngularPrimitive parameters (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core 0 radius).1) mode :=
  hilbertPhysicalField_coefficient lower (lowerHalf.trans_lt (by norm_num))
    (fun grade point => (physicalAngularPrimitive parameters (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade point).1))
    (fun grade => physicalAngularPrimitive_smooth parameters lower _ (originalSmoothResponseXCurve_smooth parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade))
    (fun grade point _ query => originalSmoothResponseP_same parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade point query)
    radius inside mode

theorem originalSmoothResponsePhysicalP_angular_periodic (radius axial : ℝ) :
    Function.Periodic (fun polar => originalSmoothResponsePhysicalP parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core (radius, polar, axial)) (2 * Real.pi) :=
  hilbertPhysicalField_angular_periodic lower (lowerHalf.trans_lt (by norm_num))
    (fun grade point => (physicalAngularPrimitive parameters (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade point).1)) radius axial

theorem originalSmoothResponsePhysicalP_cell_periodic (radius polar : ℝ) :
    Function.Periodic (fun axial => originalSmoothResponsePhysicalP parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core (radius, polar, axial)) (2 * Real.pi) :=
  hilbertPhysicalField_cell_periodic lower (lowerHalf.trans_lt (by norm_num))
    (fun grade point => (physicalAngularPrimitive parameters (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade point).1)) radius polar


/-- Exact original mean-free pressure coefficient from the SAME retained X. -/
theorem originalSmoothResponsePhysicalP_raw_coefficient (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    angularCoefficient (fun axial => angularCoefficient
      (fun polar => originalSmoothResponsePhysicalP parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core (radius.val, polar, axial)) mode.1) mode.2 =
      angularInverseMultiplier mode •
        sameCoupledXCoefficient parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
          (originalSmoothSourceResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core) 0 radius mode := by
  rw [originalSmoothResponsePhysicalP_coefficient parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core radius.val radius.property mode,
    physicalAngularPrimitive_apply]
  have same := (originalSmoothResponsePhysicalX_coefficient parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core radius.val radius.property mode).symm.trans
    (originalSmoothResponsePhysicalX_raw_coefficient parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core radius mode)
  rw [same]

theorem originalSmoothResponsePhysicalP_zeroAngularCoefficient (radius : Icc lower (1 : ℝ)) (cell : ℤ) :
    angularCoefficient (fun axial => angularCoefficient
      (fun polar => originalSmoothResponsePhysicalP parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core (radius.val, polar, axial)) 0) cell = 0 := by
  rw [originalSmoothResponsePhysicalP_raw_coefficient parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core radius (0, cell)]
  simp [angularInverseMultiplier]

/-- R p recovers the original X coefficient at every mode, including the
zero complement fixed by the retained mean-free carrier. -/
theorem originalSmoothResponsePhysicalP_R_coefficient (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    (Complex.I * (mode.1 : ℂ)) •
      angularCoefficient (fun axial => angularCoefficient
        (fun polar => originalSmoothResponsePhysicalP parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core (radius.val, polar, axial)) mode.1) mode.2 =
      angularCoefficient (fun axial => angularCoefficient
        (fun polar => originalSmoothResponsePhysicalX parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core (radius.val, polar, axial)) mode.1) mode.2 := by
  rw [originalSmoothResponsePhysicalP_coefficient parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core radius.val radius.property mode,
    originalSmoothResponsePhysicalX_coefficient parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core radius.val radius.property mode]
  apply physicalAngularPrimitive_R
  intro cell
  rw [← originalSmoothResponsePhysicalX_coefficient parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core radius.val radius.property (0, cell)]
  exact originalSmoothResponsePhysicalX_zeroAngularCoefficient parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core radius cell

end Grad.AnnularPhysicalFourier
