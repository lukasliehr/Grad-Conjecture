import AJU10ClosedHilbertFourierReconstruction
import AJT7ActualSameSolutionSmoothness

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
open Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (core : OriginalSmoothSourceCore parameters)

/-- The actual original physical X field of the SAME shared smooth-source
response, reconstructed with every original Fourier mode exactly once. -/
def originalSmoothResponsePhysicalX : (ℝ × (ℝ × ℝ)) → ComplexEuclidean 1 :=
  hilbertPhysicalField lower (lowerHalf.trans_lt (by norm_num))
    (fun grade radius => (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade radius).1)

private theorem originalSmoothResponseX_same (grade : ℕ) (radius : ℝ) (mode : ℤ × ℤ) :
    (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade radius).1 mode =
      ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core 0 radius).1 mode :=
  congrArg Prod.fst
    (originalSmoothResponsePairCurve_coefficient_grade parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade radius mode)

theorem originalSmoothResponsePhysicalX_smooth_closed :
    ContDiffOn ℝ ∞ (originalSmoothResponsePhysicalX parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core) (annularJointClosed lower) :=
  hilbertPhysicalField_smooth_closed lower positive (lowerHalf.trans_lt (by norm_num))
    (fun grade radius => (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade radius).1)
    (originalSmoothResponseXCurve_smooth parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core)
    (fun grade radius _ mode => originalSmoothResponseX_same parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade radius mode)

theorem originalSmoothResponsePhysicalX_coefficient (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    angularCoefficient (fun axial => angularCoefficient
      (fun polar => originalSmoothResponsePhysicalX parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core (radius, polar, axial)) mode.1) mode.2 =
      (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core 0 radius).1 mode :=
  hilbertPhysicalField_coefficient lower (lowerHalf.trans_lt (by norm_num))
    (fun grade point => (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade point).1)
    (originalSmoothResponseXCurve_smooth parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core)
    (fun grade point _ query => originalSmoothResponseX_same parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade point query)
    radius inside mode

theorem originalSmoothResponsePhysicalX_angular_periodic (radius axial : ℝ) :
    Function.Periodic (fun polar => originalSmoothResponsePhysicalX parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core (radius, polar, axial)) (2 * Real.pi) :=
  hilbertPhysicalField_angular_periodic lower (lowerHalf.trans_lt (by norm_num))
    (fun grade point => (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade point).1) radius axial

theorem originalSmoothResponsePhysicalX_cell_periodic (radius polar : ℝ) :
    Function.Periodic (fun axial => originalSmoothResponsePhysicalX parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core (radius, polar, axial)) (2 * Real.pi) :=
  hilbertPhysicalField_cell_periodic lower (lowerHalf.trans_lt (by norm_num))
    (fun grade point => (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade point).1) radius polar

/-- The actual original physical Xi field of the SAME shared smooth-source
response, reconstructed with every original Fourier mode exactly once. -/
def originalSmoothResponsePhysicalXi : (ℝ × (ℝ × ℝ)) → ComplexEuclidean 1 :=
  hilbertPhysicalField lower (lowerHalf.trans_lt (by norm_num))
    (fun grade radius => (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade radius).2)

private theorem originalSmoothResponseXi_same (grade : ℕ) (radius : ℝ) (mode : ℤ × ℤ) :
    (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade radius).2 mode =
      ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core 0 radius).2 mode :=
  congrArg Prod.snd
    (originalSmoothResponsePairCurve_coefficient_grade parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade radius mode)

theorem originalSmoothResponsePhysicalXi_smooth_closed :
    ContDiffOn ℝ ∞ (originalSmoothResponsePhysicalXi parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core) (annularJointClosed lower) :=
  hilbertPhysicalField_smooth_closed lower positive (lowerHalf.trans_lt (by norm_num))
    (fun grade radius => (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade radius).2)
    (originalSmoothResponseXiCurve_smooth parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core)
    (fun grade radius _ mode => originalSmoothResponseXi_same parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade radius mode)

theorem originalSmoothResponsePhysicalXi_coefficient (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    angularCoefficient (fun axial => angularCoefficient
      (fun polar => originalSmoothResponsePhysicalXi parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core (radius, polar, axial)) mode.1) mode.2 =
      (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core 0 radius).2 mode :=
  hilbertPhysicalField_coefficient lower (lowerHalf.trans_lt (by norm_num))
    (fun grade point => (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade point).2)
    (originalSmoothResponseXiCurve_smooth parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core)
    (fun grade point _ query => originalSmoothResponseXi_same parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade point query)
    radius inside mode

theorem originalSmoothResponsePhysicalXi_angular_periodic (radius axial : ℝ) :
    Function.Periodic (fun polar => originalSmoothResponsePhysicalXi parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core (radius, polar, axial)) (2 * Real.pi) :=
  hilbertPhysicalField_angular_periodic lower (lowerHalf.trans_lt (by norm_num))
    (fun grade point => (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade point).2) radius axial

theorem originalSmoothResponsePhysicalXi_cell_periodic (radius polar : ℝ) :
    Function.Periodic (fun axial => originalSmoothResponsePhysicalXi parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core (radius, polar, axial)) (2 * Real.pi) :=
  hilbertPhysicalField_cell_periodic lower (lowerHalf.trans_lt (by norm_num))
    (fun grade point => (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade point).2) radius polar

/-- Joint closed-collar smoothness of the actual full physical pair on the
unchanged B8 ball and analytic widths, with no regularity premise. -/
theorem originalSmoothResponsePhysicalPair_smooth_closed :
    ContDiffOn ℝ ∞
      (fun point => (originalSmoothResponsePhysicalX parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core point,
        originalSmoothResponsePhysicalXi parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core point)) (annularJointClosed lower) :=
  (originalSmoothResponsePhysicalX_smooth_closed parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core).prodMk
    (originalSmoothResponsePhysicalXi_smooth_closed parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core)

end Grad.AnnularPhysicalFourier
