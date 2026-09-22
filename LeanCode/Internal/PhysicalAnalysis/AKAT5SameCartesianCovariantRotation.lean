import AKAT4GenuineCartesianGradient
import AKAT3SamePhysicalXiAngular

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter
open scoped ContDiff
namespace Grad.ActualCartesianEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations Grad.AnnularKernelL2
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.ActualCartesianDescent Grad.PhysicalFamily Grad.AnnularClosedJointRegularity

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (state : AnnularReconstructionState parameters length compact)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (solution : CoupledSpace lower length positive lengthPositive)
    (curves : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution))

/-- Rw is the derivative of the SAME Q(theta)a, including the polar frame's
quarter-turn contribution. -/
theorem sharedCartesianCovariant_classical_angular
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (polar axial : ℝ) :
    HasDerivAt (fun angle =>
      (curves.covariant parameters length compact lower positive bounded state).cartesianCovariant.fullField bounded (radius,angle,axial))
      (cartesianCovariantValue polar
        ((curves.rotatedCovariant parameters length compact lower positive bounded state).fullField bounded (radius,polar,axial) +
          polarQuarter ((curves.covariant parameters length compact lower positive bounded state).fullField bounded (radius,polar,axial)))) polar := by
  have law := cartesianCovariantValue_hasDerivAt _ _ polar
    (sharedCovariant_classical_angular parameters length compact lower positive bounded lengthPositive state data solution curves radius inside polar axial)
  have same := funext (fun angle =>
    (curves.covariant parameters length compact lower positive bounded state).fullField_cartesianCovariant bounded radius inside (angle,axial))
  rw [← same] at law
  exact law

/-- The same angular law is the actual Cartesian Frechet derivative in
R=(Jy)·grad, rather than a formal derivative of Fourier coordinates. -/
theorem sharedCartesianCovariant_cartesian_rotation
    (radius : ℝ) (inside : radius ∈ Ioo lower 1) (polar axial : ℝ) :
    fderiv ℝ ((curves.covariant parameters length compact lower positive bounded state).cartesianCovariant.cartesianField bounded)
      (polarPlane (radius,polar),axial) (radius • planeQuarterTurn (radialDirection polar),0) =
      cartesianCovariantValue polar
        ((curves.rotatedCovariant parameters length compact lower positive bounded state).fullField bounded (radius,polar,axial) +
          polarQuarter ((curves.covariant parameters length compact lower positive bounded state).fullField bounded (radius,polar,axial))) := by
  let cartesian := (curves.covariant parameters length compact lower positive bounded state).cartesianCovariant
  have smooth : ContDiffOn ℝ ∞ (cartesian.fullField bounded)
      (Ioo lower 1 ×ˢ (univ : Set (ℝ × ℝ))) :=
    (cartesian.fullField_smooth bounded).mono (fun _ member => ⟨⟨member.1.1.le,member.1.2.le⟩,mem_univ _⟩)
  exact (cartesianPhysicalField_angular_hasDerivAt (cartesian.fullField bounded) lower 1 smooth
    (fun r z => cartesian.fullField_angular_periodic bounded r z) radius (positive.trans inside.1) inside polar axial).unique
    (sharedCartesianCovariant_classical_angular parameters length compact lower positive bounded lengthPositive state data solution curves
      radius ⟨inside.1.le,inside.2.le⟩ polar axial)

end Grad.ActualCartesianEquations
