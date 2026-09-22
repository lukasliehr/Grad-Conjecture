import AKAF2SamePhysicalAngularDerivative
import AJG10OriginalFullSliceEquations

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace Grad.ActualPolarEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.AnnularPhysicalReconstruction Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.ActualSmoothPhysicalField Grad.BoundaryKernelAction Grad.AnnularKernelL2

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (state : AnnularReconstructionState parameters length compact)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (solution : CoupledSpace lower length positive lengthPositive)

/-- Literal low-rho coefficients of the SAME full original polar covariant
and its reconstructed angular derivative satisfy the genuine Fourier law. -/
theorem sharedCovariant_angularCoefficients :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      lowRhoPhysicalCoefficient parameters lower positive
        (sharedFullRotatedCovariant parameters length compact lower positive bounded.le lengthPositive state data solution) radius mode =
      (Complex.I * (mode.1 : ℂ)) • lowRhoPhysicalCoefficient parameters lower positive
        (sharedFullCovariant parameters length compact lower positive bounded.le lengthPositive state data solution) radius mode := by
  filter_upwards [sharedFull_originalSliceLaws parameters length compact lower positive bounded.le lengthPositive state data solution,
    originalPhysicalSlice_coefficient parameters lower positive bounded.le
      (sharedFullCovariant parameters length compact lower positive bounded.le lengthPositive state data solution),
    originalPhysicalSlice_coefficient parameters lower positive bounded.le
      (sharedFullRotatedCovariant parameters length compact lower positive bounded.le lengthPositive state data solution)]
      with radius laws covariant rotated
  intro mode
  have law := laws.angular mode
  rw [covariant mode,rotated mode] at law
  exact law

/-- The actual full original reconstructed covariant has a classical polar
angular derivative. The derivative is the SAME full rotated reconstruction;
no derivative or PDE premise is inserted for either output. -/
theorem sharedCovariant_classical_angular
    (curves : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution))
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (polar axial : ℝ) :
    HasDerivAt (fun angle =>
      (curves.covariant parameters length compact lower positive bounded state).fullField bounded (radius,angle,axial))
      ((curves.rotatedCovariant parameters length compact lower positive bounded state).fullField bounded (radius,polar,axial)) polar :=
  samePhysical_angularDerivative _ _ bounded
    (sharedCovariant_angularCoefficients parameters length compact lower positive bounded lengthPositive state data solution)
    radius inside polar axial

end Grad.ActualPolarEquations
