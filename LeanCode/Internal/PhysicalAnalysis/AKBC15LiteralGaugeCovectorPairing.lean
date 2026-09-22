import AKBC14ActualGaugeCoordinateMeans

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
open scoped BigOperators
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.SourceCollar
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.ActualGaugeSigmaPrimitives Grad.ActualPolarFlux Grad.ActualSmoothPhysicalField
open Grad.ActualCurrentPrimitives Grad.ActualPhysicalField Grad.OriginalKernelRetainedDecay

/-- The finite polar-coordinate contraction is the literal Cartesian
bilinear pairing, with no conjugation or physical value permutation. -/
theorem originalPolarMatrixPairing (covector : Fin 3→ℂ) (inverse : Matrix (Fin 3) (Fin 3) ℂ)
    (angle : ℝ) (value : ComplexEuclidean 3) :
    (∑ component : Fin 3,matrixPairing covector inverse (polarVector component angle)*value component)=
      ∑ coordinate : Fin 3,covector coordinate*(inverse.mulVec (cartesianCovariantValue angle value)) coordinate := by
  simp [matrixPairing,polarVector,cartesianCovariantValue,polarDomainMatrix,Matrix.mulVec,dotProduct,
    Fin.sum_univ_three,physicalRadialVector,physicalTangentialVector,physicalToroidalVector]
  ring

variable (parameters : PhaseParameters) (L rho alpha delta parameter epsilon : ℝ) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 6≤originalCoefficientLowRadius parameters L)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1) (vector : ACore parameters 3)

theorem originalGaugeRow_sameU (kind : Fin 2) (radius : ℝ) (inside : radius∈Icc lower 1) (angles : ℝ×ℝ) :
    (∑ component : Fin 3,originalGaugeRow parameters L rho alpha delta parameter epsilon base kind angles.2 angles.1
      (polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2) component *
        (originalPolarCovariantCurves parameters L rho epsilon base small lower positive bounded vector).fullField bounded (radius,angles) component)=
    ∑ coordinate : Fin 3,
      physicalGaugeCovector (physicalSeedMatrix rho alpha delta parameter angles.2)
        ((L : ℂ)⁻¹ • operatorMatrix (deriv (Grad.GaugeCoefficients.Physical.Frame.harmonicSeedOperator rho alpha delta parameter) angles.2))
        angles.1 (polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2) kind coordinate *
        originalCoreCircle parameters vector ⟨radius,positive.le.trans inside.1,inside.2⟩ angles coordinate := by
  simp_rw [originalGaugeRow_covector]
  rw [originalPolarMatrixPairing]
  have same := originalPolarCovariantCurves_recovers_U parameters L rho epsilon base small lower positive bounded vector radius inside angles
  rw [SmoothLowPhysicalRow.fullField_physicalUFromPolar parameters L rho epsilon base small lower positive bounded _ radius inside angles,
    originalInverseTransposeFamily_matrix parameters L rho epsilon base small,
    originalInverseFamily_eq_matrixInverse parameters L rho epsilon base small] at same
  apply Finset.sum_congr rfl
  intro coordinate _
  congr 1
  exact congrArg (fun value : ComplexEuclidean 3 => value coordinate) same


end Grad.OriginalKernelCovariantRecovery
