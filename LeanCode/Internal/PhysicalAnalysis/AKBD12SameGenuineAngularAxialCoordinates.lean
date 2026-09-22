import AKBD11SameRVScalarExpression

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualDeterminantEquations
open Grad.BoundaryTrace Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarFullSource Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations Grad.BoundaryKernelAction Grad.AnnularKernelL2
open Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger
open Grad.ActualBoundaryPrimitives Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.SourceCollar Grad.BoundaryLift Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)

open Grad.ActualPolarFlux Grad.ActualCartesianEquations

theorem fullField_bulkUnit_zero_scalar {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ}
    {positive : 0 < lower} {row : DivisionRow dimension lower}
    (curves : SmoothLowPhysicalRow parameters lower positive row) (bounded : lower < 1)
    (component : Fin dimension) (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.bulkUnit (0 : Fin 1) component).fullField bounded (radius,angles) 0 =
      curves.fullField bounded (radius,angles) component := by
  rw [curves.fullField_bulkUnit bounded (0 : Fin 1) component radius inside angles]
  simp [matrixUnit_apply,operatorBasis]

open Grad.AnnularSmoothCore Grad.AnnularGeneralSourceRegularity Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularSourceGraph

variable (lengthPositive : 0 < length)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (solution : CoupledSpace lower length positive lengthPositive)
    (curves : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution))

/-- The genuine angular derivative is the accepted SAME rotated covariant. -/
theorem sameCovariant_scalarPolar (component : Fin 3) (radius : ℝ)
    (inside : radius ∈ Ioo lower 1) (polar axial : ℝ) :
    scalarDirectionalField (curves.covariant parameters length compact lower positive bounded state.val)
      bounded component (0,1,0) (radius,polar,axial) =
      (curves.rotatedCovariant parameters length compact lower positive bounded state.val).fullField bounded (radius,polar,axial) component := by
  have vector := sharedCovariant_classical_angular parameters length compact lower positive bounded lengthPositive state.val data solution curves
    radius ⟨inside.1.le,inside.2.le⟩ polar axial
  have scalar := ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 3 => ℂ) component).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt polar vector
  exact (scalarPolar_hasDerivAt (curves.covariant parameters length compact lower positive bounded state.val) bounded component radius inside polar axial).unique scalar

/-- The actual q=Xi/r has q_theta equal to the literal full seven slot one. -/
theorem sameSeven_scalarPolar (radius : ℝ) (inside : radius ∈ Ioo lower 1) (polar axial : ℝ) :
    scalarDirectionalField curves bounded 3 (0,1,0) (radius,polar,axial) = curves.fullField bounded (radius,polar,axial) 1 := by
  have vector := (sharedSeven_classical_angular parameters length lower positive bounded lengthPositive data solution curves
    radius ⟨inside.1.le,inside.2.le⟩ polar axial).1
  have scalar := ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 => ℂ) 0).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt polar vector
  change HasDerivAt (fun angle => (curves.bulkUnit (0 : Fin 1) 3).fullField bounded (radius,angle,axial) 0)
    ((curves.bulkUnit (0 : Fin 1) 1).fullField bounded (radius,polar,axial) 0) polar at scalar
  simp_rw [fullField_bulkUnit_zero_scalar curves bounded _ radius ⟨inside.1.le,inside.2.le⟩] at scalar
  exact (scalarPolar_hasDerivAt curves bounded 3 radius inside polar axial).unique scalar

/-- The actual q=Xi/r has q_zeta equal to slot two divided by the same radius. -/
theorem sameSeven_scalarAxial (radius : ℝ) (inside : radius ∈ Ioo lower 1) (polar axial : ℝ) :
    scalarDirectionalField curves bounded 3 (0,0,1) (radius,polar,axial) =
      (radius : ℂ)⁻¹ * curves.fullField bounded (radius,polar,axial) 2 := by
  have vector := samePhysical_scaledAxialDerivative (curves.bulkUnit (0 : Fin 1) 3) (curves.bulkUnit (0 : Fin 1) 2)
    bounded (fun location => (location : ℂ)⁻¹) (reciprocalRadius_smooth lower positive).continuousOn
    (fullSeven_physicalXi_axialCoefficients parameters lower length positive bounded lengthPositive data solution)
    radius ⟨inside.1.le,inside.2.le⟩ polar axial
  have scalar := ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 => ℂ) 0).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt axial vector
  change HasDerivAt (fun angle => (curves.bulkUnit (0 : Fin 1) 3).fullField bounded (radius,polar,angle) 0)
    ((radius : ℂ)⁻¹ * (curves.bulkUnit (0 : Fin 1) 2).fullField bounded (radius,polar,axial) 0) axial at scalar
  simp_rw [fullField_bulkUnit_zero_scalar curves bounded _ radius ⟨inside.1.le,inside.2.le⟩] at scalar
  exact (scalarAxial_hasDerivAt curves bounded 3 radius inside polar axial).unique scalar

end Grad.ActualDeterminantEquations
