import AKBR6ActualBoundaryCovectorFourier

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
namespace Grad.OriginalKernelOuterUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.NonlinearRange Grad.NonlinearQuotientBounds Grad.SourceCollar
open Grad.GaugeCoefficients.Physical.Frame Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Algebra Grad.PhysicalCoordinates Grad.OriginalKernelCovariantRecovery
open Grad.Cor18 Grad.ActualBoundaryPrimitives

/-- Evaluation of the existing original seed inverse at the SAME physical
point and axial angle; no replacement multiplier is introduced. -/
theorem originalCoreValue_seedInverse {parameters : PhaseParameters} (seed : Seed.Parameters)
    (inside : seed∈Seed.parameterDomain) (field : ACore parameters 2) (point : ClosedDisk) (angle : ℝ) :
    coreValue (seedInverseCore parameters seed inside field) point angle=
      Seed.actualInverseOperator seed angle (coreValue field point angle) := by
  rw [seedInverseCore_eq_full,coreValue_smoothMultiplier]
  have phase : Grad.GaugeCoefficients.Algebra.fourierPhase=axialPhase := by
    funext cell axial
    exact ((axialPhase_eq_character cell axial).trans (cellCharacter_coe cell axial)).symm
  rw [←phase,seedInverseCells_fourier parameters seed inside]

/-- The literal original inverse seed operator has the matrix used by AD19. -/
theorem originalSeedInverse_matrix (seed : Seed.Parameters) (inside : seed∈Seed.parameterDomain) (angle : ℝ) :
    operatorMatrix (Seed.actualInverseOperator seed angle)=
      (physicalSeedMatrix (seed 0) (seed 1) (seed 2) (seed 3) angle)⁻¹ := by
  have right := congrArg operatorMatrix (matrix_inverse_operator_id seed inside angle)
  rw [operatorMatrix_comp,operatorMatrix_one] at right
  exact (Matrix.inv_eq_right_inv right).symm

/-- The physical seed-inverted radial boundary covector agrees exactly
with the stored planar row, including the coordinate permutation. -/
theorem originalBoundaryCovector_storage (seed : Seed.Parameters) (inside : seed∈Seed.parameterDomain)
    (point : ClosedDisk) (angle : ℝ) (value : ComplexEuclidean 3) :
    (((spatialColumn point).transpose*(physicalSeedMatrix (seed 0) (seed 1) (seed 2) (seed 3) angle)⁻¹*
      planarPhysicalInclusion.transpose).mulVec value) 0=
      (point.val 0 : ℂ)*(Seed.actualInverseOperator seed angle (planarPartMap (toPhysicalValue value))) 0+
      (point.val 1 : ℂ)*(Seed.actualInverseOperator seed angle (planarPartMap (toPhysicalValue value))) 1 := by
  rw [←originalSeedInverse_matrix seed inside angle]
  have planar : planarPhysicalInclusion.transpose.mulVec value=planarPartMap (toPhysicalValue value) := by
    funext index
    fin_cases index <;> simp [planarPhysicalInclusion,Matrix.mulVec,dotProduct,planarPartMap,toPhysicalValue]
  rw [←Matrix.mulVec_mulVec,planar,←Matrix.mulVec_mulVec]
  have operator := operatorMatrix_mulVec (Seed.actualInverseOperator seed angle) (planarPartMap (toPhysicalValue value))
  have coordinate (index : Fin 2) := congrArg (fun vector : ComplexEuclidean 2 => vector index) operator
  have spatial (input : Fin 2→ℂ) : ((spatialColumn point).transpose.mulVec input) 0=
      (point.val 0 : ℂ)*input 0+(point.val 1 : ℂ)*input 1 := by
    simp [spatialColumn,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  rw [spatial]
  exact congrArg₂ (·+·) (congrArg ((point.val 0 : ℂ)*·) (coordinate 0))
    (congrArg ((point.val 1 : ℂ)*·) (coordinate 1))

end Grad.OriginalKernelOuterUniqueness
