import BCI16InverseReferenceMoments

noncomputable section
set_option maxHeartbeats 1000000
namespace Grad.ActualBoundaryInverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger

/-- The original AI9 tuple z=(Rxi,xi_zeta,xi), inserted in slots 1,2,3. -/
def retainedTupleInsertion : ComplexEuclidean 3 →L[ℂ] ComplexEuclidean 7 :=
  matrixUnit 1 0 + matrixUnit 2 1 + matrixUnit 3 2

/-- The original AI9 tuple s=(F0,RF0,F2), inserted in slots 4,5,6. -/
def sourceTupleInsertion : ComplexEuclidean 3 →L[ℂ] ComplexEuclidean 7 :=
  matrixUnit 4 0 + matrixUnit 5 1 + matrixUnit 6 2

def retainedTupleProjection : ComplexEuclidean 7 →L[ℂ] ComplexEuclidean 3 :=
  matrixUnit 0 1 + matrixUnit 1 2 + matrixUnit 2 3

def sourceTupleProjection : ComplexEuclidean 7 →L[ℂ] ComplexEuclidean 3 :=
  matrixUnit 0 4 + matrixUnit 1 5 + matrixUnit 2 6

theorem sourceTupleInsertion_apply (value : ComplexEuclidean 3) :
    sourceTupleInsertion value = WithLp.toLp 2 ![0, 0, 0, 0, value 0, value 1, value 2] := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [sourceTupleInsertion, matrixUnit_apply, operatorBasis]

theorem sourceTupleProjection_apply (value : ComplexEuclidean 7) :
    sourceTupleProjection value = WithLp.toLp 2 ![value 4, value 5, value 6] := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [sourceTupleProjection, matrixUnit_apply, operatorBasis]

theorem retainedTupleInsertion_apply (value : ComplexEuclidean 3) :
    retainedTupleInsertion value = WithLp.toLp 2 ![0, value 0, value 1, value 2, 0, 0, 0] := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [retainedTupleInsertion, matrixUnit_apply, operatorBasis]

theorem retainedTupleProjection_apply (value : ComplexEuclidean 7) :
    retainedTupleProjection value = WithLp.toLp 2 ![value 1, value 2, value 3] := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [retainedTupleProjection, matrixUnit_apply, operatorBasis]

def sourceTupleInsertionKernel (parameters : PhaseParameters) := constantMatrixKernel parameters 3 7 sourceTupleInsertion
def retainedTupleInsertionKernel (parameters : PhaseParameters) := constantMatrixKernel parameters 3 7 retainedTupleInsertion
def sourceTupleProjectionKernel (parameters : PhaseParameters) := constantMatrixKernel parameters 7 3 sourceTupleProjection
def retainedTupleProjectionKernel (parameters : PhaseParameters) := constantMatrixKernel parameters 7 3 retainedTupleProjection

theorem first_source_tuple_zero (parameters : PhaseParameters) :
    fullKernelComposition (sevenInputSlotKernel parameters 0) (sourceTupleInsertionKernel parameters) = fullZeroKernel parameters 3 1 := by
  apply FullTwoFrequencyKernel.ext_entry
  intro shift frequency
  rw [sevenInputSlotKernel, coordinateProjectionKernel, constantKernel_outer_entry,
    sourceTupleInsertionKernel, constantMatrixKernel_entry, fullZeroKernel_entry]
  split_ifs
  · apply ContinuousLinearMap.ext
    intro value
    apply PiLp.ext
    intro coordinate
    have unique := Fin.eq_zero coordinate
    subst coordinate
    simp [ContinuousLinearMap.comp_apply, sourceTupleInsertion_apply, matrixUnit_apply, operatorBasis]
  · exact ContinuousLinearMap.comp_zero _

theorem first_retained_tuple_zero (parameters : PhaseParameters) :
    fullKernelComposition (sevenInputSlotKernel parameters 0) (retainedTupleInsertionKernel parameters) = fullZeroKernel parameters 3 1 := by
  apply FullTwoFrequencyKernel.ext_entry
  intro shift frequency
  rw [sevenInputSlotKernel, coordinateProjectionKernel, constantKernel_outer_entry,
    retainedTupleInsertionKernel, constantMatrixKernel_entry, fullZeroKernel_entry]
  split_ifs
  · apply ContinuousLinearMap.ext
    intro value
    apply PiLp.ext
    intro coordinate
    have unique := Fin.eq_zero coordinate
    subst coordinate
    simp [ContinuousLinearMap.comp_apply, retainedTupleInsertion_apply, matrixUnit_apply, operatorBasis]
  · exact ContinuousLinearMap.comp_zero _

variable {parameters : PhaseParameters} {L compact : ℝ}

/-- AI9's actual N block, defined only by the prescribed coordinate insertion. -/
def actualBoundaryN (state : PhysicalBoundaryState parameters L compact) :=
  fullKernelComposition state.physicalRow (retainedTupleInsertionKernel parameters)

/-- AI9's actual H block, with arbitrary F0,RF0,F2 coordinates. -/
def actualBoundaryH (state : PhysicalBoundaryState parameters L compact) :=
  fullKernelComposition state.physicalRow (sourceTupleInsertionKernel parameters)

theorem actualBoundaryH_eq_deviation (state : PhysicalBoundaryState parameters L compact) :
    actualBoundaryH state = fullKernelComposition state.fullBoundaryDeviation (sourceTupleInsertionKernel parameters) := by
  rw [← full_physical_boundary_reference_difference, fullKernelComposition_add_outer,
    fullKernelComposition_assoc, first_source_tuple_zero, fullKernel_comp_zero, fullKernel_add_zero]
  rfl

theorem actualBoundaryN_eq_deviation (state : PhysicalBoundaryState parameters L compact) :
    actualBoundaryN state = fullKernelComposition state.fullBoundaryDeviation (retainedTupleInsertionKernel parameters) := by
  rw [← full_physical_boundary_reference_difference, fullKernelComposition_add_outer,
    fullKernelComposition_assoc, first_retained_tuple_zero, fullKernel_comp_zero, fullKernel_add_zero]
  rfl

theorem actualBoundaryH_vanishingMoments (parameters : PhaseParameters) (L compact : ℝ) :
    BoundaryDeviationMoments parameters L compact actualBoundaryH := by
  intro moment
  obtain ⟨constant, nonnegative, bound⟩ :=
    BoundaryDeviationMoments.comp_regular (fullBoundaryDeviation_vanishingMoments parameters L compact)
      (BoundaryKernelMoments.fixed parameters L compact (sourceTupleInsertionKernel parameters)) moment
  refine ⟨constant, nonnegative, fun state => ?_⟩
  rw [actualBoundaryH_eq_deviation]
  exact bound state

theorem actualBoundaryN_vanishingMoments (parameters : PhaseParameters) (L compact : ℝ) :
    BoundaryDeviationMoments parameters L compact actualBoundaryN := by
  intro moment
  obtain ⟨constant, nonnegative, bound⟩ :=
    BoundaryDeviationMoments.comp_regular (fullBoundaryDeviation_vanishingMoments parameters L compact)
      (BoundaryKernelMoments.fixed parameters L compact (retainedTupleInsertionKernel parameters)) moment
  refine ⟨constant, nonnegative, fun state => ?_⟩
  rw [actualBoundaryN_eq_deviation]
  exact bound state

/-- All of the AI9 reference block identities hold on the full source tuple. -/
theorem actualBoundary_reference_blocks (state : PhysicalBoundaryState parameters L compact)
    (reference : state.budget 0 = 0) :
    state.boundaryT = fullKernelNeg (highAngularKernel parameters 1) ∧
      actualBoundaryN state = fullZeroKernel parameters 3 1 ∧ actualBoundaryH state = fullZeroKernel parameters 3 1 := by
  refine ⟨?_, BoundaryDeviationMoments.reference_zero (actualBoundaryN_vanishingMoments parameters L compact) state reference,
    BoundaryDeviationMoments.reference_zero (actualBoundaryH_vanishingMoments parameters L compact) state reference⟩
  have errorZero := BoundaryDeviationMoments.reference_zero (actualBoundaryE_vanishingMoments parameters L compact) state reference
  have relation := boundaryT_add_high_eq_error state
  rw [errorZero] at relation
  apply FullTwoFrequencyKernel.ext_entry
  intro shift frequency
  have entry := congrArg (fun kernel : FullTwoFrequencyKernel parameters 1 1 => kernel.entry shift frequency) relation
  simp only [fullKernelAdd_entry, fullKernelNeg_entry, fullZeroKernel_entry] at entry ⊢
  exact eq_neg_of_add_eq_zero_left entry

end Grad.ActualBoundaryInverse
