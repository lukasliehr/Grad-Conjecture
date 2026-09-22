import BCI3BoundaryDeviationKernels

noncomputable section
set_option maxHeartbeats 1000000
namespace Grad.ActualBoundaryInverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger

theorem constantKernel_outer_entry {input middle output : ℕ} (parameters : PhaseParameters)
    (outer : ComplexEuclidean middle →L[ℂ] ComplexEuclidean output)
    (inner : FullTwoFrequencyKernel parameters input middle) (shift frequency : ℤ × ℤ) :
    (fullKernelComposition (constantMatrixKernel parameters middle output outer) inner).entry shift frequency =
      outer.comp (inner.entry shift frequency) := by
  rw [fullKernelComposition_entry, tsum_eq_single shift (by
    intro current distinct
    have nonzero : shift - current ≠ (0, 0) := by
      intro zero
      exact distinct (sub_eq_zero.mp zero).symm
    simp [constantMatrixKernel_entry, nonzero])]
  rw [constantMatrixKernel_entry, sub_self]
  rfl

theorem constantKernel_inner_entry {input middle output : ℕ} (parameters : PhaseParameters)
    (outer : FullTwoFrequencyKernel parameters middle output)
    (inner : ComplexEuclidean input →L[ℂ] ComplexEuclidean middle) (shift frequency : ℤ × ℤ) :
    (fullKernelComposition outer (constantMatrixKernel parameters input middle inner)).entry shift frequency =
      (outer.entry shift frequency).comp inner := by
  rw [fullKernelComposition_entry, tsum_eq_single (0, 0) (by
    intro current distinct
    simp [constantMatrixKernel_entry, distinct])]
  simp only [constantMatrixKernel_entry]
  change (outer.entry (shift - 0) (frequency + 0)).comp inner = _
  rw [sub_zero, add_zero]

theorem fullKernel_comp_zero {input middle output : ℕ} (parameters : PhaseParameters)
    (outer : FullTwoFrequencyKernel parameters middle output) :
    fullKernelComposition outer (fullZeroKernel parameters input middle) = fullZeroKernel parameters input output := by
  apply FullTwoFrequencyKernel.ext_entry
  intro shift frequency
  simp [fullKernelComposition_entry]

theorem fullKernel_zero_comp {input middle output : ℕ} (parameters : PhaseParameters)
    (inner : FullTwoFrequencyKernel parameters input middle) :
    fullKernelComposition (fullZeroKernel parameters middle output) inner = fullZeroKernel parameters input output := by
  apply FullTwoFrequencyKernel.ext_entry
  intro shift frequency
  simp [fullKernelComposition_entry]

theorem fullKernel_zero_add {input output : ℕ} (parameters : PhaseParameters)
    (kernel : FullTwoFrequencyKernel parameters input output) :
    fullKernelAdd (fullZeroKernel parameters input output) kernel = kernel := by
  apply FullTwoFrequencyKernel.ext_entry
  intro shift frequency
  simp [fullKernelAdd_entry]

theorem fullKernel_add_zero {input output : ℕ} (parameters : PhaseParameters)
    (kernel : FullTwoFrequencyKernel parameters input output) :
    fullKernelAdd kernel (fullZeroKernel parameters input output) = kernel := by
  apply FullTwoFrequencyKernel.ext_entry
  intro shift frequency
  simp [fullKernelAdd_entry]

theorem coordinateProjection_injection_distinct (parameters : PhaseParameters) (dimension : ℕ)
    (row column : Fin dimension) (distinct : row ≠ column) :
    fullKernelComposition (coordinateProjectionKernel parameters dimension row)
      (coordinateInjectionKernel parameters dimension column) = fullZeroKernel parameters 1 1 := by
  apply FullTwoFrequencyKernel.ext_entry
  intro shift frequency
  rw [coordinateProjectionKernel, constantKernel_outer_entry]
  unfold coordinateInjectionKernel
  rw [constantMatrixKernel_entry, fullZeroKernel_entry]
  split_ifs
  · apply ContinuousLinearMap.ext
    intro value
    apply PiLp.ext
    intro component
    simp [ContinuousLinearMap.comp_apply, matrixUnit_apply, operatorBasis, distinct]
  · simp

theorem coordinateProjection_injection_same (parameters : PhaseParameters) (dimension : ℕ)
    (coordinate : Fin dimension) :
    fullKernelComposition (coordinateProjectionKernel parameters dimension coordinate)
      (coordinateInjectionKernel parameters dimension coordinate) = fullIdentityKernel parameters 1 := by
  rw [coordinateProjectionKernel, coordinateInjectionKernel, constantMatrixKernel_comp]
  have same : (matrixUnit (0 : Fin 1) coordinate).comp (matrixUnit coordinate 0) =
      ContinuousLinearMap.id ℂ (ComplexEuclidean 1) := by
    apply ContinuousLinearMap.ext
    intro value
    apply PiLp.ext
    intro component
    have unique := Fin.eq_zero component
    subst component
    simp [ContinuousLinearMap.comp_apply, matrixUnit_apply, operatorBasis]
  rw [same, constantMatrixKernel_id]

theorem encodedRotationKernel_first (parameters : PhaseParameters) :
    fullKernelComposition (coordinateProjectionKernel parameters 3 0) (encodedRotationKernel parameters) =
      fullZeroKernel parameters 3 1 := by
  unfold encodedRotationKernel angularInverseComponentKernel angularMeanFreeComponentKernel componentModeKernel
  rw [fullKernelComposition_add_inner]
  simp only [← fullKernelComposition_assoc, coordinateProjection_injection_distinct parameters 3 0 1 (by decide),
    coordinateProjection_injection_distinct parameters 3 0 2 (by decide), fullKernel_zero_comp, fullKernel_zero_add]

variable (parameters : PhaseParameters) (L rho alpha delta parameter epsilon compact : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤ actualEncodedFirstLowRadius parameters L compact)
    (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
    (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)

theorem actualUnknownVKernel_first_kernel :
    fullKernelComposition (coordinateProjectionKernel parameters 3 0)
      (actualUnknownVKernel parameters L rho alpha delta parameter epsilon compact field small
        compactNonnegative alphaSmall deltaSmall parameterSmall) = fullIdentityKernel parameters 1 := by
  unfold actualUnknownVKernel firstCoordinateInjectionKernel
  rw [fullKernelComposition_add_inner, ← fullKernelComposition_assoc, encodedRotationKernel_first,
    fullKernel_zero_comp, coordinateProjection_injection_same, fullKernel_zero_add]

theorem actualKnownRAStarKernel_first_kernel :
    fullKernelComposition (coordinateProjectionKernel parameters 3 0)
      (actualKnownRAStarKernel parameters L rho alpha delta parameter epsilon compact field small
        compactNonnegative alphaSmall deltaSmall parameterSmall) = fullZeroKernel parameters 7 1 := by
  unfold actualKnownRAStarKernel actualKnownRotatedQStarKernel secondCoordinateInjectionKernel
  rw [fullKernelComposition_add_inner, ← fullKernelComposition_assoc, encodedRotationKernel_first,
    fullKernel_zero_comp, ← fullKernelComposition_assoc,
    coordinateProjection_injection_distinct parameters 3 0 1 (by decide), fullKernel_zero_comp, fullKernel_zero_add]

end Grad.ActualBoundaryInverse
