import BCI4ExactReconstructionRows

noncomputable section
set_option maxHeartbeats 1200000
namespace Grad.ActualBoundaryInverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation

def IgnoresFirstSlot {parameters : PhaseParameters} {output : ℕ}
    (kernel : FullTwoFrequencyKernel parameters 7 output) : Prop :=
  fullKernelComposition kernel (coordinateInjectionKernel parameters 7 0) = fullZeroKernel parameters 1 output

theorem IgnoresFirstSlot.comp {parameters : PhaseParameters} {middle output : ℕ}
    (outer : FullTwoFrequencyKernel parameters middle output)
    {inner : FullTwoFrequencyKernel parameters 7 middle} (ignored : IgnoresFirstSlot inner) :
    IgnoresFirstSlot (fullKernelComposition outer inner) := by
  unfold IgnoresFirstSlot at *
  rw [fullKernelComposition_assoc, ignored, fullKernel_comp_zero]

theorem IgnoresFirstSlot.add {parameters : PhaseParameters} {output : ℕ}
    {first second : FullTwoFrequencyKernel parameters 7 output}
    (hfirst : IgnoresFirstSlot first) (hsecond : IgnoresFirstSlot second) :
    IgnoresFirstSlot (fullKernelAdd first second) := by
  unfold IgnoresFirstSlot at *
  rw [fullKernelComposition_add_outer, hfirst, hsecond, fullKernel_zero_add]

theorem IgnoresFirstSlot.neg {parameters : PhaseParameters} {output : ℕ}
    {kernel : FullTwoFrequencyKernel parameters 7 output} (ignored : IgnoresFirstSlot kernel) :
    IgnoresFirstSlot (fullKernelNeg kernel) := by
  unfold IgnoresFirstSlot at *
  rw [fullKernelComposition_neg_outer, ignored]
  apply FullTwoFrequencyKernel.ext_entry
  intro shift frequency
  simp [fullKernelNeg_entry, fullZeroKernel_entry]

theorem IgnoresFirstSlot.sub {parameters : PhaseParameters} {output : ℕ}
    {first second : FullTwoFrequencyKernel parameters 7 output}
    (hfirst : IgnoresFirstSlot first) (hsecond : IgnoresFirstSlot second) :
    IgnoresFirstSlot (fullKernelSub first second) := by
  exact hfirst.add hsecond.neg

theorem IgnoresFirstSlot.smul {parameters : PhaseParameters} {output : ℕ}
    {kernel : FullTwoFrequencyKernel parameters 7 output} (ignored : IgnoresFirstSlot kernel)
    (scalar : ℂ) : IgnoresFirstSlot (fullKernelSmul scalar kernel) := by
  unfold IgnoresFirstSlot at *
  apply FullTwoFrequencyKernel.ext_entry
  intro shift frequency
  rw [coordinateInjectionKernel, constantKernel_inner_entry]
  have original := congrArg (fun current : FullTwoFrequencyKernel parameters 1 output => current.entry shift frequency) ignored
  rw [coordinateInjectionKernel, constantKernel_inner_entry, fullZeroKernel_entry] at original
  rw [fullKernelSmul_entry, ContinuousLinearMap.smul_comp, original, fullZeroKernel_entry]
  exact @smul_zero ℂ (ComplexEuclidean 1 →L[ℂ] ComplexEuclidean output) _ _ scalar

theorem sevenInputSlotKernel_ignores (parameters : PhaseParameters) (slot : Fin 7) (nonzero : slot ≠ 0) :
    IgnoresFirstSlot (sevenInputSlotKernel parameters slot) :=
  coordinateProjection_injection_distinct parameters 7 slot 0 nonzero

variable (parameters : PhaseParameters) (L rho alpha delta parameter epsilon compact : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤ actualEncodedFirstLowRadius parameters L compact)
    (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
    (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)

theorem actualKnownAStarKernel_ignores :
    IgnoresFirstSlot (actualKnownAStarKernel parameters L rho alpha delta parameter epsilon compact field small
      compactNonnegative alphaSmall deltaSmall parameterSmall) := by
  unfold actualKnownAStarKernel actualKnownEncodedWKernel actualKnownEncodedDataKernel
    actualKnownEncodedD0Kernel actualKnownEncodedD1Kernel actualKnownEncodedD2Kernel
    actualKnownQStarKernel actualKnownRotatedQStarKernel
  with_reducible repeat' first
    | apply IgnoresFirstSlot.comp
    | apply IgnoresFirstSlot.add
    | apply IgnoresFirstSlot.sub
    | apply IgnoresFirstSlot.neg
    | apply IgnoresFirstSlot.smul
    | exact sevenInputSlotKernel_ignores parameters _ (by decide)

theorem actualKnownRAStarKernel_ignores :
    IgnoresFirstSlot (actualKnownRAStarKernel parameters L rho alpha delta parameter epsilon compact field small
      compactNonnegative alphaSmall deltaSmall parameterSmall) := by
  unfold actualKnownRAStarKernel actualKnownEncodedWKernel actualKnownEncodedDataKernel
    actualKnownEncodedD0Kernel actualKnownEncodedD1Kernel actualKnownEncodedD2Kernel
    actualKnownQStarKernel actualKnownRotatedQStarKernel
  with_reducible repeat' first
    | apply IgnoresFirstSlot.comp
    | apply IgnoresFirstSlot.add
    | apply IgnoresFirstSlot.sub
    | apply IgnoresFirstSlot.neg
    | apply IgnoresFirstSlot.smul
    | exact sevenInputSlotKernel_ignores parameters _ (by decide)

theorem actualKnownJStarKernel_ignores :
    IgnoresFirstSlot (actualKnownJStarKernel parameters L rho alpha delta parameter epsilon compact field small
      compactNonnegative alphaSmall deltaSmall parameterSmall) := by
  unfold actualKnownJStarKernel
  with_reducible repeat' first
    | exact actualKnownAStarKernel_ignores parameters L rho alpha delta parameter epsilon compact field small
        compactNonnegative alphaSmall deltaSmall parameterSmall
    | exact actualKnownRAStarKernel_ignores parameters L rho alpha delta parameter epsilon compact field small
        compactNonnegative alphaSmall deltaSmall parameterSmall
    | apply IgnoresFirstSlot.comp
    | apply IgnoresFirstSlot.add
    | exact sevenInputSlotKernel_ignores parameters _ (by decide)

end Grad.ActualBoundaryInverse
