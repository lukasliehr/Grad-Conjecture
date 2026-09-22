import BKB7KernelComposition

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace

def fullZeroKernel (parameters : PhaseParameters)
    (sourceDimension targetDimension : ℕ) :
    FullTwoFrequencyKernel parameters sourceDimension targetDimension :=
  finiteKernelAsFull parameters 0

@[simp] theorem fullZeroKernel_entry (parameters : PhaseParameters)
    (sourceDimension targetDimension : ℕ) (shift input : ℤ × ℤ) :
    (fullZeroKernel parameters sourceDimension targetDimension).entry shift input = 0 := rfl

def fullIdentityFiniteKernel (dimension : ℕ) :
    FiniteTwoFrequencyKernel dimension dimension :=
  Finsupp.single (0, 0)
    (ContinuousLinearMap.id ℂ (ComplexEuclidean dimension))

def fullIdentityKernel (parameters : PhaseParameters) (dimension : ℕ) :
    FullTwoFrequencyKernel parameters dimension dimension :=
  finiteKernelAsFull parameters (fullIdentityFiniteKernel dimension)

theorem fullIdentityKernel_entry_zero (parameters : PhaseParameters)
    (dimension : ℕ) (input : ℤ × ℤ) :
    (fullIdentityKernel parameters dimension).entry (0, 0) input =
      ContinuousLinearMap.id ℂ (ComplexEuclidean dimension) := by
  simp [fullIdentityKernel, fullIdentityFiniteKernel, finiteKernelAsFull_entry]

theorem fullIdentityKernel_entry_ne_zero (parameters : PhaseParameters)
    (dimension : ℕ) (shift input : ℤ × ℤ) (nonzero : shift ≠ (0, 0)) :
    (fullIdentityKernel parameters dimension).entry shift input = 0 := by
  simp [fullIdentityKernel, fullIdentityFiniteKernel, finiteKernelAsFull_entry,
    nonzero]

def fullKernelAdd {sourceDimension targetDimension : ℕ}
    {parameters : PhaseParameters}
    (first second : FullTwoFrequencyKernel parameters sourceDimension targetDimension) :
    FullTwoFrequencyKernel parameters sourceDimension targetDimension :=
  fullKernelOfEntries parameters
    (fun shift input => first.entry shift input + second.entry shift input)
    (fun shift => first.entryNorm shift + second.entryNorm shift)
    (fun shift input => (norm_add_le _ _).trans
      (add_le_add (first.entry_le shift input) (second.entry_le shift input)))
    (fun moment => ((first.moments moment).add (second.moments moment)).congr
      (fun shift => by ring))

@[simp] theorem fullKernelAdd_entry {sourceDimension targetDimension : ℕ}
    {parameters : PhaseParameters}
    (first second : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (shift input : ℤ × ℤ) :
    (fullKernelAdd first second).entry shift input =
      first.entry shift input + second.entry shift input := rfl

def fullKernelNeg {sourceDimension targetDimension : ℕ}
    {parameters : PhaseParameters}
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension) :
    FullTwoFrequencyKernel parameters sourceDimension targetDimension :=
  fullKernelOfEntries parameters
    (fun shift input => -kernel.entry shift input)
    kernel.entryNorm
    (fun shift input => by simpa only [norm_neg] using kernel.entry_le shift input)
    kernel.moments

@[simp] theorem fullKernelNeg_entry {sourceDimension targetDimension : ℕ}
    {parameters : PhaseParameters}
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (shift input : ℤ × ℤ) :
    (fullKernelNeg kernel).entry shift input = -kernel.entry shift input := rfl

def fullKernelSub {sourceDimension targetDimension : ℕ}
    {parameters : PhaseParameters}
    (first second : FullTwoFrequencyKernel parameters sourceDimension targetDimension) :
    FullTwoFrequencyKernel parameters sourceDimension targetDimension :=
  fullKernelAdd first (fullKernelNeg second)

@[simp] theorem fullKernelSub_entry {sourceDimension targetDimension : ℕ}
    {parameters : PhaseParameters}
    (first second : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (shift input : ℤ × ℤ) :
    (fullKernelSub first second).entry shift input =
      first.entry shift input - second.entry shift input := by
  rfl

def fullKernelSmul {sourceDimension targetDimension : ℕ}
    {parameters : PhaseParameters} (scalar : ℂ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension) :
    FullTwoFrequencyKernel parameters sourceDimension targetDimension :=
  fullKernelOfEntries parameters
    (fun shift input => scalar • kernel.entry shift input)
    (fun shift => ‖scalar‖ * kernel.entryNorm shift)
    (fun shift input => (ContinuousLinearMap.opNorm_smul_le scalar
      (kernel.entry shift input)).trans
        (mul_le_mul_of_nonneg_left (kernel.entry_le shift input) (norm_nonneg scalar)))
    (fun moment => (kernel.moments moment).mul_right ‖scalar‖ |>.congr
      (fun shift => by ring))

@[simp] theorem fullKernelSmul_entry {sourceDimension targetDimension : ℕ}
    {parameters : PhaseParameters} (scalar : ℂ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (shift input : ℤ × ℤ) :
    (fullKernelSmul scalar kernel).entry shift input =
      scalar • kernel.entry shift input := rfl

theorem fullKernelAdd_entryNorm_le {sourceDimension targetDimension : ℕ}
    {parameters : PhaseParameters}
    (first second : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (shift : ℤ × ℤ) :
    (fullKernelAdd first second).entryNorm shift ≤
      first.entryNorm shift + second.entryNorm shift :=
  fullKernelOfEntries_entryNorm_le parameters _ _ _ _ shift

theorem fullKernelNeg_entryNorm_le {sourceDimension targetDimension : ℕ}
    {parameters : PhaseParameters}
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (shift : ℤ × ℤ) :
    (fullKernelNeg kernel).entryNorm shift ≤ kernel.entryNorm shift :=
  fullKernelOfEntries_entryNorm_le parameters _ _ _ _ shift

theorem fullKernelSmul_entryNorm_le {sourceDimension targetDimension : ℕ}
    {parameters : PhaseParameters} (scalar : ℂ)
    (kernel : FullTwoFrequencyKernel parameters sourceDimension targetDimension)
    (shift : ℤ × ℤ) :
    (fullKernelSmul scalar kernel).entryNorm shift ≤
      ‖scalar‖ * kernel.entryNorm shift :=
  fullKernelOfEntries_entryNorm_le parameters _ _ _ _ shift

end Grad.BoundaryKernelAction
