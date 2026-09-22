import AKDD10ActualCompositionOriginalPhase

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.AnnularRadialSmoothness

attribute [local irreducible] fullKernelComposition fullKernelAdd fullKernelNeg fullKernelSmul polynomialKernelAction
  KernelEulerDerivativeTower OriginalEulerMoments

/-- Internal assembly certificate: the base is an already defined actual
family. Every constructor supplies its literal rank-zero equality. -/
structure EulerFamilyData {State Radius : Type} (Kernel : Radius → Type)
    (base : State → (radius : Radius) → Kernel radius)
    (Derivative : (ℕ → (radius : Radius) → Kernel radius) → Prop)
    (Moments : (State → ℕ → (radius : Radius) → Kernel radius) → Prop) where
  kernels : State → ℕ → (radius : Radius) → Kernel radius
  zero : ∀ state radius, kernels state 0 radius = base state radius
  derivative : ∀ state, Derivative (kernels state)
  moments : Moments kernels

abbrev ActualEulerFamily (parameters : PhaseParameters) (L compact : ℝ) {source target : ℕ}
    (base : (state : AnnularReconstructionState parameters L compact) →
      (radius : RadialPoint) → RadialKernel parameters radius source target) :=
  EulerFamilyData (fun radius => RadialKernel parameters radius source target) base
    (fun kernels => ∀ (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1),
      KernelEulerDerivativeTower parameters lower positive bounded.le kernels)
    (OriginalEulerMoments parameters L compact)

namespace ActualEulerFamily
variable {parameters : PhaseParameters} {L compact : ℝ} {source middle target : ℕ}

def fixed (parameters : PhaseParameters) (L compact : ℝ)
    (family : (phase : PhaseParameters) → FullTwoFrequencyKernel phase source target)
    (same : ∀ first second, SameKernelEntries (family first) (family second)) :
    ActualEulerFamily parameters L compact (fun _ radius => family (radialKernelParameters parameters radius)) where
  kernels _ := fixedEulerKernel parameters family
  zero _ _ := rfl
  derivative _ lower positive bounded := fixedEulerKernel_derivativeTower parameters lower positive bounded.le family same
  moments := OriginalEulerMoments.fixed parameters L compact family same

def comp {outer : (state : AnnularReconstructionState parameters L compact) →
      (radius : RadialPoint) → RadialKernel parameters radius middle target}
    {inner : (state : AnnularReconstructionState parameters L compact) →
      (radius : RadialPoint) → RadialKernel parameters radius source middle}
    (one : ActualEulerFamily parameters L compact outer) (two : ActualEulerFamily parameters L compact inner) :
    ActualEulerFamily parameters L compact (fun state radius => fullKernelComposition (outer state radius) (inner state radius)) where
  kernels state := composedEulerKernel (one.kernels state) (two.kernels state)
  zero state radius := by rw [composedEulerKernel_zero,one.zero,two.zero]
  derivative state lower positive bounded := KernelEulerDerivativeTower.comp parameters lower positive bounded.le
    (one.kernels state) (two.kernels state) (one.derivative state lower positive bounded) (two.derivative state lower positive bounded)
  moments := one.moments.comp two.moments

def add {first second : (state : AnnularReconstructionState parameters L compact) →
      (radius : RadialPoint) → RadialKernel parameters radius source target}
    (one : ActualEulerFamily parameters L compact first) (two : ActualEulerFamily parameters L compact second) :
    ActualEulerFamily parameters L compact (fun state radius => fullKernelAdd (first state radius) (second state radius)) where
  kernels state rank radius := fullKernelAdd (one.kernels state rank radius) (two.kernels state rank radius)
  zero state radius := by rw [one.zero,two.zero]
  derivative state lower positive bounded := KernelEulerDerivativeTower.add parameters lower positive bounded.le
    (one.kernels state) (two.kernels state) (one.derivative state lower positive bounded) (two.derivative state lower positive bounded)
  moments := one.moments.add two.moments

def neg {base : (state : AnnularReconstructionState parameters L compact) →
      (radius : RadialPoint) → RadialKernel parameters radius source target}
    (family : ActualEulerFamily parameters L compact base) :
    ActualEulerFamily parameters L compact (fun state radius => fullKernelNeg (base state radius)) where
  kernels state rank radius := fullKernelNeg (family.kernels state rank radius)
  zero state radius := by rw [family.zero]
  derivative state lower positive bounded := KernelEulerDerivativeTower.neg parameters lower positive bounded.le
    (family.kernels state) (family.derivative state lower positive bounded)
  moments := family.moments.neg

def sub {first second : (state : AnnularReconstructionState parameters L compact) →
      (radius : RadialPoint) → RadialKernel parameters radius source target}
    (one : ActualEulerFamily parameters L compact first) (two : ActualEulerFamily parameters L compact second) :
    ActualEulerFamily parameters L compact (fun state radius => fullKernelSub (first state radius) (second state radius)) :=
  one.add two.neg

/-- The inverse constructor uses the accepted base inverse estimate and
actual inverse differentiability, retaining the original inverse kernel. -/
def negativeInverse {dimension : ℕ}
    {base : (state : AnnularReconstructionState parameters L compact) →
      (radius : RadialPoint) → RadialKernel parameters radius dimension dimension}
    (family : ActualEulerFamily parameters L compact base)
    (smooth : ∀ (state : AnnularReconstructionState parameters L compact) (lower : ℝ)
      (positive : 0 < lower) (bounded : lower < 1), SmoothPolynomialFamily parameters lower positive bounded.le (base state))
    (low : ℝ) (small : low < 1)
    (lowBound : ∀ state radius, fullKernelMoment (radialKernelParameters parameters radius) 0 (base state radius) ≤ low)
    (baseMoments : RadialPhysicalMoments parameters L compact (fun state radius =>
      fullKernelNegativeIdentityInverse (radialKernelParameters parameters radius) (base state radius) low (lowBound state radius) small)) :
    ActualEulerFamily parameters L compact (fun state radius =>
      fullKernelNegativeIdentityInverse (radialKernelParameters parameters radius) (base state radius) low (lowBound state radius) small) := by
  have same (state : AnnularReconstructionState parameters L compact) : family.kernels state 0 = base state := funext (family.zero state)
  let bound := fun state radius => (congrArg (fun kernel => fullKernelMoment (radialKernelParameters parameters radius) 0 kernel)
    (family.zero state radius)).le.trans (lowBound state radius)
  refine ⟨(fun state rank radius => sameNegativeInverseEulerKernel parameters radius (fun raw => family.kernels state raw radius)
    low small (bound state radius) rank),?_,?_,?_⟩
  · intro state radius
    rw [sameNegativeInverseEulerKernel_zero]
    simp only [family.zero]
  · intro state lower positive bounded
    apply KernelEulerDerivativeTower.negativeInverse parameters lower positive bounded.le
      (family.kernels state) (family.derivative state lower positive bounded)
    rw [same state]
    exact smooth state lower positive bounded
  · apply family.moments.negativeInverse low small bound
    have allSame : (fun state radius => fullKernelNegativeIdentityInverse (radialKernelParameters parameters radius)
        (family.kernels state 0 radius) low (bound state radius) small) =
        (fun state radius => fullKernelNegativeIdentityInverse (radialKernelParameters parameters radius)
          (base state radius) low (lowBound state radius) small) := by
      funext state radius
      simp only [family.zero]
    rw [allSame]
    exact baseMoments

end ActualEulerFamily
end Grad.OriginalCartesianTameEstimate
