import AHP13ActualRadialMassInverse

noncomputable section
set_option maxHeartbeats 1600000

namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger

/-- The two literal radial factors in AH20's seven-input coordinate order. -/
def radialSevenSlotNormalization (radius : ℝ) : ComplexEuclidean 7 →L[ℂ] ComplexEuclidean 7 :=
  matrixUnit 0 0 + (radius : ℂ)⁻¹ • matrixUnit 1 1 + matrixUnit 2 2 +
    (radius : ℂ)⁻¹ • matrixUnit 3 3 + matrixUnit 4 4 + matrixUnit 5 5 + matrixUnit 6 6

theorem radialSevenSlotNormalization_apply (radius : ℝ) (value : ComplexEuclidean 7) :
    radialSevenSlotNormalization radius value =
      WithLp.toLp 2 ![value 0, (radius : ℂ)⁻¹ * value 1, value 2,
        (radius : ℂ)⁻¹ * value 3, value 4, value 5, value 6] := by
  apply PiLp.ext
  intro component
  fin_cases component <;> simp [radialSevenSlotNormalization, matrixUnit_apply, operatorBasis]

theorem radialSevenSlotNormalization_one :
    radialSevenSlotNormalization 1 = ContinuousLinearMap.id ℂ (ComplexEuclidean 7) := by
  apply ContinuousLinearMap.ext
  intro value
  apply PiLp.ext
  intro component
  fin_cases component <;> simp [radialSevenSlotNormalization, matrixUnit_apply, operatorBasis]

def radialSevenSlotKernel (parameters : PhaseParameters) (r : RadialPoint) : RadialKernel parameters r 7 7 :=
  constantMatrixKernel (radialKernelParameters parameters r) 7 7 (radialSevenSlotNormalization r.val)

variable (parameters : PhaseParameters) (L compact : ℝ)
variable (state : RadialCoefficientState parameters L compact) (r : RadialPoint)
variable (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
  radialMassLowRadius parameters L compact)

def radialMassRightHandKernel : RadialKernel parameters r 7 1 :=
  fullKernelSub (sevenInputSlotKernel (radialKernelParameters parameters r) 0)
    (radialKnownJStarKernel parameters L compact state r (small.trans (min_le_left _ _)))

def radialRecoveredMassKernel : RadialKernel parameters r 7 1 :=
  fullKernelComposition (radialMassInverseKernel parameters L compact state r small)
    (radialMassRightHandKernel parameters L compact state r small)

def radialNormalizedCovariantKernel : RadialKernel parameters r 7 3 :=
  fullKernelAdd
    (fullKernelComposition
      (radialUnknownUKernel parameters L compact state r (small.trans (min_le_left _ _)))
      (radialRecoveredMassKernel parameters L compact state r small))
    (radialKnownAStarKernel parameters L compact state r (small.trans (min_le_left _ _)))

def radialNormalizedRotatedCovariantKernel : RadialKernel parameters r 7 3 :=
  fullKernelAdd
    (fullKernelComposition
      (radialUnknownVKernel parameters L compact state r (small.trans (min_le_left _ _)))
      (radialRecoveredMassKernel parameters L compact state r small))
    (radialKnownRAStarKernel parameters L compact state r (small.trans (min_le_left _ _)))

/-- Actual ordered AF16/AH20 kernel on the original seven slots. Positivity
of r is explicit; the source and scalar reciprocal-radius factors are never
silently evaluated at the outer circle. -/
def radialCovariantKernel (_positive : 0 < r.val) : RadialKernel parameters r 7 3 :=
  fullKernelComposition (radialNormalizedCovariantKernel parameters L compact state r small)
    (radialSevenSlotKernel parameters r)

def radialRotatedCovariantKernel (_positive : 0 < r.val) : RadialKernel parameters r 7 3 :=
  fullKernelComposition (radialNormalizedRotatedCovariantKernel parameters L compact state r small)
    (radialSevenSlotKernel parameters r)

theorem radialRecoveredMassKernel_solves :
    fullKernelComposition
      (fullKernelNegativeIdentityPerturbation (radialKernelParameters parameters r)
        (radialMassPerturbationKernel parameters L compact state r (small.trans (min_le_left _ _))))
      (radialRecoveredMassKernel parameters L compact state r small) =
        radialMassRightHandKernel parameters L compact state r small := by
  unfold radialRecoveredMassKernel
  rw [← fullKernelComposition_assoc,
    (radialMassInverseKernel_twoSided parameters L compact state r small).1,
    fullIdentityKernel_comp_rect]

/-- The exact left identity gives uniqueness for arbitrary input dimension,
so no restricted support or independently chosen source is assumed. -/
theorem radialMassEquation_unique {input : ℕ}
    (candidate : RadialKernel parameters r input 1)
    (rightHand : RadialKernel parameters r input 1)
    (equation : fullKernelComposition
      (fullKernelNegativeIdentityPerturbation (radialKernelParameters parameters r)
        (radialMassPerturbationKernel parameters L compact state r (small.trans (min_le_left _ _))))
      candidate = rightHand) :
    candidate = fullKernelComposition (radialMassInverseKernel parameters L compact state r small) rightHand := by
  rw [← equation, ← fullKernelComposition_assoc,
    (radialMassInverseKernel_twoSided parameters L compact state r small).2,
    fullIdentityKernel_comp_rect]

end Grad.AnnularReconstruction
