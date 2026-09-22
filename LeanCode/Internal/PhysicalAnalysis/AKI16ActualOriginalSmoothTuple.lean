import AKI15OriginalIndependentResidualCoordinates
import AKF14ActualSameWeightedRadialRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.AnnularOriginalSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.AnnularSmoothCore
open Grad.AnnularStrongOrbit Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.AnnularCurrentLow Grad.AnnularKnownLow Grad.AnnularSourceGraph Grad.AnnularPhysicalFourier
open Grad.AnnularWeightedSmoothCore Grad.AnnularWeightedSystem Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (core : OriginalSmoothSourceCore parameters)

/-- An actual literal four-field smooth tuple of the SAME inverse. All
original weighted radial/tangential regularity is proved unconditionally. -/
def originalSmoothResponseCoreTuple : OriginalSmoothTuple parameters lower :=
  sameResponseOriginalTuple parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core
    (originalSmoothResponse_phaseWeighted_radial parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core)

theorem originalSmoothResponseCoreTuple_F1 :
    ∀ᵐ location ∂volume.restrict (Icc lower 1), ∀ inside : location ∈ Icc lower 1, ∀ mode,
      originalTupleF1 parameters length compact lower positive state
        (originalSmoothResponseCoreTuple parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core)
        ⟨location, inside⟩ mode =
      originalF1Coefficient parameters lower positive (lowerHalf.trans (by norm_num))
        (originalSmoothStrongData parameters lower positive (lowerHalf.trans (by norm_num)) core).val.ofLp.1.ofLp.2.ofLp.1 location mode := by
  filter_upwards [sameResponseOriginalTuple_F1_projected parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core
      (originalSmoothResponse_phaseWeighted_radial parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core),
    originalF1Coefficient_meanFree parameters lower positive (lowerHalf.trans (by norm_num))
      (originalSmoothStrongData parameters lower positive (lowerHalf.trans (by norm_num)) core).val.ofLp.1.ofLp.2.ofLp.1
      (OriginalStrongCarrier.mean_free parameters lower 0 0 (originalSmoothStrongData parameters lower positive (lowerHalf.trans (by norm_num)) core)).2.1]
    with location residual mean
  intro inside mode
  exact (residual inside mode).trans ((congrArg (fun value => (if mode.1 = 0 then (0 : ℂ) else 1) • value)
    (actualOriginalIndependentF_original parameters length lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive core location mode)).trans (mean mode))

theorem originalSmoothResponseCoreTuple_G3 :
    ∀ᵐ location ∂volume.restrict (Icc lower 1), ∀ inside : location ∈ Icc lower 1, ∀ mode,
      originalTupleG3 parameters length compact lower positive state
        (originalSmoothResponseCoreTuple parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core)
        ⟨location, inside⟩ mode =
      originalG3Coefficient parameters lower positive (lowerHalf.trans (by norm_num))
        (originalSmoothStrongData parameters lower positive (lowerHalf.trans (by norm_num)) core).val.ofLp.1.ofLp.2.ofLp.2 location mode := by
  filter_upwards [sameResponseOriginalTuple_G3_projected parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core
      (originalSmoothResponse_phaseWeighted_radial parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core),
    originalG3Coefficient_meanFree parameters lower positive (lowerHalf.trans (by norm_num))
      (originalSmoothStrongData parameters lower positive (lowerHalf.trans (by norm_num)) core).val.ofLp.1.ofLp.2.ofLp.2
      (OriginalStrongCarrier.mean_free parameters lower 0 0 (originalSmoothStrongData parameters lower positive (lowerHalf.trans (by norm_num)) core)).2.2]
    with location residual mean
  intro inside mode
  exact (residual inside mode).trans ((congrArg (fun value => (if mode.1 = 0 then (0 : ℂ) else 1) • value)
    (actualOriginalIndependentG_original parameters length lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive core location mode)).trans (mean mode))

theorem originalSmoothResponseCoreTuple_strengthenedG3 :
    ∀ᵐ location ∂volume.restrict (Icc lower 1), ∀ inside : location ∈ Icc lower 1, ∀ mode,
      ((1 + |(mode.1 : ℝ)| : ℝ) : ℂ) • originalTupleG3 parameters length compact lower positive state
        (originalSmoothResponseCoreTuple parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core)
        ⟨location, inside⟩ mode =
      originalF1Coefficient parameters lower positive (lowerHalf.trans (by norm_num))
        (originalSmoothStrongData parameters lower positive (lowerHalf.trans (by norm_num)) core).val.ofLp.1.ofLp.2.ofLp.2 location mode := by
  filter_upwards [originalSmoothResponseCoreTuple_G3 parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core,
    originalG3Coefficient_strengthened parameters lower positive (lowerHalf.trans (by norm_num))
      (originalSmoothStrongData parameters lower positive (lowerHalf.trans (by norm_num)) core).val.ofLp.1.ofLp.2.ofLp.2] with location same original
  intro inside mode
  rw [same inside mode, original mode]

end Grad.AnnularOriginalSmoothCore
