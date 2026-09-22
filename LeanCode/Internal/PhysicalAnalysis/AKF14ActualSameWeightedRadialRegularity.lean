import AKF13SameWeightedRadialBootstrap
import AKC29OriginalPhysicalRowConjugatedRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.AnnularWeightedSystem
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit Grad.AnnularVariational
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.PhaseAlgebra Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularHighGenerators Grad.AnnularCurrentLow Grad.AnnularStrongSolution
open Grad.AnnularWeightedSmoothness Grad.AnnularKernelL2

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (core : OriginalSmoothSourceCore parameters)

/-- The SAME full original inverse has every phase-weighted radial and
Fourier grade on the entire closed collar. Actual kernel regularity and the
genuine coordinate PDE are discharged; original B8 and analytic widths remain. -/
theorem originalSmoothResponse_phaseWeighted_radial :
    ∀ grade, ContDiffOn ℝ ∞
      (conjugatedSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small core grade) (Icc lower 1) :=
  conjugatedSmoothResponse_smooth_of_kernelOrders parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small core
    (fun row grade order => originalPhysicalRowKernel_finiteOrder parameters length compact state lower positive
      (lowerHalf.trans_lt (by norm_num)) row grade order)

/-- The smooth weighted representatives belong to the SAME physical inverse,
coefficient by coefficient and including both original collar endpoints. -/
theorem originalSmoothResponse_phaseWeighted_sameField :
    ∃ curve : ℕ → ℝ → PhysicalHilbertPair,
      (∀ grade, ContDiffOn ℝ ∞ (curve grade) (Icc lower 1)) ∧
      ∀ grade radius, radius ∈ Icc lower 1 → ∀ mode : ℤ × ℤ,
        hilbertPairCoefficient mode (curve grade radius) =
          Real.exp (radialPhase parameters radius mode.2) •
            hilbertPairCoefficient mode
              (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive
                widthHalf widthLength state small core grade radius) :=
  ⟨conjugatedSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core,
    originalSmoothResponse_phaseWeighted_radial parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core,
    fun grade radius inside mode => conjugatedSmoothResponsePairCurve_physical parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core grade mode radius inside⟩

end Grad.AnnularWeightedSystem
