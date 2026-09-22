import AIX8CompletedScalarKernelAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularKernelOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularKernelContinuity

variable {src tgt : ℕ} (parameters : PhaseParameters)
    (kernel : (r : RadialPoint) → RadialKernel parameters r src tgt) (regular : RegularKernelFamily kernel)

include regular in
theorem kernelOrbitRemainder_regular (tau step : OrbitParameter) (angular cell : ℕ) :
    RegularKernelFamily (fun r => kernelOrbitRemainder tau step angular cell (kernel r)) :=
  displacementKernel_regular parameters kernel regular (orbitRemainderFactor tau step angular cell)
    (angular + cell + 2) (3 * orbitStepSize step ^ 2) (by positivity)
    (orbitRemainderFactor_bound tau step angular cell)

def radialOrbitRemainderAction (power : ℕ) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (tau step : OrbitParameter) (angular cell : ℕ) : DivisionRow src lower →L[ℂ] DivisionRow tgt lower :=
  regularRadialBulkAction parameters power lower positive bounded
    (fun r => kernelOrbitRemainder tau step angular cell (kernel r))
    (kernelOrbitRemainder_regular parameters kernel regular tau step angular cell)

/-- Exact quadratic Taylor residual for the ACTUAL completed operators. -/
theorem radialOrbitRemainderAction_eq (power : ℕ) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (tau step : OrbitParameter) (angular cell : ℕ) :
    radialOrbitRemainderAction parameters kernel regular power lower positive bounded tau step angular cell =
      radialOrbitJetAction parameters kernel regular power lower positive bounded (tau + step) angular cell -
      radialOrbitJetAction parameters kernel regular power lower positive bounded tau angular cell -
      (step.1 : ℂ) • radialOrbitJetAction parameters kernel regular power lower positive bounded tau (angular + 1) cell -
      (step.2 : ℂ) • radialOrbitJetAction parameters kernel regular power lower positive bounded tau angular (cell + 1) := by
  let plus := kernelOrbitJet_regular parameters kernel regular (tau + step) angular cell
  let base := kernelOrbitJet_regular parameters kernel regular tau angular cell
  let first := kernelOrbitJet_regular parameters kernel regular tau (angular + 1) cell
  let second := kernelOrbitJet_regular parameters kernel regular tau angular (cell + 1)
  let firstScaled := constantSmulKernel_regular parameters (fun r => kernelOrbitJet tau (angular + 1) cell (kernel r)) first (step.1 : ℂ)
  let secondScaled := constantSmulKernel_regular parameters (fun r => kernelOrbitJet tau angular (cell + 1) (kernel r)) second (step.2 : ℂ)
  let residual := ((plus.sub base).sub firstScaled).sub secondScaled
  calc
    _ = regularRadialBulkAction parameters power lower positive bounded
        (fun r => fullKernelSub
          (fullKernelSub (fullKernelSub (kernelOrbitJet (tau + step) angular cell (kernel r))
            (kernelOrbitJet tau angular cell (kernel r)))
            (fullKernelSmul (step.1 : ℂ) (kernelOrbitJet tau (angular + 1) cell (kernel r))))
          (fullKernelSmul (step.2 : ℂ) (kernelOrbitJet tau angular (cell + 1) (kernel r)))) residual :=
      regularRadialBulkAction_congr parameters power lower positive bounded
        (fun r => kernelOrbitRemainder tau step angular cell (kernel r))
        (kernelOrbitRemainder_regular parameters kernel regular tau step angular cell) _ residual
        (fun r => kernelOrbitRemainder_identity tau step angular cell (kernel r))
    _ = _ := by
      rw [regularRadialBulkAction_sub parameters power lower positive bounded _ ((plus.sub base).sub firstScaled) _ secondScaled]
      rw [regularRadialBulkAction_sub parameters power lower positive bounded _ (plus.sub base) _ firstScaled]
      rw [regularRadialBulkAction_sub parameters power lower positive bounded _ plus _ base]
      rw [regularAction_smul parameters _ first power lower positive bounded (step.1 : ℂ),
        regularAction_smul parameters _ second power lower positive bounded (step.2 : ℂ)]
      rfl

/-- Operator norm remainder with two next displacement moments; the
constant and radius domain are exactly those of the original kernel family. -/
theorem radialOrbitJetAction_remainder_bound (power : ℕ) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (tau step : OrbitParameter) (angular cell : ℕ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (momentBound : ∀ r, fullKernelMoment (radialKernelParameters parameters r)
      (power + (angular + cell + 2)) (kernel r) ≤ constant) :
    ‖radialOrbitJetAction parameters kernel regular power lower positive bounded (tau + step) angular cell -
      radialOrbitJetAction parameters kernel regular power lower positive bounded tau angular cell -
      (step.1 : ℂ) • radialOrbitJetAction parameters kernel regular power lower positive bounded tau (angular + 1) cell -
      (step.2 : ℂ) • radialOrbitJetAction parameters kernel regular power lower positive bounded tau angular (cell + 1)‖ ≤
        3 * orbitStepSize step ^ 2 * constant := by
  rw [← radialOrbitRemainderAction_eq]
  apply regularAction_norm_le parameters (fun r => kernelOrbitRemainder tau step angular cell (kernel r))
    (kernelOrbitRemainder_regular parameters kernel regular tau step angular cell) power lower positive bounded
    (3 * orbitStepSize step ^ 2 * constant) (by positivity)
  intro radius
  exact (kernelOrbitRemainder_moment_le tau step angular cell (kernel radius) power).trans
    (mul_le_mul_of_nonneg_left (momentBound radius) (by positivity))

end Grad.AnnularKernelOrbit
