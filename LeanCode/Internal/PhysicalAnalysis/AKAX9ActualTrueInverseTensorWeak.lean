import AKAX8TrueInverseCompactTranspose

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets

/-- The elementary finite composition identity retains the order of both angular kernels. -/
theorem startupMeanCovectorAlgebra {Field : Type*} [NormedAddCommGroup Field] [NormedSpace ℂ Field]
    (pairings : Fin 2 → Field →L[ℂ] ℂ)
    (primitive mean : Fin 2 → Fin 2 → Field →L[ℂ] Field) (input : Fin 2) :
    (∑ output : Fin 2, (pairings output).comp (primitive input output)) -
      (∑ middle : Fin 2, (∑ output : Fin 2, (pairings output).comp (primitive middle output)).comp (mean input middle)) =
      ∑ output : Fin 2, (pairings output).comp
        (primitive input output - ∑ middle : Fin 2, (primitive middle output).comp (mean input middle)) := by
  ext field
  simp only [sub_apply, sum_apply, ContinuousLinearMap.comp_apply, map_sub, map_sum, Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_comm

/-- The actual true-Z0 inverse tensor is exactly the weak input-derivative transfer.
 Both inverse covectors and the resonant subtraction are present in the literal stored kernel. -/
theorem startupTestPairing_trueInverseDerivative (cell : ℤ) (vector : PhysicalValue 3)
    (test : TestFunction openUnitDisk) (input : Fin 2) :
    startupTestPairing cell vector (startupDerivativeTest input (startupTrueInverseTest test)) =
      ∑ output : Fin 2,
        (startupTestPairing cell vector (startupDerivativeTest output test)).comp
          (startupTrueInverseTensorKernel input output) := by
  simp only [startupTrueInverseTest, startupDerivativeTest_sub, startupTestPairing_sub,
    startupTestPairing_angularDerivative, startupTrueInverseTensor_real]
  exact startupMeanCovectorAlgebra
    (fun output => startupTestPairing cell vector (startupDerivativeTest output test))
    (fun middle output => startupRealAngularKernel (startupRealCovectorWeight (fun angle : ℝ => angle) middle output)
      (startupRealCovectorWeight_smooth (fun angle : ℝ => angle) contDiff_id middle output))
    (fun middle output => startupRealAngularKernel (startupRealCovectorWeight (fun _ : ℝ => 1) middle output)
      (startupRealCovectorWeight_smooth (fun _ : ℝ => 1) contDiff_const middle output)) input

/-- Exact weak second-order tensor identity for every rough full-cell L2 field. -/
theorem startupTrueInverseTensor_mixedWeak (cell : ℤ) (vector : PhysicalValue 3)
    (test : TestFunction openUnitDisk) (field : StartupL2 3) (outer input : Fin 2) :
    startupTestPairing cell vector (startupDerivativeTest input
      (startupTrueInverseTest (startupDerivativeTest outer test))) field =
      ∑ output : Fin 2,
        startupTestPairing cell vector (startupDerivativeTest output (startupDerivativeTest outer test))
          (startupTrueInverseTensorKernel input output field) := by
  have identity := congrArg (fun pairing : StartupL2 3 →L[ℂ] ℂ => pairing field)
    (startupTestPairing_trueInverseDerivative cell vector (startupDerivativeTest outer test) input)
  simpa only [sum_apply, ContinuousLinearMap.comp_apply] using identity

end Grad.CartesianStartup
