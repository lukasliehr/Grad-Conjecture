import AKAS2InverseRotationWeights

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000

open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ActualAngularInverse Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger

/-- The input derivative of the TRUE inverse retains the primitive's
 resonant subtraction. The two angular integrations each carry their
 actual inverse covector. -/
def startupTrueInverseTensorKernel (input output : Fin 2) : StartupL2 3 →L[ℂ] StartupL2 3 :=
  startupCovectorAngularKernel (shiftPrimitiveKernel 0) (shiftPrimitiveKernel_smooth 0) input output -
    ∑ middle : Fin 2,
      (startupCovectorAngularKernel (shiftPrimitiveKernel 0) (shiftPrimitiveKernel_smooth 0) middle output).comp
        (startupCovectorAngularKernel (angularCharacter 0) (angularCharacter_smooth 0) input middle)

def startupTrueInverseTensorFirst (input output : Fin 2) : StartupFirst 3 →L[ℂ] StartupFirst 3 :=
  startupCovectorAngularFirst (shiftPrimitiveKernel 0) (shiftPrimitiveKernel_smooth 0) input output -
    ∑ middle : Fin 2,
      (startupCovectorAngularFirst (shiftPrimitiveKernel 0) (shiftPrimitiveKernel_smooth 0) middle output).comp
        (startupCovectorAngularFirst (angularCharacter 0) (angularCharacter_smooth 0) input middle)

theorem startupCompatible_sum {Index : Type*} [Fintype Index]
    {input output : ℕ}
    (coarse : Index → StartupL2 input →L[ℂ] StartupL2 output)
    (fine : Index → StartupFirst input →L[ℂ] StartupFirst output)
    (compatible : ∀ index, StartupCompatible (coarse index) (fine index)) :
    StartupCompatible (∑ index, coarse index) (∑ index, fine index) := by
  intro field
  simp only [sum_apply, map_sum]
  exact Finset.sum_congr rfl (fun index _ => compatible index field)

theorem startupTrueInverseTensor_compatible (input output : Fin 2) :
    StartupCompatible (startupTrueInverseTensorKernel input output) (startupTrueInverseTensorFirst input output) :=
  startupCompatible_sub
    (startupCovectorAngular_compatible (shiftPrimitiveKernel 0) (shiftPrimitiveKernel_smooth 0) input output)
    (startupCompatible_sum
      (fun middle : Fin 2 =>
        (startupCovectorAngularKernel (shiftPrimitiveKernel 0) (shiftPrimitiveKernel_smooth 0) middle output).comp
          (startupCovectorAngularKernel (angularCharacter 0) (angularCharacter_smooth 0) input middle))
      (fun middle : Fin 2 =>
        (startupCovectorAngularFirst (shiftPrimitiveKernel 0) (shiftPrimitiveKernel_smooth 0) middle output).comp
          (startupCovectorAngularFirst (angularCharacter 0) (angularCharacter_smooth 0) input middle))
      (fun middle : Fin 2 => startupCompatible_comp
        (startupCovectorAngular_compatible (shiftPrimitiveKernel 0) (shiftPrimitiveKernel_smooth 0) middle output)
        (startupCovectorAngular_compatible (angularCharacter 0) (angularCharacter_smooth 0) input middle)))

end Grad.CartesianStartup
