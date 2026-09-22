import AKDQ14RotatedSampledTimeDerivative

noncomputable section
open Set
open scoped ContDiff

namespace Grad.PhysicalEquilibrium
open Grad.MainTarget Grad.PhysicalFamily

/-- Algebraic contraction of the literal ambient force after its two chain
rules. The chain rules are supplied for the actual reconstructed fields. -/
theorem pullback_force_pairing
    (position magneticLift : Vec → Vec) (pressureLift : Vec → ℝ)
    (magnetic : Vec → Vec) (pressure : Vec → ℝ) (point angular direction : Vec)
    (value : magnetic (position point) = magneticLift point)
    (pushforward : fderiv ℝ position point angular = magneticLift point)
    (magneticChain : (fderiv ℝ magnetic (position point)).comp (fderiv ℝ position point) =
      fderiv ℝ magneticLift point)
    (pressureChain : (fderiv ℝ pressure (position point)).comp (fderiv ℝ position point) =
      fderiv ℝ pressureLift point) :
    inner ℝ (cross (magnetic (position point)) (curl magnetic (position point)) + gradient pressure (position point))
      (fderiv ℝ position point direction) =
        inner ℝ (magneticLift point) (fderiv ℝ magneticLift point direction) -
          inner ℝ (fderiv ℝ position point direction) (fderiv ℝ magneticLift point angular) +
            fderiv ℝ pressureLift point direction := by
  have magneticDirection := congrArg (fun linear : Vec →L[ℝ] Vec => linear direction) magneticChain
  have magneticAngular := congrArg (fun linear : Vec →L[ℝ] Vec => linear angular) magneticChain
  have pressureDirection := congrArg (fun linear : Vec →L[ℝ] ℝ => linear direction) pressureChain
  change fderiv ℝ magnetic (position point) (fderiv ℝ position point direction) = _ at magneticDirection
  change fderiv ℝ magnetic (position point) (fderiv ℝ position point angular) = _ at magneticAngular
  change fderiv ℝ pressure (position point) (fderiv ℝ position point direction) = _ at pressureDirection
  rw [pushforward] at magneticAngular
  rw [ambient_force_pairing, value, magneticDirection, magneticAngular, pressureDirection]

end Grad.PhysicalEquilibrium
