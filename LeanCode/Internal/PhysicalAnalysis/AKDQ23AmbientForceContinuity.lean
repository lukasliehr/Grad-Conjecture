import AKDQ22AnnularCoordinateSpanning

noncomputable section
open Set
open scoped ContDiff

namespace Grad.PhysicalEquilibrium
open Grad.MainTarget Grad.PhysicalFamily
open Grad.PhysicalFamily.SampledFullGeometry

theorem ambient_force_smooth (magnetic : Vec → Vec) (pressure : Vec → ℝ)
    (magneticSmooth : ContDiff ℝ ∞ magnetic) (pressureSmooth : ContDiff ℝ ∞ pressure) :
    ContDiff ℝ ∞ (fun point => cross (magnetic point) (curl magnetic point) + gradient pressure point) := by
  have magneticDerivative : ContDiff ℝ ∞ (fderiv ℝ magnetic) := magneticSmooth.fderiv_right (by simp)
  have pressureDerivative : ContDiff ℝ ∞ (fderiv ℝ pressure) := pressureSmooth.fderiv_right (by simp)
  have magneticCoordinates (first second : Fin 3) :
      ContDiff ℝ ∞ (fun point => (fderiv ℝ magnetic point (basisVector first)) second) :=
    (vecCoordinateCLM second).contDiff.comp (magneticDerivative.clm_apply contDiff_const)
  have pressureCoordinates (coordinate : Fin 3) :
      ContDiff ℝ ∞ (fun point => fderiv ℝ pressure point (basisVector coordinate)) :=
    pressureDerivative.clm_apply contDiff_const
  have fieldCoordinates (coordinate : Fin 3) : ContDiff ℝ ∞ (fun point => magnetic point coordinate) :=
    (vecCoordinateCLM coordinate).contDiff.comp magneticSmooth
  rw [contDiff_piLp]
  intro coordinate
  fin_cases coordinate <;> simp [cross, curl, gradient, vector] <;> fun_prop

end Grad.PhysicalEquilibrium
