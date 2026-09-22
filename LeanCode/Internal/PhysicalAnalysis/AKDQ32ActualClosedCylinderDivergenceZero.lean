import AKDQ31ActualDivergenceFrameIdentity

noncomputable section
set_option maxHeartbeats 1600000
open Set
open scoped ContDiff

namespace Grad.PhysicalEquilibrium
open Grad.MainTarget Grad.PhysicalFamily Grad.PhysicalAmbient Grad.NonlinearQuotient
open Grad.PhysicalFamily.IntegerSampling Grad.PhysicalFamily.SampledSmoothFamily
open Grad.PhysicalFamily.SampledConfigurationRegularity Grad.PhysicalFamily.SampledFullGeometry
open Grad.MainAssembly.SampledAxisBasics Grad.MainAssembly.PhysicalNormalHessian

theorem divergence_smooth (magnetic : Vec → Vec) (smooth : ContDiff ℝ ∞ magnetic) :
    ContDiff ℝ ∞ (divergence magnetic) := by
  have derivative : ContDiff ℝ ∞ (fderiv ℝ magnetic) := smooth.fderiv_right (by simp)
  have coordinate (index : Fin 3) : ContDiff ℝ ∞ (fun point => (fderiv ℝ magnetic point (basisVector index)) index) :=
    (vecCoordinateCLM index).contDiff.comp (derivative.clm_apply contDiff_const)
  unfold divergence
  simp only [Fin.sum_univ_three]
  exact ((coordinate 0).add (coordinate 1)).add (coordinate 2)

theorem actual_divergence_zero_closedCylinder (length : ℝ) (family : CellSolutionFamily length) (period : ℕ) (periodPositive : 0 < period)
    (epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero)
    (potential : ℝ) (parameter : Icc family.lower family.upper)
    (magnetic : Vec → Vec) (pressure : Vec → ℝ)
    (magneticSmooth : ContDiff ℝ ∞ magnetic) (pressureSmooth : ContDiff ℝ ∞ pressure)
    (same : ∀ argument,
      magnetic ((sampledRepresentativeFamily length family period epsilonIn potential parameter).position argument) =
        (sampledRepresentativeFamily length family period epsilonIn potential parameter).magnetic argument ∧
      pressure ((sampledRepresentativeFamily length family period epsilonIn potential parameter).position argument) =
        (sampledRepresentativeFamily length family period epsilonIn potential parameter).pressure argument)
    (injective : ∀ point : Plane, ‖point‖ ≤ 1 → ∀ time : ℝ,
      Function.Injective (fderiv ℝ (sampledPositionCoordinateValue length family period parameter.val)
        (coordinateDirection point time)))
    (point : Plane) (pointBound : ‖point‖ ≤ 1) (time : ℝ) :
    let position := sampledPositionCoordinateValue length family period parameter.val
    divergence magnetic (position (coordinateDirection point time)) = 0 := by
  let field : Plane → ℝ := fun point => divergence magnetic
    (sampledPositionCoordinateValue length family period parameter.val (coordinateDirection point time))
  have punctured (current : Plane) (currentBound : ‖current‖ ≤ 1) (nonzero : current ≠ 0) : field current = 0 := by
    let linear := fderiv ℝ (sampledPositionCoordinateValue length family period parameter.val) (coordinateDirection current time)
    have determinant : tripleDeterminant (linear (coordinateDirection current 0))
        (linear (coordinateDirection (planeQuarterTurn current) 0)) (linear (coordinateDirection 0 1)) ≠ 0 :=
      tripleDeterminant_ne_zero_of_separating _ _ _ (fun value radial angular temporal =>
        vector_zero_of_coordinate_pairings linear (injective current currentBound time) current nonzero value radial angular temporal)
    have product := actual_divergence_times_frame_zero length family period periodPositive epsilonIn potential parameter
      magnetic pressure magneticSmooth pressureSmooth same current currentBound time
    exact (mul_eq_zero.mp product).resolve_right determinant
  by_cases nonzero : point ≠ 0
  · exact punctured point pointBound nonzero
  · have pointZero : point = 0 := not_ne_iff.mp nonzero
    subst point
    have insertionSmooth : ContDiff ℝ ∞ (fun point : Plane => coordinateDirection point time) := by
      rw [contDiff_piLp]
      intro coordinate
      fin_cases coordinate <;> simp [coordinateDirection, vector] <;> fun_prop
    have argumentIn : coordinateDirection (0 : Plane) time ∈ sampledAmbientCollar family :=
      sampledAmbientCollar_contains family (referenceCoverPoint_mem ((⟨0, by simp⟩ : ClosedDisk), time))
    have positionContinuous := (sampled_actual_lifts_smooth length family period epsilonIn potential parameter).1.contDiffAt
      ((sampledAmbientCollar_isOpen family).mem_nhds argumentIn) |>.continuousAt
    have positionSectionContinuous : ContinuousAt (fun point : Plane =>
        sampledPositionCoordinateValue length family period parameter.val (coordinateDirection point time)) 0 :=
      positionContinuous.comp (f := fun point : Plane => coordinateDirection point time)
        insertionSmooth.continuous.continuousAt
    have fieldContinuous : ContinuousAt field 0 :=
      (divergence_smooth magnetic magneticSmooth).continuous.continuousAt.comp
        (f := fun point : Plane => sampledPositionCoordinateValue length family period parameter.val
          (coordinateDirection point time)) positionSectionContinuous
    exact zero_at_axis_of_punctured_zero field fieldContinuous punctured

end Grad.PhysicalEquilibrium
