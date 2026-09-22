import AKDT3ActualBodyAxis

noncomputable section
open Set
open scoped ContDiff

namespace Grad.PhysicalGeometry
open Grad.MainTarget Grad.PhysicalFamily Grad.PhysicalAmbient Grad.PhysicalEquilibrium
open Grad.PhysicalFamily.IntegerSampling Grad.PhysicalFamily.SampledSmoothFamily
open Grad.PhysicalFamily.SampledConfigurationRegularity Grad.PhysicalFamily.SampledFullGeometry
open Grad.MainAssembly.SampledAxisBasics Grad.MainAssembly.PhysicalNormalHessian
open Grad.PhysicalFamily.SampledGlobalEmbedding Grad.NonlinearQuotient

/-- The pressure lift has the genuine radial differential in all three
coordinates, not only along the punctured reference disk. -/
theorem sampledPressure_fderiv_all (potential : ℝ) (point : Plane) (time : ℝ) (direction : Vec) :
    fderiv ℝ (sampledPressureCoordinateValue potential) (coordinateDirection point time) direction =
      -2 * inner ℝ point (planarPart direction) := by
  have decomposition : direction = coordinateDirection (planarPart direction) (direction 2) := by
    ext coordinate
    fin_cases coordinate <;> simp [coordinateDirection, planarPart, vector]
  conv_lhs => rw [decomposition, coordinateDirection_add (planarPart direction) (direction 2), map_add]
  rw [sampledPressure_fderiv_disk]
  have timeScale : coordinateDirection 0 (direction 2) = (direction 2) • coordinateDirection 0 1 := by
    ext coordinate
    fin_cases coordinate <;> simp [coordinateDirection, vector]
  rw [timeScale, map_smul, sampledPressure_fderiv_time, smul_zero, add_zero]

variable (length : ℝ) (family : CellSolutionFamily length) (period : ℕ)
  (epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero)
  (potential : ℝ) (parameter : Icc family.lower family.upper)
  (magnetic : Vec → Vec) (pressure : Vec → ℝ)
  (magneticSmooth : ContDiff ℝ ∞ magnetic) (pressureSmooth : ContDiff ℝ ∞ pressure)
  (same : ∀ argument,
    magnetic ((sampledRepresentativeFamily length family period epsilonIn potential parameter).position argument) =
      (sampledRepresentativeFamily length family period epsilonIn potential parameter).magnetic argument ∧
    pressure ((sampledRepresentativeFamily length family period epsilonIn potential parameter).position argument) =
      (sampledRepresentativeFamily length family period epsilonIn potential parameter).pressure argument)
  (point : Plane) (pointBound : ‖point‖ ≤ 1) (time : ℝ)
  (injective : Function.Injective (fderiv ℝ (sampledPositionCoordinateValue length family period parameter.val)
    (coordinateDirection point time)))

include epsilonIn potential magnetic pressure magneticSmooth pressureSmooth same pointBound injective

/-- The actual canonical magnetic field vanishes precisely at the zero disk. -/
theorem actual_magnetic_zero_iff :
    magnetic (sampledPositionCoordinateValue length family period parameter.val (coordinateDirection point time)) = 0 ↔
      point = 0 := by
  have values := (actual_reconstructed_derivatives length family period epsilonIn potential parameter
    magnetic pressure magneticSmooth pressureSmooth same point pointBound time).1
  rw [values, ← actualMagneticLift_pushforward length family period epsilonIn parameter point pointBound time]
  constructor
  · intro zero
    have coordinateZero := injective (zero.trans (map_zero _).symm)
    have quarterZero := congrArg planarPart coordinateZero
    rw [planarPart_coordinateDirection] at quarterZero
    have planarZero : planarPart (0 : Vec) = 0 := by ext coordinate; fin_cases coordinate <;> simp [planarPart]
    rw [planarZero] at quarterZero
    have quarterZero' : planeQuarterTurn point = 0 := quarterZero
    have twice := congrArg planeQuarterTurn quarterZero'
    rw [quarterTurn_twice] at twice
    have quarterZeroAtZero : planeQuarterTurn (0 : Plane) = 0 := by ext coordinate; fin_cases coordinate <;> simp [planeQuarterTurn]
    rw [quarterZeroAtZero, neg_eq_zero] at twice
    exact twice
  · intro zero
    subst point
    have quarterZero : planeQuarterTurn (0 : Plane) = 0 := by ext coordinate; fin_cases coordinate <;> simp [planeQuarterTurn]
    have directionZero : coordinateDirection (0 : Plane) 0 = 0 := by ext coordinate; fin_cases coordinate <;> simp [coordinateDirection, vector]
    rw [quarterZero, directionZero, map_zero]

/-- The actual ambient pressure has precisely the zero disk as its critical
set, by the full position derivative and the literal pressure chain rule. -/
theorem actual_pressure_critical_iff :
    fderiv ℝ pressure (sampledPositionCoordinateValue length family period parameter.val (coordinateDirection point time)) = 0 ↔
      point = 0 := by
  have chain := (actual_reconstructed_derivatives length family period epsilonIn potential parameter
    magnetic pressure magneticSmooth pressureSmooth same point pointBound time).2.2
  constructor
  · intro zero
    have radial := congrArg (fun linear : Vec →L[ℝ] ℝ => linear (coordinateDirection point 0)) chain
    rw [zero] at radial
    simp only [ContinuousLinearMap.zero_comp, zero_apply,
      sampledPressure_fderiv_disk] at radial
    have normZero : inner ℝ point point = 0 := by linarith
    exact inner_self_eq_zero.mp normZero
  · intro zero
    subst point
    apply ContinuousLinearMap.ext
    intro direction
    obtain ⟨preimage, preimageSame⟩ := LinearMap.injective_iff_surjective.mp injective direction
    change fderiv ℝ (sampledPositionCoordinateValue length family period parameter.val)
      (coordinateDirection (0 : Plane) time) preimage = direction at preimageSame
    have value := congrArg (fun linear : Vec →L[ℝ] ℝ => linear preimage) chain
    change fderiv ℝ pressure _ (fderiv ℝ (sampledPositionCoordinateValue length family period parameter.val)
      (coordinateDirection (0 : Plane) time) preimage) = _ at value
    rw [preimageSame, sampledPressure_fderiv_all, inner_zero_left, mul_zero] at value
    exact value

end Grad.PhysicalGeometry
