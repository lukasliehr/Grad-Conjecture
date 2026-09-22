import CellSolutionFamily
import Mathlib.Tactic.FinCases

noncomputable section

open Set Filter

namespace Grad.PhysicalFamily.IntegerSampling

open Grad.MainTarget
open Grad.PhysicalFamily

def sampledEpsilon (period : ℕ) : ℝ := (period : ℝ)⁻¹

def sampledPositionLift (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ) (parameter : ℝ)
    (point : Plane) (time : ℝ) : Vec :=
  rotation time
    ((period * cellLength) • basisVector 0 +
      family.v (sampledEpsilon period) parameter point ((period : ℝ) * time))

def sampledMagneticLift (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ) (parameter : ℝ)
    (point : Plane) (time : ℝ) : Vec :=
  rotation time
    (diskAngular (family.v (sampledEpsilon period) parameter)
      point ((period : ℝ) * time))

def sampledPressureLift (potential : ℝ) (point : Plane) (_time : ℝ) : ℝ :=
  potential - ‖point‖ ^ 2

theorem periodic_nat_mul {Target : Type*} (mapping : ℝ → Target)
    (periodic : ∀ time, mapping (time + 2 * Real.pi) = mapping time)
    (count : ℕ) (time : ℝ) :
    mapping (time + 2 * Real.pi * count) = mapping time := by
  induction count with
  | zero => simp
  | succ count inductionHypothesis =>
      calc
        mapping (time + 2 * Real.pi * (count + 1 : ℕ)) =
            mapping ((time + 2 * Real.pi * count) + 2 * Real.pi) := by
              congr 1
              push_cast
              ring
        _ = mapping (time + 2 * Real.pi * count) := periodic _
        _ = mapping time := inductionHypothesis

theorem rotation_add_two_pi (time : ℝ) (point : Vec) :
    rotation (time + 2 * Real.pi) point = rotation time point := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rotation, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem parameter_mem_open (cellLength : ℝ)
    (family : CellSolutionFamily cellLength)
    (parameter : Set.Icc family.lower family.upper) :
    parameter.val ∈ Set.Ioo family.parameterLower family.parameterUpper :=
  ⟨lt_of_lt_of_le family.parameterContains.1 parameter.property.1,
    lt_of_le_of_lt parameter.property.2 family.parameterContains.2⟩

theorem closed_disk_mem_collar (cellLength : ℝ)
  (family : CellSolutionFamily cellLength) (point : Plane)
    (pointIn : ‖point‖ ≤ 1) :
    point ∈ Metric.ball (0 : Plane) family.collarRadius := by
  rw [Metric.mem_ball, dist_zero_right]
  exact lt_of_le_of_lt pointIn family.collarLarge

theorem diskAngular_periodic_nat (cellLength : ℝ)
    (family : CellSolutionFamily cellLength)
    (epsilon parameter : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameterIn : parameter ∈ Set.Ioo family.parameterLower family.parameterUpper)
    (point : Plane) (pointIn : point ∈ Metric.ball (0 : Plane) family.collarRadius)
    (count : ℕ) (time : ℝ) :
    diskAngular (family.v epsilon parameter) point
        (time + 2 * Real.pi * count) =
      diskAngular (family.v epsilon parameter) point time := by
  have neighborhood : Metric.ball (0 : Plane) family.collarRadius ∈ nhds point :=
    Metric.isOpen_ball.mem_nhds pointIn
  have localEquality :
      (fun argument => family.v epsilon parameter argument
        (time + 2 * Real.pi * count)) =ᶠ[nhds point]
      (fun argument => family.v epsilon parameter argument time) := by
    filter_upwards [neighborhood] with argument argumentIn
    exact periodic_nat_mul (family.v epsilon parameter argument)
      (family.vPeriodic epsilon epsilonIn parameter parameterIn
        argument argumentIn) count time
  have derivativeEquality :
      fderiv ℝ
          (fun argument : Plane => family.v epsilon parameter argument
            (time + 2 * Real.pi * count)) point =
        fderiv ℝ
          (fun argument : Plane => family.v epsilon parameter argument time)
          point :=
    localEquality.fderiv_eq
  exact congrArg (fun derivative : Plane →L[ℝ] Vec =>
      derivative (planeQuarterTurn point))
    derivativeEquality

theorem sampledPosition_periodic (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (parameter : Set.Icc family.lower family.upper)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (point : Plane) (pointIn : ‖point‖ ≤ 1) (time : ℝ) :
    sampledPositionLift cellLength family period parameter.val point
        (time + 2 * Real.pi) =
      sampledPositionLift cellLength family period parameter.val point time := by
  have pointInCollar := closed_disk_mem_collar cellLength family point pointIn
  have parameterIn := parameter_mem_open cellLength family parameter
  unfold sampledPositionLift
  rw [rotation_add_two_pi]
  rw [show (period : ℝ) * (time + 2 * Real.pi) =
      (period : ℝ) * time + 2 * Real.pi * period by ring]
  rw [periodic_nat_mul
    (family.v (sampledEpsilon period) parameter.val point)
    (family.vPeriodic (sampledEpsilon period) epsilonIn parameter.val
      parameterIn point pointInCollar) period ((period : ℝ) * time)]

theorem sampledMagnetic_periodic (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (parameter : Set.Icc family.lower family.upper)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (point : Plane) (pointIn : ‖point‖ ≤ 1) (time : ℝ) :
    sampledMagneticLift cellLength family period parameter.val point
        (time + 2 * Real.pi) =
      sampledMagneticLift cellLength family period parameter.val point time := by
  have pointInCollar := closed_disk_mem_collar cellLength family point pointIn
  have parameterIn := parameter_mem_open cellLength family parameter
  unfold sampledMagneticLift
  rw [rotation_add_two_pi]
  rw [show (period : ℝ) * (time + 2 * Real.pi) =
      (period : ℝ) * time + 2 * Real.pi * period by ring]
  rw [diskAngular_periodic_nat cellLength family (sampledEpsilon period)
    parameter.val epsilonIn parameterIn point pointInCollar period
    ((period : ℝ) * time)]

theorem sampledPressure_periodic (potential : ℝ) (point : Plane) (time : ℝ) :
    sampledPressureLift potential point (time + 2 * Real.pi) =
      sampledPressureLift potential point time := rfl

theorem sampledPosition_isPeriodic (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (parameter : Set.Icc family.lower family.upper)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (point : ClosedDisk) :
    Function.Periodic
      (sampledPositionLift cellLength family period parameter.val point.val)
      (2 * Real.pi) :=
  sampledPosition_periodic cellLength family period parameter epsilonIn
    point.val point.property

theorem sampledMagnetic_isPeriodic (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (parameter : Set.Icc family.lower family.upper)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (point : ClosedDisk) :
    Function.Periodic
      (sampledMagneticLift cellLength family period parameter.val point.val)
      (2 * Real.pi) :=
  sampledMagnetic_periodic cellLength family period parameter epsilonIn
    point.val point.property

theorem sampledPressure_isPeriodic (potential : ℝ) (point : ClosedDisk) :
    Function.Periodic (sampledPressureLift potential point.val)
      (2 * Real.pi) :=
  sampledPressure_periodic potential point.val

/-- The exact sampled `Representative` obtained by descending the three real
`2*pi`-periodic lifts through `AddCircle`.  Integer sampling is essential in
the position and magnetic components. -/
def sampledRepresentative (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (parameter : Set.Icc family.lower family.upper)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (potential : ℝ) : Representative where
  position reference :=
    (sampledPosition_isPeriodic cellLength family period parameter epsilonIn
      reference.1).lift reference.2
  magnetic reference :=
    (sampledMagnetic_isPeriodic cellLength family period parameter epsilonIn
      reference.1).lift reference.2
  pressure reference :=
    (sampledPressure_isPeriodic potential reference.1).lift reference.2

@[simp] theorem sampledRepresentative_position_coe (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (parameter : Set.Icc family.lower family.upper)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (potential : ℝ) (point : ClosedDisk) (time : ℝ) :
    (sampledRepresentative cellLength family period parameter epsilonIn
      potential).position (point, (time : CellCircle)) =
      sampledPositionLift cellLength family period parameter.val point.val time :=
  rfl

@[simp] theorem sampledRepresentative_magnetic_coe (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (parameter : Set.Icc family.lower family.upper)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (potential : ℝ) (point : ClosedDisk) (time : ℝ) :
    (sampledRepresentative cellLength family period parameter epsilonIn
      potential).magnetic (point, (time : CellCircle)) =
      sampledMagneticLift cellLength family period parameter.val point.val time :=
  rfl

@[simp] theorem sampledRepresentative_pressure_coe (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (parameter : Set.Icc family.lower family.upper)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (potential : ℝ) (point : ClosedDisk) (time : ℝ) :
    (sampledRepresentative cellLength family period parameter epsilonIn
      potential).pressure (point, (time : CellCircle)) =
      sampledPressureLift potential point.val time :=
  rfl

/-- On the closed cylinder, pulling the descended position map back along the
target quotient recovers the literal sampled real lift. -/
theorem periodicLift_sampledRepresentative_position (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (parameter : Set.Icc family.lower family.upper)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (potential : ℝ) (point : Vec) (pointIn : point ∈ cylinder) :
    periodicLift
        (sampledRepresentative cellLength family period parameter epsilonIn
          potential).position point =
      sampledPositionLift cellLength family period parameter.val
        (planarPart point) (point 2) := by
  simp [periodicLift, pointIn, quotientPoint]

/-- On the closed cylinder, pulling the descended magnetic map back along the
target quotient recovers the literal sampled real lift. -/
theorem periodicLift_sampledRepresentative_magnetic (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (parameter : Set.Icc family.lower family.upper)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (potential : ℝ) (point : Vec) (pointIn : point ∈ cylinder) :
    periodicLift
        (sampledRepresentative cellLength family period parameter epsilonIn
          potential).magnetic point =
      sampledMagneticLift cellLength family period parameter.val
        (planarPart point) (point 2) := by
  simp [periodicLift, pointIn, quotientPoint]

/-- On the closed cylinder, pulling the descended pressure map back along the
target quotient recovers the literal sampled real lift. -/
theorem periodicLift_sampledRepresentative_pressure (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (parameter : Set.Icc family.lower family.upper)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (potential : ℝ) (point : Vec) (pointIn : point ∈ cylinder) :
    periodicLift
        (sampledRepresentative cellLength family period parameter epsilonIn
          potential).pressure point =
      sampledPressureLift potential (planarPart point) (point 2) := by
  simp [periodicLift, pointIn, quotientPoint]

end Grad.PhysicalFamily.IntegerSampling
