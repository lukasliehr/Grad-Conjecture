import FC4Proof
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section

open Set MeasureTheory
open scoped ENNReal BigOperators Topology

namespace Grad.CartesianState

open Grad.ClosedJets

/-- A continuous closed-disk field whose actual open-disk `L²` class is zero
vanishes on the whole closed disk.  The boundary conclusion uses density. -/
theorem closedContinuousToDiskL2_eq_zero {dimension : ℕ}
    (field : ContinuousMap ClosedDisk (ComplexEuclidean dimension))
    (equality : closedContinuousToDiskL2 field = 0) :
    field = 0 := by
  have almostEverywhere :
      closedDiskLift field =ᵐ[volume.restrict openUnitDisk]
        (0 : SpatialPlane → ComplexEuclidean dimension) := by
    filter_upwards [closedContinuousToDiskL2_ae field,
      Lp.coeFn_zero (ComplexEuclidean dimension) 2
        (volume.restrict openUnitDisk)] with point fieldAt zeroAt
    rw [← fieldAt, equality, zeroAt]
  have onOpen : Set.EqOn (closedDiskLift field)
      (0 : SpatialPlane → ComplexEuclidean dimension) openUnitDisk :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq almostEverywhere openUnitDisk_isOpen
      (closedDiskLift_continuousOn_open field) continuousOn_const
  apply continuousMap_eq_of_openDisk
  intro point membership
  have atPoint := onOpen membership
  simpa [closedDiskLift, openDiskMembershipClosed point.val membership] using atPoint

/-- The unordered multi-index `alpha = 0`, present at every grade. -/
def zeroGradeIndex (grade : ℕ) : GradeMultiIndex grade :=
  ⟨(⟨0, Nat.zero_lt_succ grade⟩, ⟨0, Nat.zero_lt_succ grade⟩), by simp⟩

@[simp]
theorem zeroGradeIndex_toCartesian (grade : ℕ) :
    (zeroGradeIndex grade).toCartesian = (0, 0) := rfl

theorem closedMultiDerivative_zeroGradeIndex {dimension grade : ℕ}
    (field : ClosedJet dimension) :
    closedMultiDerivative field (zeroGradeIndex grade).toCartesian = field.value := by
  change closedDerivative field 0 (cartesianMultiIndexWord (0, 0)) = field.value
  rw [show cartesianMultiIndexWord (0, 0) = emptyCartesianWord by
    funext position
    exact Fin.elim0 position]
  exact closedDerivative_zero_order field

theorem closedMultiDerivative_zero {dimension : ℕ} (field : ClosedJet dimension) :
    closedMultiDerivative field (0, 0) = field.value := by
  simpa only [← zeroGradeIndex_toCartesian 0] using
    (closedMultiDerivative_zeroGradeIndex (grade := 0) field)

/-- The exact COR04 coordinates have trivial kernel on actual closed jets. -/
theorem gradeCore_eq_zero_of_coordinates_eq_zero {dimension grade : ℕ}
    (parameters : PhaseParameters) (field : GradeCore parameters dimension grade)
    (coordinatesZero : gradeCoreCoordinates parameters field = 0) :
    field = 0 := by
  apply GradeCore.ext
  apply Subtype.ext
  funext cell
  have coordinateZero :
      gradeCoreCoordinates parameters field cell (zeroGradeIndex grade) = 0 := by
    rw [coordinatesZero]
    rfl
  have frequencyPositive : 0 < cellFrequency cell :=
    lt_of_lt_of_le zero_lt_one (cellFrequency_one_le cell)
  have frequencyComplexNonzero : (cellFrequency cell : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr frequencyPositive.ne'
  have frequencyPowerNonzero :
      (cellFrequency cell : ℂ) ^ grade ≠ 0 :=
    pow_ne_zero grade frequencyComplexNonzero
  have weightedL2Zero :
      closedContinuousToDiskL2
        (phaseWeightedJet parameters cell (field.toCore.1 cell)).value = 0 := by
    have scaledZero :
        (cellFrequency cell : ℂ) ^ grade •
          closedContinuousToDiskL2
            (phaseWeightedJet parameters cell (field.toCore.1 cell)).value = 0 := by
      simpa only [gradeCoreCoordinates_apply, cartesianGradeCoordinates_apply,
        zeroGradeIndex_toCartesian, cartesianOrder, zero_add, Nat.sub_zero,
        closedMultiDerivative_zero, Pi.zero_apply] using coordinateZero
    exact (smul_eq_zero.mp scaledZero).resolve_left frequencyPowerNonzero
  have weightedValueZero :
      (phaseWeightedJet parameters cell (field.toCore.1 cell)).value = 0 :=
    closedContinuousToDiskL2_eq_zero _ weightedL2Zero
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  have weightedAtPoint := congrArg
    (fun value : ContinuousMap ClosedDisk (ComplexEuclidean dimension) => value point)
    weightedValueZero
  rw [phaseWeightedJet_value] at weightedAtPoint
  have weightNonzero : cartesianWeight parameters cell point.val ≠ 0 :=
    (cartesianWeight_pos parameters cell point.val).ne'
  exact (smul_eq_zero.mp weightedAtPoint).resolve_left weightNonzero

/-- The actual grade coordinate map is injective, coefficient by coefficient
and including the boundary values of every closed jet. -/
theorem gradeCoreCoordinates_injective {dimension grade : ℕ}
    (parameters : PhaseParameters) :
    Function.Injective (gradeCoreCoordinates parameters :
      GradeCore parameters dimension grade →
        lp (fun _ : ℤ => CartesianGradeRow dimension grade) 2) := by
  intro first second equality
  apply sub_eq_zero.mp
  apply gradeCore_eq_zero_of_coordinates_eq_zero parameters
  rw [map_sub, equality, sub_self]

end Grad.CartesianState
