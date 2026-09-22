import GQC36PhysicalFiniteJet

noncomputable section

set_option maxHeartbeats 1600000

open Set Filter
open scoped Topology ContDiff

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Envelope

/-- The Cartesian derivative of the actual complete full Fourier field,
at the unchanged analytic width and including every axial cell. -/
theorem apPhysicalValue_hasFDerivAt {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension grade : ℕ} (large : 2 ≤ grade) (angle : ℝ)
    (field : apGrade L sigma gamma ell dimension (grade + 1)) (point : SpatialPlane) (inside : point ∈ openUnitDisk) :
    HasFDerivAt (closedDiskLift (apPhysicalValue admissible (large.trans (Nat.le_succ grade)) angle field))
      (planarDerivative
        (closedDiskLift (apPhysicalValue admissible large angle (apPartial admissible dimension grade 0 field)) point)
        (closedDiskLift (apPhysicalValue admissible large angle (apPartial admissible dimension grade 1 field)) point)) point := by
  let valueMap := apPhysicalValue (dimension := dimension) admissible (large.trans (Nat.le_succ grade)) angle
  let firstMap := (apPhysicalValue admissible large angle).comp (apPartial admissible dimension grade 0)
  let secondMap := (apPhysicalValue admissible large angle).comp (apPartial admissible dimension grade 1)
  have actual : ∀ candidate : SpatialPlane, candidate ∈ openUnitDisk →
      HasFDerivAt (closedDiskLift (valueMap field))
        (closedDiskLift (planarDerivativeMap (firstMap field) (secondMap field)) candidate) candidate := by
    apply isClosed_property (apFiniteInto_denseRange (dimension := dimension) (grade := grade + 1) L sigma gamma ell)
      (closedDerivativeGraph_isClosed.preimage
        (valueMap.continuous.prodMk (planarDerivativeMap_continuous.comp
          (firstMap.continuous.prodMk secondMap.continuous)))) _ field
    intro core candidate member
    change HasFDerivAt (closedDiskLift (apPhysicalValue admissible (large.trans (Nat.le_succ grade)) angle (apFiniteInto L sigma gamma ell core)))
      (closedDiskLift (planarDerivativeMap
        (apPhysicalValue admissible large angle (apPartial admissible dimension grade 0 (apFiniteInto L sigma gamma ell core)))
        (apPhysicalValue admissible large angle (apPartial admissible dimension grade 1 (apFiniteInto L sigma gamma ell core)))) candidate) candidate
    rw [apPartial_core, apPartial_core, apPhysicalValue_finiteJet, apPhysicalValue_finiteJet,
      apPhysicalValue_finiteJet, physicalFiniteJet_map, physicalFiniteJet_map,
      closedLift_value _ candidate member]
    have derivative := closedJet_first (physicalFiniteJet dimension angle core) candidate member
    rw [closedLift_value _ candidate member, closedLift_value _ candidate member] at derivative
    exact derivative
  have result := actual point inside
  rw [closedLift_value _ point inside] at result
  rw [closedLift_value _ point inside, closedLift_value _ point inside]
  exact result

theorem apPhysicalValue_lowering {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension low high : ℕ} (large : 2 ≤ low) (ordered : low ≤ high) (angle : ℝ)
    (field : apGrade L sigma gamma ell dimension high) :
    apPhysicalValue admissible large angle (apLowering L sigma gamma ell ordered field) =
      apPhysicalValue admissible (large.trans ordered) angle field := by
  apply isClosed_property (apFiniteInto_denseRange (dimension := dimension) (grade := high) L sigma gamma ell)
    (isClosed_eq ((apPhysicalValue admissible large angle).continuous.comp (apLowering L sigma gamma ell ordered).continuous)
      (apPhysicalValue admissible (large.trans ordered) angle).continuous) _ field
  intro core
  simp only [Function.comp_apply]
  rw [apLowering_core, apPhysicalValue_core, apPhysicalValue_core]

def apSmoothPhysicalValue {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (dimension : ℕ) (angle : ℝ) : APSmooth L sigma gamma ell dimension →ₗ[ℂ] C(ClosedDisk, ComplexEuclidean dimension) :=
  (apPhysicalValue admissible (by omega : 2 ≤ 2) angle).toLinearMap.comp
    (apSmoothGrade L sigma gamma ell dimension 2)

theorem apSmoothPhysicalValue_grade {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension grade : ℕ} (large : 2 ≤ grade) (angle : ℝ) (field : APSmooth L sigma gamma ell dimension) :
    apSmoothPhysicalValue admissible dimension angle field = apPhysicalValue admissible large angle (field.val grade) := by
  change apPhysicalValue admissible (by omega : 2 ≤ 2) angle (field.val 2) = _
  rw [← field.property 2 grade large, apPhysicalValue_lowering]

theorem apSmoothPhysicalValue_hasFDerivAt {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (angle : ℝ) (field : APSmooth L sigma gamma ell dimension)
    (point : SpatialPlane) (inside : point ∈ openUnitDisk) :
    HasFDerivAt (closedDiskLift (apSmoothPhysicalValue admissible dimension angle field))
      (planarDerivative
        (closedDiskLift (apSmoothPhysicalValue admissible dimension angle (apSmoothPartial admissible dimension 0 field)) point)
        (closedDiskLift (apSmoothPhysicalValue admissible dimension angle (apSmoothPartial admissible dimension 1 field)) point)) point := by
  rw [apSmoothPhysicalValue_grade admissible (by omega : 2 ≤ 3) angle field]
  exact apPhysicalValue_hasFDerivAt admissible (by omega : 2 ≤ 2) angle (field.val 3) point inside

end Grad.GaugeCoefficients.Physical.Compensated
