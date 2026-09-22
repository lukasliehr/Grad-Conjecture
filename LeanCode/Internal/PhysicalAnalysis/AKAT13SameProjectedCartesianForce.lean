import AKAT12ProjectedForceCancellation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter
open scoped ContDiff
namespace Grad.ActualCartesianEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations Grad.AnnularKernelL2
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.ActualPolarFlux Grad.ActualForceMatrixFidelity Grad.SourceCollar
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.ActualCartesianDescent Grad.PhysicalFamily Grad.AnnularClosedJointRegularity

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (solution : CoupledSpace lower length positive lengthPositive)
    (curves : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution))

open Grad.AnnularGeneralSourceRegularity Grad.AnnularHighGenerators Grad.AnnularSourceGraph
open Grad.SourceCollarFullSource
variable (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade solution weighted)
    (smooth : ∀ grade, ContDiffOn ℝ ∞
      (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive solution grade) (Icc lower 1))
    (force : SmoothLowPhysicalRow parameters lower positive (strongKnownBulk parameters lower positive bounded.le data 3))
include allGrades smooth

/-- Genuine normalized Cartesian force equation from the SAME Xi radial
PDE. The radial complement is explicit, and no tangential mean is removed. -/
theorem sameCartesianProjectedForce_from_radial (radius : ℝ) (inside : radius ∈ Ioo lower 1)
    (radialLaw : ∀ angles : ℝ × ℝ, HasDerivWithinAt
      (fun query => originalPhysicalComponentField parameters lower length positive bounded lengthPositive solution 1 (query,angles))
      (((curves.lowPhysicalCurves parameters length compact lower positive bounded state 0).add force).meanFree.fullField bounded (radius,angles))
      (Icc lower 1) radius) (angles : ℝ × ℝ) :
    cartesianRadialMeanFree (fun query => sameCartesianRawForce parameters length compact lower positive bounded lengthPositive state data solution curves
      radius ⟨inside.1.le,inside.2.le⟩ query.1 query.2) angles =
    cartesianCovariantValue angles.1 (WithLp.toLp 2 ![
      removePolarMean (fun query => force.fullField bounded (radius,query) 0) angles,
      (curves.bulkUnit (0 : Fin 1) 4).fullField bounded (radius,angles) 0,0]) := by
  let j := curves.lowPhysicalCurves parameters length compact lower positive bounded state 0
  have closedInside : radius ∈ Icc lower 1 := ⟨inside.1.le,inside.2.le⟩
  have raw : (fun query : ℝ × ℝ => sameCartesianRawForce parameters length compact lower positive bounded lengthPositive state data solution curves
      radius closedInside query.1 query.2) =
    fun query => cartesianCovariantValue query.1 (WithLp.toLp 2 ![
      removePolarMean (fun point => j.fullField bounded (radius,point)+force.fullField bounded (radius,point)) query 0-j.fullField bounded (radius,query) 0,
      (curves.bulkUnit (0 : Fin 1) 4).fullField bounded (radius,query) 0,0]) := by
    funext query
    have law := sameCartesianRawForce_from_radial parameters length compact lower positive bounded lengthPositive state data solution curves allGrades smooth
      radius inside query.1 query.2 _ (radialLaw query)
    have radialValue : (j.add force).meanFree.fullField bounded (radius,query) =
        removePolarMean (fun point => j.fullField bounded (radius,point)+force.fullField bounded (radius,point)) query := by
      rw [SmoothLowPhysicalRow.fullField_meanFree (j.add force) bounded radius closedInside query]
      congr 1
      funext point
      exact j.fullField_add bounded force radius closedInside point
    change sameCartesianRawForce parameters length compact lower positive bounded lengthPositive state data solution curves
      radius closedInside query.1 query.2 = cartesianCovariantValue query.1 (WithLp.toLp 2 ![
        (j.add force).meanFree.fullField bounded (radius,query) 0-j.fullField bounded (radius,query) 0,
        (curves.bulkUnit (0 : Fin 1) 4).fullField bounded (radius,query) 0,0]) at law
    rw [radialValue] at law
    exact law
  rw [raw]
  exact cartesianProjectedForce_cancellation (fun point => j.fullField bounded (radius,point))
    (fun point => force.fullField bounded (radius,point))
    (fun point => (curves.bulkUnit (0 : Fin 1) 4).fullField bounded (radius,point) 0)
    (j.fullField_continuous_angles bounded radius closedInside) (force.fullField_continuous_angles bounded radius closedInside) angles

end Grad.ActualCartesianEquations
