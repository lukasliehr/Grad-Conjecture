import AKBE7ActualObservedCartesianEquations
import AKBF14SameNativeXiMean

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.ActualScalarWeakEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.PhaseAlgebra Grad.AnnularWeightedSmoothness
open Grad.AnnularGeneralSourceRegularity Grad.AnnularOriginalCoreRealization Grad.AnnularReconstruction
open Grad.AnnularKernelContinuity Grad.AnnularKernelL2 Grad.AnnularRestriction Grad.AnnularPhysicalReconstruction
open Grad.AnnularStrongSolution Grad.AnnularStrongData Grad.AnnularStrongOrbit Grad.AnnularHighGenerators
open Grad.AnnularFullGraph Grad.AnnularWeakExhaustion Grad.AnnularCoupledInverse
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.ExhaustionSourceAllocation
open Grad.GaugeCoefficients.Physical.Allocation

variable
    (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1/2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (coefficientSmall : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 6 ≤
      originalCoefficientLowRadius parameters length)
    (source : SmoothQuotient parameters) (flat : IsFlat source)
    (point : OriginalFiveBlockAmbient parameters lower length positive)
    (member : point ∈ OriginalObservedEquationGraph parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state)
    (sameSources : point.ofLp.2 =
      (actualOriginalSourceDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall
        lower positive (lowerHalf.trans_lt (by norm_num)) 0 source flat).val.ofLp.1)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade
        (originalWeightedRetainedObservation parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive point) weighted)


open Grad.AnnularPhysicalFourier Grad.ActualCartesianDescent Grad.AnnularClosedJointRegularity Grad.ActualSmoothPhysicalField Grad.ActualCartesianEquations Grad.ActualPolarEquations Grad.ActualPolarFlux Grad.SourceCollarFullSource Grad.AnnularExhaustionEstimate

variable (seven : SmoothLowPhysicalRow parameters lower positive
    (originalSevenPacket parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive
      (actualOriginalSourceDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall lower positive (lowerHalf.trans_lt (by norm_num)) 0 source flat) point.ofLp.1))

include member sameSources allGrades small in
/-- The SAME observed native Xi/r row is the original scalar Hilbert field divided by radius. -/
theorem actualObserved_XiOverRadius_full (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (seven.bulkUnit (0 : Fin 1) 3).fullField (lowerHalf.trans_lt (by norm_num)) (radius,angles) =
      (radius : ℂ)⁻¹ • originalPhysicalComponentField parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
        (originalWeightedRetainedObservation parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive point) 1 (radius,angles) := by
  have smooth := actualCartesianObserved_phaseWeighted_radial parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small coefficientSmall source flat point member sameSources allGrades
  exact fullSeven_physicalXiOverRadius parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
    (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0
      (actualOriginalSourceDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall
        lower positive (lowerHalf.trans_lt (by norm_num)) 0 source flat))
    (originalWeightedRetainedObservation parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive point)
    allGrades smooth seven radius inside angles

include member sameSources allGrades small in
/-- Multiplication by the genuine radius recovers original Xi without changing the reconstruction. -/
theorem actualObserved_radius_XiOverRadius (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    radius • (seven.bulkUnit (0 : Fin 1) 3).fullField (lowerHalf.trans_lt (by norm_num)) (radius,angles) =
      originalPhysicalComponentField parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
        (originalWeightedRetainedObservation parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive point) 1 (radius,angles) := by
  rw [actualObserved_XiOverRadius_full parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength
    state small coefficientSmall source flat point member sameSources allGrades seven radius inside angles,
    RCLike.real_smul_eq_coe_smul (K := ℂ),smul_smul]
  change ((radius : ℂ) * (radius : ℂ)⁻¹) • _ = _
  rw [mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (positive.trans_le inside.1).ne'),one_smul]

include member sameSources allGrades small in
/-- Literal Cartesian scalar on each closed collar, before differentiation. -/
theorem actualObserved_cartesianXi_same (spatial : SpatialPlane)
    (inside : ‖spatial‖ ∈ Icc lower 1) (axial : ℝ) :
    ‖spatial‖ • (seven.bulkUnit (0 : Fin 1) 3).cartesianField (lowerHalf.trans_lt (by norm_num)) (spatial,axial) =
      cartesianPhysicalField (originalPhysicalComponentField parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
        (originalWeightedRetainedObservation parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive point) 1) (spatial,axial) := by
  let closed : Grad.ClosedJets.ClosedDisk := ⟨spatial,inside.2⟩
  obtain ⟨angle,polar⟩ := Grad.Constraints.closedPoint_has_polar_angle closed
  have represented : polarPlane (‖spatial‖,angle) = spatial := by
    have coordinates := congrArg Subtype.val polar
    rw [Grad.Constraints.polarClosedPoint_coordinates] at coordinates
    simpa only [polarPlane,Grad.BoundaryTrace.collarPlane,closed,sub_sub_cancel] using coordinates
  have scalar := actualObserved_radius_XiOverRadius parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength
    state small coefficientSmall source flat point member sameSources allGrades seven ‖spatial‖ inside (angle,axial)
  have cartesianSame := cartesianPhysicalField_at_polar
    (originalPhysicalComponentField parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
      (originalWeightedRetainedObservation parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive point) 1)
    (fun radius axial => hilbertPhysicalField_angular_periodic lower (lowerHalf.trans_lt (by norm_num)) _ radius axial)
    ‖spatial‖ (positive.trans_le inside.1) angle axial
  rw [represented] at cartesianSame
  rw [cartesianSame]
  have localSame := (seven.bulkUnit (0 : Fin 1) 3).cartesianField_polar (lowerHalf.trans_lt (by norm_num))
    ‖spatial‖ (positive.trans_le inside.1) angle axial
  rw [polarPlane_originalParametrization,represented] at localSame
  exact (congrArg (‖spatial‖ • ·) localSame).trans scalar

end Grad.ActualScalarWeakEquations
