import AKV12GeneralPhysicalPairSections

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
namespace Grad.AnnularGeneralSourceRegularity
open Grad.AnnularVariational
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.PhaseAlgebra
open Grad.AnnularHighGenerators Grad.AnnularCurrentLow Grad.AnnularStrongSolution Grad.AnnularStrongData
open Grad.AnnularHighRadial Grad.CircularHighRegularity Grad.AnnularLowClassical Grad.AnnularLowEnergy

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1/2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (curves : ActualSourceRadialCurves parameters lower positive (lowerHalf.trans_lt (by norm_num)) data)


variable (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
  CoupledInsertedGrade lower length positive lengthPositive grade (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) weighted)
include allGrades curves


/-- Genuine high coordinate derivatives for any prescribed source possessing
its actual smooth radial representatives. No derivative of the solution is a premise. -/
theorem generalShared_high_derivative (mode : HighAnnularMode) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt (fun point => hilbertPairCoefficient mode.val ((originalPairCurve parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)) 0 point))
      ((generalPhysicalRHSCurve parameters length compact lower positive lowerHalf lengthPositive state data (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) curves allGrades) mode.val radius) (Icc lower 1) radius := by
  let rhsX : C(ℝ,ComplexEuclidean 1) := ⟨fun point => ((generalPhysicalRHSCurve parameters length compact lower positive lowerHalf lengthPositive state data (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) curves allGrades) mode.val point).1,
    continuous_fst.comp ((generalPhysicalRHSCurve parameters length compact lower positive lowerHalf lengthPositive state data (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) curves allGrades) mode.val).continuous⟩
  let rhsXi : C(ℝ,ComplexEuclidean 1) := ⟨fun point => ((generalPhysicalRHSCurve parameters length compact lower positive lowerHalf lengthPositive state data (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) curves allGrades) mode.val point).2,
    continuous_snd.comp ((generalPhysicalRHSCurve parameters length compact lower positive lowerHalf lengthPositive state data (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) curves allGrades) mode.val).continuous⟩
  have nonzero : mode.val.1 ≠ 0 := by have large := mode.property; intro zero; simp [zero] at large
  have sameX : sharedRawHighXRHS parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data mode
      =ᵐ[volume.restrict (Icc lower 1)] rhsX := by
    filter_upwards [generalSharedHighXRHS_actual parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data mode,
      generalPhysicalRHSCurve_actual parameters length compact lower positive lowerHalf lengthPositive state data (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) curves allGrades mode.val]
      with point raw actual
    simp only [if_neg nonzero,one_smul] at actual
    exact raw.trans (congrArg Prod.fst actual).symm
  have sameXi : sharedRawHighXiRHS parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data mode
      =ᵐ[volume.restrict (Icc lower 1)] rhsXi := by
    filter_upwards [generalSharedHighXiRHS_actual parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data mode,
      generalPhysicalRHSCurve_actual parameters length compact lower positive lowerHalf lengthPositive state data (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) curves allGrades mode.val]
      with point raw actual
    simp only [if_neg nonzero,one_smul] at actual
    exact raw.trans (congrArg Prod.snd actual).symm
  have dx := sharedRawHighX_hasDerivWithinAt parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data mode rhsX sameX radius inside
  have dxi := sharedRawHighXi_hasDerivWithinAt parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data mode rhsXi sameXi radius inside
  exact (dx.prodMk dxi).congr
    (fun point _ => Prod.ext
      (originalPairCurve_highX parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) allGrades mode point)
      (originalPairCurve_highXi parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) allGrades mode point))
    (Prod.ext
      (originalPairCurve_highX parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) allGrades mode radius)
      (originalPairCurve_highXi parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) allGrades mode radius))

/-- The original low weak graph, with its full source/cross terms, yields the
closed-collar coordinate derivative of the same (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data). -/
theorem generalShared_low_derivative (index : LowAnnularIndex) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt (fun point => lowPhysicalPairCoefficient index ((originalPairCurve parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)) 0 point))
      (if index.1 = 0 then ((generalPhysicalRHSCurve parameters length compact lower positive lowerHalf lengthPositive state data (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) curves allGrades) index.2.val radius).2 else ((generalPhysicalRHSCurve parameters length compact lower positive lowerHalf lengthPositive state data (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) curves allGrades) index.2.val radius).1)
      (Icc lower 1) radius := by
  let rhs : C(ℝ,ComplexEuclidean 1) := ⟨fun point =>
    if index.1 = 0 then ((generalPhysicalRHSCurve parameters length compact lower positive lowerHalf lengthPositive state data (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) curves allGrades) index.2.val point).2 else ((generalPhysicalRHSCurve parameters length compact lower positive lowerHalf lengthPositive state data (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) curves allGrades) index.2.val point).1,
    by split_ifs
       · exact continuous_snd.comp ((generalPhysicalRHSCurve parameters length compact lower positive lowerHalf lengthPositive state data (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) curves allGrades) index.2.val).continuous
       · exact continuous_fst.comp ((generalPhysicalRHSCurve parameters length compact lower positive lowerHalf lengthPositive state data (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) curves allGrades) index.2.val).continuous⟩
  have nonzero : index.2.val.1 ≠ 0 := by
    intro zero
    have low := index.2.property
    simp only [zero,abs_zero] at low
    omega
  have actual : rhs =ᵐ[volume.restrict (Icc lower 1)]
      sharedStrongLowRawSlope parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data index := by
    filter_upwards [generalSharedLowRawSlope_actual parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data index,
      generalPhysicalRHSCurve_actual parameters length compact lower positive lowerHalf lengthPositive state data (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) curves allGrades index.2.val]
      with point low same
    change (if index.1 = 0 then ((generalPhysicalRHSCurve parameters length compact lower positive lowerHalf lengthPositive state data (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) curves allGrades) index.2.val point).2 else ((generalPhysicalRHSCurve parameters length compact lower positive lowerHalf lengthPositive state data (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) curves allGrades) index.2.val point).1) = _
    rw [same,if_neg nonzero,one_smul,low]
    rfl
  have derivative := sharedStrongResponse_lowPhysicalSection_derivative parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data index rhs actual radius inside
  exact derivative.congr
    (fun point _ => originalPairCurve_low parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) allGrades index point)
    (originalPairCurve_low parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) allGrades index radius)

end Grad.AnnularGeneralSourceRegularity
