import AKV9GeneralHighFluxRow

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
namespace Grad.AnnularGeneralSourceRegularity
open Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularLowClassical Grad.AnnularLowEnergy Grad.AnnularReconstruction
open Grad.AnnularSourceGraph
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCurrentSource
open Grad.AnnularCurrentLow Grad.AnnularKnownLow Grad.AnnularStrongOrbit
open Grad.AnnularCoupledInverse Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)

/-- Exact full original low PDE of the SAME smooth-source inverse response.
All homogeneous and known seven inputs, original rho, P, f and positive Rg
are retained. The pair order is (x,xi), the low index order is (xi,x). -/
theorem generalSharedLowRawSlope_actual (index : LowAnnularIndex) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      sharedStrongLowRawSlope parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small
        data
        index radius =
      let rhs := actualOriginalUnknownRHS parameters length compact lower positive
          (lowerHalf.trans_lt (by norm_num)) lengthPositive state
          (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) radius index.2.val +
        generalOriginalSourceRHS parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state data radius index.2.val
      if index.1 = 0 then rhs.2 else rhs.1 := by
  let bounded : lower < 1 := lowerHalf.trans_lt (by norm_num)
  let field := sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
  let full := fun row : Fin 3 => lowPhysicalRowAction parameters length compact lower positive bounded.le state row
    (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data field)
  let unknown := fun row : Fin 3 => lowPhysicalRowAction parameters length compact lower positive bounded.le state row
    (homogeneousCoupledSevenInput parameters length lower lengthPositive positive field)
  let bulk := strongKnownBulk parameters lower positive bounded.le data
  let known := fun row : Fin 3 => lowPhysicalRowAction parameters length compact lower positive bounded.le state row
    (knownLowSevenPacket lower bulk)
  let g := (strongToLow parameters lower positive bounded.le 0 0 data).ofLp.1.ofLp.2
  have rowSame := fun row : Fin 3 => fullStrongPhysicalCoefficient_split parameters length compact lower
    lengthPositive positive bounded.le state data field row
  filter_upwards [rowSame 0, rowSame 1, rowSame 2,
    lowRhoPhysicalCoefficient_add_ae parameters lower positive (full 0) (highSourceF lower bulk),
    lowRhoPhysicalCoefficient_sub_ae parameters lower positive (full 2) (radialRadiusRow lower positive g),
    lowRhoPhysicalCoefficient_radius_ae parameters lower positive g,
    ae_restrict_mem measurableSet_Icc] with radius rowJ rowC rowV first angular radial inside
  rcases index with ⟨entry, mode⟩
  have notLarge : ¬ 3 ≤ |mode.val.1| := by rcases mode.property with h | h <;> omega
  have modeNonzero : mode.val.1 ≠ 0 := by
    intro zero
    have h := mode.property
    simp only [zero, abs_zero] at h
    omega
  have sameX : sameCoupledXCoefficient parameters lower length positive bounded lengthPositive field 0
      (radialClamp lower bounded.le radius) mode.val =
      radialSectionExtension 1 lower bounded.le
        (lowPhysicalSection parameters lower length positive bounded field.ofLp.2 (1, mode)) radius := by
    simp only [sameCoupledXCoefficient, dif_neg notLarge, dif_pos mode.property,
      pow_zero, Complex.ofReal_one, one_smul, radialSectionExtension]
    rfl
  change lowPhysicalRawSlope parameters lower length positive bounded field.ofLp.2
    (full 0 + highSourceF lower bulk) (full 1) (full 2 - radialRadiusRow lower positive g) (entry, mode) radius =
    let rhs := actualOriginalUnknownRHS parameters length compact lower positive bounded lengthPositive state field radius mode.val +
      generalOriginalSourceRHS parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state data radius mode.val
    if entry = 0 then rhs.2 else rhs.1
  fin_cases entry
  · simp only [lowPhysicalRawSlope]
    rw [first mode.val, rowJ mode.val]
    exact lowOriginalXi_source_split length radius mode.val modeNonzero _ _ _ _ _ _ _ _ _
  · simp only [lowPhysicalRawSlope]
    rw [rowC mode.val, angular mode.val, rowV mode.val, radial mode.val]
    change _ = (rawOriginalUnknownRHS length radius mode.val
      (sameCoupledXCoefficient parameters lower length positive bounded lengthPositive field 0
        (radialClamp lower bounded.le radius) mode.val)
      (lowRhoPhysicalCoefficient parameters lower positive (unknown 0) radius mode.val)
      (lowRhoPhysicalCoefficient parameters lower positive (unknown 1) radius mode.val)
      (lowRhoPhysicalCoefficient parameters lower positive (unknown 2) radius mode.val) +
      rawOriginalSourceRHS length radius mode.val
      (lowRhoPhysicalCoefficient parameters lower positive (known 0) radius mode.val)
      (lowRhoPhysicalCoefficient parameters lower positive (known 1) radius mode.val)
      (lowRhoPhysicalCoefficient parameters lower positive (known 2) radius mode.val)
      (lowRhoPhysicalCoefficient parameters lower positive (bulk 3) radius mode.val)
      (lowRhoPhysicalCoefficient parameters lower positive g radius mode.val)).1
    rw [sameX]
    exact lowOriginalX_source_split length radius (positive.trans_le inside.1).ne' mode.val _ _ _ _ _ _ _ _ _

end Grad.AnnularGeneralSourceRegularity
