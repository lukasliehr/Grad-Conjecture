import AJN5ActualSharedHighFluxRow

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology
namespace Grad.AnnularHighRadial
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.CircularHighWeak Grad.AnnularVariational Grad.AnnularReconstruction
open Grad.AnnularCurrentEnergy Grad.AnnularCurrentSource Grad.AnnularCurrentGreen Grad.AnnularStrongData
open Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularCurrentLow Grad.AnnularKnownLow Grad.AnnularFullSource
open Grad.AnnularCircularForm Grad.AnnularPhysicalSolution
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.GaugeCoefficients.Physical.Allocation

private theorem highTriplePacket_output (lower : ℝ) (slot : Fin 3) (x c v : DivisionRow 1 lower) :
    highPhysicalOutput lower slot
      (bulkMatrixUnit lower (0 : Fin 3) 0 x + bulkMatrixUnit lower (1 : Fin 3) 0 c + bulkMatrixUnit lower (2 : Fin 3) 0 v) =
      highFullRestriction lower (![x,c,v] slot) := by
  change highFullRestriction lower ((bulkMatrixUnit lower (0 : Fin 1) slot)
    (bulkMatrixUnit lower (0 : Fin 3) 0 x + bulkMatrixUnit lower (1 : Fin 3) 0 c + bulkMatrixUnit lower (2 : Fin 3) 0 v)) = _
  apply congrArg (highFullRestriction lower)
  simp only [map_add]
  fin_cases slot <;> simp [bulkScalarProjection_same, bulkScalarProjection_distinct]

theorem rawReciprocalRadius_source (lower : ℝ) (positive : 0 < lower) (g : DivisionRow 1 lower) (mode : ℤ × ℤ) :
    collarScalar 1 lower (highReciprocalRadius lower positive)
      (radialOrdinary 1 lower positive (radialRadiusRow lower positive g mode)) = radialOrdinary 1 lower positive (g mode) := by
  apply Lp.ext
  filter_upwards [collarScalar_ae 1 lower (highReciprocalRadius lower positive)
      (radialOrdinary 1 lower positive (radialRadiusRow lower positive g mode)),
    radialOrdinary_ae 1 lower positive (radialRadiusRow lower positive g mode),
    radialOrdinary_ae 1 lower positive (g mode), radialRadiusRow_ae lower positive g,
    ae_restrict_mem measurableSet_Icc] with radius outer ordinary original radial inside
  rw [outer, ordinary, original, radial mode]
  change (max lower radius)⁻¹ • (reciprocalRadialWeight lower (fun _ => 1) radius • (radius • g mode radius)) = _
  rw [max_eq_right inside.1]
  rw [smul_comm (reciprocalRadialWeight lower (fun _ => 1) radius) radius, ← mul_smul,
    inv_mul_cancel₀ (ne_of_gt (positive.trans_le inside.1)), one_smul]

theorem rawHighXPacketRHS_sources (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower)
    (packet : DivisionRow 3 lower) (c v g : DivisionRow 1 lower) (mode : HighAnnularMode)
    (cell : highPhysicalOutput lower 1 packet mode = c mode.val)
    (angular : highPhysicalOutput lower 2 packet mode = (v - radialRadiusRow lower positive g) mode.val) :
    rawHighXPacketRHS parameters lower L positive packet mode =
      collarScalar 1 lower (rawHighPhase parameters lower positive mode.val.2)
        (-collarScalar 1 lower (highReciprocalRadius lower positive)
            (radialOrdinary 1 lower positive (highPhysicalOutput lower 0 packet mode)) -
          (Complex.I * (((mode.val.2 : ℝ) / L) : ℝ)) • radialOrdinary 1 lower positive (c mode.val) -
          (Complex.I * (mode.val.1 : ℂ)) • collarScalar 1 lower (highReciprocalRadius lower positive)
            (radialOrdinary 1 lower positive (v mode.val)) +
          (Complex.I * (mode.val.1 : ℂ)) • radialOrdinary 1 lower positive (g mode.val)) := by
  unfold rawHighXPacketRHS
  rw [cell, angular]
  simp only [lp.coeFn_sub, Pi.sub_apply, map_sub, smul_sub]
  rw [rawReciprocalRadius_source]
  simp only [map_add, map_sub]
  abel

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (state : RetainedInverseState parameters L compact)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (solution : CoupledSpace lower L positive lengthPositive)

theorem fullStrongHighPacket_cell (mode : HighAnnularMode) :
    highPhysicalOutput lower 1 (fullStrongHighPacket parameters L compact lower positive lowerHalf lengthPositive state data solution) mode =
      lowPhysicalRowAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 1
        (fullStrongSevenInput parameters L lower lengthPositive positive (lowerHalf.trans (by norm_num)) data solution) mode.val := by
  exact (congrArg (fun value : AnnularBulk lower => value mode)
    (highTriplePacket_output lower 1
      (highBulkIntoFull lower (Grad.AnnularCrossMaps.crossHighX lower L positive lengthPositive solution.ofLp.1))
      (highRowProjection lower (lowPhysicalRowAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 1
        (fullStrongSevenInput parameters L lower lengthPositive positive (lowerHalf.trans (by norm_num)) data solution)))
      (highRowProjection lower (lowPhysicalRowAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 2
        (fullStrongSevenInput parameters L lower lengthPositive positive (lowerHalf.trans (by norm_num)) data solution) -
        radialRadiusRow lower positive (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data).ofLp.1.ofLp.2)))).trans
    (highRowProjection_high lower _ mode)

theorem fullStrongHighPacket_angular (mode : HighAnnularMode) :
    highPhysicalOutput lower 2 (fullStrongHighPacket parameters L compact lower positive lowerHalf lengthPositive state data solution) mode =
      (lowPhysicalRowAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 2
        (fullStrongSevenInput parameters L lower lengthPositive positive (lowerHalf.trans (by norm_num)) data solution) -
        radialRadiusRow lower positive (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data).ofLp.1.ofLp.2) mode.val := by
  exact (congrArg (fun value : AnnularBulk lower => value mode)
    (highTriplePacket_output lower 2
      (highBulkIntoFull lower (Grad.AnnularCrossMaps.crossHighX lower L positive lengthPositive solution.ofLp.1))
      (highRowProjection lower (lowPhysicalRowAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 1
        (fullStrongSevenInput parameters L lower lengthPositive positive (lowerHalf.trans (by norm_num)) data solution)))
      (highRowProjection lower (lowPhysicalRowAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 2
        (fullStrongSevenInput parameters L lower lengthPositive positive (lowerHalf.trans (by norm_num)) data solution) -
        radialRadiusRow lower positive (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data).ofLp.1.ofLp.2)))).trans
    (highRowProjection_high lower _ mode)

/-- The exact positive Rg contribution is restored from the stored rV-rg.
No source is discarded when passing from the compact row to the physical row. -/
theorem rawHighXPacketRHS_full_sources (mode : HighAnnularMode) :
    rawHighXPacketRHS parameters lower L positive
      (fullStrongHighPacket parameters L compact lower positive lowerHalf lengthPositive state data solution) mode =
    collarScalar 1 lower (rawHighPhase parameters lower positive mode.val.2)
      (-collarScalar 1 lower (highReciprocalRadius lower positive)
          (radialOrdinary 1 lower positive (highPhysicalOutput lower 0
            (fullStrongHighPacket parameters L compact lower positive lowerHalf lengthPositive state data solution) mode)) -
        (Complex.I * (((mode.val.2 : ℝ) / L) : ℝ)) • radialOrdinary 1 lower positive
          (lowPhysicalRowAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 1
            (fullStrongSevenInput parameters L lower lengthPositive positive (lowerHalf.trans (by norm_num)) data solution) mode.val) -
        (Complex.I * (mode.val.1 : ℂ)) • collarScalar 1 lower (highReciprocalRadius lower positive)
          (radialOrdinary 1 lower positive
            (lowPhysicalRowAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 2
              (fullStrongSevenInput parameters L lower lengthPositive positive (lowerHalf.trans (by norm_num)) data solution) mode.val)) +
        (Complex.I * (mode.val.1 : ℂ)) • radialOrdinary 1 lower positive
          ((strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data).ofLp.1.ofLp.2 mode.val)) := by
  exact rawHighXPacketRHS_sources parameters lower L positive _ _ _ _ mode
    (fullStrongHighPacket_cell parameters L compact lower positive lowerHalf lengthPositive state data solution mode)
    (fullStrongHighPacket_angular parameters L compact lower positive lowerHalf lengthPositive state data solution mode)


end Grad.AnnularHighRadial
