import BKA10SevenSlotInput

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.NonlinearQuotientBounds Grad.BoundaryTrace
open Grad.AxisCore Grad.QuotientProjection Grad.FlatSourceProjection

/-- Exact AH16 carrier consumer: both signed half-order weighted sequence
spaces are complete at every pair of angular and cell orders. -/
theorem ah16_complete_carriers {dimension : ℕ} (parameters : PhaseParameters)
    (angular cell : ℕ) :
    IsComplete (Set.univ : Set (NegativeTrace parameters angular cell dimension)) ∧
      IsComplete (Set.univ : Set (PositiveTrace parameters angular cell dimension)) :=
  ⟨negativeTrace_complete parameters angular cell,
    positiveTrace_complete parameters angular cell⟩

/-- Exact AH17--AH18 consumer for an arbitrary finite rectangular
two-frequency kernel.  The first clause is the shifted negative-half weight,
and the other two clauses are the literal convolution and its operator bound. -/
theorem ah17_ah18_finite_kernel_consumer {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (kernel : FiniteTwoFrequencyKernel sourceDimension targetDimension)
    (field : NegativeTrace parameters angular cell sourceDimension) :
    (∀ mode shift,
      negativeTraceWeight parameters angular cell mode ≤
        negativeShiftCost parameters angular cell shift *
          negativeTraceWeight parameters angular cell
            (twoFrequencyTranslation shift mode)) ∧
    (∀ mode,
      negativeTraceCoefficient parameters angular cell
          (finiteNegativeKernelAction parameters angular cell kernel field) mode =
        ∑ shift ∈ kernel.support, kernel shift
          (negativeTraceCoefficient parameters angular cell field
            (twoFrequencyTranslation shift mode))) ∧
    ‖finiteNegativeKernelAction parameters angular cell kernel field‖ ≤
      finiteKernelMoment parameters angular cell kernel * ‖field‖ := by
  exact ⟨fun mode shift =>
      negativeTraceWeight_shift_le parameters angular cell mode shift,
    finiteNegativeKernelAction_coefficient parameters angular cell kernel field,
    finiteNegativeKernelAction_bound parameters angular cell kernel field⟩

/-- Exact AH19 one-high consumer.  Compatibility says that `high` and `low`
are two weighted realizations of the same physical trace. -/
theorem ah19_one_high_kernel_consumer {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (kernel : FiniteTwoFrequencyKernel sourceDimension targetDimension)
    (high : NegativeTotalTrace parameters grade sourceDimension)
    (low : NegativeTotalTrace parameters 0 sourceDimension)
    (compatible : TotalTraceCompatible parameters grade high low) :
    (∀ mode,
      negativeTotalCoefficient parameters grade
          (finiteOneHighKernelAction parameters grade kernel high low) mode =
        ∑ shift ∈ kernel.support, kernel shift
          (negativeTotalCoefficient parameters grade high
            (twoFrequencyTranslation shift mode))) ∧
    ‖finiteOneHighKernelAction parameters grade kernel high low‖ ≤
      2 ^ grade *
        (totalKernelMoment parameters 1 kernel * ‖high‖ +
          totalKernelMoment parameters (grade + 1) kernel * ‖low‖) :=
  ⟨finiteOneHighKernelAction_coefficient parameters grade kernel high low compatible,
    finiteOneHighKernelAction_bound parameters grade kernel high low⟩

/-- AH20's exact seven ordered inputs, with the last three slots supplied by
the accepted original source outer trace.  This is deliberately only the
input boundary for the later physical reconstruction kernel. -/
theorem ah20_actual_seven_slot_consumer (parameters : PhaseParameters) (L : ℝ)
    (positive : 0 < L) (angular cell : ℕ)
    (x : NegativeTrace parameters angular cell 1)
    (xi : PositiveTrace parameters angular cell 1)
    (source : ZAmbient parameters (angular + cell + 2)) :
    (fun slot => actualSevenSlotTrace parameters L angular cell x xi source slot) =
      ![x,
        positiveRotationToNegative parameters angular cell xi,
        positiveCellToNegative parameters angular cell xi,
        positiveToNegative parameters angular cell xi,
        sourceBoundaryToNegative parameters angular cell
          (sourceOuterTrace parameters L (angular + cell) source 0),
        sourceBoundaryToNegative parameters angular cell
          (sourceOuterTrace parameters L (angular + cell) source 1),
        sourceBoundaryToNegative parameters angular cell
          (sourceOuterTrace parameters L (angular + cell) source 2)] ∧
    ‖actualSevenSlotTrace parameters L angular cell x xi source‖ ^ 2 ≤
      ‖x‖ ^ 2 + 3 * ‖xi‖ ^ 2 +
        sourceOuterTraceConstant L (angular + cell) ^ 2 * ‖source‖ ^ 2 :=
  ⟨actualSevenSlotTrace_components parameters L angular cell x xi source,
    actualSevenSlotTrace_bound_sq parameters L positive angular cell x xi source⟩

/-- Smooth-core realization of the three known-source slots in AH20. -/
theorem ah20_actual_source_core_consumer (parameters : PhaseParameters) (L : ℝ)
    (angular cell : ℕ) (x : NegativeTrace parameters angular cell 1)
    (xi : PositiveTrace parameters angular cell 1)
    (source : SmoothQuotient parameters) (mode : ℤ × ℤ) :
    (fun slot : Fin 3 => negativeTraceCoefficient parameters angular cell
      (actualSevenSlotTrace parameters L angular cell x xi
        (quotientEta parameters (angular + cell + 2) source) (Fin.natAdd 4 slot)) mode) =
      ![originalBoundaryCoefficient parameters
          (tangentialBoundaryCore parameters (cartesianSourceVector source)) mode,
        originalBoundaryCoefficient parameters
          (rotationCore parameters
            (tangentialBoundaryCore parameters (cartesianSourceVector source))) mode,
        (L : ℂ)⁻¹ • originalBoundaryCoefficient parameters (source 3) mode] :=
  actualSevenSlotTrace_source_core parameters L angular cell x xi source mode

end Grad.BoundaryKernelAction
