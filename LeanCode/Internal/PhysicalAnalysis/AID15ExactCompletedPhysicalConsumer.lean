import AID14CompletedPhysicalGreenConverse

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularCurrentGreen
open Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularCircularForm
open Grad.AnnularTiltedReference Grad.AnnularGrades Grad.CircularHighRegularity Grad.AnnularSourceGraph
open Grad.AnnularCurrentBoundary Grad.AnnularOmegaGraph Grad.BoundaryKernelAction

variable (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))

/-- The completed packet equation is exactly the compact physical equation and its actual outer trace. -/
theorem physicalPacketLaw_iff_compact_endpoint (field : DivisionRow 3 lower)
    (boundary : NegativeTrace parameters 0 0 1) :
    (∀ test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive,
      inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test.val) field =
        inner ℂ (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0 test.val) boundary) ↔
    ∃ equation : CompactPhysicalPacketEquation parameters lower L positive lengthPositive widthHalf widthLength field,
      ∀ mode : HighAnnularMode,
        weightedRadialTrace 1 lower positive (lowerHalf.trans_lt (by norm_num)) 1
          (physicalFluxMomentGraph parameters lower L positive lengthPositive widthHalf widthLength
            (lowerHalf.trans_lt (by norm_num)) field equation mode) =
          (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) • boundary mode.val := by
  constructor
  · intro law
    have compactLaw : ∀ test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive,
        actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0 test.val = 0 →
        inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test.val) field = 0 := by
      intro test zero
      rw [law test, zero, inner_zero_left]
    let equation := compactPhysicalPacketEquation_of_testLaw parameters lower L positive lowerHalf lengthPositive
      widthHalf widthLength field compactLaw
    exact ⟨equation, physicalFluxMomentGraph_outer parameters lower L positive lowerHalf lengthPositive
      widthHalf widthLength field boundary equation law⟩
  · rintro ⟨equation, outer⟩
    exact physicalFlux_packet_converse parameters lower L positive lowerHalf lengthPositive
      widthHalf widthLength field boundary equation outer

/-- Exact downstream realization: the full variational law produces the original closed graph, uniformly. -/
theorem fullPhysicalPacketLaw_Domega (field : DivisionRow 3 lower) (boundary : NegativeTrace parameters 0 0 1)
    (law : ∀ test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive,
      inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test.val) field =
        inner ℂ (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0 test.val) boundary) :
    physicalOmegaCoordinates parameters lower L positive lengthPositive widthHalf widthLength field ∈
      annularOmegaGraph lower L positive lengthPositive ∧
      ‖physicalOmegaCoordinates parameters lower L positive lengthPositive widthHalf widthLength field‖ ≤ 4 * ‖field‖ := by
  obtain ⟨equation, _outer⟩ := (physicalPacketLaw_iff_compact_endpoint parameters lower L positive lowerHalf
    lengthPositive widthHalf widthLength field boundary).mp law
  exact ⟨physicalOmegaCoordinates_mem parameters lower L positive lengthPositive widthHalf widthLength
    (lowerHalf.trans_lt (by norm_num)) field equation,
    physicalOmegaCoordinates_bound parameters lower L positive lengthPositive widthHalf widthLength field⟩

end Grad.AnnularCurrentGreen
