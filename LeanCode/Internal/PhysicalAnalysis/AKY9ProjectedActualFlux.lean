import AKY8ActualFullCellRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.CartesianUncompressed
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Frame Grad.RawCircularSectors Grad.NonlinearRange
open Grad.CartesianScalarElimination

def scalarMeanFreeLinear : ClosedJet 1 →ₗ[ℂ] ClosedJet 1 := LinearMap.id - angularClosedJetLinear 1 0

def vectorMeanFreeLinear : ClosedJet 2 →ₗ[ℂ] ClosedJet 2 := LinearMap.id - equivariantAverageLinear

theorem scalarMeanFree_zeroMean (field : ClosedJet 1) :
    angularClosedJet 0 (scalarMeanFreeLinear field) = 0 := by
  change angularClosedJetLinear 1 0 (field - angularClosedJet 0 field) = 0
  rw [map_sub]
  change angularClosedJet 0 field - angularClosedJet 0 (angularClosedJet 0 field) = 0
  rw [angularClosedJet_projection, if_pos rfl, sub_self]

theorem vectorMeanFree_zeroMean (field : ClosedJet 2) :
    equivariantAverageJet (vectorMeanFreeLinear field) = 0 := by
  change equivariantAverageJet (field - equivariantAverageJet field) = 0
  rw [equivariantAverageJet_sub, equivariantAverageJet_idempotent, sub_self]

theorem scalarMeanFree_idempotent (field : ClosedJet 1) :
    scalarMeanFreeLinear (scalarMeanFreeLinear field) = scalarMeanFreeLinear field := by
  change scalarMeanFreeLinear field - angularClosedJet 0 (scalarMeanFreeLinear field) = _
  rw [scalarMeanFree_zeroMean, sub_zero]

theorem projectedDiv_vectorMeanFree (field : ClosedJet 2) :
    scalarMeanFreeLinear (vectorDivJet (vectorMeanFreeLinear field)) =
      scalarMeanFreeLinear (vectorDivJet field) := by
  have div : vectorDivJet (vectorMeanFreeLinear field) = scalarMeanFreeLinear (vectorDivJet field) := by
    change vectorDivLinear (field - equivariantAverageJet field) = _
    rw [map_sub]
    exact congrArg (fun value : ClosedJet 1 => vectorDivJet field - value) (average_div field)
  rw [div, scalarMeanFree_idempotent]

theorem projectedFlux_preserved (frequency : ℂ) (vector flux : ClosedJet 2)
    (scalar third : ClosedJet 1) :
    scalarMeanFreeLinear (-vectorDivJet vector - frequency • scalar + vectorDivJet flux + frequency • third) =
      scalarMeanFreeLinear (-vectorDivJet vector - frequency • scalar +
        vectorDivJet (vectorMeanFreeLinear flux) + frequency • scalarMeanFreeLinear third) := by
  rw [map_add, map_add, map_add, map_add, projectedDiv_vectorMeanFree, map_smul, map_smul,
    scalarMeanFree_idempotent]

variable {L sigma gamma ell : ℝ}

theorem apSmoothDiv_components_jet (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 3) (cell : ℤ) :
    apSmoothJet admissible 1 cell (apSmoothDiv admissible field) =
      vectorDivJet (apSmoothJet admissible 2 cell (apSmoothPlanar L sigma gamma ell field)) +
        seedScaledFrequency L ell cell •
          apSmoothJet admissible 1 cell (apSmoothScalar L sigma gamma ell field) := by
  have first := (apSmoothDiv_jet admissible field cell).trans
    (congrArg (fun value : ClosedJet 1 => value + seedScaledFrequency L ell cell •
      valueMapJet toroidalPartMap (apSmoothJet admissible 3 cell field))
        (planarDivJet_components (apSmoothJet admissible 3 cell field)))
  exact first.trans (congrArg₂ (fun vector scalar => vectorDivJet vector + seedScaledFrequency L ell cell • scalar)
    (apSmoothValueMap_jet admissible planarPartMap field cell).symm
    (apSmoothValueMap_jet admissible toroidalPartMap field cell).symm)

theorem projectedDiv_sum_fullCell (admissible : Admissible L sigma gamma ell)
    (field flux : APSmooth L sigma gamma ell 3) (cell : ℤ) :
    apSmoothJet admissible 1 cell (apSmoothRemoveMean L sigma gamma ell 1
      (apSmoothDiv admissible (-field + flux))) = scalarMeanFreeLinear
        (-vectorDivJet (apSmoothJet admissible 2 cell (apSmoothPlanar L sigma gamma ell field)) -
          seedScaledFrequency L ell cell • apSmoothJet admissible 1 cell (apSmoothScalar L sigma gamma ell field) +
          vectorDivJet (apSmoothJet admissible 2 cell (apSmoothPlanar L sigma gamma ell flux)) +
          seedScaledFrequency L ell cell • apSmoothJet admissible 1 cell (apSmoothScalar L sigma gamma ell flux)) := by
  let derivative := (apSmoothJet admissible 1 cell).comp (apSmoothDiv admissible)
  have expanded := (derivative.map_add (-field) flux).trans
    (congrArg (fun value : ClosedJet 1 => value + derivative flux) (derivative.map_neg field))
  have parts := congrArg₂ (fun first second : ClosedJet 1 => -first + second)
    (apSmoothDiv_components_jet admissible field cell) (apSmoothDiv_components_jet admissible flux cell)
  have rearranged :
      -(vectorDivJet (apSmoothJet admissible 2 cell (apSmoothPlanar L sigma gamma ell field)) +
        seedScaledFrequency L ell cell • apSmoothJet admissible 1 cell (apSmoothScalar L sigma gamma ell field)) +
      (vectorDivJet (apSmoothJet admissible 2 cell (apSmoothPlanar L sigma gamma ell flux)) +
        seedScaledFrequency L ell cell • apSmoothJet admissible 1 cell (apSmoothScalar L sigma gamma ell flux)) =
      -vectorDivJet (apSmoothJet admissible 2 cell (apSmoothPlanar L sigma gamma ell field)) -
        seedScaledFrequency L ell cell • apSmoothJet admissible 1 cell (apSmoothScalar L sigma gamma ell field) +
        vectorDivJet (apSmoothJet admissible 2 cell (apSmoothPlanar L sigma gamma ell flux)) +
        seedScaledFrequency L ell cell • apSmoothJet admissible 1 cell (apSmoothScalar L sigma gamma ell flux) := by module
  exact (apSmoothRemoveMean_jet admissible (apSmoothDiv admissible (-field + flux)) cell).trans
    (congrArg scalarMeanFreeLinear (expanded.trans (parts.trans rearranged)))

theorem actualDeterminant_fullCell (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (state : CompensatedData L sigma gamma ell) (cell : ℤ) :
    apSmoothJet admissible 1 cell (actualDeterminant admissible data coherent state) =
      scalarMeanFreeLinear
        (-vectorDivJet (apSmoothJet admissible 2 cell
            (apSmoothPlanar L sigma gamma ell (actualErQuotient admissible state))) -
          seedScaledFrequency L ell cell • apSmoothJet admissible 1 cell
            (apSmoothScalar L sigma gamma ell (actualErQuotient admissible state)) +
          vectorDivJet (vectorMeanFreeLinear (apSmoothJet admissible 2 cell
            (apSmoothPlanar L sigma gamma ell (actualErFlux admissible data coherent
              (compensatedReconstruct admissible state))))) +
          seedScaledFrequency L ell cell • scalarMeanFreeLinear (apSmoothJet admissible 1 cell
            (apSmoothScalar L sigma gamma ell (actualErFlux admissible data coherent
              (compensatedReconstruct admissible state))))) := by
  have row := congrArg (apSmoothJet admissible 1 cell)
    (actualDeterminant_normalized admissible data coherent state)
  exact row.trans ((projectedDiv_sum_fullCell admissible (actualErQuotient admissible state)
    (actualErFlux admissible data coherent (compensatedReconstruct admissible state)) cell).trans
      (projectedFlux_preserved _ _ _ _ _))

end Grad.CartesianUncompressed
