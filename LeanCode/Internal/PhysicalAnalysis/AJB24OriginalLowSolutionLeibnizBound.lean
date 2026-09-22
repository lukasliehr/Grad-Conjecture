import AJB17ActualFiniteDataOrbitSmoothness
import AJB23ActualAxisDerivativeRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped BigOperators ContDiff
namespace Grad.AnnularLowOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularCurrentLow Grad.AnnularKernelOrbit
open Grad.AnnularCoupledOrbit Grad.AnnularReconstruction Grad.AnnularInverseCalculus Grad.AnnularOrbitGenerators
open Grad.GaugeCoefficients.Physical.Allocation

/-- The genuine derivative of the independent bulk/incoming data orbit. -/
def actualLowDataCellGenerator (lower : ℝ) (data : LowEnergyData lower) (order : ℕ) : LowEnergyData lower :=
  iteratedDeriv order (fun time : ℝ => lowDataTranslationEquivalence lower (0, time) data) 0

/-- A cutoff-independent Leibniz bound for the genuine solution generator,
with the unchanged inverse and the actual independently prescribed data. -/
theorem actualLowSolutionCellGenerator_Leibniz (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      lowCurrentNeighborhood parameters length compact)
    (data : LowEnergyData lower)
    (dataSmooth : ContDiff ℝ ∞ (fun time : ℝ => lowDataTranslationEquivalence lower (0, time) data)) (order : ℕ) :
    ‖actualLowSolutionCellGenerator parameters length compact lower lengthPositive positive bounded state data order‖ ≤
      ∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ) *
        ‖orderedOrbitDerivative (List.replicate index true)
          (actualLowInverseOrbit parameters length compact lower lengthPositive positive bounded state) 0‖ *
        ‖actualLowDataCellGenerator lower data (order - index)‖ := by
  have inverseSmooth := actualLowInverseOrbit_contDiff parameters length compact lower lengthPositive positive bounded state small
  have bound := iteratedDeriv_operatorCellApplication_bound
    (E := LowEnergyData lower) (F := lowEnergyGraph lower length positive)
    (actualLowInverseOrbit parameters length compact lower lengthPositive positive bounded state)
    (fun time => lowDataTranslationEquivalence lower (0, time) data)
    inverseSmooth dataSmooth order 0
  have same : (fun time : ℝ => actualLowInverseOrbit parameters length compact lower lengthPositive positive bounded state (0, time)
      (lowDataTranslationEquivalence lower (0, time) data)) =
      (fun time : ℝ => lowTranslation lower length positive (0, time)
        (lowCurrentInverse parameters length compact lower lengthPositive positive bounded state data)) := by
    funext time
    exact actualLowInverseOrbit_translation parameters length compact lower lengthPositive positive bounded state (0, time) data
  rw [same] at bound
  exact bound

/-- Finite original Fourier data supply every smoothness hypothesis in the
actual norm estimate; no cutoff size occurs in the bound. -/
theorem lowFiniteDataSolutionCellGenerator_Leibniz (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      lowCurrentNeighborhood parameters length compact)
    (data : LowEnergyData lower) (support : Finset LowAnnularIndex)
    (bulkFinite : ∀ index, index ∉ support → data.ofLp.1 index = 0)
    (incomingFinite : ∀ index, index ∉ support → data.ofLp.2 index = 0) (order : ℕ) :
    ‖actualLowSolutionCellGenerator parameters length compact lower lengthPositive positive bounded state data order‖ ≤
      ∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ) *
        ‖orderedOrbitDerivative (List.replicate index true)
          (actualLowInverseOrbit parameters length compact lower lengthPositive positive bounded state) 0‖ *
        ‖actualLowDataCellGenerator lower data (order - index)‖ :=
  actualLowSolutionCellGenerator_Leibniz parameters length compact lower lengthPositive positive bounded state small data
    (lowFiniteDataOrbit_contDiff lower data support bulkFinite incomingFinite) order

end Grad.AnnularLowOrbit
