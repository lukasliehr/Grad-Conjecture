import AKB6ConjugatedFluxHilbert

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
namespace Grad.AnnularWeightedSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction
open Grad.AnnularSmoothCore Grad.AnnularJointRegularity Grad.AnnularLowEnergy Grad.GaugeCoefficients.Physical.WeightedTrace

variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)

def conjugatedLowHilbertSection (component : Fin 2) (grade : ℕ)
    (field : lowEnergyGraph lower length positive) (radius : Icc lower (1 : ℝ)) :
    lp (fun _ : LowAnnularMode => ComplexEuclidean 1) 2 :=
  hilbertSectionValue (fun mode radius =>
    ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ grade : ℝ) : ℂ) •
      conjugatedLowSection parameters lower length positive bounded field (component, mode) radius) radius

variable (lengthPositive : 0 < length) (component : Fin 2) (grade : ℕ)
    (field weighted : lowEnergyGraph lower length positive)
    (same : ∀ (coordinate : Fin 2) (index : LowAnnularIndex), weighted.val coordinate index =
      ((Grad.AnnularVariational.annularFrequency index.2.val.1 index.2.val.2 ^ (grade + 5) : ℝ) : ℂ) •
        field.val coordinate index)

include lengthPositive weighted same

theorem conjugatedLowHilbertSection_continuous :
    Continuous (conjugatedLowHilbertSection parameters lower length positive bounded component grade field) := by
  unfold conjugatedLowHilbertSection
  exact hilbertSection_continuous
    (fun (mode : LowAnnularMode) (radius : Icc lower (1 : ℝ)) =>
      ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ grade : ℝ) : ℂ) •
        conjugatedLowSection parameters lower length positive bounded field (component, mode) radius)
    (fun mode => (conjugatedLowSection parameters lower length positive bounded field (component, mode)).continuous.const_smul
      (((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ grade : ℝ) : ℂ)))
    (fun mode => ((2 * sourceEndpointConstant lower) * (‖weighted.val 0‖ + (length⁻¹ + lower⁻¹) * ‖weighted.val 1‖)) *
      (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ 4)⁻¹)
    (actualLow_inverse_four_summable.mul_left _)
    (fun mode radius => conjugatedLowSection_decay parameters lower length positive bounded lengthPositive grade field weighted same (component, mode) radius)

theorem conjugatedLowHilbertSection_coefficient (radius : Icc lower (1 : ℝ)) (mode : LowAnnularMode) :
    conjugatedLowHilbertSection parameters lower length positive bounded component grade field radius mode =
      ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ grade : ℝ) : ℂ) •
        conjugatedLowSection parameters lower length positive bounded field (component, mode) radius := by
  unfold conjugatedLowHilbertSection
  exact hilbertSection_coefficient
    (fun (mode : LowAnnularMode) (radius : Icc lower (1 : ℝ)) =>
      ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ grade : ℝ) : ℂ) •
        conjugatedLowSection parameters lower length positive bounded field (component, mode) radius)
    (fun mode => ((2 * sourceEndpointConstant lower) * (‖weighted.val 0‖ + (length⁻¹ + lower⁻¹) * ‖weighted.val 1‖)) *
      (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ 4)⁻¹)
    (actualLow_inverse_four_summable.mul_left _)
    (fun mode radius => conjugatedLowSection_decay parameters lower length positive bounded lengthPositive grade field weighted same (component, mode) radius) radius mode

end Grad.AnnularWeightedSmoothCore
