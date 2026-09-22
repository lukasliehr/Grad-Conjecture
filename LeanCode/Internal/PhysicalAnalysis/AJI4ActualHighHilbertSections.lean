import AJI3ActualHighContinuousBounds
import AAZJ4TwoExtraGradeSummability

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction
open Grad.AnnularJointRegularity Grad.GaugeCoefficients.Physical.WeightedTrace

variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)

def actualHighHilbertSection (grade : ℕ) (field : annularEnergySpace lower length positive)
    (radius : Icc lower (1 : ℝ)) : lp (fun _ : HighAnnularMode => ComplexEuclidean 1) 2 :=
  hilbertSectionValue (fun mode radius =>
    ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ grade : ℝ) : ℂ) •
      annularPhysicalValueSection parameters lower length positive bounded mode field radius) radius

variable (grade : ℕ) (field weighted : annularEnergySpace lower length positive)
    (same : ∀ mode : HighAnnularMode, weighted.val mode =
      ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ (grade + 4) : ℝ) : ℂ) • field.val mode)

include weighted same

theorem actualHighHilbertSection_continuous :
    Continuous (actualHighHilbertSection parameters lower length positive bounded grade field) := by
  unfold actualHighHilbertSection
  exact hilbertSection_continuous
    (fun (mode : HighAnnularMode) (radius : Icc lower (1 : ℝ)) =>
      ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ grade : ℝ) : ℂ) •
        annularPhysicalValueSection parameters lower length positive bounded mode field radius)
    (fun mode => (annularPhysicalValueSection parameters lower length positive bounded mode field).continuous.const_smul
      (((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ grade : ℝ) : ℂ)))
    (fun mode => ((2 * sourceEndpointConstant lower) * ‖weighted‖) *
      (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ 4)⁻¹)
    (annularHigh_inverse_four_summable.mul_left _)
    (actualHighPhysicalSection_decay lower length positive bounded parameters grade field weighted same)

theorem actualHighHilbertSection_coefficient (radius : Icc lower (1 : ℝ)) (mode : HighAnnularMode) :
    actualHighHilbertSection parameters lower length positive bounded grade field radius mode =
      ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ grade : ℝ) : ℂ) •
        annularPhysicalValueSection parameters lower length positive bounded mode field radius := by
  unfold actualHighHilbertSection
  exact hilbertSection_coefficient
    (fun (mode : HighAnnularMode) (radius : Icc lower (1 : ℝ)) =>
      ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ grade : ℝ) : ℂ) •
        annularPhysicalValueSection parameters lower length positive bounded mode field radius)
    (fun mode => ((2 * sourceEndpointConstant lower) * ‖weighted‖) *
      (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ 4)⁻¹)
    (annularHigh_inverse_four_summable.mul_left _)
    (actualHighPhysicalSection_decay lower length positive bounded parameters grade field weighted same) radius mode

end Grad.AnnularSmoothCore
