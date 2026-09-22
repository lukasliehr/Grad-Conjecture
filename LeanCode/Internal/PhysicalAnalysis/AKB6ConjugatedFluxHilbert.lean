import AKB5ConjugatedHighHilbert

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
namespace Grad.AnnularWeightedSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction
open Grad.AnnularSmoothCore Grad.AnnularJointRegularity Grad.AnnularFluxTrace Grad.GaugeCoefficients.Physical.WeightedTrace

variable (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)

def conjugatedFluxHilbertSection (grade : ℕ) (field : annularFluxWeakGraph lower positive)
    (radius : Icc lower (1 : ℝ)) : lp (fun _ : HighAnnularMode => ComplexEuclidean 1) 2 :=
  hilbertSectionValue (fun mode radius =>
    ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ grade : ℝ) : ℂ) •
      annularFluxSection lower positive bounded field mode radius) radius

variable (grade : ℕ) (field weighted : annularFluxWeakGraph lower positive)
    (sameValue : ∀ mode : HighAnnularMode, weighted.val.1 mode =
      ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ (grade + 5) : ℝ) : ℂ) • field.val.1 mode)
    (sameSlope : ∀ mode : HighAnnularMode, weighted.val.2 mode =
      ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ (grade + 5) : ℝ) : ℂ) • field.val.2 mode)

include weighted sameValue sameSlope

theorem conjugatedFluxHilbertSection_continuous :
    Continuous (conjugatedFluxHilbertSection lower positive bounded grade field) := by
  unfold conjugatedFluxHilbertSection
  exact hilbertSection_continuous
    (fun (mode : HighAnnularMode) (radius : Icc lower (1 : ℝ)) =>
      ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ grade : ℝ) : ℂ) •
        annularFluxSection lower positive bounded field mode radius)
    (fun mode => (annularFluxSection lower positive bounded field mode).continuous.const_smul
      (((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ grade : ℝ) : ℂ)))
    (fun mode => (sourceEndpointConstant lower * (‖weighted.val.1‖ + ‖weighted.val.2‖)) *
      (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ 4)⁻¹)
    (annularHigh_inverse_four_summable.mul_left _)
    (conjugatedFluxSection_decay lower positive bounded grade field weighted sameValue sameSlope)

theorem conjugatedFluxHilbertSection_coefficient (radius : Icc lower (1 : ℝ)) (mode : HighAnnularMode) :
    conjugatedFluxHilbertSection lower positive bounded grade field radius mode =
      ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ grade : ℝ) : ℂ) •
        annularFluxSection lower positive bounded field mode radius := by
  unfold conjugatedFluxHilbertSection
  exact hilbertSection_coefficient
    (fun (mode : HighAnnularMode) (radius : Icc lower (1 : ℝ)) =>
      ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ grade : ℝ) : ℂ) •
        annularFluxSection lower positive bounded field mode radius)
    (fun mode => (sourceEndpointConstant lower * (‖weighted.val.1‖ + ‖weighted.val.2‖)) *
      (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ^ 4)⁻¹)
    (annularHigh_inverse_four_summable.mul_left _)
    (conjugatedFluxSection_decay lower positive bounded grade field weighted sameValue sameSlope) radius mode

end Grad.AnnularWeightedSmoothCore
