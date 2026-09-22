import AKB9ConjugatedCoupledFourierFidelity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set
namespace Grad.AnnularWeightedSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularLowEnergy Grad.AnnularOmegaGraph Grad.AnnularFluxTrace
open Grad.AnnularHighGenerators Grad.AnnularCoupledInverse Grad.AnnularHighTilt Grad.AnnularTiltedReference Grad.AnnularSmoothCore Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem weightedSection_phase_commute (radial phase : ℝ) (frequency : ℂ) (value : ComplexEuclidean 1) :
    radial • (frequency • (phase • value)) = phase • (radial • (frequency • value)) := by
  rw [smul_comm frequency phase value, smul_comm radial phase (frequency • value)]

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (field : CoupledSpace lower length positive lengthPositive)

/-- Original analytic phase, with no change of width or Fourier field. -/
theorem conjugatedCoupledXiCoefficient_physical (grade : ℕ)
    (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    conjugatedCoupledXiCoefficient parameters lower length positive bounded lengthPositive field grade radius mode =
      Real.exp (radialPhase parameters radius.val mode.2) •
        sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive field grade radius mode := by
  unfold conjugatedCoupledXiCoefficient sameCoupledXiCoefficient
  split_ifs
  · rw [← conjugatedHighSection_physical lower length positive bounded parameters]
    exact weightedSection_phase_commute _ _ _ _
  · rw [← conjugatedLowSection_physical parameters lower length positive bounded]
    exact smul_comm _ _ _
  · rw [smul_zero]

theorem conjugatedCoupledXCoefficient_physical (grade : ℕ)
    (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    conjugatedCoupledXCoefficient parameters lower length positive bounded lengthPositive field grade radius mode =
      Real.exp (radialPhase parameters radius.val mode.2) •
        sameCoupledXCoefficient parameters lower length positive bounded lengthPositive field grade radius mode := by
  unfold conjugatedCoupledXCoefficient sameCoupledXCoefficient
  split_ifs
  · rw [← conjugatedFluxSection_physical lower positive bounded parameters]
    exact weightedSection_phase_commute _ _ _ _
  · rw [← conjugatedLowSection_physical parameters lower length positive bounded]
    exact smul_comm _ _ _
  · rw [smul_zero]

variable (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)

include allGrades

/-- The Hilbert curve coefficients are exp(Phi) times the actual SAME physical coefficients. -/
theorem conjugatedCoupledXiSection_physical (grade : ℕ)
    (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    conjugatedCoupledXiSection parameters lower length positive bounded lengthPositive grade field radius mode =
      Real.exp (radialPhase parameters radius.val mode.2) •
        sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive field grade radius mode :=
  (conjugatedCoupledXiSection_coefficient parameters lower length positive bounded lengthPositive field allGrades grade radius mode).trans
    (conjugatedCoupledXiCoefficient_physical parameters lower length positive bounded lengthPositive field grade radius mode)

theorem conjugatedCoupledXSection_physical (grade : ℕ)
    (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    conjugatedCoupledXSection parameters lower length positive bounded lengthPositive grade field radius mode =
      Real.exp (radialPhase parameters radius.val mode.2) •
        sameCoupledXCoefficient parameters lower length positive bounded lengthPositive field grade radius mode :=
  (conjugatedCoupledXSection_coefficient parameters lower length positive bounded lengthPositive field allGrades grade radius mode).trans
    (conjugatedCoupledXCoefficient_physical parameters lower length positive bounded lengthPositive field grade radius mode)

end Grad.AnnularWeightedSmoothCore
