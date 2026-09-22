import AKR2FullOriginalTupleSourceGraphs

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.AnnularOriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.BoundaryKernelAction Grad.AnnularSourceGraph Grad.AnnularPhysicalFourier
open Grad.AnnularOriginalSmoothCore Grad.AnnularReconstruction Grad.AnnularCurrentLow Grad.AnnularCurrentSource
open Grad.AnnularSmoothCore Grad.AnnularHighTilt Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (tuple : OriginalSmoothTuple parameters lower) (slot : Fin 4)

theorem tupleConjugatedJetL2_value :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      tupleConjugatedJetL2 parameters lower positive bounded tuple slot 0 mode radius =
        Real.exp (radialPhase parameters radius mode.2) •
          originalPhysicalCoefficient (tuple.val slot) radius mode := by
  rw [ae_all_iff]
  intro mode
  filter_upwards [radialSectionL2_ae 1 lower positive bounded.le
    (tupleConjugatedJetSection parameters lower bounded tuple slot 0 mode),
    ae_restrict_mem measurableSet_Icc] with radius stored inside
  change radialSectionExtension 1 lower bounded.le
    (tupleConjugatedJetSection parameters lower bounded tuple slot 0 mode) radius =
      tupleConjugatedJetL2 parameters lower positive bounded tuple slot 0 mode radius at stored
  rw [← stored]
  change (tupleConjugatedJetSection parameters lower bounded tuple slot 0 mode)
    (radialClamp lower bounded.le radius) = _
  rw [radialClamp_eq lower bounded.le radius inside]
  change iteratedDerivWithin 0 (tupleWeightedCurve parameters lower tuple slot 0) (Icc lower 1) radius mode = _
  rw [iteratedDerivWithin_zero, tupleWeightedCurve_coefficient parameters lower tuple slot 0 radius inside mode]
  simp only [pow_zero,Complex.ofReal_one,one_smul,RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

/-- Literal completed AH10 source coefficients of an arbitrary original
admissible field, with its actual phase-weighted radial derivative. -/
theorem tupleOriginalSourceGraph_physical (angular cell : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      annularSourceCoefficient parameters 1 lower positive bounded.le angular cell
        (tupleOriginalSourceGraph parameters lower positive bounded tuple slot angular cell) mode radius =
      originalPhysicalCoefficient (tuple.val slot) radius mode := by
  filter_upwards [tupleConjugatedJetL2_value parameters lower positive bounded tuple slot] with radius actual
  intro mode
  rw [annularSourceCoefficient,tupleOriginalSourceGraph_value,actual mode,
    smul_smul,inv_mul_cancel₀ (Real.exp_pos _).ne',one_smul]

/-- The original high/rho source normalization exactly cancels the sqrt(r)
coordinate of the genuine source H1 graph. -/
theorem originalSourceStorage_decode (radius : ℝ) (inside : radius ∈ Icc lower 1)
    (mode : ℤ × ℤ) (value : ComplexEuclidean 1) :
    (lowRhoPhysicalWeight parameters lower positive radius mode : ℂ)⁻¹ •
      (((radius ^ (-9 / 4 : ℝ) : ℝ) : ℂ) • (Real.sqrt radius • value)) =
        annularInversePhase parameters mode.2 radius • value := by
  have storage := originalHighSection_storageFactor parameters lower positive radius inside mode
  have power := highPowerCurve_inverse lower highTiltExponent positive radius
  have negative : highPowerCurve lower (-highTiltExponent) positive radius = radius ^ (-9 / 4 : ℝ) := by
    rw [highPowerCurve_physical lower (-highTiltExponent) positive radius inside]
    congr 1
    norm_num [highTiltExponent]
  rw [negative] at power
  have scalar : (lowRhoPhysicalWeight parameters lower positive radius mode)⁻¹ *
      (radius ^ (-9 / 4 : ℝ)) * Real.sqrt radius = annularInversePhase parameters mode.2 radius := by
    rw [← storage]
    calc
      _ = ((lowRhoPhysicalWeight parameters lower positive radius mode)⁻¹ *
        lowRhoPhysicalWeight parameters lower positive radius mode) *
        (radius ^ (-9 / 4 : ℝ) * highPowerCurve lower highTiltExponent positive radius) *
        annularInversePhase parameters mode.2 radius := by ring
      _ = _ := by rw [inv_mul_cancel₀ (lowRhoPhysicalWeight_pos parameters lower positive radius mode).ne',power,one_mul,one_mul]
  apply PiLp.ext
  intro coordinate
  change (lowRhoPhysicalWeight parameters lower positive radius mode : ℂ)⁻¹ *
    (((radius ^ (-9 / 4 : ℝ) : ℝ) : ℂ) * ((Real.sqrt radius : ℂ) * value coordinate)) =
      (annularInversePhase parameters mode.2 radius : ℂ) * value coordinate
  have castScalar : (lowRhoPhysicalWeight parameters lower positive radius mode : ℂ)⁻¹ *
      ((radius ^ (-9 / 4 : ℝ) : ℝ) : ℂ) * (Real.sqrt radius : ℂ) =
      (annularInversePhase parameters mode.2 radius : ℂ) := by
    exact_mod_cast scalar
  calc
    _ = ((lowRhoPhysicalWeight parameters lower positive radius mode : ℂ)⁻¹ *
      ((radius ^ (-9 / 4 : ℝ) : ℝ) : ℂ) * (Real.sqrt radius : ℂ)) * value coordinate := by ring
    _ = _ := congrArg (fun coefficient : ℂ => coefficient * value coordinate) castScalar

end Grad.AnnularOriginalCoreRealization
