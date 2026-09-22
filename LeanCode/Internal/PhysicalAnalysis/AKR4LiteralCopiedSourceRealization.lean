import AKR3ExactOriginalTupleSourceCoefficients

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
namespace Grad.AnnularOriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.BoundaryKernelAction Grad.AnnularSourceGraph Grad.AnnularPhysicalFourier
open Grad.AnnularOriginalSmoothCore Grad.AnnularReconstruction Grad.AnnularCurrentLow Grad.AnnularCurrentSource
open Grad.AnnularSmoothCore Grad.AnnularHighTilt Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (tuple : OriginalSmoothTuple parameters lower) (slot : Fin 4)

theorem tupleSourceF0Bulk_mode (mode : ℤ × ℤ) :
    unweightedSourceF0Bulk parameters lower
      (tupleOriginalSourceGraph parameters lower positive bounded tuple slot 1 0) mode =
      radialSqrtMap 1 lower (tupleConjugatedJetL2 parameters lower positive bounded tuple slot 0 mode) := by
  change sourceGradeRatio 0 0 1 0 mode • weightedRadialCoordinate 1 lower 0
    (tupleOriginalSourceGraph parameters lower positive bounded tuple slot 1 0 mode) = _
  rw [tupleOriginalSourceGraph_stored,smul_smul]
  have ratio : sourceGradeRatio 0 0 1 0 mode * splitTangentialWeight 1 0 mode = 1 := by
    unfold sourceGradeRatio
    rw [div_mul_cancel₀ _ (splitTangentialWeight_pos 1 0 mode).ne']
    simp [splitTangentialWeight]
  rw [ratio,one_smul]
  rfl

theorem tupleSourceF2Bulk_mode (mode : ℤ × ℤ) :
    unweightedSourceF2Bulk parameters lower
      (tupleOriginalSourceGraph parameters lower positive bounded tuple slot 0 0) mode =
      radialSqrtMap 1 lower (tupleConjugatedJetL2 parameters lower positive bounded tuple slot 0 mode) := by
  change weightedRadialCoordinate 1 lower 0
    (tupleOriginalSourceGraph parameters lower positive bounded tuple slot 0 0 mode) = _
  rw [tupleOriginalSourceGraph_stored]
  simp [splitTangentialWeight]

/-- Any genuine sqrt-stored source row decodes to the SAME original
physical field after the literal BF high tilt and rho normalization. -/
theorem originalF1Coefficient_of_tupleStorage (source : DivisionRow 1 lower)
    (stored : ∀ mode, source mode = radialSqrtMap 1 lower
      (tupleConjugatedJetL2 parameters lower positive bounded tuple slot 0 mode)) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      originalF1Coefficient parameters lower positive bounded.le source radius mode =
        originalPhysicalCoefficient (tuple.val slot) radius mode := by
  rw [ae_all_iff]
  intro mode
  filter_upwards [divisionHighWeight_ae lower positive bounded.le source,
    radialSqrtMap_ae 1 lower (tupleConjugatedJetL2 parameters lower positive bounded tuple slot 0 mode),
    tupleConjugatedJetL2_value parameters lower positive bounded tuple slot,
    ae_restrict_mem measurableSet_Icc] with radius high sqrtStored value inside
  unfold originalF1Coefficient lowRhoPhysicalCoefficient
  rw [high mode,stored mode,sqrtStored,originalSourceStorage_decode parameters lower positive radius inside mode,value mode]
  change Real.exp (-radialPhase parameters radius mode.2) •
    (Real.exp (radialPhase parameters radius mode.2) • _) = _
  rw [Real.exp_neg,smul_smul,inv_mul_cancel₀ (Real.exp_pos _).ne',one_smul]

/-- Exact original copied F0 coordinate, with the same H1 derivative. -/
theorem tupleSourceF0_physical :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      originalF1Coefficient parameters lower positive bounded.le
        (unweightedSourceF0Bulk parameters lower
          (tupleOriginalSourceGraph parameters lower positive bounded tuple 2 1 0)) radius mode =
        originalPhysicalCoefficient (tuple.val 2) radius mode :=
  originalF1Coefficient_of_tupleStorage parameters lower positive bounded tuple 2 _
    (tupleSourceF0Bulk_mode parameters lower positive bounded tuple 2)

/-- Exact original copied F2 coordinate, with the same H1 derivative. -/
theorem tupleSourceF2_physical :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      originalF1Coefficient parameters lower positive bounded.le
        (unweightedSourceF2Bulk parameters lower
          (tupleOriginalSourceGraph parameters lower positive bounded tuple 3 0 0)) radius mode =
        originalPhysicalCoefficient (tuple.val 3) radius mode :=
  originalF1Coefficient_of_tupleStorage parameters lower positive bounded tuple 3 _
    (tupleSourceF2Bulk_mode parameters lower positive bounded tuple 3)

end Grad.AnnularOriginalCoreRealization
