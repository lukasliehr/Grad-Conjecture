import AHT2FullBulkKernelAction

noncomputable section
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace Grad.AnnularKernelL2
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.SourceCollarCoefficients
open Grad.PhaseAlgebra Grad.BoundaryLift

variable {src tgt : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (measure : Measure ℝ) (radius : ℝ → RadialPoint)
    (radiusContinuous : Continuous radius)
    (kernel : (x : ℝ) → RadialKernel parameters (radius x) src tgt)
    (entryMeasurable : ∀ shift mode, AEStronglyMeasurable
      (fun x => (kernel x).entry shift mode) measure)

include radiusContinuous entryMeasurable in
theorem bulkShiftAction_measurable (field : ℝ → CellL2 src)
    (fieldMeasurable : AEStronglyMeasurable field measure) (shift : ℤ × ℤ) :
    AEStronglyMeasurable (fun x =>
      bulkShiftAction parameters power (radius x) (kernel x) shift (field x)) measure := by
  apply cellL2_measurable_of_coordinates
  intro mode
  simp only [bulkShiftAction_apply]
  have scalar : AEStronglyMeasurable (fun x =>
      (bulkWeightRatio parameters power (radius x).val shift mode : ℂ)) measure :=
    (Complex.continuous_ofReal.comp
      ((bulkWeightRatio_continuous parameters power shift mode).comp
        (continuous_subtype_val.comp radiusContinuous))).aestronglyMeasurable
  have coordinate : AEStronglyMeasurable
      (fun x => field x (twoFrequencyTranslation shift mode)) measure :=
    (lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean src) 2
      (twoFrequencyTranslation shift mode)).continuous.comp_aestronglyMeasurable fieldMeasurable
  have vector : AEStronglyMeasurable (fun x =>
      (kernel x).entry shift (twoFrequencyTranslation shift mode)
        (field x (twoFrequencyTranslation shift mode))) measure :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      ((entryMeasurable shift (twoFrequencyTranslation shift mode)).prodMk coordinate)
  exact scalar.smul vector

include radiusContinuous entryMeasurable in
theorem bulkKernelAction_measurable (field : ℝ → CellL2 src)
    (fieldMeasurable : AEStronglyMeasurable field measure) :
    AEStronglyMeasurable (fun x =>
      bulkKernelAction parameters power (radius x) (kernel x) (field x)) measure := by
  apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset (ℤ × ℤ)))
    (f := fun shifts x => ∑ shift ∈ shifts,
      bulkShiftAction parameters power (radius x) (kernel x) shift (field x))
  · intro shifts
    exact Finset.aestronglyMeasurable_fun_sum shifts (fun shift _ =>
      bulkShiftAction_measurable parameters power measure radius radiusContinuous kernel
        entryMeasurable field fieldMeasurable shift)
  · filter_upwards with x
    exact bulkKernelAction_hasSum parameters power (radius x) (kernel x) (field x)

end Grad.AnnularKernelL2
