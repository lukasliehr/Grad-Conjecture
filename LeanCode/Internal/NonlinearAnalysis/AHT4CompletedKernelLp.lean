import AHT3BulkActionMeasurable

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
    (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (momentBound : ∀ᵐ x ∂measure,
      fullKernelMoment (radialKernelParameters parameters (radius x)) power (kernel x) ≤ bound)

include radiusContinuous entryMeasurable momentBound in
theorem kernelLp_mem (field : Lp (CellL2 src) 2 measure) :
    MemLp (fun x => bulkKernelAction parameters power (radius x) (kernel x) (field x)) 2 measure := by
  apply (Lp.memLp field).of_le_mul (c := bound)
  · exact bulkKernelAction_measurable parameters power measure radius radiusContinuous kernel
      entryMeasurable field (Lp.aestronglyMeasurable field)
  · filter_upwards [momentBound] with x boundAt
    exact (bulkKernelAction_bound parameters power (radius x) (kernel x) (field x)).trans
      (mul_le_mul_of_nonneg_right boundAt (norm_nonneg _))

def kernelLp (field : Lp (CellL2 src) 2 measure) : Lp (CellL2 tgt) 2 measure :=
  (kernelLp_mem parameters power measure radius radiusContinuous kernel entryMeasurable bound
    momentBound field).toLp (fun x => bulkKernelAction parameters power (radius x) (kernel x) (field x))

theorem kernelLp_ae (field : Lp (CellL2 src) 2 measure) :
    ∀ᵐ x ∂measure,
      kernelLp parameters power measure radius radiusContinuous kernel entryMeasurable bound
        momentBound field x = bulkKernelAction parameters power (radius x) (kernel x) (field x) :=
  (kernelLp_mem parameters power measure radius radiusContinuous kernel entryMeasurable bound
    momentBound field).coeFn_toLp

include momentBound in
theorem kernelLp_norm (field : Lp (CellL2 src) 2 measure) :
    ‖kernelLp parameters power measure radius radiusContinuous kernel entryMeasurable bound
        momentBound field‖ ≤ bound * ‖field‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [kernelLp_ae parameters power measure radius radiusContinuous kernel
    entryMeasurable bound momentBound field, momentBound] with x literal estimate
  rw [literal]
  exact (bulkKernelAction_bound parameters power (radius x) (kernel x) (field x)).trans
    (mul_le_mul_of_nonneg_right estimate (norm_nonneg _))

theorem kernelLp_add (first second : Lp (CellL2 src) 2 measure) :
    kernelLp parameters power measure radius radiusContinuous kernel entryMeasurable bound momentBound (first + second) =
      kernelLp parameters power measure radius radiusContinuous kernel entryMeasurable bound momentBound first +
      kernelLp parameters power measure radius radiusContinuous kernel entryMeasurable bound momentBound second := by
  apply Lp.ext
  filter_upwards [kernelLp_ae parameters power measure radius radiusContinuous kernel entryMeasurable bound momentBound (first + second),
    kernelLp_ae parameters power measure radius radiusContinuous kernel entryMeasurable bound momentBound first,
    kernelLp_ae parameters power measure radius radiusContinuous kernel entryMeasurable bound momentBound second,
    Lp.coeFn_add first second,
    Lp.coeFn_add
      (kernelLp parameters power measure radius radiusContinuous kernel entryMeasurable bound momentBound first)
      (kernelLp parameters power measure radius radiusContinuous kernel entryMeasurable bound momentBound second)]
    with x sumLiteral firstLiteral secondLiteral inputSum outputSum
  rw [sumLiteral, outputSum, Pi.add_apply, firstLiteral, secondLiteral, inputSum, Pi.add_apply, map_add]

theorem kernelLp_smul (scalar : ℂ) (field : Lp (CellL2 src) 2 measure) :
    kernelLp parameters power measure radius radiusContinuous kernel entryMeasurable bound momentBound (scalar • field) =
      scalar • kernelLp parameters power measure radius radiusContinuous kernel entryMeasurable bound momentBound field := by
  apply Lp.ext
  filter_upwards [kernelLp_ae parameters power measure radius radiusContinuous kernel entryMeasurable bound momentBound (scalar • field),
    kernelLp_ae parameters power measure radius radiusContinuous kernel entryMeasurable bound momentBound field,
    Lp.coeFn_smul scalar field,
    Lp.coeFn_smul scalar (kernelLp parameters power measure radius radiusContinuous kernel entryMeasurable bound momentBound field)]
    with x scaledLiteral literal inputScale outputScale
  rw [scaledLiteral, outputScale, Pi.smul_apply, literal, inputScale, Pi.smul_apply, map_smul]

def kernelLpLinear : Lp (CellL2 src) 2 measure →ₗ[ℂ] Lp (CellL2 tgt) 2 measure where
  toFun := kernelLp parameters power measure radius radiusContinuous kernel entryMeasurable bound momentBound
  map_add' := kernelLp_add parameters power measure radius radiusContinuous kernel entryMeasurable bound momentBound
  map_smul' := kernelLp_smul parameters power measure radius radiusContinuous kernel entryMeasurable bound momentBound

def kernelLpCLM : Lp (CellL2 src) 2 measure →L[ℂ] Lp (CellL2 tgt) 2 measure :=
  (kernelLpLinear parameters power measure radius radiusContinuous kernel entryMeasurable bound momentBound).mkContinuous
    bound (kernelLp_norm parameters power measure radius radiusContinuous kernel entryMeasurable bound momentBound)

include boundNonnegative in
theorem kernelLpCLM_norm :
    ‖kernelLpCLM parameters power measure radius radiusContinuous kernel entryMeasurable bound momentBound‖ ≤ bound :=
  LinearMap.mkContinuous_norm_le _ boundNonnegative _

end Grad.AnnularKernelL2
