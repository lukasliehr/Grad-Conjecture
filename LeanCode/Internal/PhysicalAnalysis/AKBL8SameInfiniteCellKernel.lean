import AKBL6SameOriginalWeakEllipticRows
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set MeasureTheory MeasureTheory.Measure
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

/-- The existing Schur kernel's SAME all-cell field has its literal infinite
row action almost everywhere. Absolute L2 row summability pays the passage
from finite cells; no unproved pointwise exchange is assumed. -/
theorem startupKernel_allCell_hasSum_ae {Parameter : Type*} [MeasurableSpace Parameter]
    {measure : Measure Parameter} [SigmaFinite measure]
    {inputDimension outputDimension : ℕ} {domain : Set Spatial}
    (data : Grad.FullCellKernel.L2KernelData measure inputDimension outputDimension domain)
    (field : FieldL2 inputDimension domain) :
    ∀ᵐ point ∂volume.restrict domain, ∀ output : ℤ,
      HasSum (fun input : ℤ => ∫ parameter,
        data.coefficient output input (parameter,point)
          (field (data.orthogonal parameter point) input) ∂measure)
        (Grad.FullCellKernel.kernel data field point output) := by
  apply ae_all_iff.mpr
  intro output
  have summable := Grad.SchurKernel.Discrete.row_norm_summable
    (Grad.FullCellKernel.entry data) (Grad.FullCellKernel.integratedWeight data)
    (Grad.FullCellKernel.integratedWeight_nonneg data) (Grad.FullCellKernel.entry_norm_le data)
    data.rowsSummable (Grad.FullCellKernel.coordinateIsometry inputDimension domain field) output
  have series := Lp.hasSum_coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr summable)
  have entries : ∀ᵐ point ∂volume.restrict domain, ∀ input : ℤ,
      Grad.FullCellKernel.entry data output input (fieldCellProjection inputDimension domain input field) point =
        ∫ parameter, data.coefficient output input (parameter,point)
          (field (data.orthogonal parameter point) input) ∂measure :=
    ae_all_iff.mpr (fun input => Grad.FullCellKernel.entry_field_ae data field output input)
  filter_upwards [series,entries,fieldCellProjection_ae outputDimension domain (Grad.FullCellKernel.kernel data field)]
    with point literal same coordinate
  rw [← coordinate output,Grad.FullCellKernel.kernel_coordinate]
  exact literal.congr_fun (fun input => (same input).symm)

/-- The literal phase-conjugated Cartesian matrix action, with every integer
input cell present and convergence justified by the accepted row majorant. -/
theorem startupMatrix_allCell_hasSum_ae {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (field : StartupL2 inputDimension) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ output : ℤ,
      HasSum (fun input : ℤ => closedDiskLift
        (startupDerivativeCoefficient admissible family coherent zeroDerivativeIndex input (output-input)) point
          (field point input))
        (originalMatrixKernel admissible family coherent field point output) := by
  have series := startupKernel_allCell_hasSum_ae
    (startupDerivativeKernelData admissible family coherent zeroDerivativeIndex) field
  filter_upwards [series] with point literal
  intro output
  have row := literal output
  change HasSum (fun input : ℤ => ∫ _parameter : ℝ, closedDiskLift
    (startupDerivativeCoefficient admissible family coherent zeroDerivativeIndex input (output-input)) point
      (field point input) ∂Measure.dirac (0 : ℝ)) _ at row
  simpa only [originalMatrixKernel,startupDerivativeKernel,integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul] using row

end Grad.CartesianStartup
