import AKAO15PolarCoefficientJetBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualPolarFlux
open Grad.BoundaryTrace Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations Grad.BoundaryKernelAction Grad.AnnularKernelL2
open Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger
open Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.SourceCollar Grad.BoundaryLift Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3)
    (coherent : FamilyCoherent family) (row component : Fin 3)

/-- The original polar coefficient radial jets differentiate classically on the punctured disk. -/
theorem polarRadialScalarSeries_hasDerivAt (rank : ℕ) (radius : ℝ) (inside : radius ∈ Ioo 0 1) (angles : ℝ × ℝ) :
    HasDerivAt (fun point => polarRadialScalarSeries parameters family coherent row component rank point angles)
      (polarRadialScalarSeries parameters family coherent row component (rank+1) radius angles) radius := by
  exact finiteIntervalSeries_hasDerivAt 0 1 (by norm_num) (rank+1)
    (fun order mode point => cellExponential mode.2 angles.2 *
      (cellExponential mode.1 angles.1 * polarEntryScalar parameters family coherent row component order point mode))
    (fun order _ mode point _ => ((polarEntryScalar_hasDerivAt parameters family coherent row component order point mode).const_mul
      (cellExponential mode.1 angles.1)).const_mul (cellExponential mode.2 angles.2))
    (polarScalarJetMajorant parameters family row component)
    (fun order _ => polarScalarJetMajorant_summable parameters family row component order)
    (fun order _ mode point member => by
      simpa only [norm_mul,cellExponential_norm,one_mul] using
        polarScalarJetMajorant_bound parameters family coherent row component order mode point member.1 member.2)
    rank (by omega) radius inside

/-- Full angular continuity of every original polar radial coefficient jet. -/
theorem polarRadialScalarSeries_continuous_angles (rank : ℕ) (radius : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    Continuous (polarRadialScalarSeries parameters family coherent row component rank radius) := by
  apply continuous_tsum
    (fun mode : ℤ × ℤ => ((cellExponential_smooth mode.2).continuous.comp continuous_snd).mul
      (((cellExponential_smooth mode.1).continuous.comp continuous_fst).mul continuous_const))
    (polarScalarJetMajorant_summable parameters family row component rank)
  intro mode angles
  change ‖cellExponential mode.2 angles.2 * (cellExponential mode.1 angles.1 * polarEntryScalar parameters family coherent row component rank radius mode)‖ ≤ _
  simpa only [norm_mul,cellExponential_norm,one_mul] using
    polarScalarJetMajorant_bound parameters family coherent row component rank mode radius nonnegative bounded

end Grad.ActualPolarFlux
