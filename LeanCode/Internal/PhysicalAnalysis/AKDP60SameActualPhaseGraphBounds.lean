import AKDP59ActualPhaseGraphAbsorption

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets
open Grad.ActualOriginalSourceMoments Grad.OriginalCartesianTameEstimate Grad.SpatialDilation Grad.CellWeights

/-- Any graph of the genuine first phase field satisfies the lower-order
estimate; its actual natural moment is retained explicitly. -/
theorem startupActualPhaseFirst_graph_bound (parameters : PhaseParameters) (scale : Scale)
    (order grade : ℕ) (allocated : order+1≤grade) (direction : Fin 2) (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ remainder : ℝ,0≤remainder ∧ ∀ (core : ACore parameters 3) (moment : StartupL2 3)
      (output : GraphGrade 3 order 0 openUnitDisk),
      StartupRadialRelated (fun cell _ => cellWeight cell) moment (originalSourceMoments parameters core).field →
      base 3 order openUnitDisk (fun _ => 0) output=
        startupScaledPhaseFirstField parameters.sigma0 parameters.gamma scale.val parameters.gamma_pos.le
          scale.property.1.le scale.property.2 direction moment →
      ‖output‖≤epsilon*originalPlanarNorm parameters grade core+remainder*originalCellNorm parameters grade core := by
  let symbol := startupPhaseSlopeSymbol parameters.sigma0 parameters.gamma scale.val parameters.gamma_pos.le scale.property.1.le order direction
  obtain ⟨remainder,nonnegative,bound⟩ := symbol.graph_adjustable parameters grade 1 (by norm_num) allocated
    (fun index => startupPhaseDerivativeConstant parameters.gamma scale.val (degree index+1))
    (fun index => startupPhaseDerivativeConstant_nonnegative _ _ parameters.gamma_pos.le scale.property.1.le _)
    (fun index cell point => startupPhaseSlope_scalar_bound parameters.sigma0 parameters.gamma scale.val
      parameters.gamma_pos.le scale.property.1.le index cell direction point) epsilon positive
  refine ⟨remainder,nonnegative,?_⟩
  intro core moment output momentSame outputSame
  let inputProof := startupOriginal_reservedGraph parameters core (L := 1) (ell := 1) one_ne_zero one_ne_zero order (order+1)
  let input := inputProof.choose
  have inputSame := inputProof.choose_spec
  apply bound 3 core input output inputSame
  rw [outputSame]
  have actual := startupScaledPhaseFirstField_same parameters.sigma0 parameters.gamma scale.val parameters.gamma_pos.le
    scale.property.1.le scale.property.2 direction (originalSourceMoments parameters core).field moment momentSame
  have symbolic := symbol.baseField_same input
  rw [inputSame] at symbolic
  apply startupField_ae_ext
  filter_upwards [actual,symbolic] with point actualValue symbolicValue
  intro cell
  simpa only [symbol,startupPhaseSlopeSymbol,Complex.coe_smul] using (actualValue cell).trans (symbolicValue cell).symm

/-- The same full Hessian plus gradient-square field is paid at exactly
two complementary cell orders; no extra spatial derivative is required. -/
theorem startupActualPhaseSecond_graph_bound (parameters : PhaseParameters) (scale : Scale)
    (order grade : ℕ) (allocated : order+2≤grade) (outer inner : Fin 2) (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ remainder : ℝ,0≤remainder ∧ ∀ (core : ACore parameters 3) (moment : StartupL2 3)
      (output : GraphGrade 3 order 0 openUnitDisk),
      StartupRadialRelated (fun cell _ => cellWeight cell^2) moment (originalSourceMoments parameters core).field →
      base 3 order openUnitDisk (fun _ => 0) output=
        startupScaledPhaseSecondField parameters.sigma0 parameters.gamma scale.val parameters.gamma_pos.le
          scale.property.1.le scale.property.2 outer inner moment →
      ‖output‖≤epsilon*originalPlanarNorm parameters grade core+remainder*originalCellNorm parameters grade core := by
  let symbol := startupPhaseSecondSymbol parameters.sigma0 parameters.gamma scale.val parameters.gamma_pos.le scale.property.1.le order outer inner
  obtain ⟨remainder,nonnegative,bound⟩ := symbol.graph_adjustable parameters grade 2 (by norm_num) allocated
    (fun index => startupPhaseDerivativeConstant parameters.gamma scale.val (degree index+2)+
      startupPhaseProductConstant parameters.gamma scale.val index)
    (fun index => add_nonneg
      (startupPhaseDerivativeConstant_nonnegative _ _ parameters.gamma_pos.le scale.property.1.le _)
      (startupPhaseProductConstant_nonnegative _ _ parameters.gamma_pos.le scale.property.1.le index))
    (fun index cell point => startupPhaseSecond_scalar_bound parameters.sigma0 parameters.gamma scale.val
      parameters.gamma_pos.le scale.property.1.le index cell outer inner point) epsilon positive
  refine ⟨remainder,nonnegative,?_⟩
  intro core moment output momentSame outputSame
  let inputProof := startupOriginal_reservedGraph parameters core (L := 1) (ell := 1) one_ne_zero one_ne_zero order (order+2)
  let input := inputProof.choose
  have inputSame := inputProof.choose_spec
  apply bound 3 core input output inputSame
  rw [outputSame]
  have actual := startupScaledPhaseSecondField_same parameters.sigma0 parameters.gamma scale.val parameters.gamma_pos.le
    scale.property.1.le scale.property.2 outer inner (originalSourceMoments parameters core).field moment momentSame
  have symbolic := symbol.baseField_same input
  rw [inputSame] at symbolic
  apply startupField_ae_ext
  filter_upwards [actual,symbolic] with point actualValue symbolicValue
  intro cell
  simpa only [symbol,startupPhaseSecondSymbol,Complex.coe_smul] using (actualValue cell).trans (symbolicValue cell).symm

end Grad.CartesianStartup
