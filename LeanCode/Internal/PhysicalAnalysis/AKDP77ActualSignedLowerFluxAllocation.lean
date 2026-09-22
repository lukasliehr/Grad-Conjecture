import AKDP76SignedAxialMixedOrderNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets Grad.NonlinearProduct
open Grad.ActualOriginalSourceFirst Grad.ActualOriginalSourceMoments Grad.OriginalCartesianTameEstimate Grad.SpatialDilation Grad.CellWeights

/-- Strict mixed order is adjustable directly in the original full norm. -/
theorem startupMixedOrder_fullAdjustable (grade order : ℕ) (strict : order<grade)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ constant : ℝ,0≤constant ∧ ∀ dimension (parameters : PhaseParameters) (core : ACore parameters dimension),
      originalMixedOrderNorm parameters grade order core≤epsilon*originalGradeNorm grade core+
        constant*originalCellNorm parameters grade core := by
  let delta := epsilon/((Fintype.card (JetIndex grade) : ℝ)+1)
  have deltaPositive : 0<delta := div_pos positive (by positivity)
  obtain ⟨constant,nonnegative,bounded⟩ := startupFiniteMixedOrders_adjustable grade (fun _ : Unit => order)
    (fun _ => strict) (fun _ => 1) (fun _ => zero_le_one) delta deltaPositive
  refine ⟨constant,nonnegative,?_⟩
  intro dimension parameters core
  have first := bounded dimension parameters core
  simp only [Fintype.sum_unique,one_mul] at first
  have planar := mul_le_mul_of_nonneg_left (startupOriginalPlanarNorm_le_full parameters grade core) deltaPositive.le
  have allocated : delta*(Fintype.card (JetIndex grade) : ℝ)≤epsilon := by
    have exactDelta : delta*((Fintype.card (JetIndex grade) : ℝ)+1)=epsilon := div_mul_cancel₀ epsilon (by positivity)
    nlinarith [deltaPositive]
  have main := mul_le_mul_of_nonneg_right allocated (originalGradeNorm_nonnegative grade core)
  nlinarith only [first,planar,main]

/-- The literal single axial shift in the native lower flux is paid at
complementary total order, with no extra unknown spatial derivative. -/
theorem startupSignedAxial_lowerGraph_fullAdjustable (order grade : ℕ) (allocated : order≤grade)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ constant : ℝ,0≤constant ∧ ∀ dimension (parameters : PhaseParameters) (core : ACore parameters dimension)
      (graph : GraphGrade dimension order 0 openUnitDisk),
      base dimension order openUnitDisk (fun _ => 0) graph=
        (originalSourceMoments parameters (originalSignedAxialCore parameters core 1 1 1)).field →
      ‖graph‖≤epsilon*originalGradeNorm (grade+1) core+constant*originalCellNorm parameters (grade+1) core := by
  obtain ⟨constant,nonnegative,bounded⟩ := startupMixedOrder_fullAdjustable (grade+1) order (by omega) epsilon positive
  refine ⟨constant,nonnegative,?_⟩
  intro dimension parameters core graph same
  rw [←startupOriginalPlanarNorm_eq_graph parameters (originalSignedAxialCore parameters core 1 1 1) graph same]
  exact ((startupOriginalPlanar_mixedOrder parameters _ grade order allocated).trans
    (startupSignedAxial_mixedOrder_bound parameters core grade order 1 allocated)).trans (bounded dimension parameters core)

/-- First phase times the genuine axial lower flux consumes two cell
orders in total; the strict spatial order is still adjustable. -/
theorem startupSignedAxial_phaseFirst_fullAdjustable (parameters : PhaseParameters) (scale : Scale)
    (order grade : ℕ) (allocated : order+1≤grade) (direction : Fin 2) (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ constant : ℝ,0≤constant ∧ ∀ (core : ACore parameters 3) (moment : StartupL2 3)
      (graph : GraphGrade 3 order 0 openUnitDisk),
      StartupRadialRelated (fun cell _ => cellWeight cell) moment
        (originalSourceMoments parameters (originalSignedAxialCore parameters core 1 1 1)).field →
      base 3 order openUnitDisk (fun _ => 0) graph=startupScaledPhaseFirstField parameters.sigma0 parameters.gamma scale.val
        parameters.gamma_pos.le scale.property.1.le scale.property.2 direction moment →
      ‖graph‖≤epsilon*originalGradeNorm (grade+1) core+constant*originalCellNorm parameters (grade+1) core := by
  obtain ⟨phaseConstant,phaseNonnegative,phaseBound⟩ := startupActualPhaseFirst_graph_bound parameters scale order grade allocated direction 1 zero_lt_one
  obtain ⟨mixedConstant,mixedNonnegative,mixedBound⟩ := startupMixedOrder_fullAdjustable (grade+1) grade (by omega) epsilon positive
  refine ⟨phaseConstant+mixedConstant,add_nonneg phaseNonnegative mixedNonnegative,?_⟩
  intro core moment graph same represented
  have phase := phaseBound (originalSignedAxialCore parameters core 1 1 1) moment graph same represented
  have planar := (startupSignedAxial_planar_bound parameters core grade 1).trans (mixedBound 3 parameters core)
  have cell := mul_le_mul_of_nonneg_left (startupSignedAxial_cell_bound parameters core grade 1) phaseNonnegative
  nlinarith only [phase,planar,cell]

end Grad.CartesianStartup
