import AKAQ7CompletionFourierBound
import AKAQ9OriginalFlatTraceFidelity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open scoped BigOperators ENNReal Topology
namespace Grad.OriginalFlatAxisDecay
open Grad.FourierGrade Grad.CartesianState Grad.ClosedJets Grad.COR12Extension
open Grad.COR13Completion Grad.SourceCollarDivision

variable {dimension : ℕ}

/-- Original A4 only: the exact conjugated Taylor series follows from the
accepted completion and the original zero jets. -/
theorem originalFlat_taylor_hasSum (parameters : PhaseParameters)
    (field : AGrade parameters dimension 4) (flat : OriginalFirstJetFlat parameters field)
    (cell : ℤ) (point : ClosedDisk) :
    HasSum (fun mode : SpatialMode => taylorSymbol point.val mode •
      coefficient 4 (completedExtension parameters field) (fibreMode (cell,mode)))
      (completedWeightedCell parameters (by omega) cell field point) := by
  have law := continuous_fibre_hasSum cell (taylorSymbol point.val)
    ((weightedTaylorAt parameters cell point).comp (completedRetraction parameters))
    (fun mode source value => completedRetraction_single_taylor parameters mode source cell value point)
    (completedExtension parameters field)
  simpa only [ContinuousLinearMap.comp_apply,completedRetraction_extension_apply,
    weightedTaylorAt_flat parameters field flat] using law

theorem originalFlat_rotation_hasSum (parameters : PhaseParameters)
    (field : AGrade parameters dimension 4) (flat : OriginalFirstJetFlat parameters field)
    (cell : ℤ) (point : ClosedDisk) :
    HasSum (fun mode : SpatialMode => rotationRemainderSymbol point.val mode •
      coefficient 4 (completedExtension parameters field) (fibreMode (cell,mode)))
      (cartesianWeight parameters cell point.val • originalRotationAt parameters cell point field) := by
  have law := continuous_fibre_hasSum cell (rotationRemainderSymbol point.val)
    ((weightedRotationRemainderAt parameters cell point).comp (completedRetraction parameters))
    (fun mode source value => completedRetraction_single_rotationRemainder parameters mode source cell value point)
    (completedExtension parameters field)
  simpa only [ContinuousLinearMap.comp_apply,completedRetraction_extension_apply,
    weightedRotationRemainderAt_flat parameters field flat] using law

theorem originalFlat_value_finiteEnergy (parameters : PhaseParameters)
    (field : AGrade parameters dimension 4) (flat : OriginalFirstJetFlat parameters field)
    (point : ClosedDisk) (cells : Finset ℤ) :
    ∑ cell ∈ cells, cellFrequency cell^2 * ‖completedWeightedCell parameters (by omega) cell field point‖^2 ≤
      9 * Real.pi^3 * ‖point.val‖^3 * spatialDecayConstant * ‖completedExtension parameters field‖^2 :=
  completedFourier_symbol_bound _ _ (by positivity) (taylorSymbol_bound point.val)
    (completedExtension parameters field) _
    (fun cell => originalFlat_taylor_hasSum parameters field flat cell point) cells

theorem originalFlat_rotation_finiteEnergy (parameters : PhaseParameters)
    (field : AGrade parameters dimension 4) (flat : OriginalFirstJetFlat parameters field)
    (point : ClosedDisk) (cells : Finset ℤ) :
    ∑ cell ∈ cells, cellFrequency cell^2 *
      ‖cartesianWeight parameters cell point.val • originalRotationAt parameters cell point field‖^2 ≤
      4 * Real.pi^3 * ‖point.val‖^3 * spatialDecayConstant * ‖completedExtension parameters field‖^2 :=
  completedFourier_symbol_bound _ _ (by positivity) (rotationRemainderSymbol_bound point.val)
    (completedExtension parameters field) _
    (fun cell => originalFlat_rotation_hasSum parameters field flat cell point) cells

theorem originalFlat_value_memlp (parameters : PhaseParameters)
    (field : AGrade parameters dimension 4) (flat : OriginalFirstJetFlat parameters field) (point : ClosedDisk) :
    Memℓp (fun cell => (cellFrequency cell : ℂ) • completedWeightedCell parameters (by omega) cell field point) 2 :=
  completedFourier_symbol_memlp _ _ (by positivity) (taylorSymbol_bound point.val)
    (completedExtension parameters field) _
    (fun cell => originalFlat_taylor_hasSum parameters field flat cell point)

theorem originalFlat_rotation_memlp (parameters : PhaseParameters)
    (field : AGrade parameters dimension 4) (flat : OriginalFirstJetFlat parameters field) (point : ClosedDisk) :
    Memℓp (fun cell => (cellFrequency cell : ℂ) •
      (cartesianWeight parameters cell point.val • originalRotationAt parameters cell point field)) 2 :=
  completedFourier_symbol_memlp _ _ (by positivity) (rotationRemainderSymbol_bound point.val)
    (completedExtension parameters field) _
    (fun cell => originalFlat_rotation_hasSum parameters field flat cell point)

end Grad.OriginalFlatAxisDecay
