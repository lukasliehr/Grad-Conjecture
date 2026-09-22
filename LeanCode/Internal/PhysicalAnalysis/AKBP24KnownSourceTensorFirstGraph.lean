import AKBP21CoordinateDivDivAssembly
import AKBP18KnownFirstGraphRemainder

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets
open Grad.Constraints Grad.Constraints.Gauges Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.RadialLedger

def startupERSourceFluxFirst (source : StartupFirst 2) : StartupFirst 2 :=
  (1/2 : ℂ) • originalValueFirstGraph quarterValueMap (originalAverageFirstGraph source)

theorem startupERSourceFluxFirst_base (source : StartupFirst 2) :
    base 2 1 openUnitDisk (fun _ => 0) (startupERSourceFluxFirst source) =
      startupERSourceFlux (base 2 1 openUnitDisk (fun _ => 0) source) := by
  rw [startupERSourceFluxFirst,map_smul,originalValueFirstGraph_compatible,
    originalAverageFirstGraph_compatible]
  rfl

def startupThreeRowTensorFirst (force : StartupFirst 2) (scalar : StartupFirst 1) (flux : StartupFirst 2)
    (outer inside : Fin 2) : StartupFirst 3 :=
  ∑ row : Fin 3, startupPrincipalFixedFirst outer inside row
    (![originalValueFirstGraph planarInclusionMap force,originalValueFirstGraph toroidalInclusionMap scalar,
      originalValueFirstGraph planarInclusionMap flux] row)

theorem startupThreeRowTensorFirst_base (force : StartupFirst 2) (scalar : StartupFirst 1) (flux : StartupFirst 2)
    (outer inside : Fin 2) :
    base 3 1 openUnitDisk (fun _ => 0) (startupThreeRowTensorFirst force scalar flux outer inside) =
      startupThreeRowTensor (base 2 1 openUnitDisk (fun _ => 0) force)
        (base 1 1 openUnitDisk (fun _ => 0) scalar) (base 2 1 openUnitDisk (fun _ => 0) flux) outer inside := by
  simp only [startupThreeRowTensorFirst,startupThreeRowTensor,map_sum]
  apply Finset.sum_congr rfl
  intro row _
  rw [startupPrincipalFixed_compatible]
  congr 1
  fin_cases row
  · exact originalValueFirstGraph_compatible planarInclusionMap force
  · exact originalValueFirstGraph_compatible toroidalInclusionMap scalar
  · exact originalValueFirstGraph_compatible planarInclusionMap flux

def startupKnownTensorFirst (force : StartupFirst 2) (third : StartupFirst 1)
    (outer inside : Fin 2) : StartupFirst 3 :=
  startupThreeRowTensorFirst (-force) third (startupERSourceFluxFirst force) outer inside

/-- Only first regularity of the genuine known source is needed for its
second-order ER tensor; angular inverse covariance preserves that graph. -/
theorem startupKnownTensorFirst_base (force : StartupFirst 2) (third : StartupFirst 1)
    (outer inside : Fin 2) :
    base 3 1 openUnitDisk (fun _ => 0) (startupKnownTensorFirst force third outer inside) =
      startupThreeRowTensor (-(base 2 1 openUnitDisk (fun _ => 0) force))
        (base 1 1 openUnitDisk (fun _ => 0) third)
        (startupERSourceFlux (base 2 1 openUnitDisk (fun _ => 0) force)) outer inside := by
  rw [startupKnownTensorFirst,startupThreeRowTensorFirst_base,map_neg,startupERSourceFluxFirst_base]

end Grad.CartesianStartup
