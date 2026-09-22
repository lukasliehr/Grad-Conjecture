import AKDT16ActualPressureLeaves

noncomputable section
open Set
open scoped ContDiff

namespace Grad.PhysicalGeometry
open Grad.MainTarget

def torusDirectionCLM : Plane →L[ℝ] Vec :=
  LinearMap.toContinuousLinearMap
    { toFun := fun point => vector 0 (point 0) (point 1)
      map_add' := by
        intro first second
        ext coordinate
        fin_cases coordinate <;> simp [vector]
      map_smul' := by
        intro scalar point
        ext coordinate
        fin_cases coordinate <;> simp [vector] }

def torusCoordinateInsertion (radius : ℝ) (point : Plane) : Vec := vector radius (point 0) (point 1)

theorem torusCoordinateInsertion_smooth (radius : ℝ) : ContDiff ℝ ∞ (torusCoordinateInsertion radius) := by
  rw [contDiff_piLp]
  intro coordinate
  fin_cases coordinate <;> simp [torusCoordinateInsertion, vector] <;> fun_prop

theorem torusCoordinateInsertion_hasFDerivAt (radius : ℝ) (point : Plane) :
    HasFDerivAt (torusCoordinateInsertion radius) torusDirectionCLM point := by
  have identity : torusCoordinateInsertion radius = fun argument : Plane => vector radius 0 0 + torusDirectionCLM argument := by
    funext argument
    ext coordinate
    fin_cases coordinate <;> simp [torusCoordinateInsertion, torusDirectionCLM, LinearMap.toContinuousLinearMap, vector]
  rw [identity]
  exact torusDirectionCLM.hasFDerivAt.const_add (vector radius 0 0)

theorem torusDirectionCLM_injective : Function.Injective torusDirectionCLM := by
  intro first second equal
  ext coordinate
  fin_cases coordinate
  · exact congrArg (fun point : Vec => point 1) equal
  · exact congrArg (fun point : Vec => point 2) equal

theorem torusCoordinateInsertion_mem (radius : Ioc (0 : ℝ) 1) (point : Plane) :
    torusCoordinateInsertion radius.val point ∈ foliationCylinder := radius.property

end Grad.PhysicalGeometry
