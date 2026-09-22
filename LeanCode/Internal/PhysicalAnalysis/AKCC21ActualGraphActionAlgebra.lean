import AKCC20ActualFixedAllGradeGraphs

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.WeightedJets

namespace StartupPreservesGraph

theorem identity (dimension : ℕ) : StartupPreservesGraph (ContinuousLinearMap.id ℂ (StartupL2 dimension)) := by
  intro order weight field
  exact ⟨field, rfl⟩

theorem add {input output : ℕ} {first second : StartupL2 input →L[ℂ] StartupL2 output}
    (firstGraph : StartupPreservesGraph first) (secondGraph : StartupPreservesGraph second) :
    StartupPreservesGraph (first + second) := by
  intro order weight field
  obtain ⟨firstImage, firstSame⟩ := firstGraph order weight field
  obtain ⟨secondImage, secondSame⟩ := secondGraph order weight field
  refine ⟨firstImage + secondImage, ?_⟩
  rw [map_add, firstSame, secondSame]
  rfl

theorem sub {input output : ℕ} {first second : StartupL2 input →L[ℂ] StartupL2 output}
    (firstGraph : StartupPreservesGraph first) (secondGraph : StartupPreservesGraph second) :
    StartupPreservesGraph (first - second) := by
  intro order weight field
  obtain ⟨firstImage, firstSame⟩ := firstGraph order weight field
  obtain ⟨secondImage, secondSame⟩ := secondGraph order weight field
  refine ⟨firstImage - secondImage, ?_⟩
  rw [map_sub, firstSame, secondSame]
  rfl

theorem smul {input output : ℕ} {kernel : StartupL2 input →L[ℂ] StartupL2 output}
    (graph : StartupPreservesGraph kernel) (scalar : ℂ) : StartupPreservesGraph (scalar • kernel) := by
  intro order weight field
  obtain ⟨image, same⟩ := graph order weight field
  refine ⟨scalar • image, ?_⟩
  rw [map_smul, same]
  rfl

theorem comp {input middle output : ℕ} {outer : StartupL2 middle →L[ℂ] StartupL2 output}
    {inner : StartupL2 input →L[ℂ] StartupL2 middle}
    (outerGraph : StartupPreservesGraph outer) (innerGraph : StartupPreservesGraph inner) :
    StartupPreservesGraph (outer.comp inner) := by
  intro order weight field
  obtain ⟨middleImage, middleSame⟩ := innerGraph order weight field
  obtain ⟨image, same⟩ := outerGraph order weight middleImage
  refine ⟨image, ?_⟩
  rw [same, middleSame]
  rfl

end StartupPreservesGraph
end Grad.CartesianStartup
