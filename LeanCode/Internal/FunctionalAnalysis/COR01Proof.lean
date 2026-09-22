import COR01DiskCell

namespace Grad.ClosedJets

theorem closedJetCarrier_and_ext : BlockGoal :=
  ⟨disk_topology_goal, closed_jet_goal, closed_jet_linear_goal,
    disk_cell_topology_goal, disk_cell_closed_jet_goal, disk_cell_linear_goal⟩

end Grad.ClosedJets
