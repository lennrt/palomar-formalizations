import ZombieDamage.Data
import ZombieDamage.Gadgets

/-! Generated mathematical-to-certificate bridges. See the generator
and the independent graph definitions in Gadgets.lean. -/
namespace ZombieDamage.RegistryProofs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem k23_00 : Gadget.RouteExit .k23 (2 : Fin 8) (3 : Fin 8) := by
  have heq : Data.K2_3.task_00.task = Gadget.exitTask .k23 (3 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.K2_3.task_00.wins_bounded

theorem k23_01 : Gadget.RouteExit .k23 (2 : Fin 8) (4 : Fin 8) := by
  have heq : Data.K2_3.task_01.task = Gadget.exitTask .k23 (4 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.K2_3.task_01.wins_bounded

theorem k23_02 : Gadget.RouteTarget .k23 (2 : Fin 8) (0 : Fin 8) := by
  have heq : Data.K2_3.task_02.task = Gadget.targetTask .k23 (2 : Fin 8) (0 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.K2_3.task_02.wins_bounded

theorem k23_03 : Gadget.RouteTarget .k23 (2 : Fin 8) (1 : Fin 8) := by
  have heq : Data.K2_3.task_03.task = Gadget.targetTask .k23 (2 : Fin 8) (1 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.K2_3.task_03.wins_bounded

theorem k23_04 : Gadget.RouteTarget .k23 (2 : Fin 8) (2 : Fin 8) := by
  have heq : Data.K2_3.task_04.task = Gadget.targetTask .k23 (2 : Fin 8) (2 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.K2_3.task_04.wins_bounded

theorem k23_05 : Gadget.RouteTarget .k23 (2 : Fin 8) (3 : Fin 8) := by
  have heq : Data.K2_3.task_05.task = Gadget.targetTask .k23 (2 : Fin 8) (3 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.K2_3.task_05.wins_bounded

theorem k23_06 : Gadget.RouteTarget .k23 (2 : Fin 8) (4 : Fin 8) := by
  have heq : Data.K2_3.task_06.task = Gadget.targetTask .k23 (2 : Fin 8) (4 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.K2_3.task_06.wins_bounded

theorem k23_07 : Gadget.RouteExit .k23 (3 : Fin 8) (2 : Fin 8) := by
  have heq : Data.K2_3.task_07.task = Gadget.exitTask .k23 (2 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.K2_3.task_07.wins_bounded

theorem k23_08 : Gadget.RouteExit .k23 (3 : Fin 8) (4 : Fin 8) := by
  have heq : Data.K2_3.task_08.task = Gadget.exitTask .k23 (4 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.K2_3.task_08.wins_bounded

theorem k23_09 : Gadget.RouteTarget .k23 (3 : Fin 8) (0 : Fin 8) := by
  have heq : Data.K2_3.task_09.task = Gadget.targetTask .k23 (3 : Fin 8) (0 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.K2_3.task_09.wins_bounded

theorem k23_10 : Gadget.RouteTarget .k23 (3 : Fin 8) (1 : Fin 8) := by
  have heq : Data.K2_3.task_10.task = Gadget.targetTask .k23 (3 : Fin 8) (1 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.K2_3.task_10.wins_bounded

theorem k23_11 : Gadget.RouteTarget .k23 (3 : Fin 8) (2 : Fin 8) := by
  have heq : Data.K2_3.task_11.task = Gadget.targetTask .k23 (3 : Fin 8) (2 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.K2_3.task_11.wins_bounded

theorem k23_12 : Gadget.RouteTarget .k23 (3 : Fin 8) (3 : Fin 8) := by
  have heq : Data.K2_3.task_12.task = Gadget.targetTask .k23 (3 : Fin 8) (3 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.K2_3.task_12.wins_bounded

theorem k23_13 : Gadget.RouteTarget .k23 (3 : Fin 8) (4 : Fin 8) := by
  have heq : Data.K2_3.task_13.task = Gadget.targetTask .k23 (3 : Fin 8) (4 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.K2_3.task_13.wins_bounded

theorem k23_14 : Gadget.RouteExit .k23 (4 : Fin 8) (2 : Fin 8) := by
  have heq : Data.K2_3.task_14.task = Gadget.exitTask .k23 (2 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.K2_3.task_14.wins_bounded

theorem k23_15 : Gadget.RouteExit .k23 (4 : Fin 8) (3 : Fin 8) := by
  have heq : Data.K2_3.task_15.task = Gadget.exitTask .k23 (3 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.K2_3.task_15.wins_bounded

theorem k23_16 : Gadget.RouteTarget .k23 (4 : Fin 8) (0 : Fin 8) := by
  have heq : Data.K2_3.task_16.task = Gadget.targetTask .k23 (4 : Fin 8) (0 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.K2_3.task_16.wins_bounded

theorem k23_17 : Gadget.RouteTarget .k23 (4 : Fin 8) (1 : Fin 8) := by
  have heq : Data.K2_3.task_17.task = Gadget.targetTask .k23 (4 : Fin 8) (1 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.K2_3.task_17.wins_bounded

theorem k23_18 : Gadget.RouteTarget .k23 (4 : Fin 8) (2 : Fin 8) := by
  have heq : Data.K2_3.task_18.task = Gadget.targetTask .k23 (4 : Fin 8) (2 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.K2_3.task_18.wins_bounded

theorem k23_19 : Gadget.RouteTarget .k23 (4 : Fin 8) (3 : Fin 8) := by
  have heq : Data.K2_3.task_19.task = Gadget.targetTask .k23 (4 : Fin 8) (3 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.K2_3.task_19.wins_bounded

theorem k23_20 : Gadget.RouteTarget .k23 (4 : Fin 8) (4 : Fin 8) := by
  have heq : Data.K2_3.task_20.task = Gadget.targetTask .k23 (4 : Fin 8) (4 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.K2_3.task_20.wins_bounded

theorem k33e_00 : Gadget.RouteExit .k33e (0 : Fin 8) (3 : Fin 8) := by
  have heq : Data.K3_3_minus_edge.task_00.task = Gadget.exitTask .k33e (3 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.K3_3_minus_edge.task_00.wins_bounded

theorem k33e_01 : Gadget.RouteTarget .k33e (0 : Fin 8) (0 : Fin 8) := by
  have heq : Data.K3_3_minus_edge.task_01.task = Gadget.targetTask .k33e (0 : Fin 8) (0 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.K3_3_minus_edge.task_01.wins_bounded

theorem k33e_02 : Gadget.RouteTarget .k33e (0 : Fin 8) (1 : Fin 8) := by
  have heq : Data.K3_3_minus_edge.task_02.task = Gadget.targetTask .k33e (0 : Fin 8) (1 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.K3_3_minus_edge.task_02.wins_bounded

theorem k33e_03 : Gadget.RouteTarget .k33e (0 : Fin 8) (2 : Fin 8) := by
  have heq : Data.K3_3_minus_edge.task_03.task = Gadget.targetTask .k33e (0 : Fin 8) (2 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.K3_3_minus_edge.task_03.wins_bounded

theorem k33e_04 : Gadget.RouteTarget .k33e (0 : Fin 8) (3 : Fin 8) := by
  have heq : Data.K3_3_minus_edge.task_04.task = Gadget.targetTask .k33e (0 : Fin 8) (3 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.K3_3_minus_edge.task_04.wins_bounded

theorem k33e_05 : Gadget.RouteTarget .k33e (0 : Fin 8) (4 : Fin 8) := by
  have heq : Data.K3_3_minus_edge.task_05.task = Gadget.targetTask .k33e (0 : Fin 8) (4 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.K3_3_minus_edge.task_05.wins_bounded

theorem k33e_06 : Gadget.RouteTarget .k33e (0 : Fin 8) (5 : Fin 8) := by
  have heq : Data.K3_3_minus_edge.task_06.task = Gadget.targetTask .k33e (0 : Fin 8) (5 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.K3_3_minus_edge.task_06.wins_bounded

theorem k33e_07 : Gadget.RouteExit .k33e (3 : Fin 8) (0 : Fin 8) := by
  have heq : Data.K3_3_minus_edge.task_07.task = Gadget.exitTask .k33e (0 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.K3_3_minus_edge.task_07.wins_bounded

theorem k33e_08 : Gadget.RouteTarget .k33e (3 : Fin 8) (0 : Fin 8) := by
  have heq : Data.K3_3_minus_edge.task_08.task = Gadget.targetTask .k33e (3 : Fin 8) (0 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.K3_3_minus_edge.task_08.wins_bounded

theorem k33e_09 : Gadget.RouteTarget .k33e (3 : Fin 8) (1 : Fin 8) := by
  have heq : Data.K3_3_minus_edge.task_09.task = Gadget.targetTask .k33e (3 : Fin 8) (1 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.K3_3_minus_edge.task_09.wins_bounded

theorem k33e_10 : Gadget.RouteTarget .k33e (3 : Fin 8) (2 : Fin 8) := by
  have heq : Data.K3_3_minus_edge.task_10.task = Gadget.targetTask .k33e (3 : Fin 8) (2 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.K3_3_minus_edge.task_10.wins_bounded

theorem k33e_11 : Gadget.RouteTarget .k33e (3 : Fin 8) (3 : Fin 8) := by
  have heq : Data.K3_3_minus_edge.task_11.task = Gadget.targetTask .k33e (3 : Fin 8) (3 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.K3_3_minus_edge.task_11.wins_bounded

theorem k33e_12 : Gadget.RouteTarget .k33e (3 : Fin 8) (4 : Fin 8) := by
  have heq : Data.K3_3_minus_edge.task_12.task = Gadget.targetTask .k33e (3 : Fin 8) (4 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.K3_3_minus_edge.task_12.wins_bounded

theorem k33e_13 : Gadget.RouteTarget .k33e (3 : Fin 8) (5 : Fin 8) := by
  have heq : Data.K3_3_minus_edge.task_13.task = Gadget.targetTask .k33e (3 : Fin 8) (5 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.K3_3_minus_edge.task_13.wins_bounded

theorem prism3e_00 : Gadget.RouteExit .prism3e (0 : Fin 8) (1 : Fin 8) := by
  have heq : Data.triangular_prism_minus_triangle_edge.task_00.task = Gadget.exitTask .prism3e (1 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.triangular_prism_minus_triangle_edge.task_00.wins_bounded

theorem prism3e_01 : Gadget.RouteTarget .prism3e (0 : Fin 8) (0 : Fin 8) := by
  have heq : Data.triangular_prism_minus_triangle_edge.task_01.task = Gadget.targetTask .prism3e (0 : Fin 8) (0 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.triangular_prism_minus_triangle_edge.task_01.wins_bounded

theorem prism3e_02 : Gadget.RouteTarget .prism3e (0 : Fin 8) (1 : Fin 8) := by
  have heq : Data.triangular_prism_minus_triangle_edge.task_02.task = Gadget.targetTask .prism3e (0 : Fin 8) (1 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.triangular_prism_minus_triangle_edge.task_02.wins_bounded

theorem prism3e_03 : Gadget.RouteTarget .prism3e (0 : Fin 8) (2 : Fin 8) := by
  have heq : Data.triangular_prism_minus_triangle_edge.task_03.task = Gadget.targetTask .prism3e (0 : Fin 8) (2 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.triangular_prism_minus_triangle_edge.task_03.wins_bounded

theorem prism3e_04 : Gadget.RouteTarget .prism3e (0 : Fin 8) (3 : Fin 8) := by
  have heq : Data.triangular_prism_minus_triangle_edge.task_04.task = Gadget.targetTask .prism3e (0 : Fin 8) (3 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.triangular_prism_minus_triangle_edge.task_04.wins_bounded

theorem prism3e_05 : Gadget.RouteTarget .prism3e (0 : Fin 8) (4 : Fin 8) := by
  have heq : Data.triangular_prism_minus_triangle_edge.task_05.task = Gadget.targetTask .prism3e (0 : Fin 8) (4 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.triangular_prism_minus_triangle_edge.task_05.wins_bounded

theorem prism3e_06 : Gadget.RouteTarget .prism3e (0 : Fin 8) (5 : Fin 8) := by
  have heq : Data.triangular_prism_minus_triangle_edge.task_06.task = Gadget.targetTask .prism3e (0 : Fin 8) (5 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.triangular_prism_minus_triangle_edge.task_06.wins_bounded

theorem prism3e_07 : Gadget.RouteExit .prism3e (1 : Fin 8) (0 : Fin 8) := by
  have heq : Data.triangular_prism_minus_triangle_edge.task_07.task = Gadget.exitTask .prism3e (0 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.triangular_prism_minus_triangle_edge.task_07.wins_bounded

theorem prism3e_08 : Gadget.RouteTarget .prism3e (1 : Fin 8) (0 : Fin 8) := by
  have heq : Data.triangular_prism_minus_triangle_edge.task_08.task = Gadget.targetTask .prism3e (1 : Fin 8) (0 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.triangular_prism_minus_triangle_edge.task_08.wins_bounded

theorem prism3e_09 : Gadget.RouteTarget .prism3e (1 : Fin 8) (1 : Fin 8) := by
  have heq : Data.triangular_prism_minus_triangle_edge.task_09.task = Gadget.targetTask .prism3e (1 : Fin 8) (1 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.triangular_prism_minus_triangle_edge.task_09.wins_bounded

theorem prism3e_10 : Gadget.RouteTarget .prism3e (1 : Fin 8) (2 : Fin 8) := by
  have heq : Data.triangular_prism_minus_triangle_edge.task_10.task = Gadget.targetTask .prism3e (1 : Fin 8) (2 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.triangular_prism_minus_triangle_edge.task_10.wins_bounded

theorem prism3e_11 : Gadget.RouteTarget .prism3e (1 : Fin 8) (3 : Fin 8) := by
  have heq : Data.triangular_prism_minus_triangle_edge.task_11.task = Gadget.targetTask .prism3e (1 : Fin 8) (3 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.triangular_prism_minus_triangle_edge.task_11.wins_bounded

theorem prism3e_12 : Gadget.RouteTarget .prism3e (1 : Fin 8) (4 : Fin 8) := by
  have heq : Data.triangular_prism_minus_triangle_edge.task_12.task = Gadget.targetTask .prism3e (1 : Fin 8) (4 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.triangular_prism_minus_triangle_edge.task_12.wins_bounded

theorem prism3e_13 : Gadget.RouteTarget .prism3e (1 : Fin 8) (5 : Fin 8) := by
  have heq : Data.triangular_prism_minus_triangle_edge.task_13.task = Gadget.targetTask .prism3e (1 : Fin 8) (5 : Fin 8) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.triangular_prism_minus_triangle_edge.task_13.wins_bounded

theorem cubeV_00 : Gadget.RouteExit .cubeV (3 : Fin 10) (5 : Fin 10) := by
  have heq : Data.cube_minus_vertex.task_00.task = Gadget.exitTask .cubeV (5 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_vertex.task_00.wins_bounded

theorem cubeV_01 : Gadget.RouteExit .cubeV (3 : Fin 10) (6 : Fin 10) := by
  have heq : Data.cube_minus_vertex.task_01.task = Gadget.exitTask .cubeV (6 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_vertex.task_01.wins_bounded

theorem cubeV_02 : Gadget.RouteTarget .cubeV (3 : Fin 10) (0 : Fin 10) := by
  have heq : Data.cube_minus_vertex.task_02.task = Gadget.targetTask .cubeV (3 : Fin 10) (0 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_vertex.task_02.wins_bounded

theorem cubeV_03 : Gadget.RouteTarget .cubeV (3 : Fin 10) (1 : Fin 10) := by
  have heq : Data.cube_minus_vertex.task_03.task = Gadget.targetTask .cubeV (3 : Fin 10) (1 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_vertex.task_03.wins_bounded

theorem cubeV_04 : Gadget.RouteTarget .cubeV (3 : Fin 10) (2 : Fin 10) := by
  have heq : Data.cube_minus_vertex.task_04.task = Gadget.targetTask .cubeV (3 : Fin 10) (2 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_vertex.task_04.wins_bounded

theorem cubeV_05 : Gadget.RouteTarget .cubeV (3 : Fin 10) (3 : Fin 10) := by
  have heq : Data.cube_minus_vertex.task_05.task = Gadget.targetTask .cubeV (3 : Fin 10) (3 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_vertex.task_05.wins_bounded

theorem cubeV_06 : Gadget.RouteTarget .cubeV (3 : Fin 10) (4 : Fin 10) := by
  have heq : Data.cube_minus_vertex.task_06.task = Gadget.targetTask .cubeV (3 : Fin 10) (4 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_vertex.task_06.wins_bounded

theorem cubeV_07 : Gadget.RouteTarget .cubeV (3 : Fin 10) (5 : Fin 10) := by
  have heq : Data.cube_minus_vertex.task_07.task = Gadget.targetTask .cubeV (3 : Fin 10) (5 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_vertex.task_07.wins_bounded

theorem cubeV_08 : Gadget.RouteTarget .cubeV (3 : Fin 10) (6 : Fin 10) := by
  have heq : Data.cube_minus_vertex.task_08.task = Gadget.targetTask .cubeV (3 : Fin 10) (6 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_vertex.task_08.wins_bounded

theorem cubeV_09 : Gadget.RouteExit .cubeV (5 : Fin 10) (3 : Fin 10) := by
  have heq : Data.cube_minus_vertex.task_09.task = Gadget.exitTask .cubeV (3 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_vertex.task_09.wins_bounded

theorem cubeV_10 : Gadget.RouteExit .cubeV (5 : Fin 10) (6 : Fin 10) := by
  have heq : Data.cube_minus_vertex.task_10.task = Gadget.exitTask .cubeV (6 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_vertex.task_10.wins_bounded

theorem cubeV_11 : Gadget.RouteTarget .cubeV (5 : Fin 10) (0 : Fin 10) := by
  have heq : Data.cube_minus_vertex.task_11.task = Gadget.targetTask .cubeV (5 : Fin 10) (0 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_vertex.task_11.wins_bounded

theorem cubeV_12 : Gadget.RouteTarget .cubeV (5 : Fin 10) (1 : Fin 10) := by
  have heq : Data.cube_minus_vertex.task_12.task = Gadget.targetTask .cubeV (5 : Fin 10) (1 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_vertex.task_12.wins_bounded

theorem cubeV_13 : Gadget.RouteTarget .cubeV (5 : Fin 10) (2 : Fin 10) := by
  have heq : Data.cube_minus_vertex.task_13.task = Gadget.targetTask .cubeV (5 : Fin 10) (2 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_vertex.task_13.wins_bounded

theorem cubeV_14 : Gadget.RouteTarget .cubeV (5 : Fin 10) (3 : Fin 10) := by
  have heq : Data.cube_minus_vertex.task_14.task = Gadget.targetTask .cubeV (5 : Fin 10) (3 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_vertex.task_14.wins_bounded

theorem cubeV_15 : Gadget.RouteTarget .cubeV (5 : Fin 10) (4 : Fin 10) := by
  have heq : Data.cube_minus_vertex.task_15.task = Gadget.targetTask .cubeV (5 : Fin 10) (4 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_vertex.task_15.wins_bounded

theorem cubeV_16 : Gadget.RouteTarget .cubeV (5 : Fin 10) (5 : Fin 10) := by
  have heq : Data.cube_minus_vertex.task_16.task = Gadget.targetTask .cubeV (5 : Fin 10) (5 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_vertex.task_16.wins_bounded

theorem cubeV_17 : Gadget.RouteTarget .cubeV (5 : Fin 10) (6 : Fin 10) := by
  have heq : Data.cube_minus_vertex.task_17.task = Gadget.targetTask .cubeV (5 : Fin 10) (6 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_vertex.task_17.wins_bounded

theorem cubeV_18 : Gadget.RouteExit .cubeV (6 : Fin 10) (3 : Fin 10) := by
  have heq : Data.cube_minus_vertex.task_18.task = Gadget.exitTask .cubeV (3 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_vertex.task_18.wins_bounded

theorem cubeV_19 : Gadget.RouteExit .cubeV (6 : Fin 10) (5 : Fin 10) := by
  have heq : Data.cube_minus_vertex.task_19.task = Gadget.exitTask .cubeV (5 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_vertex.task_19.wins_bounded

theorem cubeV_20 : Gadget.RouteTarget .cubeV (6 : Fin 10) (0 : Fin 10) := by
  have heq : Data.cube_minus_vertex.task_20.task = Gadget.targetTask .cubeV (6 : Fin 10) (0 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_vertex.task_20.wins_bounded

theorem cubeV_21 : Gadget.RouteTarget .cubeV (6 : Fin 10) (1 : Fin 10) := by
  have heq : Data.cube_minus_vertex.task_21.task = Gadget.targetTask .cubeV (6 : Fin 10) (1 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_vertex.task_21.wins_bounded

theorem cubeV_22 : Gadget.RouteTarget .cubeV (6 : Fin 10) (2 : Fin 10) := by
  have heq : Data.cube_minus_vertex.task_22.task = Gadget.targetTask .cubeV (6 : Fin 10) (2 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_vertex.task_22.wins_bounded

theorem cubeV_23 : Gadget.RouteTarget .cubeV (6 : Fin 10) (3 : Fin 10) := by
  have heq : Data.cube_minus_vertex.task_23.task = Gadget.targetTask .cubeV (6 : Fin 10) (3 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_vertex.task_23.wins_bounded

theorem cubeV_24 : Gadget.RouteTarget .cubeV (6 : Fin 10) (4 : Fin 10) := by
  have heq : Data.cube_minus_vertex.task_24.task = Gadget.targetTask .cubeV (6 : Fin 10) (4 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_vertex.task_24.wins_bounded

theorem cubeV_25 : Gadget.RouteTarget .cubeV (6 : Fin 10) (5 : Fin 10) := by
  have heq : Data.cube_minus_vertex.task_25.task = Gadget.targetTask .cubeV (6 : Fin 10) (5 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_vertex.task_25.wins_bounded

theorem cubeV_26 : Gadget.RouteTarget .cubeV (6 : Fin 10) (6 : Fin 10) := by
  have heq : Data.cube_minus_vertex.task_26.task = Gadget.targetTask .cubeV (6 : Fin 10) (6 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_vertex.task_26.wins_bounded

theorem cubeE_00 : Gadget.RouteExit .cubeE (0 : Fin 10) (1 : Fin 10) := by
  have heq : Data.cube_minus_edge.task_00.task = Gadget.exitTask .cubeE (1 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_edge.task_00.wins_bounded

theorem cubeE_01 : Gadget.RouteTarget .cubeE (0 : Fin 10) (0 : Fin 10) := by
  have heq : Data.cube_minus_edge.task_01.task = Gadget.targetTask .cubeE (0 : Fin 10) (0 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_edge.task_01.wins_bounded

theorem cubeE_02 : Gadget.RouteTarget .cubeE (0 : Fin 10) (1 : Fin 10) := by
  have heq : Data.cube_minus_edge.task_02.task = Gadget.targetTask .cubeE (0 : Fin 10) (1 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_edge.task_02.wins_bounded

theorem cubeE_03 : Gadget.RouteTarget .cubeE (0 : Fin 10) (2 : Fin 10) := by
  have heq : Data.cube_minus_edge.task_03.task = Gadget.targetTask .cubeE (0 : Fin 10) (2 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_edge.task_03.wins_bounded

theorem cubeE_04 : Gadget.RouteTarget .cubeE (0 : Fin 10) (3 : Fin 10) := by
  have heq : Data.cube_minus_edge.task_04.task = Gadget.targetTask .cubeE (0 : Fin 10) (3 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_edge.task_04.wins_bounded

theorem cubeE_05 : Gadget.RouteTarget .cubeE (0 : Fin 10) (4 : Fin 10) := by
  have heq : Data.cube_minus_edge.task_05.task = Gadget.targetTask .cubeE (0 : Fin 10) (4 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_edge.task_05.wins_bounded

theorem cubeE_06 : Gadget.RouteTarget .cubeE (0 : Fin 10) (5 : Fin 10) := by
  have heq : Data.cube_minus_edge.task_06.task = Gadget.targetTask .cubeE (0 : Fin 10) (5 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_edge.task_06.wins_bounded

theorem cubeE_07 : Gadget.RouteTarget .cubeE (0 : Fin 10) (6 : Fin 10) := by
  have heq : Data.cube_minus_edge.task_07.task = Gadget.targetTask .cubeE (0 : Fin 10) (6 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_edge.task_07.wins_bounded

theorem cubeE_08 : Gadget.RouteTarget .cubeE (0 : Fin 10) (7 : Fin 10) := by
  have heq : Data.cube_minus_edge.task_08.task = Gadget.targetTask .cubeE (0 : Fin 10) (7 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_edge.task_08.wins_bounded

theorem cubeE_09 : Gadget.RouteExit .cubeE (1 : Fin 10) (0 : Fin 10) := by
  have heq : Data.cube_minus_edge.task_09.task = Gadget.exitTask .cubeE (0 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_edge.task_09.wins_bounded

theorem cubeE_10 : Gadget.RouteTarget .cubeE (1 : Fin 10) (0 : Fin 10) := by
  have heq : Data.cube_minus_edge.task_10.task = Gadget.targetTask .cubeE (1 : Fin 10) (0 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_edge.task_10.wins_bounded

theorem cubeE_11 : Gadget.RouteTarget .cubeE (1 : Fin 10) (1 : Fin 10) := by
  have heq : Data.cube_minus_edge.task_11.task = Gadget.targetTask .cubeE (1 : Fin 10) (1 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_edge.task_11.wins_bounded

theorem cubeE_12 : Gadget.RouteTarget .cubeE (1 : Fin 10) (2 : Fin 10) := by
  have heq : Data.cube_minus_edge.task_12.task = Gadget.targetTask .cubeE (1 : Fin 10) (2 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_edge.task_12.wins_bounded

theorem cubeE_13 : Gadget.RouteTarget .cubeE (1 : Fin 10) (3 : Fin 10) := by
  have heq : Data.cube_minus_edge.task_13.task = Gadget.targetTask .cubeE (1 : Fin 10) (3 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_edge.task_13.wins_bounded

theorem cubeE_14 : Gadget.RouteTarget .cubeE (1 : Fin 10) (4 : Fin 10) := by
  have heq : Data.cube_minus_edge.task_14.task = Gadget.targetTask .cubeE (1 : Fin 10) (4 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_edge.task_14.wins_bounded

theorem cubeE_15 : Gadget.RouteTarget .cubeE (1 : Fin 10) (5 : Fin 10) := by
  have heq : Data.cube_minus_edge.task_15.task = Gadget.targetTask .cubeE (1 : Fin 10) (5 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_edge.task_15.wins_bounded

theorem cubeE_16 : Gadget.RouteTarget .cubeE (1 : Fin 10) (6 : Fin 10) := by
  have heq : Data.cube_minus_edge.task_16.task = Gadget.targetTask .cubeE (1 : Fin 10) (6 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_edge.task_16.wins_bounded

theorem cubeE_17 : Gadget.RouteTarget .cubeE (1 : Fin 10) (7 : Fin 10) := by
  have heq : Data.cube_minus_edge.task_17.task = Gadget.targetTask .cubeE (1 : Fin 10) (7 : Fin 10) := by
    apply Task.ext <;> decide
  exact Task.metric_within_transport _ _ heq _ _ _ Data.cube_minus_edge.task_17.wins_bounded

end ZombieDamage.RegistryProofs

namespace ZombieDamage.Verified

/-- The complete exceptional-component routing lemma. No arbitrary-order
cubic graph statement or ambient gluing is asserted by this theorem. -/
theorem finite_component_routing (g : Gadget) :
    (∀ p q : g.Vertex, g.port p = true → g.port q = true → p ≠ q →
      g.RouteExit p q) ∧
    (∀ p t : g.Vertex, g.port p = true → g.inside t = true →
      g.RouteTarget p t) := by
  cases g with
  | k23 =>
    constructor
    · intro p q hp hq hne
      have pp : p = 2 ∨ p = 3 ∨ p = 4 := by
        have h : ∀ v : Fin 8, Gadget.port .k23 v = true → v = 2 ∨ v = 3 ∨ v = 4 := by decide
        exact h p hp
      have qq : q = 2 ∨ q = 3 ∨ q = 4 := by
        have h : ∀ v : Fin 8, Gadget.port .k23 v = true → v = 2 ∨ v = 3 ∨ v = 4 := by decide
        exact h q hq
      rcases pp with rfl | rfl | rfl
      all_goals rcases qq with rfl | rfl | rfl
      all_goals first
        | exact False.elim (hne rfl)
        | exact RegistryProofs.k23_00
        | exact RegistryProofs.k23_01
        | exact RegistryProofs.k23_07
        | exact RegistryProofs.k23_08
        | exact RegistryProofs.k23_14
        | exact RegistryProofs.k23_15
    · intro p t hp ht
      have pp : p = 2 ∨ p = 3 ∨ p = 4 := by
        have h : ∀ v : Fin 8, Gadget.port .k23 v = true → v = 2 ∨ v = 3 ∨ v = 4 := by decide
        exact h p hp
      have tt : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by
        have h : ∀ v : Fin 8, Gadget.inside .k23 v = true → v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 := by decide
        exact h t ht
      rcases pp with rfl | rfl | rfl
      all_goals rcases tt with rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact RegistryProofs.k23_02
        | exact RegistryProofs.k23_03
        | exact RegistryProofs.k23_04
        | exact RegistryProofs.k23_05
        | exact RegistryProofs.k23_06
        | exact RegistryProofs.k23_09
        | exact RegistryProofs.k23_10
        | exact RegistryProofs.k23_11
        | exact RegistryProofs.k23_12
        | exact RegistryProofs.k23_13
        | exact RegistryProofs.k23_16
        | exact RegistryProofs.k23_17
        | exact RegistryProofs.k23_18
        | exact RegistryProofs.k23_19
        | exact RegistryProofs.k23_20
  | k33e =>
    constructor
    · intro p q hp hq hne
      have pp : p = 0 ∨ p = 3 := by
        have h : ∀ v : Fin 8, Gadget.port .k33e v = true → v = 0 ∨ v = 3 := by decide
        exact h p hp
      have qq : q = 0 ∨ q = 3 := by
        have h : ∀ v : Fin 8, Gadget.port .k33e v = true → v = 0 ∨ v = 3 := by decide
        exact h q hq
      rcases pp with rfl | rfl
      all_goals rcases qq with rfl | rfl
      all_goals first
        | exact False.elim (hne rfl)
        | exact RegistryProofs.k33e_00
        | exact RegistryProofs.k33e_07
    · intro p t hp ht
      have pp : p = 0 ∨ p = 3 := by
        have h : ∀ v : Fin 8, Gadget.port .k33e v = true → v = 0 ∨ v = 3 := by decide
        exact h p hp
      have tt : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 := by
        have h : ∀ v : Fin 8, Gadget.inside .k33e v = true → v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 := by decide
        exact h t ht
      rcases pp with rfl | rfl
      all_goals rcases tt with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact RegistryProofs.k33e_01
        | exact RegistryProofs.k33e_02
        | exact RegistryProofs.k33e_03
        | exact RegistryProofs.k33e_04
        | exact RegistryProofs.k33e_05
        | exact RegistryProofs.k33e_06
        | exact RegistryProofs.k33e_08
        | exact RegistryProofs.k33e_09
        | exact RegistryProofs.k33e_10
        | exact RegistryProofs.k33e_11
        | exact RegistryProofs.k33e_12
        | exact RegistryProofs.k33e_13
  | prism3e =>
    constructor
    · intro p q hp hq hne
      have pp : p = 0 ∨ p = 1 := by
        have h : ∀ v : Fin 8, Gadget.port .prism3e v = true → v = 0 ∨ v = 1 := by decide
        exact h p hp
      have qq : q = 0 ∨ q = 1 := by
        have h : ∀ v : Fin 8, Gadget.port .prism3e v = true → v = 0 ∨ v = 1 := by decide
        exact h q hq
      rcases pp with rfl | rfl
      all_goals rcases qq with rfl | rfl
      all_goals first
        | exact False.elim (hne rfl)
        | exact RegistryProofs.prism3e_00
        | exact RegistryProofs.prism3e_07
    · intro p t hp ht
      have pp : p = 0 ∨ p = 1 := by
        have h : ∀ v : Fin 8, Gadget.port .prism3e v = true → v = 0 ∨ v = 1 := by decide
        exact h p hp
      have tt : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 := by
        have h : ∀ v : Fin 8, Gadget.inside .prism3e v = true → v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 := by decide
        exact h t ht
      rcases pp with rfl | rfl
      all_goals rcases tt with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact RegistryProofs.prism3e_01
        | exact RegistryProofs.prism3e_02
        | exact RegistryProofs.prism3e_03
        | exact RegistryProofs.prism3e_04
        | exact RegistryProofs.prism3e_05
        | exact RegistryProofs.prism3e_06
        | exact RegistryProofs.prism3e_08
        | exact RegistryProofs.prism3e_09
        | exact RegistryProofs.prism3e_10
        | exact RegistryProofs.prism3e_11
        | exact RegistryProofs.prism3e_12
        | exact RegistryProofs.prism3e_13
  | cubeV =>
    constructor
    · intro p q hp hq hne
      have pp : p = 3 ∨ p = 5 ∨ p = 6 := by
        have h : ∀ v : Fin 10, Gadget.port .cubeV v = true → v = 3 ∨ v = 5 ∨ v = 6 := by decide
        exact h p hp
      have qq : q = 3 ∨ q = 5 ∨ q = 6 := by
        have h : ∀ v : Fin 10, Gadget.port .cubeV v = true → v = 3 ∨ v = 5 ∨ v = 6 := by decide
        exact h q hq
      rcases pp with rfl | rfl | rfl
      all_goals rcases qq with rfl | rfl | rfl
      all_goals first
        | exact False.elim (hne rfl)
        | exact RegistryProofs.cubeV_00
        | exact RegistryProofs.cubeV_01
        | exact RegistryProofs.cubeV_09
        | exact RegistryProofs.cubeV_10
        | exact RegistryProofs.cubeV_18
        | exact RegistryProofs.cubeV_19
    · intro p t hp ht
      have pp : p = 3 ∨ p = 5 ∨ p = 6 := by
        have h : ∀ v : Fin 10, Gadget.port .cubeV v = true → v = 3 ∨ v = 5 ∨ v = 6 := by decide
        exact h p hp
      have tt : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 := by
        have h : ∀ v : Fin 10, Gadget.inside .cubeV v = true → v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 := by decide
        exact h t ht
      rcases pp with rfl | rfl | rfl
      all_goals rcases tt with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact RegistryProofs.cubeV_02
        | exact RegistryProofs.cubeV_03
        | exact RegistryProofs.cubeV_04
        | exact RegistryProofs.cubeV_05
        | exact RegistryProofs.cubeV_06
        | exact RegistryProofs.cubeV_07
        | exact RegistryProofs.cubeV_08
        | exact RegistryProofs.cubeV_11
        | exact RegistryProofs.cubeV_12
        | exact RegistryProofs.cubeV_13
        | exact RegistryProofs.cubeV_14
        | exact RegistryProofs.cubeV_15
        | exact RegistryProofs.cubeV_16
        | exact RegistryProofs.cubeV_17
        | exact RegistryProofs.cubeV_20
        | exact RegistryProofs.cubeV_21
        | exact RegistryProofs.cubeV_22
        | exact RegistryProofs.cubeV_23
        | exact RegistryProofs.cubeV_24
        | exact RegistryProofs.cubeV_25
        | exact RegistryProofs.cubeV_26
  | cubeE =>
    constructor
    · intro p q hp hq hne
      have pp : p = 0 ∨ p = 1 := by
        have h : ∀ v : Fin 10, Gadget.port .cubeE v = true → v = 0 ∨ v = 1 := by decide
        exact h p hp
      have qq : q = 0 ∨ q = 1 := by
        have h : ∀ v : Fin 10, Gadget.port .cubeE v = true → v = 0 ∨ v = 1 := by decide
        exact h q hq
      rcases pp with rfl | rfl
      all_goals rcases qq with rfl | rfl
      all_goals first
        | exact False.elim (hne rfl)
        | exact RegistryProofs.cubeE_00
        | exact RegistryProofs.cubeE_09
    · intro p t hp ht
      have pp : p = 0 ∨ p = 1 := by
        have h : ∀ v : Fin 10, Gadget.port .cubeE v = true → v = 0 ∨ v = 1 := by decide
        exact h p hp
      have tt : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 := by
        have h : ∀ v : Fin 10, Gadget.inside .cubeE v = true → v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7 := by decide
        exact h t ht
      rcases pp with rfl | rfl
      all_goals rcases tt with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact RegistryProofs.cubeE_01
        | exact RegistryProofs.cubeE_02
        | exact RegistryProofs.cubeE_03
        | exact RegistryProofs.cubeE_04
        | exact RegistryProofs.cubeE_05
        | exact RegistryProofs.cubeE_06
        | exact RegistryProofs.cubeE_07
        | exact RegistryProofs.cubeE_08
        | exact RegistryProofs.cubeE_10
        | exact RegistryProofs.cubeE_11
        | exact RegistryProofs.cubeE_12
        | exact RegistryProofs.cubeE_13
        | exact RegistryProofs.cubeE_14
        | exact RegistryProofs.cubeE_15
        | exact RegistryProofs.cubeE_16
        | exact RegistryProofs.cubeE_17

end ZombieDamage.Verified
