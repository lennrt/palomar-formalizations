import ZombieMain.ComponentQuotient
import Mathlib.Combinatorics.SimpleGraph.Metric

namespace ZombieMain
open SimpleGraph ZombieDamage
variable {V : Type} {G : SimpleGraph V}

/-- Actual Mathlib walks and the game's length-indexed walks agree. -/
theorem game_walk (p : G.Walk u v) : (gameGraph G).Walk p.length u v := by
  induction p with
  | nil => exact .nil _
  | cons h p ih => exact .cons h ih

theorem graph_walk {k : Nat} {u v : V} (p : (gameGraph G).Walk k u v) :
    ∃ q : G.Walk u v,q.length=k := by
  induction p with
  | nil v => exact ⟨.nil,rfl⟩
  | cons h p ih =>
    obtain ⟨q,hq⟩ := ih
    exact ⟨.cons h q,congrArg Nat.succ hq⟩

/-- Distance is compared with actual shortest walks, in both directions. -/
theorem game_distance (hconn : G.Connected) (u v : V) :
    (gameGraph G).Distance (G.dist u v) u v := by
  constructor
  · obtain ⟨p,hp⟩ := (hconn.preconnected u v).exists_walk_length_eq_dist
    exact hp ▸ game_walk p
  · intro j hj
    obtain ⟨p,hp⟩ := graph_walk hj
    rw [← hp]
    exact dist_le p


theorem game_distance_unique {a b : Nat} {u v : V}
    (ha : (gameGraph G).Distance a u v) (hb : (gameGraph G).Distance b u v) : a=b :=
  Nat.le_antisymm (ha.2 b hb.1) (hb.2 a ha.1)

theorem reply_dist_eq (hconn : G.Connected) {u v y : V}
    (hy : (gameGraph G).GeodesicReply u v y) : G.dist u v=G.dist y v+1 := by
  obtain ⟨_,d,hd,hy⟩ := hy
  have h1 := game_distance_unique hd (game_distance hconn u v)
  have h2 := game_distance_unique hy (game_distance hconn y v)
  omega

theorem exists_game_reply (hconn : G.Connected) {u v : V} (hne : u≠v) :
    ∃ y,(gameGraph G).GeodesicReply u v y := by
  obtain ⟨p,hp⟩ := hconn.exists_walk_length_eq_dist u v
  cases p with
  | nil => exact False.elim (hne rfl)
  | @cons u y v huy tail =>
    have ht : G.dist u v≤G.dist u y+G.dist y v := hconn.dist_triangle
    have hd : G.dist u y=1 := dist_eq_one_iff_adj.mpr huy
    have htail := dist_le tail
    simp only [Walk.length_cons] at hp
    have he : G.dist y v+1=G.dist u v := by omega
    refine ⟨y,huy,G.dist y v,?_,game_distance hconn y v⟩
    rw [show (G.dist y v).succ=G.dist u v by omega]
    exact game_distance hconn u v


theorem graph_dist_lt_card [Fintype V] (hconn : G.Connected) (u v : V) :
    G.dist u v < Fintype.card V := by
  obtain ⟨p,hpath,hp⟩ := hconn.exists_path_of_dist u v
  rw [← hp]
  exact hpath.length_lt

end ZombieMain
