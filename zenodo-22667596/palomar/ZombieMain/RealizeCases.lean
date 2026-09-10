import ZombieMain.AttachmentRealization

namespace ZombieMain
open SimpleGraph
variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {H J : G.Subgraph} {D : Diagram}

theorem realize_edge (e : D.Embedding H)
    (hmin : ∀ v ∈ H.verts, 2 ≤ (H.neighborSet v).ncard)
    (hmax : ∀ v, G.degree v ≤ 3) (p q : Fin D.order)
    (hpq : G.Adj (e.vertices p) (e.vertices q)) (hn : ¬ H.Adj (e.vertices p) (e.vertices q))
    (hr : D.reach 3 p.val q.val = true) (hv : J.verts = H.verts)
    (ha : ∀ u v, J.Adj u v ↔ H.Adj u v ∨
      (u=e.vertices p ∧ v=e.vertices q) ∨ (v=e.vertices p ∧ u=e.vertices q)) :
    RealizedAttachment D H J := by
  have hpd := e.label_port hmin hmax p hpq hn
  have hqd := e.label_port hmin hmax q hpq.symm (fun h => hn h.symm)
  have hneq : p.val ≠ q.val := by
    intro hh
    exact hpq.ne (congrArg e.vertices (Fin.ext hh))
  have hfalse : D.adj p.val q.val = false := by
    cases hb : D.adj p.val q.val
    · rfl
    · exact False.elim (hn ((e.adjacency p q).mp hb))
  exact Or.inr (Or.inl ⟨p.val,q.val,1,
    ⟨p.isLt,q.isLt,hneq,hpd,hqd,by decide,by decide,hr,fun _ => hfalse⟩,
    ⟨e.attachEdge p q hv ha⟩⟩)

theorem realize_one (e : D.Embedding H)
    (hmin : ∀ v ∈ H.verts, 2 ≤ (H.neighborSet v).ncard)
    (hmax : ∀ v, G.degree v ≤ 3) (p q : Fin D.order) (x : V)
    (hpq : e.vertices p ≠ e.vertices q) (hx : x ∉ H.verts)
    (hpx : G.Adj (e.vertices p) x) (hxq : G.Adj x (e.vertices q))
    (hr : D.reach 2 p.val q.val = true)
    (hv : ∀ v, v ∈ J.verts ↔ v ∈ H.verts ∨ v=x)
    (ha : ∀ u v, J.Adj u v ↔ H.Adj u v ∨
      (u=e.vertices p ∧ v=x) ∨ (v=e.vertices p ∧ u=x) ∨
      (u=x ∧ v=e.vertices q) ∨ (v=x ∧ u=e.vertices q)) :
    RealizedAttachment D H J := by
  have hpd := e.label_port hmin hmax p hpx (fun h => hx h.snd_mem)
  have hqd := e.label_port hmin hmax q hxq.symm (fun h => hx h.snd_mem)
  have hneq : p.val ≠ q.val := by
    intro hh
    exact hpq (congrArg e.vertices (Fin.ext hh))
  exact Or.inr (Or.inl ⟨p.val,q.val,2,
    ⟨p.isLt,q.isLt,hneq,hpd,hqd,by decide,by decide,hr,by omega⟩,
    ⟨e.attachOne p q x hx hv ha⟩⟩)

theorem realize_two (e : D.Embedding H)
    (hmin : ∀ v ∈ H.verts, 2 ≤ (H.neighborSet v).ncard)
    (hmax : ∀ v, G.degree v ≤ 3) (p q : Fin D.order) (x y : V)
    (hpq : e.vertices p ≠ e.vertices q)
    (hx : x ∉ H.verts) (hy : y ∉ H.verts) (hxy : x ≠ y)
    (hpx : G.Adj (e.vertices p) x) (hyq : G.Adj y (e.vertices q))
    (hr : D.reach 1 p.val q.val = true)
    (hv : ∀ v, v ∈ J.verts ↔ v ∈ H.verts ∨ v=x ∨ v=y)
    (ha : ∀ u v, J.Adj u v ↔ H.Adj u v ∨
      (u=e.vertices p ∧ v=x) ∨ (v=e.vertices p ∧ u=x) ∨
      (u=x ∧ v=y) ∨ (v=x ∧ u=y) ∨
      (u=y ∧ v=e.vertices q) ∨ (v=y ∧ u=e.vertices q)) :
    RealizedAttachment D H J := by
  have hpd := e.label_port hmin hmax p hpx (fun h => hx h.snd_mem)
  have hqd := e.label_port hmin hmax q hyq.symm (fun h => hy h.snd_mem)
  have hneq : p.val ≠ q.val := by
    intro hh
    exact hpq (congrArg e.vertices (Fin.ext hh))
  exact Or.inr (Or.inl ⟨p.val,q.val,3,
    ⟨p.isLt,q.isLt,hneq,hpd,hqd,by decide,by decide,hr,by omega⟩,
    ⟨e.attachTwo p q x y hx hy hxy hv ha⟩⟩)

theorem realize_matching (e : D.Embedding H)
    (hmin : ∀ v ∈ H.verts, 2 ≤ (H.neighborSet v).ncard)
    (hmax : ∀ v, G.degree v ≤ 3) (a b c d : Fin D.order)
    (hd : [a,b,c,d].Nodup)
    (hab : H.Adj (e.vertices a) (e.vertices b))
    (hcd : H.Adj (e.vertices c) (e.vertices d))
    (hac : G.Adj (e.vertices a) (e.vertices c))
    (hbd : G.Adj (e.vertices b) (e.vertices d))
    (hnac : ¬ H.Adj (e.vertices a) (e.vertices c))
    (hnbd : ¬ H.Adj (e.vertices b) (e.vertices d))
    (hv : J.verts = H.verts)
    (ha : ∀ u v, J.Adj u v ↔ H.Adj u v ∨
      (u=e.vertices a ∧ v=e.vertices c) ∨ (u=e.vertices c ∧ v=e.vertices a) ∨
      (u=e.vertices b ∧ v=e.vertices d) ∨ (u=e.vertices d ∧ v=e.vertices b)) :
    RealizedAttachment D H J := by
  have haD := e.label_port hmin hmax a hac hnac
  have hbD := e.label_port hmin hmax b hbd hnbd
  have hcD := e.label_port hmin hmax c hac.symm (fun h => hnac h.symm)
  have hdD := e.label_port hmin hmax d hbd.symm (fun h => hnbd h.symm)
  have hfalse : ∀ i j : Fin D.order, ¬ H.Adj (e.vertices i) (e.vertices j) →
      D.adj i.val j.val = false := by
    intro i j hij
    cases he : D.adj i.val j.val
    · rfl
    · exact False.elim (hij ((e.adjacency i j).mp he))
  have hdNat : [a.val,b.val,c.val,d.val].Nodup := by
    simpa using hd.map Fin.val_injective
  exact Or.inr (Or.inr ⟨a.val,b.val,c.val,d.val,
    ⟨a.isLt,b.isLt,c.isLt,d.isLt,hdNat,haD,hbD,hcD,hdD,
      (e.adjacency a b).mpr hab,(e.adjacency c d).mpr hcd,
      hfalse a c hnac,hfalse b d hnbd⟩,
    ⟨e.attachMatching a b c d hv ha⟩⟩)

end ZombieMain
