theory Algebraic_Digraph
  imports 
    Graph_Theory.Digraph_Component
    Algebraic_Graphs
begin

fun overlay_pair_digraph :: "'a pair_pre_digraph \<Rightarrow> 'a pair_pre_digraph \<Rightarrow> 'a pair_pre_digraph" where
  "overlay_pair_digraph x y = \<lparr> pverts = pverts x \<union> pverts y, parcs = parcs x \<union> parcs y \<rparr>"

fun connect_pair_digraph :: "'a pair_pre_digraph \<Rightarrow> 'a pair_pre_digraph \<Rightarrow> 'a pair_pre_digraph" where
  "connect_pair_digraph x y = \<lparr> pverts = pverts x \<union> pverts y, parcs = parcs x \<union> parcs y \<union> pverts x \<times> pverts y \<rparr>"

fun vertex_pair_digraph :: "'a \<Rightarrow> 'a pair_pre_digraph" where
  "vertex_pair_digraph v = \<lparr> pverts = {v}, parcs = {} \<rparr>"

lemma wf_overlay:
  assumes "pair_wf_digraph x" "pair_wf_digraph y"
  shows "pair_wf_digraph (overlay_pair_digraph x y)"
  by standard
     (auto simp: assms pair_wf_digraph.in_arcsD1 pair_wf_digraph.in_arcsD2)

lemma wf_connect:
  assumes "pair_wf_digraph x" "pair_wf_digraph y"
  shows "pair_wf_digraph (connect_pair_digraph x y)"
  by standard
     (auto simp: assms pair_wf_digraph.in_arcsD1 pair_wf_digraph.in_arcsD2)

lemma wf_vertex:
  "pair_wf_digraph (vertex_pair_digraph v)"
  by standard
     auto

definition "pair_degraph_empty \<equiv> \<lparr> pverts = {}, parcs = {} \<rparr>"

lemma wf_empty: "pair_wf_digraph pair_degraph_empty"
  by standard
     (simp_all add: pair_degraph_empty_def)

interpretation algebraic_graph pair_degraph_empty vertex_pair_digraph overlay_pair_digraph connect_pair_digraph
proof
  show "\<And>x y. overlay_pair_digraph x y = overlay_pair_digraph y x" by auto
next
  show "\<And>x y z. overlay_pair_digraph x (overlay_pair_digraph y z) = overlay_pair_digraph (overlay_pair_digraph x y) z"
    by auto
next
  show "\<And>a b c. connect_pair_digraph (connect_pair_digraph a b) c = connect_pair_digraph a (connect_pair_digraph b c)"
    by auto
next
  show "\<And>a. connect_pair_digraph pair_degraph_empty a = a"
    by (auto simp: pair_degraph_empty_def)
next
  show "\<And>a. connect_pair_digraph a pair_degraph_empty = a"
    by (auto simp: pair_degraph_empty_def)
next
  show "\<And>x y z. connect_pair_digraph x (overlay_pair_digraph y z) = overlay_pair_digraph (connect_pair_digraph x y) (connect_pair_digraph x z)"
    by auto
next
  show "\<And>x y z. connect_pair_digraph (overlay_pair_digraph x y) z = overlay_pair_digraph (connect_pair_digraph x z) (connect_pair_digraph y z)"
    by auto
next
  show "\<And>x y z.
       connect_pair_digraph (connect_pair_digraph x y) z =
       overlay_pair_digraph (overlay_pair_digraph (connect_pair_digraph x y) (connect_pair_digraph x z)) (connect_pair_digraph y z)"
    by auto
qed

end