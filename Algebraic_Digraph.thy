theory Algebraic_Digraph
  imports 
    Graph_Theory.Digraph_Component
    Algebraic_Graphs_Class
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

definition "pair_digraph_empty \<equiv> \<lparr> pverts = {}, parcs = {} \<rparr>"

lemma wf_empty: "pair_wf_digraph pair_digraph_empty"
  by standard
     (simp_all add: pair_digraph_empty_def)

interpretation algebraic_pair_digraph: algebraic_digraph pair_digraph_empty vertex_pair_digraph overlay_pair_digraph connect_pair_digraph
proof
  show "\<And>x y. overlay_pair_digraph x y = overlay_pair_digraph y x" by auto
next
  show "\<And>x y z. overlay_pair_digraph x (overlay_pair_digraph y z) = overlay_pair_digraph (overlay_pair_digraph x y) z"
    by auto
next
  show "\<And>a b c. connect_pair_digraph (connect_pair_digraph a b) c = connect_pair_digraph a (connect_pair_digraph b c)"
    by auto
next
  show "\<And>a. connect_pair_digraph pair_digraph_empty a = a"
    by (auto simp: pair_digraph_empty_def)
next
  show "\<And>a. connect_pair_digraph a pair_digraph_empty = a"
    by (auto simp: pair_digraph_empty_def)
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

lemma algebraic_vertices_eq: "algebraic_pair_digraph.vertices vs = \<lparr> pverts = set vs, parcs = {} \<rparr>"
  unfolding algebraic_pair_digraph.vertices.simps
  by (induction vs)
     (auto simp: pair_digraph_empty_def)

lemma algebraic_edges_eq: "algebraic_pair_digraph.edges es = \<lparr> pverts = set (map fst es) \<union> set (map snd es), parcs = set es \<rparr>"
  unfolding algebraic_pair_digraph.edges.simps algebraic_pair_digraph.edge.simps
  by (induction es)
     (auto simp: pair_digraph_empty_def)

lemma map_fst_Un_map_snd_eq_UN: "set (map fst xs) \<union> set (map snd xs) = \<Union> {{u,v} | u v. (u,v) \<in> set xs}"
  by (induction xs)
     (auto, blast+)

lemma algebraic_edges_eq': "algebraic_pair_digraph.edges es = \<lparr> pverts = \<Union> {{u,v} | u v. (u,v) \<in> set es}, parcs = set es \<rparr>"
  by (simp only: algebraic_edges_eq map_fst_Un_map_snd_eq_UN)

lemma algebraic_graph_eq: "algebraic_pair_digraph.graph vs es = \<lparr> pverts = set vs \<union> set (map fst es) \<union> set (map snd es), parcs = set es \<rparr>"
  unfolding algebraic_pair_digraph.graph.simps algebraic_vertices_eq algebraic_edges_eq
  by auto

lemma pair_wf_digraph_edges_subs_vertices:
  assumes "pair_wf_digraph \<lparr> pverts = vs, parcs = es \<rparr>"
  shows "fst ` es \<subseteq> vs" "snd ` es \<subseteq> vs"
  using assms
  by (auto dest: pair_wf_digraph.wellformed')

lemma algebraic_pair_digraph_complete:
  assumes "G = \<lparr> pverts = v_set, parcs = e_set \<rparr>"
  assumes "pair_wf_digraph G"
  assumes "set vs = v_set" "set es = e_set"
  shows "algebraic_pair_digraph.graph vs es = G"
  using assms
  unfolding algebraic_graph_eq
  by (simp add: Un_absorb2 pair_wf_digraph_edges_subs_vertices(1) pair_wf_digraph_edges_subs_vertices(2))


end