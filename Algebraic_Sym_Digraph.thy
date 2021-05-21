theory Algebraic_Sym_Digraph
  imports Algebraic_Digraph
begin

fun connect_sym_pair_graph :: "'a pair_pre_digraph \<Rightarrow> 'a pair_pre_digraph \<Rightarrow> 'a pair_pre_digraph" where
  "connect_sym_pair_graph x y = \<lparr> pverts = pverts x \<union> pverts y, parcs = parcs x \<union> parcs y \<union> pverts x \<times> pverts y \<union> pverts y \<times> pverts x \<rparr>"

lemma wf_sym_empty:
  shows "pair_sym_digraph empty_pair_graph"
  by standard
     (auto simp: empty_pair_graph_def symmetric_def intro: symI)

lemma wf_sym_vertex:
  shows "pair_sym_digraph (vertex_pair_graph v)"
  by standard
     (auto simp: symmetric_def intro: symI)

lemma wf_sym_overlay:
  assumes "pair_sym_digraph x" "pair_sym_digraph y"
  shows "pair_sym_digraph (overlay_pair_graph x y)"
  by standard
     (auto simp: assms pair_sym_digraph.axioms pair_wf_digraph.in_arcsD1
                 pair_wf_digraph.in_arcsD2 symmetric_def pair_sym_digraph.arcs_symmetric
           intro: symI)

lemma wf_sym_connect:
  assumes "pair_sym_digraph x" "pair_sym_digraph y"
  shows "pair_sym_digraph (connect_sym_pair_graph x y)"
  using assms
  by unfold_locales
     (auto simp: pair_sym_digraph.axioms pair_wf_digraph.in_arcsD1 
                      pair_wf_digraph.in_arcsD2 symmetric_def 
           dest: pair_sym_digraph.arcs_symmetric
           intro: symI)

interpretation algebraic_pair_graph: algebraic_graph empty_pair_graph vertex_pair_graph overlay_pair_graph connect_sym_pair_graph
proof
  show "\<And>x y. overlay_pair_graph x y = overlay_pair_graph y x" by auto
next
  show "\<And>x y z. overlay_pair_graph x (overlay_pair_graph y z) = overlay_pair_graph (overlay_pair_graph x y) z"
    by auto
next
  show "\<And>x y. connect_sym_pair_graph x y = connect_sym_pair_graph y x"
    by auto
next
  show "\<And>x. connect_sym_pair_graph x empty_pair_graph = x"
    by (simp add: empty_pair_graph_def)
next
  show "\<And>x y z. connect_sym_pair_graph x (overlay_pair_graph y z) = overlay_pair_graph (connect_sym_pair_graph x y) (connect_sym_pair_graph x z)"
    by auto
next
  show "\<And>x y z.
       connect_sym_pair_graph (connect_sym_pair_graph x y) z =
       overlay_pair_graph (overlay_pair_graph (connect_sym_pair_graph x y) (connect_sym_pair_graph x z)) (connect_sym_pair_graph y z)"
    by auto
qed


end