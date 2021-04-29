theory Algebraic_Graph_Deep_Embedding
  imports Algebraic_Digraph
begin

quotient_type 'v algebraic_graph = "'v pre_algebraic_graph" / algebraic_pair_digraph.algebraic_graph_eq
  by (rule algebraic_pair_digraph.equivp_algebraic_graph_eq)

lift_definition AEmpty :: "'v algebraic_graph" (\<open>\<epsilon>\<close>) is Empty .
lift_definition AVertex :: "'v \<Rightarrow> 'v algebraic_graph" is Vertex .
lift_definition AOverlay :: "'v algebraic_graph \<Rightarrow> 'v algebraic_graph \<Rightarrow> 'v algebraic_graph" (infixl \<open>\<oplus>\<close> 75) is Overlay
  by (simp add: algebraic_pair_digraph.algebraic_graph_eq_def)
lift_definition AConnect :: "'v algebraic_graph \<Rightarrow> 'v algebraic_graph \<Rightarrow> 'v algebraic_graph" (infixl \<open>\<rightarrow>\<close> 80) is Connect
  by (simp add: algebraic_pair_digraph.algebraic_graph_eq_def)


interpretation algebraic_digraph_deep_embedding: algebraic_digraph AEmpty AVertex AOverlay AConnect
proof
  show "\<And>x y. AOverlay x y = AOverlay y x"
    by (simp add: AOverlay_def algebraic_graph.abs_eq_iff algebraic_pair_digraph.deep_embedding_overlay_commute)
  show "\<And>x y z. AOverlay x (AOverlay y z) = AOverlay (AOverlay x y) z"
    by (metis (no_types, lifting) AOverlay.abs_eq AOverlay_def Quotient_algebraic_graph Quotient_rel_abs2 algebraic_graph.abs_eq_iff algebraic_pair_digraph.deep_embedding_overlay_assoc map_fun_apply)
  show "\<And>a b c. AConnect (AConnect a b) c = AConnect a (AConnect b c)"
    by (metis AConnect.abs_eq AConnect_def  Quotient_algebraic_graph Quotient_rep_abs_fold_unmap algebraic_graph.abs_eq_iff algebraic_pair_digraph.deep_embedding_connect_assoc map_fun_apply)
  show "\<And>a. AConnect AEmpty a = a"
    by (metis AConnect.abs_eq  AEmpty.abs_eq Quotient3_abs_rep Quotient3_algebraic_graph algebraic_graph.abs_eq_iff algebraic_pair_digraph.deep_embedding_connect_left_neutral)
  show "\<And>a. AConnect a AEmpty = a"
    by (metis AConnect.abs_eq AEmpty_def Quotient3_abs_rep Quotient3_algebraic_graph algebraic_graph.abs_eq_iff algebraic_pair_digraph.deep_embedding_connect_right_neutral)
  show "\<And>x y z. AConnect x (AOverlay y z) = AOverlay (AConnect x y) (AConnect x z)"
    by (smt (z3) AConnect.abs_eq AConnect_def AOverlay.abs_eq AOverlay_def \<open>\<And>a. AConnect a AEmpty = a\<close> algebraic_graph.abs_eq_iff algebraic_pair_digraph.deep_embedding_connect_distr_overlay_l map_fun_apply)
  show "\<And>x y z. AConnect (AOverlay x y) z = AOverlay (AConnect x z) (AConnect y z)"
    by (metis AConnect.abs_eq AConnect_def AOverlay.abs_eq \<open>\<And>a. AConnect a AEmpty = a\<close> \<open>\<And>c b a. AConnect (AConnect a b) c = AConnect a (AConnect b c)\<close> algebraic_graph.abs_eq_iff algebraic_pair_digraph.deep_embedding_connect_distr_overlay_r map_fun_apply)
  show "\<And>x y z. AConnect (AConnect x y) z = AOverlay (AOverlay (AConnect x y) (AConnect x z)) (AConnect y z)"
    unfolding AConnect_def AOverlay_def
    by auto
       (smt (z3) AConnect.abs_eq AOverlay.abs_eq Quotient3_abs_rep Quotient3_algebraic_graph Quotient_algebraic_graph Quotient_rel_abs algebraic_pair_digraph.deep_embedding_decomp)
qed

subsection \<open>Lifting functions to \<^typ>\<open>'a algebraic_graph\<close>\<close>
notation algebraic_pair_digraph.algebraic_graph_eq (infix \<open>\<equiv>\<^sub>A\<close> 50)


subsubsection \<open>Helper Lemmas\<close>

lemma fold_eq: "algebraic_pair_digraph.fold g = \<lparr> pverts = vertexSet g, parcs = edgeSet g \<rparr>"
  by (induction g)
     (auto simp: pair_digraph_empty_def algebraic_pre_graph.fold.simps)

lemma algebraic_graph_eq_iff: "vertexSet x = vertexSet y \<and> edgeSet x = edgeSet y \<longleftrightarrow> (x \<equiv>\<^sub>A y)"
  by (simp add: algebraic_pre_graph.algebraic_graph_eq_def fold_eq)

lemma algebraic_graph_eqI[intro]: "vertexSet x = vertexSet y \<Longrightarrow> edgeSet x = edgeSet y \<Longrightarrow> x \<equiv>\<^sub>A y"
  using algebraic_graph_eq_iff by blast

lemma algebraic_graph_eq_fmap: "x \<equiv>\<^sub>A y \<Longrightarrow> fmap f x \<equiv>\<^sub>A fmap f y"
  by (auto simp flip: algebraic_graph_eq_iff simp: fmap_edgeSet fmap_vertexSet)

lemma algebraic_graph_eq_overlay:
  assumes "x \<equiv>\<^sub>A y" "g \<equiv>\<^sub>A h"
  shows "x \<oplus> g \<equiv>\<^sub>A y \<oplus> h"
  using assms
  by (auto simp flip: algebraic_graph.abs_eq_iff AOverlay.abs_eq)

lemma algebraic_graph_eq_connect:
  assumes "x \<equiv>\<^sub>A y" "g \<equiv>\<^sub>A h"
  shows "x \<rightarrow> g \<equiv>\<^sub>A y \<rightarrow> h"
  using assms
  by (auto simp flip: algebraic_graph.abs_eq_iff AConnect.abs_eq)

lemma algebraic_graph_eq_overlays: 
  assumes "list_all2 (\<equiv>\<^sub>A) gs gs'"
  shows "overlays gs \<equiv>\<^sub>A overlays gs'"
  using assms
  by (induction gs arbitrary: gs')
     (auto simp: list_all2_Cons1 intro!: algebraic_graph_eq_overlay)

lemma algebraic_graph_eq_connects:
  assumes "list_all2 (\<equiv>\<^sub>A) gs gs'"
  shows "connects gs \<equiv>\<^sub>A connects gs'"
  using assms
  by (induction gs arbitrary: gs')
     (auto simp: list_all2_Cons1 intro!: algebraic_graph_eq_connect)

lemma algebraic_graph_eq_isEmpty:
  "g \<equiv>\<^sub>A g' \<Longrightarrow> isEmpty g = isEmpty g'"
  by (induction g) (auto simp flip: algebraic_graph_eq_iff no_vertex_iff_empty)

subsubsection \<open>Lifting\<close>

lift_definition Afoldg :: "'b \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a algebraic_graph \<Rightarrow> 'b"
  is foldg
  oops \<comment> \<open>@{thm foldg_size}\<close>

lift_definition Avertices :: "'a list \<Rightarrow> 'a algebraic_graph" is vertices .
lift_definition Aedges :: "('a \<times> 'a) list \<Rightarrow> 'a algebraic_graph" is edges .
lift_definition Aedge :: "'a \<Rightarrow> 'a \<Rightarrow> 'a algebraic_graph" is edge .
lift_definition Apath :: "'a list \<Rightarrow> 'a algebraic_graph" is path .

lift_definition Aoverlays :: "('a algebraic_graph) list \<Rightarrow> 'a algebraic_graph" is overlays
  using algebraic_graph_eq_overlays by blast

lift_definition Aconnects :: "('a algebraic_graph) list \<Rightarrow> 'a algebraic_graph" is connects
  using algebraic_graph_eq_connects by blast

text \<open>
  Cannot lift \<^term>\<open>foldg\<close> as it depends on the structure of the graph, see e.g.\ @{thm foldg_size}.
\<close>

lift_definition Abuildg :: "('a algebraic_graph \<Rightarrow> ('a \<Rightarrow> 'a algebraic_graph) \<Rightarrow> ('a algebraic_graph \<Rightarrow> 'a algebraic_graph \<Rightarrow> 'a algebraic_graph) \<Rightarrow> ('a algebraic_graph \<Rightarrow> 'a algebraic_graph \<Rightarrow> 'a algebraic_graph) \<Rightarrow> 'a algebraic_graph) \<Rightarrow> 'a algebraic_graph"
is buildg
  by (smt (verit, ccfv_SIG) algebraic_graph_eq_connect algebraic_graph_eq_overlay algebraic_graph_equivp buildg.simps equivp_def)

lift_definition AisEmpty :: "'a algebraic_graph \<Rightarrow> bool" is isEmpty
  using algebraic_graph_eq_isEmpty by blast

lift_definition Afmap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a algebraic_graph \<Rightarrow> 'b algebraic_graph" is fmap
  using algebraic_graph_eq_fmap by blast

lift_definition Asimplify :: "'a algebraic_graph \<Rightarrow> 'a algebraic_graph" is simplify
  by (auto simp flip: algebraic_graph_eq_iff simp: simplify_edgeSet simplify_vertexSet)

subsection \<open>Lemmas on lifted functions\<close>
text \<open>Lemmas which are generally as such not provable on the 'raw' datatype\<close>

lemma vertices_append: "vertices (xs @ ys) = vertices xs \<oplus> vertices ys"
  oops \<comment> \<open>see quickcheck counterexample\<close>

lemma Avertices_append: "Avertices (xs @ ys) = Avertices xs \<oplus> Avertices ys"
  apply (induction xs)
   apply (auto simp: Avertices_def)
   apply (metis AEmpty_def algebraic_digraph_deep_embedding.empty_least algebraic_digraph_deep_embedding.subgraph_def)
  by (metis AOverlay.abs_eq algebraic_digraph_deep_embedding.overlay_assoc)

lemma edges_append: "edges (xs @ ys) = edges xs \<oplus> edges ys"
  oops \<comment> \<open>see quickcheck counterexample\<close>

lemma Aedges_append: "Aedges (xs @ ys) = Aedges xs \<oplus> Aedges ys"
  apply (induction xs)
   apply (auto simp: Aedges_def)
   apply (metis AEmpty.abs_eq algebraic_digraph_deep_embedding.empty_least algebraic_digraph_deep_embedding.subgraph_def)
  by (metis AOverlay.abs_eq algebraic_digraph_deep_embedding.overlay_assoc)

lemma overlays_append: "overlays (xs @ ys) = overlays xs \<oplus> overlays ys"
  oops

lemma Aoverlays_append: "Aoverlays (xs @ ys) = Aoverlays xs \<oplus> Aoverlays ys"
  apply (induction xs)
   apply (auto simp: Aoverlays_def)
   apply (metis AEmpty_def algebraic_digraph_deep_embedding.empty_least algebraic_digraph_deep_embedding.subgraph_def)
  by (metis AOverlay.abs_eq algebraic_digraph_deep_embedding.overlay_assoc)

lemma connects_append: "connects (xs @ ys) = connects xs \<rightarrow> connects ys"
  oops

lemma Aconnects_append: "Aconnects (xs @ ys) = Aconnects xs \<rightarrow> Aconnects ys"
  apply (induction xs)
   apply (auto simp: Aconnects_def)
   apply (metis AEmpty_def algebraic_digraph_deep_embedding.connect_monoid monoid.left_neutral)
  by (metis AConnect.abs_eq algebraic_digraph_deep_embedding.connect_assoc)

lemma isEmpty_iff': "isEmpty g \<longleftrightarrow> g \<equiv>\<^sub>A \<epsilon>"
  by (induction g)
     (auto simp: algebraic_pre_graph.algebraic_graph_eq_def algebraic_pre_graph.fold.simps pair_digraph_empty_def)

lemma isEmpty_iff: "AisEmpty g \<longleftrightarrow> g = \<epsilon>"
  by (metis AEmpty_def AisEmpty.abs_eq AisEmpty.rep_eq Quotient_algebraic_graph Quotient_rel_abs2 isEmpty.simps(1) isEmpty_iff')

lemma simplify_eq: "Asimplify g = g"
  by (metis (mono_tags, hide_lams) Asimplify.abs_eq Quotient3_algebraic_graph Quotient3_rel_rep algebraic_graph_eq_iff rep_abs_rsp simplify_edgeSet simplify_vertexSet)
end
