theory Algebraic_Graph_Deep_Embedding
  imports Algebraic_Digraph
begin

notation algebraic_pair_digraph.algebraic_graph_eq (infix \<open>\<equiv>\<^sub>A\<close> 50)

quotient_type 'v algebraic_graph = "'v pre_algebraic_graph" / algebraic_pair_digraph.algebraic_graph_eq
  by (rule algebraic_pair_digraph.equivp_algebraic_graph_eq)

lift_definition AEmpty :: "'v algebraic_graph" (\<open>\<epsilon>\<close>) is Empty .
lift_definition AVertex :: "'v \<Rightarrow> 'v algebraic_graph" is Vertex .
lift_definition AOverlay :: "'v algebraic_graph \<Rightarrow> 'v algebraic_graph \<Rightarrow> 'v algebraic_graph" (infixl \<open>\<oplus>\<close> 75) is Overlay
  by (simp add: algebraic_pair_digraph.algebraic_graph_eq_def)
lift_definition AConnect :: "'v algebraic_graph \<Rightarrow> 'v algebraic_graph \<Rightarrow> 'v algebraic_graph" (infixl \<open>\<rightarrow>\<close> 80) is Connect
  by (simp add: algebraic_pair_digraph.algebraic_graph_eq_def)

lemma deep_embedding_overlay_commute: "x \<oplus> y \<equiv>\<^sub>A y \<oplus> x"
  by (auto intro: algebraic_pair_digraph.algebraic_graph_eqI)

lemma deep_embedding_overlay_assoc: "x \<oplus> (y \<oplus> z) \<equiv>\<^sub>A (x \<oplus> y) \<oplus> z"
  by (auto intro: algebraic_pair_digraph.algebraic_graph_eqI)

lemma deep_embedding_connect_assoc: "(x \<rightarrow> y) \<rightarrow> z \<equiv>\<^sub>A x \<rightarrow> (y \<rightarrow> z)"
  by (auto intro: algebraic_pair_digraph.algebraic_graph_eqI)

lemma deep_embedding_connect_left_neutral: "\<epsilon> \<rightarrow> x \<equiv>\<^sub>A x"
  using algebraic_pair_digraph.connect_monoid monoid.left_neutral 
  by (intro algebraic_pair_digraph.algebraic_graph_eqI) fastforce

lemma deep_embedding_connect_right_neutral: "x \<rightarrow> \<epsilon> \<equiv>\<^sub>A x"
  by (auto intro!: algebraic_pair_digraph.algebraic_graph_eqI simp only: algebraic_pair_digraph.fold.simps)
     (meson algebraic_pair_digraph.connect_monoid monoid.right_neutral)

lemma deep_embedding_connect_distr_overlay_l: "x \<rightarrow> (y \<oplus> z) \<equiv>\<^sub>A x \<rightarrow> y \<oplus> x \<rightarrow> z "
  by (auto intro: algebraic_pair_digraph.algebraic_graph_eqI)

lemma deep_embedding_connect_distr_overlay_r: "(x \<oplus> y) \<rightarrow> z \<equiv>\<^sub>A x \<rightarrow> z \<oplus> y \<rightarrow> z"
  by (auto intro: algebraic_pair_digraph.algebraic_graph_eqI)

lemma deep_embedding_decomp: "x \<rightarrow> y \<rightarrow> z \<equiv>\<^sub>A x \<rightarrow> y \<oplus> x \<rightarrow> z \<oplus> y \<rightarrow> z"
  by (auto intro: algebraic_pair_digraph.algebraic_graph_eqI)

interpretation algebraic_digraph_deep_embedding: algebraic_digraph AEmpty AVertex AOverlay AConnect
proof
  show "\<And>x y. AOverlay x y = AOverlay y x"
    by (simp add: AOverlay_def algebraic_graph.abs_eq_iff deep_embedding_overlay_commute)
  show "\<And>x y z. AOverlay x (AOverlay y z) = AOverlay (AOverlay x y) z"
    by (metis (no_types, lifting) AOverlay.abs_eq AOverlay_def Quotient_algebraic_graph Quotient_rel_abs2 algebraic_graph.abs_eq_iff deep_embedding_overlay_assoc map_fun_apply)
  show "\<And>a b c. AConnect (AConnect a b) c = AConnect a (AConnect b c)"
    by (metis AConnect.abs_eq AConnect_def  Quotient_algebraic_graph Quotient_rep_abs_fold_unmap algebraic_graph.abs_eq_iff deep_embedding_connect_assoc map_fun_apply)
  show "\<And>a. AConnect AEmpty a = a"
    by (metis AConnect.abs_eq  AEmpty.abs_eq Quotient3_abs_rep Quotient3_algebraic_graph algebraic_graph.abs_eq_iff deep_embedding_connect_left_neutral)
  show "\<And>a. AConnect a AEmpty = a"
    by (metis AConnect.abs_eq AEmpty_def Quotient3_abs_rep Quotient3_algebraic_graph algebraic_graph.abs_eq_iff deep_embedding_connect_right_neutral)
  show "\<And>x y z. AConnect x (AOverlay y z) = AOverlay (AConnect x y) (AConnect x z)"
    by (smt (z3) AConnect.abs_eq AConnect_def AOverlay.abs_eq AOverlay_def \<open>\<And>a. AConnect a AEmpty = a\<close> algebraic_graph.abs_eq_iff deep_embedding_connect_distr_overlay_l map_fun_apply)
  show "\<And>x y z. AConnect (AOverlay x y) z = AOverlay (AConnect x z) (AConnect y z)"
    by (metis AConnect.abs_eq AConnect_def AOverlay.abs_eq \<open>\<And>a. AConnect a AEmpty = a\<close> \<open>\<And>c b a. AConnect (AConnect a b) c = AConnect a (AConnect b c)\<close> algebraic_graph.abs_eq_iff deep_embedding_connect_distr_overlay_r map_fun_apply)
  show "\<And>x y z. AConnect (AConnect x y) z = AOverlay (AOverlay (AConnect x y) (AConnect x z)) (AConnect y z)"
    unfolding AConnect_def AOverlay_def
    by auto
       (smt (z3) AConnect.abs_eq AOverlay.abs_eq Quotient3_abs_rep Quotient3_algebraic_graph Quotient_algebraic_graph Quotient_rel_abs deep_embedding_decomp)
qed

end