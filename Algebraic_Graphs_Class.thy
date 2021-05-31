theory Algebraic_Graphs_Class
  imports 
    Algebraic_Graphs
begin

no_notation Empty (\<open>\<epsilon>\<close>)
no_notation Overlay (infixl \<open>\<oplus>\<close> 75)
no_notation Connect (infixl \<open>\<rightarrow>\<close> 80)

subsection \<open>Core\<close>
locale algebraic_pre_graph = 
  fixes empty :: 'g ("\<epsilon>")
    and vertex :: "'v \<Rightarrow> 'g"
    and overlay :: "'g \<Rightarrow> 'g \<Rightarrow> 'g" (infixl \<open>\<oplus>\<close> 75)
    and connect :: "'g \<Rightarrow> 'g \<Rightarrow> 'g" (infixl \<open>\<rightarrow>\<close> 80)
begin

fun edge :: "'v \<Rightarrow> 'v \<Rightarrow> 'g" where
  "edge u v = (vertex u) \<rightarrow> (vertex v)"

fun edges :: "('v \<times> 'v) list \<Rightarrow> 'g" where
  "edges es = foldr (\<oplus>) (map (\<lambda>(u,v). edge u v) es) \<epsilon>"

fun vertices :: "'v list \<Rightarrow> 'g" where
  "vertices vs = foldr (\<oplus>) (map vertex vs) \<epsilon>"

fun clique :: "'v list \<Rightarrow> 'g" where
  "clique vs = foldr (\<rightarrow>) (map vertex vs) \<epsilon>"

fun graph :: "'v list \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> 'g" where
  "graph vs es = vertices vs \<oplus> edges es"

definition subgraph :: "'g \<Rightarrow> 'g \<Rightarrow> bool" (infixl \<open>\<sqsubseteq>\<close> 50) where
  "x \<sqsubseteq> y \<equiv> x \<oplus> y = y"

fun path :: "'v list \<Rightarrow> 'g" where
  "path [] = empty" |
  "path [x] = vertex x" |
  "path xs = edges (zip xs (tl xs))"

fun circuit :: "'v list \<Rightarrow> 'g" where
  "circuit [] = empty" |
  "circuit (x#xs) = path (x#xs @ [x])"

fun star :: "'v \<Rightarrow> 'v list \<Rightarrow> 'g" where
  "star x ys = vertex x \<rightarrow> vertices ys"

definition has_vertex :: "'g \<Rightarrow> 'v \<Rightarrow> bool" where 
  "has_vertex g u \<equiv> vertex u \<sqsubseteq> g"

lemma has_vertexI[intro]: "vertex u \<sqsubseteq> g \<Longrightarrow> has_vertex g u"
  unfolding has_vertex_def .

definition vertex_set :: "'g \<Rightarrow> 'v set" where
  "vertex_set g \<equiv> {u. has_vertex g u}"

lemma in_vertex_set_iff: "u \<in> vertex_set g \<longleftrightarrow> has_vertex g u"
  unfolding vertex_set_def by auto

definition has_edge :: "'g \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool" where 
  "has_edge g u v \<equiv> edge u v \<sqsubseteq> g"

lemma has_edgeI[intro]: "edge u v \<sqsubseteq> g \<Longrightarrow> has_edge g u v"
  unfolding has_edge_def .

definition edge_set :: "'g \<Rightarrow> ('v \<times> 'v) set" where
  "edge_set g \<equiv> {(u,v) | u v. has_edge g u v}"

lemma in_edge_set_iff: "(u,v) \<in> edge_set g \<longleftrightarrow> has_edge g u v"
  unfolding edge_set_def by auto

definition is_empty :: "'g \<Rightarrow> bool" where
  "is_empty g \<longleftrightarrow> g \<sqsubseteq> \<epsilon>"

lemma is_emptyI[intro]: "g \<sqsubseteq> \<epsilon> \<Longrightarrow> is_empty g"
  unfolding is_empty_def .

lemma is_emptyD: "is_empty g \<Longrightarrow> g \<sqsubseteq> \<epsilon>"
  unfolding is_empty_def .

definition is_vertex :: "'g \<Rightarrow> 'v \<Rightarrow> bool" where
  "is_vertex g u \<equiv> has_vertex g u \<and> g \<sqsubseteq> vertex u"

lemma is_vertexI[intro]: "has_vertex g u \<Longrightarrow> g \<sqsubseteq> vertex u \<Longrightarrow> is_vertex g u"
  unfolding is_vertex_def by auto

definition reachable_trancl where
  "reachable_trancl g u v \<equiv> (u = v \<and> u \<in> vertex_set g) \<or> (u,v) \<in> trancl (edge_set g)"



subsubsection \<open>Vertex Walks\<close>
inductive vwalk where
  vwalk_Nil[simp]: "vwalk g []" |
  vwalk_single[simp]: "has_vertex g u \<Longrightarrow> vwalk g [u]" |
  vwalk_Cons[simp]: "vwalk g (v#xs) \<Longrightarrow> has_edge g u v \<Longrightarrow> vwalk g (u#v#xs)"

definition "vwalk_bet g u p v \<equiv> vwalk g p \<and> p \<noteq> [] \<and> hd p = u \<and> last p = v"

definition reachable_vwalk_bet where
  "reachable_vwalk_bet g u v \<equiv> (u = v \<and> u \<in> vertex_set g) \<or> (\<exists>w. vwalk_bet g u w v)"

lemma vwalk_has_edge: "vwalk_bet g u w v \<Longrightarrow> u \<noteq> v \<Longrightarrow> \<exists>v'. has_edge g u v'"
  by (cases w)
     (auto split: if_splits simp: vwalk_bet_def elim: vwalk.cases)

lemma vwalk_Cons_has_edge: "vwalk g (u#v#ws) \<Longrightarrow> has_edge g u v"
  by (auto elim: vwalk.cases)

lemma hd_of_vwalk_bet: "vwalk_bet g u w v \<Longrightarrow> \<exists>w'. w = u # w'"
  by (auto simp: vwalk_bet_def neq_Nil_conv)

lemma hd_of_vwalk_bet': "vwalk_bet g u w v \<Longrightarrow> hd w = u"
  by (simp add: vwalk_bet_def)

lemma last_of_vwalk_bet: "vwalk_bet g u w v \<Longrightarrow> last w = v"
  by (simp add: vwalk_bet_def)

lemma append_vwalk_suff: "vwalk g (w1 @ w2) \<Longrightarrow> vwalk g w2"
  by (induction w1)
     (fastforce intro: vwalk.intros elim: vwalk.cases)+

lemma append_vwalk:
  assumes "vwalk g w1" "vwalk g w2"
    and "w1 \<noteq> [] \<Longrightarrow> w2 \<noteq> [] \<Longrightarrow> has_edge g (last w1) (hd w2)"
  shows "vwalk g (w1 @ w2)"
  using assms
  by (induction w1)
     (fastforce intro: vwalk.intros elim: vwalk.cases)+

lemma vwalk_Cons: "vwalk g (u # w) \<Longrightarrow> vwalk g w"
  by (auto elim: vwalk.cases)

lemma split_vwalk_bet:
  assumes "vwalk_bet g v1 (w @ v2 # w') v3"
  shows "vwalk_bet g v2 (v2 # w') v3"
  using assms
  by (cases w)
     (auto dest: hd_of_vwalk_bet vwalk_Cons append_vwalk_suff simp: vwalk_bet_def)

lemma vwalk_bet_Cons:
  "vwalk_bet g u (u # w) v \<Longrightarrow> w \<noteq> [] \<Longrightarrow> vwalk_bet g (hd w) w v"
  by (auto simp: vwalk_bet_def dest: vwalk_Cons)

lemma vwalk_bet_Cons_2:
  "vwalk_bet g u w v \<Longrightarrow> w \<noteq> [] \<Longrightarrow> vwalk_bet g u (u # tl w) v"
  by (auto simp: vwalk_bet_def neq_Nil_conv)

lemma vwalk_bet_snoC:
  "vwalk_bet g u (w @ [v]) v' \<Longrightarrow> v = v'"
  by (auto simp: vwalk_bet_def)

lemma vwalk_bet_iff_vwalk:
  "w \<noteq> [] \<Longrightarrow> vwalk_bet g (hd w) w (last w) \<longleftrightarrow> vwalk g w"
  by (auto simp: vwalk_bet_def)

lemma vwalk_snoc_edge_2: "vwalk g (w @ [u, v]) \<Longrightarrow> has_edge g u v"
  by (auto dest: append_vwalk_suff vwalk_Cons_has_edge)

lemma vwalk_append_edge: "vwalk g (w1 @ w2) \<Longrightarrow> w1 \<noteq> [] \<Longrightarrow> w2 \<noteq> [] \<Longrightarrow> has_edge g (last w1) (hd w2)"
  by (induction w1)
     (auto elim: vwalk.cases)

lemma tl_vwalk_is_vwalk: "vwalk E p \<Longrightarrow> vwalk E (tl p)"
  by (induction p rule: vwalk.induct; simp)

lemma vwalk_concat:
  assumes "vwalk E p" "vwalk E q" "q \<noteq> []" "p \<noteq> [] \<Longrightarrow> last p = hd q"
  shows "vwalk E (p @ tl q)"
  using assms
  by (induction) (simp_all add: tl_vwalk_is_vwalk)

lemma vwalk_bet_join:
  assumes "vwalk_bet g u w v" "vwalk_bet g v w' s"
  shows "vwalk_bet g u (w @ tl w') s"
  using assms
  unfolding vwalk_bet_def
  by (auto simp: vwalk_concat)
     (metis append_butlast_last_id hd_Cons_tl last_append last_tl)
        
lemma reachable_trancl_trans:
  assumes "reachable_trancl g u v" "reachable_trancl g v s"
  shows "reachable_trancl g u s"          
  using assms
  unfolding reachable_trancl_def
  by (auto dest: trancl_trans)

lemma reachable_vwalk_bet_trans:
  assumes "reachable_vwalk_bet g u v" "reachable_vwalk_bet g v s"
  shows "reachable_vwalk_bet g u s"
  using assms
  unfolding reachable_vwalk_bet_def
  by (auto dest: vwalk_bet_join)

lemma reachable_defs_eq:
  "reachable_trancl g u v \<longleftrightarrow> reachable_vwalk_bet g u v"
  unfolding reachable_trancl_def reachable_vwalk_bet_def vwalk_bet_def
  apply auto
  sorry

end

subsection \<open>Directed graphs\<close>
locale algebraic_digraph = algebraic_pre_graph + 
assumes overlay_comm: "x \<oplus> y = y \<oplus> x"
  and overlay_assoc: "x \<oplus> (y \<oplus> z) = (x \<oplus> y) \<oplus>  z"
  and connect_monoid[simp]: "monoid (\<rightarrow>) \<epsilon>"
  and connect_distr_overlay_l: "x \<rightarrow> (y \<oplus> z) = x \<rightarrow> y \<oplus> x \<rightarrow> z"
  and connect_distr_overlay_r: "(x \<oplus> y) \<rightarrow> z = x \<rightarrow> z \<oplus> y \<rightarrow> z"
  and decomp: "x \<rightarrow> y \<rightarrow> z = x \<rightarrow> y \<oplus> x \<rightarrow> z \<oplus> y \<rightarrow> z"

begin


lemma connect_assoc: "x \<rightarrow> (y \<rightarrow> z) = x \<rightarrow> y \<rightarrow> z"
  by (metis connect_monoid monoid.axioms(1) semigroup.assoc)

lemma r_decomposition: "x = x \<oplus> x \<oplus> \<epsilon>"
proof -
  have "x = x \<rightarrow> \<epsilon> \<rightarrow> \<epsilon>"
    by (simp add: monoid.right_neutral)
  also have "\<dots> = (x \<rightarrow> \<epsilon>) \<oplus> (x \<rightarrow> \<epsilon>) \<oplus> (\<epsilon> \<rightarrow> \<epsilon>)"
    by (simp add: decomp)
  also have "\<dots> = x \<oplus> x \<oplus> \<epsilon>"
    by (simp add: monoid.right_neutral)
  finally show ?thesis .
qed

lemma overlay_empty_neutral: "x \<oplus> \<epsilon> = x"
  by (metis overlay_assoc r_decomposition)
(* proof -
  have "x = x \<oplus> x \<oplus> \<epsilon>"
    by (simp add: r_decomposition)
  also have "\<dots> = x \<oplus> x \<oplus> (\<epsilon> \<oplus> \<epsilon> \<oplus> \<epsilon>)"
    using r_decomposition by auto
  also have "\<dots> = (x \<oplus> \<epsilon>) \<oplus> (x \<oplus> \<epsilon>) \<oplus> \<epsilon>"
    by (metis overlay_assoc overlay_comm)
  also have "\<dots> = x \<oplus> \<epsilon>"
    by (simp flip: r_decomposition)
  finally show ?thesis by simp
qed *)

lemma overlay_empty_neutral_left: "\<epsilon> \<oplus> x = x"
  by (metis overlay_comm overlay_empty_neutral)

lemma overlay_idempotent[simp]: "x \<oplus> x = x"
  using overlay_empty_neutral r_decomposition by auto

lemma left_absorption: "x \<oplus> x \<rightarrow> y = x \<rightarrow> y"
proof -
  have "x \<oplus> x \<rightarrow> y = (x \<rightarrow> \<epsilon>) \<oplus> (x \<rightarrow> y)"
    by (simp add: monoid.right_neutral)
  also have "\<dots> = x \<rightarrow> (\<epsilon> \<oplus> y)"
    by (simp add: connect_distr_overlay_l)
  finally show ?thesis
    by (metis overlay_comm overlay_empty_neutral)
qed

lemma right_absorption: "y \<oplus> x \<rightarrow> y = x \<rightarrow> y"
proof -
  have "y \<oplus> x \<rightarrow> y = (\<epsilon> \<rightarrow> y) \<oplus> (x \<rightarrow> y)"
    by (simp add: monoid.left_neutral)
  also have "\<dots> = (\<epsilon> \<oplus> x) \<rightarrow> y"
    by (simp add: connect_distr_overlay_r)
  finally show ?thesis
    by (metis overlay_comm overlay_empty_neutral)
qed

lemma saturation: "x \<rightarrow> x \<rightarrow> x = x \<rightarrow> x"
  by (simp add: decomp)

lemma comm_monoid_overlay[simp]: "comm_monoid (\<oplus>) \<epsilon>"
  by (unfold_locales; metis overlay_assoc overlay_empty_neutral overlay_comm)

lemma "vertex x = vertices [x]"
  by (simp add: overlay_empty_neutral)

lemma "edge x y = clique [x, y]"
  by (simp add: monoid.right_neutral)

lemma clique_Nil: "clique [] = \<epsilon>"
  by simp

lemma clique_append: "clique (xs @ ys) = (clique xs) \<rightarrow> (clique ys)"
  by (induction xs)
     (auto simp add: monoid.left_neutral, metis connect_monoid monoid.axioms(1) semigroup.assoc)



lemma subgraphI: "x \<oplus> y = y \<Longrightarrow> x \<sqsubseteq> y"
  unfolding subgraph_def by simp

\<comment> \<open>TODO: partial\_order from HOL-Algebra.Order ?\<close>
lemma
  shows subgraph_refl: "x \<sqsubseteq> x"
    and subgraph_antisym: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> x \<Longrightarrow> x = y"
    and subgraph_trans: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> z"
  by (auto intro: subgraphI simp: subgraph_def overlay_comm)
     (metis overlay_assoc)

lemma empty_least: "\<epsilon> \<sqsubseteq> x"
  using overlay_empty_neutral[simplified overlay_comm]
  by (auto intro: subgraphI)

lemma subgraph_overlay: "x \<sqsubseteq> (x \<oplus> y)"
  by (auto intro: subgraphI simp: overlay_assoc)

lemma subgraph_overlay_connect: "x \<oplus> y \<sqsubseteq> x \<rightarrow> y"
  by (auto intro!: subgraphI)
     (metis left_absorption overlay_assoc right_absorption)

lemma subgraph_connectD:
  assumes "x \<rightarrow> y \<sqsubseteq> g"
  shows "x \<sqsubseteq> g"
    and "y \<sqsubseteq> g"
  using assms
  by (metis right_absorption left_absorption overlay_assoc subgraph_def)+

lemma subgraph_monotonicity:
  assumes "x \<sqsubseteq> y"
  shows "x \<oplus> z \<sqsubseteq> y \<oplus> z"
    and "x \<rightarrow> z \<sqsubseteq> y \<rightarrow> z"
    and "z \<rightarrow> x \<sqsubseteq> z \<rightarrow> y"
  using assms
  by (auto intro!: subgraphI simp: subgraph_def)
     (metis overlay_assoc overlay_comm overlay_idempotent connect_distr_overlay_r connect_distr_overlay_l)+

lemma vertices_subgraph_clique: "vertices xs \<sqsubseteq> clique xs"
  by (induction xs)
     (auto intro: subgraphI simp: subgraph_def, metis left_absorption overlay_assoc right_absorption)

lemma vertices_has_vertex: "u \<in> set xs \<Longrightarrow> has_vertex (vertices xs) u"
  apply (induction xs)
   apply (auto simp: has_vertex_def subgraph_overlay)
  by (metis overlay_assoc overlay_comm subgraph_def)

lemma vertices_no_edge: "\<not>has_edge (vertices xs) u v"
  apply (induction xs)
   apply (auto simp: has_edge_def)
  oops

lemma vertices_vertex_set: "set xs \<subseteq> vertex_set (vertices xs)"
  unfolding vertex_set_def
  using vertices_has_vertex by blast

lemma vertices_append: "vertices (xs @ ys) = vertices xs \<oplus> vertices ys"
  using overlay_assoc
  by (induction xs)
     (auto simp: overlay_empty_neutral_left)


lemma subgraph_mono_vertex: "h \<sqsubseteq> g \<Longrightarrow> has_vertex h u \<Longrightarrow> has_vertex g u"
  unfolding has_vertex_def
  using subgraph_trans by blast

lemma subgraph_mono_edge: "h \<sqsubseteq> g \<Longrightarrow> has_edge h u v \<Longrightarrow> has_edge g u v"
  unfolding has_edge_def
  using subgraph_trans by blast

lemma overlay_no_inverse:
  assumes "x \<oplus> y = \<epsilon>"
  shows "x = \<epsilon>" "y = \<epsilon>"
  using assms
  by (metis overlay_assoc overlay_empty_neutral overlay_idempotent overlay_comm)+

lemma connect_no_inverse_aux:
  assumes "x \<rightarrow> y = \<epsilon>"
  shows "x = \<epsilon>" "y = \<epsilon>"
  using assms left_absorption right_absorption overlay_no_inverse 
  by blast+

lemma connect_no_inverse:
  assumes "x \<noteq> \<epsilon> \<or> y \<noteq> \<epsilon>"
  shows "x \<rightarrow> y \<noteq> \<epsilon>"
  using assms connect_no_inverse_aux
  by blast

lemma subgraph_empty_is_empty: "g \<sqsubseteq> \<epsilon> \<Longrightarrow> g = \<epsilon>"
  by (simp add: empty_least subgraph_antisym)

lemma empty_no_vertex: "vertex u \<noteq> \<epsilon> \<Longrightarrow> has_vertex \<epsilon> u \<Longrightarrow> False"
  unfolding has_vertex_def
  by (auto dest: subgraph_empty_is_empty)

lemma vertex_set_empty: "vertex_set \<epsilon> \<noteq> {} \<Longrightarrow> \<exists>u. vertex u = \<epsilon>"
  unfolding vertex_set_def has_vertex_def
  by (auto dest: subgraph_empty_is_empty)

lemma "\<forall>u. vertex u \<noteq> \<epsilon> \<Longrightarrow> vertex_set \<epsilon> = {}"
  unfolding vertex_set_def has_vertex_def
  by (auto dest: subgraph_empty_is_empty)

lemma edge_has_vertex:
  assumes "has_edge g u v"
  shows "has_vertex g u"
    and "has_vertex g v"
  using assms
  unfolding has_edge_def has_vertex_def
  by (auto dest: subgraph_connectD)

lemma vwalk_has_vertex: "vwalk g p \<Longrightarrow> u \<in> set p \<Longrightarrow> has_vertex g u"
  by (induction rule: vwalk.induct)
     (auto dest: edge_has_vertex)

lemma append_vwalk_pref: "vwalk g (p1 @ p2) \<Longrightarrow> vwalk g p1"
  by (induction p1)
     (fastforce intro: vwalk.intros elim: vwalk.cases simp: edge_has_vertex)+

lemma split_vwalk_bet':
  "vwalk_bet g v1 (w @ v2 # w') v3 \<Longrightarrow> vwalk_bet g v1 (w @ [v2]) v2"
  by (induction w)
     (auto simp: vwalk_bet_def vwalk_has_vertex append_vwalk_pref split: if_splits)

lemma vwalk_snoC_edge': "vwalk g (w @ [u]) \<Longrightarrow> has_edge g u v \<Longrightarrow> vwalk g ((w @ [u]) @ [v])"
  by (rule append_vwalk) (auto dest: edge_has_vertex)

lemma vwalk_snoC_edge: "vwalk g (w @ [u]) \<Longrightarrow> has_edge g u v \<Longrightarrow> vwalk g (w @ [u, v])"
  using vwalk_snoC_edge'
  by simp

lemma vwalk_hd: "vwalk g (u # w) \<Longrightarrow> vwalk g [u]"
  by (simp add: vwalk_has_vertex)

end

subsection \<open>Undirected Graphs\<close>
locale algebraic_graph = algebraic_pre_graph + 
  assumes overlay_comm': "x \<oplus> y = y \<oplus> x"
    and overlay_assoc': "x \<oplus> (y \<oplus> z) = (x \<oplus> y) \<oplus> z"
    and connect_comm: "x \<rightarrow> y = y \<rightarrow> x"
    and connect_identity: "x \<rightarrow> \<epsilon> = x"
    and left_distr: "x \<rightarrow> (y \<oplus> z) = x \<rightarrow> y \<oplus> x \<rightarrow> z"
    and left_decomp: "(x \<rightarrow> y) \<rightarrow> z = x \<rightarrow> y \<oplus> x \<rightarrow> z \<oplus> y \<rightarrow> z"
begin

lemma connect_assoc': "(x \<rightarrow> y) \<rightarrow> z = x \<rightarrow> (y \<rightarrow> z)"
  by (metis connect_comm left_decomp overlay_comm')

end

sublocale algebraic_graph \<subseteq> algebraic_digraph
  using connect_assoc' connect_comm overlay_assoc' overlay_comm' left_decomp
  by unfold_locales
     (force simp add: connect_identity left_distr)+

context algebraic_graph
begin

lemma has_edge_comm: "has_edge g u v \<Longrightarrow> has_edge g v u"
  by (simp add: connect_comm has_edge_def)

lemma vwalk_rev: "vwalk g w \<Longrightarrow> vwalk g (rev w)"
  by (induction w rule: vwalk.induct)
     (auto simp: has_edge_comm vwalk_snoC_edge)
end

subsection \<open>Reflexive Graphs\<close>
locale algebraic_reflexive_graph = algebraic_digraph +
  assumes refl: "v = v \<rightarrow> v"
begin
end

subsection \<open>Transitive Graphs\<close>
text \<open>
  "Original" motivation: parallel (overlay) and sequential (connect) composition
\<close>
locale algebraic_transitive_graph = algebraic_digraph +
  assumes trans: "y \<noteq> \<epsilon> \<Longrightarrow> x \<rightarrow> y \<oplus> y \<rightarrow> z \<oplus> x \<rightarrow> z = x \<rightarrow> y \<oplus> y \<rightarrow> z"
begin

end

notation Empty (\<open>\<epsilon>\<close>)
notation Overlay (infixl \<open>\<oplus>\<close> 75)
notation Connect (infixl \<open>\<rightarrow>\<close> 80)

context algebraic_pre_graph
begin

fun fold :: "'v pre_algebraic_graph \<Rightarrow> 'g" where
  "fold \<epsilon> = \<epsilon>" |
  "fold (Vertex x) = vertex x" |
  "fold (x \<oplus> y) = (fold x) \<oplus> (fold y)" |
  "fold (x \<rightarrow> y) = (fold x) \<rightarrow> (fold y)"

definition algebraic_graph_eq :: "'v pre_algebraic_graph \<Rightarrow> 'v pre_algebraic_graph \<Rightarrow> bool" (infix \<open>\<equiv>\<^sub>A\<close> 50) where
  "algebraic_graph_eq x y \<equiv> fold x = fold y"

lemma algebraic_graph_eqI: "fold x = fold y \<Longrightarrow> algebraic_graph_eq x y"
  unfolding algebraic_graph_eq_def .

lemma equivp_algebraic_graph_eq: "equivp algebraic_graph_eq"
  by (auto simp: algebraic_graph_eq_def equivp_def fun_eq_iff)

end

subsection \<open>Equalities for deep embedding\<close>
context algebraic_digraph
begin

lemma deep_embedding_overlay_commute: "x \<oplus> y \<equiv>\<^sub>A y \<oplus> x"
  by (auto intro: algebraic_graph_eqI simp: overlay_comm)

lemma deep_embedding_overlay_assoc: "x \<oplus> (y \<oplus> z) \<equiv>\<^sub>A (x \<oplus> y) \<oplus> z"
  by (auto intro: algebraic_graph_eqI simp: overlay_assoc)

lemma deep_embedding_connect_assoc: "(x \<rightarrow> y) \<rightarrow> z \<equiv>\<^sub>A x \<rightarrow> (y \<rightarrow> z)"
  by (auto intro: algebraic_graph_eqI simp: connect_assoc)

lemma deep_embedding_connect_left_neutral: "\<epsilon> \<rightarrow> x \<equiv>\<^sub>A x"
  by (simp add: algebraic_graph_eqI monoid.left_neutral)

lemma deep_embedding_connect_right_neutral: "x \<rightarrow> \<epsilon> \<equiv>\<^sub>A x"
  by (simp add: algebraic_graph_eqI monoid.right_neutral)

lemma deep_embedding_connect_distr_overlay_l: "x \<rightarrow> (y \<oplus> z) \<equiv>\<^sub>A x \<rightarrow> y \<oplus> x \<rightarrow> z "
  by (auto intro: algebraic_graph_eqI simp: connect_distr_overlay_l)

lemma deep_embedding_connect_distr_overlay_r: "(x \<oplus> y) \<rightarrow> z \<equiv>\<^sub>A x \<rightarrow> z \<oplus> y \<rightarrow> z"
  by (auto intro: algebraic_graph_eqI simp: connect_distr_overlay_r)

lemma deep_embedding_decomp: "x \<rightarrow> y \<rightarrow> z \<equiv>\<^sub>A x \<rightarrow> y \<oplus> x \<rightarrow> z \<oplus> y \<rightarrow> z"
  by (auto intro: algebraic_graph_eqI simp: decomp)

end


end