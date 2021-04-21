theory Algebraic_Graphs
  imports 
    Main
begin

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
  "star x ys = connect (vertex x) (vertices ys)"
end

subsection \<open>Directed graphs\<close>
locale algebraic_digraph = algebraic_pre_graph + 
assumes overlay_comm: "x \<oplus> y = y \<oplus> x"
  and overlay_assoc: "x \<oplus> (y \<oplus> z) = (x \<oplus> y) \<oplus>  z"
  and connect_monoid[simp]: "monoid connect \<epsilon>"
  and connect_distr_overlay_l: "x \<rightarrow> (y \<oplus> z) = x \<rightarrow> y \<oplus> x \<rightarrow> z"
  and connect_distr_overlay_r: "(x \<oplus> y) \<rightarrow> z = x \<rightarrow> z \<oplus> y \<rightarrow> z"
  and decomp: "x \<rightarrow> y \<rightarrow> z = x \<rightarrow> y \<oplus> x \<rightarrow> z \<oplus> y \<rightarrow> z"

begin

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
proof -
  have "x = x \<oplus> x \<oplus> \<epsilon>"
    by (simp add: r_decomposition)
  also have "\<dots> = x \<oplus> x \<oplus> (\<epsilon> \<oplus> \<epsilon> \<oplus> \<epsilon>)"
    using r_decomposition by auto
  also have "\<dots> = (x \<oplus> \<epsilon>) \<oplus> (x \<oplus> \<epsilon>) \<oplus> \<epsilon>"
    by (metis overlay_assoc overlay_comm)
  also have "\<dots> = x \<oplus> \<epsilon>"
    by (simp flip: r_decomposition)
  finally show ?thesis by simp
qed

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

\<comment> \<open>TODO: partial_order from HOL-Algebra.Order ?\<close>
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
end

subsection \<open>Undirected Graphs\<close>
locale algebraic_graph = algebraic_pre_graph + 
  assumes overlay_comm: "x \<oplus> y = y \<oplus> x"
    and overlay_assoc: "x \<oplus> (y \<oplus> z) = (x \<oplus> y) \<oplus> z"
    and connect_comm: "x \<rightarrow> y = y \<rightarrow> x"
    and connect_identity: "x \<rightarrow> \<epsilon> = x"
    and left_distr: "x \<rightarrow> (y \<oplus> z) = x \<rightarrow> y \<oplus> x \<rightarrow> z"
    and left_decomp: "(x \<rightarrow> y) \<rightarrow> z = x \<rightarrow> y \<oplus> x \<rightarrow> z \<oplus> y \<rightarrow> z"
begin

lemma connect_assoc: "(x \<rightarrow> y) \<rightarrow> z = x \<rightarrow> (y \<rightarrow> z)"
  by (metis connect_comm left_decomp overlay_comm)

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

datatype 'a pre_algebraic_graph = 
  Empty (\<open>\<epsilon>\<close>) | 
  Vertex 'a | 
  Overlay "'a pre_algebraic_graph" "'a pre_algebraic_graph" (infixl \<open>\<oplus>\<close> 75) |
  Connect "'a pre_algebraic_graph" "'a pre_algebraic_graph" (infixl \<open>\<rightarrow>\<close> 80)

context algebraic_pre_graph
begin

fun fold :: "'v pre_algebraic_graph \<Rightarrow> 'g" where
  "fold \<epsilon> = \<epsilon>" |
  "fold (Vertex x) = vertex x" |
  "fold (x \<oplus> y) = (fold x) \<oplus> (fold y)" |
  "fold (x \<rightarrow> y) = (fold x) \<rightarrow> (fold y)"

definition algebraic_graph_eq :: "'v pre_algebraic_graph \<Rightarrow> 'v pre_algebraic_graph \<Rightarrow> bool" where
  "algebraic_graph_eq x y \<equiv> fold x = fold y"

lemma algebraic_graph_eqI: "fold x = fold y \<Longrightarrow> algebraic_graph_eq x y"
  unfolding algebraic_graph_eq_def .

lemma equivp_algebraic_graph_eq: "equivp algebraic_graph_eq"
  by (auto simp: algebraic_graph_eq_def equivp_def fun_eq_iff)




end



end