theory Algebraic_Graphs
  imports 
    Main
begin

locale algebraic_graph = 
  fixes empty :: 'g ("\<epsilon>")
    and vertex :: "'v \<Rightarrow> 'g"
    and overlay :: "'g \<Rightarrow> 'g \<Rightarrow> 'g" (infixl \<open>+\<close> 75)
    and connect :: "'g \<Rightarrow> 'g \<Rightarrow> 'g" (infixl \<open>\<rightarrow>\<close> 80)

assumes overlay_comm: "(x::'g) + y = y + x"
  and overlay_assoc: "(x::'g) + (y + z) = (x + y) +  z"
  and connect_monoid[simp]: "monoid connect \<epsilon>"
  and connect_distr_overlay_l: "x \<rightarrow> ((y::'g) + z) = x \<rightarrow> y + x \<rightarrow> z"
  and connect_distr_overlay_r: "(x + y) \<rightarrow> z = x \<rightarrow> z + y \<rightarrow> z"
  and decomp: "(x::'g) \<rightarrow> y \<rightarrow> z = x \<rightarrow> y + x \<rightarrow> z + y \<rightarrow> z"

begin

lemma r_decomposition: "(x::'g) = x + x + \<epsilon>"
proof -
  have "x = x \<rightarrow> \<epsilon> \<rightarrow> \<epsilon>"
    by (simp add: monoid.right_neutral)
  also have "\<dots> = (x \<rightarrow> \<epsilon>) + (x \<rightarrow> \<epsilon>) + (\<epsilon> \<rightarrow> \<epsilon>)"
    by (simp add: decomp)
  also have "\<dots> = x + x + \<epsilon>"
    by (simp add: monoid.right_neutral)
  finally show ?thesis .
qed

lemma overlay_empty_neutral: "x + \<epsilon> = x"
proof -
  have "x = x + x + \<epsilon>"
    by (simp add: r_decomposition)
  also have "\<dots> = x + x + (\<epsilon> + \<epsilon> + \<epsilon>)"
    using r_decomposition by auto
  also have "\<dots> = (x + \<epsilon>) + (x + \<epsilon>) + \<epsilon>"
    by (metis overlay_assoc overlay_comm)
  also have "\<dots> = x + \<epsilon>"
    by (simp flip: r_decomposition)
  finally show ?thesis by simp
qed

lemma overlay_idempotent[simp]: "(x::'g) + x = x"
  using overlay_empty_neutral r_decomposition by auto

lemma left_absorption: "x + x \<rightarrow> (y::'g) = x \<rightarrow> y"
proof -
  have "x + x \<rightarrow> y = (x \<rightarrow> \<epsilon>) + (x \<rightarrow> y)"
    by (simp add: monoid.right_neutral)
  also have "\<dots> = x \<rightarrow> (\<epsilon> + y)"
    by (simp add: connect_distr_overlay_l)
  finally show ?thesis
    by (metis overlay_comm overlay_empty_neutral)
qed

lemma right_absorption: "y + x \<rightarrow> y = x \<rightarrow> y"
proof -
  have "y + x \<rightarrow> y = (\<epsilon> \<rightarrow> y) + (x \<rightarrow> y)"
    by (simp add: monoid.left_neutral)
  also have "\<dots> = (\<epsilon> + x) \<rightarrow> y"
    by (simp add: connect_distr_overlay_r)
  finally show ?thesis
    by (metis overlay_comm overlay_empty_neutral)
qed

lemma saturation: "x \<rightarrow> x \<rightarrow> x = x \<rightarrow> x"
  by (simp add: decomp)

lemma comm_monoid_overlay[simp]: "comm_monoid (+) \<epsilon>"
  by (unfold_locales; metis overlay_assoc overlay_empty_neutral overlay_comm)

fun edge :: "'v \<Rightarrow> 'v \<Rightarrow> 'g" where
  "edge u v = (vertex u) \<rightarrow> (vertex v)"

fun edges :: "('v \<times> 'v) list \<Rightarrow> 'g" where
  "edges es = foldr (+) (map (\<lambda>(u,v). edge u v) es) \<epsilon>"

fun vertices :: "'v list \<Rightarrow> 'g" where
  "vertices vs = foldr (+) (map vertex vs) \<epsilon>"

fun clique :: "'v list \<Rightarrow> 'g" where
  "clique vs = foldr (\<rightarrow>) (map vertex vs) \<epsilon>"

fun graph :: "'v list \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> 'g" where
  "graph vs es = vertices vs + edges es"

lemma "vertex x = vertices [x]"
  by (simp add: overlay_empty_neutral)

lemma "edge x y = clique [x, y]"
  by (simp add: monoid.right_neutral)

lemma clique_Nil: "clique [] = \<epsilon>"
  by simp

lemma clique_append: "clique (xs @ ys) = (clique xs) \<rightarrow> (clique ys)"
  by (induction xs)
     (auto simp add: monoid.left_neutral, metis connect_monoid monoid.axioms(1) semigroup.assoc)

definition subgraph :: "'g \<Rightarrow> 'g \<Rightarrow> bool" (infixl \<open>\<subseteq>\<close> 50) where
  "x \<subseteq> y \<equiv> x + y = y"

lemma subgraphI: "x + y = y \<Longrightarrow> x \<subseteq> y"
  unfolding subgraph_def by simp

\<comment> \<open>TODO: partial_order from HOL-Algebra.Order ?\<close>
lemma
  fixes x y :: 'g
  shows subgraph_refl: "x \<subseteq> x"
    and subgraph_antisym: "x \<subseteq> y \<Longrightarrow> y \<subseteq> x \<Longrightarrow> x = y"
    and subgraph_trans: "x \<subseteq> y \<Longrightarrow> y \<subseteq> z \<Longrightarrow> x \<subseteq> z"
  by (auto intro: subgraphI simp: subgraph_def overlay_comm)
     (metis overlay_assoc)

lemma empty_least: "\<epsilon> \<subseteq> x"
  using overlay_empty_neutral[simplified overlay_comm]
  by (auto intro: subgraphI)

lemma subgraph_overlay: "x \<subseteq> (x + y)"
  by (auto intro: subgraphI simp: overlay_assoc)

lemma subgraph_overlay_connect: "x + y \<subseteq> x \<rightarrow> y"
  by (auto intro!: subgraphI)
     (metis left_absorption overlay_assoc right_absorption)

lemma subgraph_monotony:
  fixes x y z :: 'g
  assumes "x \<subseteq> y"
  shows "x + z \<subseteq> y + z"
    and "x \<rightarrow> z \<subseteq> y \<rightarrow> z"
    and "z \<rightarrow> x \<subseteq> z \<rightarrow> y"
  using assms
  by (auto intro!: subgraphI simp: subgraph_def)
     (metis overlay_assoc overlay_comm overlay_idempotent connect_distr_overlay_r connect_distr_overlay_l)+

lemma vertices_subgraph_clique: "vertices xs \<subseteq> clique xs"
  by (induction xs)
     (auto intro: subgraphI simp: subgraph_def, metis left_absorption overlay_assoc right_absorption)
end


end