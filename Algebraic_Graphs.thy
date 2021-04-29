theory Algebraic_Graphs
  imports Main
begin

subsubsection \<open>Algebraic data type for graphs\<close>
datatype 'a pre_algebraic_graph = 
  Empty (\<open>\<epsilon>\<close>) | 
  Vertex 'a | 
  Overlay "'a pre_algebraic_graph" "'a pre_algebraic_graph" (infixl \<open>\<oplus>\<close> 75) |
  Connect "'a pre_algebraic_graph" "'a pre_algebraic_graph" (infixl \<open>\<rightarrow>\<close> 80)

subsubsection \<open>Basic graph construction primitives\<close>
fun edge :: "'a \<Rightarrow> 'a \<Rightarrow> 'a pre_algebraic_graph" where
  "edge u v = Vertex u \<rightarrow> Vertex v"

fun vertices :: "'a list \<Rightarrow> 'a pre_algebraic_graph" where
  "vertices [] = \<epsilon>" |
  "vertices (a#as) = Vertex a \<oplus> vertices as"

fun edges :: "('a \<times> 'a) list \<Rightarrow> 'a pre_algebraic_graph" where
  "edges [] = \<epsilon>" |
  "edges ((u,v)#es) = edge u v \<oplus> edges es"

fun overlays :: "('a pre_algebraic_graph) list \<Rightarrow> 'a pre_algebraic_graph" where
  "overlays [] = \<epsilon>" |
  "overlays (g#gs) = g \<oplus> overlays gs"

fun connects :: "('a pre_algebraic_graph) list \<Rightarrow> 'a pre_algebraic_graph" where
  "connects [] = \<epsilon>" |
  "connects (g#gs) = g \<rightarrow> connects gs"

subsubsection \<open>Graph folding\<close>
fun foldg :: "'b \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a pre_algebraic_graph \<Rightarrow> 'b" where
  "foldg e _ _ _ \<epsilon> = e" |
  "foldg _ v _ _ (Vertex a) = v a" |
  "foldg e v ov c (x \<oplus> y) = ov (foldg e v ov c x) (foldg e v ov c y)" |
  "foldg e v ov c (x \<rightarrow> y) = c (foldg e v ov c x) (foldg e v ov c y)"

fun buildg :: "('a pre_algebraic_graph \<Rightarrow> ('a \<Rightarrow> 'a pre_algebraic_graph) \<Rightarrow> ('a pre_algebraic_graph \<Rightarrow> 'a pre_algebraic_graph \<Rightarrow> 'a pre_algebraic_graph) \<Rightarrow> ('a pre_algebraic_graph \<Rightarrow> 'a pre_algebraic_graph \<Rightarrow> 'a pre_algebraic_graph) \<Rightarrow> 'a pre_algebraic_graph) \<Rightarrow> 'a pre_algebraic_graph" where
  "buildg f = f \<epsilon> Vertex (\<oplus>) (\<rightarrow>)"

subsubsection \<open>Graph properties\<close>
fun isEmpty :: "'a pre_algebraic_graph \<Rightarrow> bool" where
  "isEmpty \<epsilon> = True" |
  "isEmpty (Vertex _) = False" |
  "isEmpty (x \<oplus> y) = (isEmpty x \<and> isEmpty y)" |
  "isEmpty (x \<rightarrow> y) = (isEmpty x \<and> isEmpty y)"

fun size :: "'a pre_algebraic_graph \<Rightarrow> nat" where
  "size \<epsilon> = 1" |
  "size (Vertex _) = 1" |
  "size (x \<oplus> y) = size x + size y" |
  "size (x \<rightarrow> y) = size x + size y"

fun hasVertex :: "'a pre_algebraic_graph \<Rightarrow> 'a \<Rightarrow> bool" where
  "hasVertex \<epsilon> _ = False" |
  "hasVertex (Vertex b) a = (a = b)" |
  "hasVertex (x \<oplus> y) a = (hasVertex x a \<or> hasVertex y a)" |
  "hasVertex (x \<rightarrow> y) a = (hasVertex x a \<or> hasVertex y a)"

fun hasEdge :: "'a pre_algebraic_graph \<Rightarrow> 'a \<Rightarrow> 'a  \<Rightarrow> bool" where
  "hasEdge \<epsilon> _ _ = False" |
  "hasEdge (Vertex _) _ _ = False" |
  "hasEdge (x \<oplus> y) u v = (hasEdge x u v \<or> hasEdge y u v)" |
  "hasEdge (x \<rightarrow> y) u v = (hasEdge x u v \<or> hasEdge y u v \<or> (hasVertex x u \<and> hasVertex y v))"

fun vertexSet :: "'a pre_algebraic_graph \<Rightarrow> 'a set" where
  "vertexSet \<epsilon> = {}" |
  "vertexSet (Vertex u) = {u}" |
  "vertexSet (x \<oplus> y) = vertexSet x \<union> vertexSet y" |
  "vertexSet (x \<rightarrow> y) = vertexSet x \<union> vertexSet y"

fun edgeSet :: "'a pre_algebraic_graph \<Rightarrow> ('a \<times> 'a) set" where
  "edgeSet \<epsilon> = {}" |
  "edgeSet (Vertex _) = {}" |
  "edgeSet (x \<oplus> y) = edgeSet x \<union> edgeSet y" |
  "edgeSet (x \<rightarrow> y) = edgeSet x \<union> edgeSet y \<union> {(u,v)| u v. u \<in> vertexSet x \<and> v \<in> vertexSet y}"

subsubsection \<open>Standard families of graphs\<close>
fun path :: "'a list \<Rightarrow> 'a pre_algebraic_graph" where
  "path [] = \<epsilon>" |
  "path [u] = Vertex u" |
  "path (u#v#xs) = edge u v \<oplus> path (v#xs)"

fun circuit :: "'a list \<Rightarrow> 'a pre_algebraic_graph" where
  "circuit [] = \<epsilon>" |
  "circuit (x#xs) = path (x#xs @ [x])"

fun clique :: "'a list \<Rightarrow> 'a pre_algebraic_graph" where
  "clique vs = foldr (\<rightarrow>) (map Vertex vs) \<epsilon>"


subsection \<open>Graph transformation\<close>
fun fmap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a pre_algebraic_graph \<Rightarrow> 'b pre_algebraic_graph" where
  "fmap _ \<epsilon> = \<epsilon>" |
  "fmap f (Vertex a) = Vertex (f a)" |
  "fmap f (x \<oplus> y) = (fmap f x) \<oplus> (fmap f y)" |
  "fmap f (x \<rightarrow> y) = (fmap f x) \<rightarrow> (fmap f y)"

fun replaceVertex :: "'a \<Rightarrow> 'a \<Rightarrow> 'a pre_algebraic_graph \<Rightarrow> 'a pre_algebraic_graph" where
  "replaceVertex u v = fmap (\<lambda>w. if w = u then v else w)"

fun mergeVertices :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a pre_algebraic_graph \<Rightarrow> 'a pre_algebraic_graph" where
  "mergeVertices p v = fmap (\<lambda>w. if p w then v else w)"

fun splitVertex :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a pre_algebraic_graph \<Rightarrow> 'a pre_algebraic_graph" where
  "splitVertex _ _ \<epsilon> = \<epsilon>" |
  "splitVertex u vs (Vertex v) = (if u = v then vertices vs else Vertex v)" |
  "splitVertex u vs (x \<oplus> y) = splitVertex u vs x \<oplus> splitVertex u vs y" |
  "splitVertex u vs (x \<rightarrow> y) = splitVertex u vs x \<rightarrow> splitVertex u vs y"

fun transpose :: "'a pre_algebraic_graph \<Rightarrow> 'a pre_algebraic_graph" where
  "transpose \<epsilon> = \<epsilon>" |
  "transpose (Vertex a) = Vertex a" |
  "transpose (x \<oplus> y) = transpose x \<oplus> transpose y" |
  "transpose (x \<rightarrow> y) = transpose y \<rightarrow> transpose x"

fun bind :: "'a pre_algebraic_graph \<Rightarrow> ('a \<Rightarrow> 'a pre_algebraic_graph) \<Rightarrow> 'a pre_algebraic_graph" where
  "bind \<epsilon> _ = \<epsilon>" |
  "bind (Vertex u) f = f u" |
  "bind (x \<oplus> y) f = bind x f \<oplus> bind y f" |
  "bind (x \<rightarrow> y) f = bind x f \<rightarrow> bind y f"

definition induce :: "('a \<Rightarrow> bool) \<Rightarrow> 'a pre_algebraic_graph \<Rightarrow> 'a pre_algebraic_graph" where
  "induce p g = bind g (\<lambda>v. if p v then Vertex v else \<epsilon>)"

fun removeVertex :: "'a \<Rightarrow> 'a pre_algebraic_graph \<Rightarrow> 'a pre_algebraic_graph" where
  "removeVertex v = induce (\<lambda>u. u \<noteq> v)"

fun splitVertex' :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a pre_algebraic_graph \<Rightarrow> 'a pre_algebraic_graph" where
  "splitVertex' u vs g = bind g (\<lambda>v. if u = v then vertices vs else Vertex v)"

fun simplify :: "'a pre_algebraic_graph \<Rightarrow> 'a pre_algebraic_graph" where
  "simplify (x \<oplus> y) = 
    (if isEmpty x \<and> isEmpty y then \<epsilon>
      else if x = y then simplify x
      else if isEmpty x then simplify y
      else if isEmpty y then simplify x
      else simplify x \<oplus> simplify y)" |
  "simplify (x \<rightarrow> y) = 
    (if isEmpty x \<and> isEmpty y then \<epsilon>
      else if isEmpty x then simplify y
      else if isEmpty y then simplify x
      else simplify x \<rightarrow> simplify y)" |
  "simplify g = g"

lemma wellformed:
  assumes "hasEdge g u v"
  shows "hasVertex g u" "hasVertex g v"
  using assms
  by (induction g) auto

lemma wellformed':
  assumes "(u,v) \<in> edgeSet g"
  shows "u \<in> vertexSet g" "v \<in> vertexSet g"
  using assms
  by (induction g) auto

lemma vertexSet_eq: "u \<in> vertexSet g \<longleftrightarrow> hasVertex g u"
  by (induction g) auto

lemma edgeSet_eq: "(u,v) \<in> edgeSet g \<longleftrightarrow> hasEdge g u v"
  by (induction g) (auto simp: vertexSet_eq)

subsubsection \<open>\<^term>\<open>vertices\<close>\<close>
lemma vertices_vertexSet: "vertexSet (vertices xs) = set xs"
  by (induction xs) auto

lemma vertices_edgeSet: "edgeSet (vertices xs) = {}"
  by (induction xs) auto

subsubsection \<open>\<^term>\<open>edges\<close>\<close>
lemma edges_vertexSet: "vertexSet (edges es) = set (map fst es) \<union> set (map snd es)"
  by (induction es) force+

lemma edges_edgeSet: "edgeSet (edges es) = set es"
  by (induction es) force+

subsubsection \<open>\<^term>\<open>overlays\<close>\<close>
lemma overlays_vertexSet: "vertexSet (overlays gs) = \<Union> (set (map vertexSet gs))"
  by (induction gs) auto

lemma overlays_edgeSet: "edgeSet (overlays gs) = \<Union> (set (map edgeSet gs))"
  by (induction gs) auto

subsubsection \<open>\<^term>\<open>connects\<close>\<close>
lemma connects_vertexSet: "vertexSet (connects gs) = \<Union> (set (map vertexSet gs))"
  by (induction gs rule: connects.induct) auto

lemma connects_perserves_edges: "\<Union> (set (map edgeSet gs)) \<subseteq> edgeSet (connects gs)"
  by (induction gs rule: connects.induct) auto

lemma
  assumes "gs = pre @ g # suff"
      and "u \<in> vertexSet g"
      and "g' \<in> set suff"
      and "v \<in> vertexSet g'"
    shows "(u,v) \<in> edgeSet (connects gs)"
  using assms
  sorry

subsubsection \<open>\<^term>\<open>foldg\<close>\<close>
lemma foldg_id: "foldg \<epsilon> Vertex (\<oplus>) (\<rightarrow>) g = g"
  by (induction g) auto

lemma foldg_transpose: "foldg \<epsilon> Vertex (\<oplus>) (\<lambda>x y. y \<rightarrow> x) g = transpose g"
  by (induction g) auto

lemma foldg_size: "foldg 1 (\<lambda>_. 1) (+) (+) g = size g"
  by (induction g) auto

lemma foldg_isEmpty: "foldg True (\<lambda>_. False) (\<and>) (\<and>) g = isEmpty g"
  by (induction g) auto

lemma foldg_hasVertex: "foldg False (\<lambda>x. a = x) (\<or>) (\<or>) g = hasVertex g a"
  by (induction g) auto

subsubsection \<open>\<^term>\<open>buildg\<close>\<close>
lemma buildg_f: "buildg f = f \<epsilon> Vertex (\<oplus>) (\<rightarrow>)"
  by simp

lemma buildg_empty: "buildg (\<lambda>e _ _ _. e) = \<epsilon>"
  by simp

lemma buildg_vertex: "buildg (\<lambda>_ v _ _. v x) = Vertex x"
  by simp

lemma buildg_overlay: "buildg (\<lambda>e v ov c. ov (foldg e v ov c x) (foldg e v ov c y)) = x \<oplus> y"
  by (auto simp add: foldg_id)

lemma buildg_connect: "buildg (\<lambda>e v ov c. c (foldg e v ov c x) (foldg e v ov c y)) = x \<rightarrow> y"
  by (auto simp add: foldg_id)

lemma buildg_vertices: "buildg (\<lambda>e v ov _ . foldr ov  (map v xs) e) = vertices xs"
  by (induction xs) auto

lemma buildg_transpose: "buildg (\<lambda>e v ov c. foldg e v ov (\<lambda>x y. c y x) g) = transpose g"
  by (induction g) auto

subsubsection \<open>\<^term>\<open>isEmpty\<close>\<close>
lemma no_vertex_iff_empty: "vertexSet g = {} \<longleftrightarrow> isEmpty g"
  by (induction g) auto

lemma empty_no_edge: "isEmpty g \<Longrightarrow> edgeSet g = {}"
  by (induction g) (auto simp: no_vertex_iff_empty)

subsubsection \<open>\<^term>\<open>size\<close>\<close>
lemma size_geq_1: "1 \<le> size g"
  by (induction g) auto

subsubsection \<open>\<^term>\<open>path\<close>\<close>
lemma path_vertexSet: "vertexSet (path xs) = set xs"
  by (induction xs rule: path.induct) auto

lemma path_edgeSet: "edgeSet (path xs) = set (zip xs (tl xs))"
  by (induction xs rule: path.induct) auto

lemma path_append: "path (xs @ ys) = path xs \<oplus> path ys"
  oops

lemma path_rev_vertexSet: "vertexSet (path xs) = vertexSet (path (rev xs))"
  by (induction xs rule: path.induct) (simp_all add: insert_commute path_vertexSet)

lemma path_edge_append: "(u, v) \<in> edgeSet (path (xs @ [u,v]))"
  by (induction xs rule: path.induct) auto

lemma path_append_mono: 
  assumes "(u,v) \<in> edgeSet (path (xs @ [s]))"
  shows "(u,v) \<in> edgeSet (path (xs @ [s, t]))"
  using assms
  by (induction xs rule: path.induct) auto

lemma path_append_edge_last:
  assumes "(u, v) \<in> edgeSet (path (xs @ [s, t]))"
    and "(u, v) \<notin> edgeSet (path (xs @ [s]))"
  shows "u = s" "v = t"
  using assms
  by (induction xs rule: path.induct) auto

lemma path_rev_edgeSet: "(u,v) \<in> edgeSet (path xs) \<longleftrightarrow> (v,u) \<in> edgeSet (path (rev xs))"
  by (induction xs rule: path.induct)
     (auto simp: path_edge_append path_append_mono path_append_edge_last)

lemma path_rev_converse_edgeSet: "edgeSet (path (rev xs)) = (edgeSet (path xs))\<inverse>"
  using path_rev_edgeSet by fast

subsubsection \<open>\<^term>\<open>circuit\<close>\<close>
lemma circuit_vertexSet: "vertexSet (circuit xs) = set xs"
  by (cases xs) (auto simp: path_vertexSet)

lemma circuit_edgeSet: "(last (x#xs), x) \<in> edgeSet (circuit (x#xs))"
  by (induction xs rule: path.induct, auto)
     (smt (verit, ccfv_threshold) Cons_eq_appendI append.assoc append_butlast_last_id butlast.simps(2) last_ConsL path_edge_append)
  
subsubsection \<open>\<^term>\<open>clique\<close>\<close>
lemma clique_vertexSet: "vertexSet (clique vs) = set vs"
  by (induction vs) auto


subsubsection \<open>\<^term>\<open>fmap\<close>\<close>
lemma fmap_vertexSet: "vertexSet (fmap f g) = f ` vertexSet g"
  by (induction g) auto

lemma fmap_edgeSet: "edgeSet (fmap f g) = {(f u, f v)| u v. (u,v) \<in> edgeSet g}"
  by (induction g) (auto simp: fmap_vertexSet)

subsubsection \<open>\<^term>\<open>replaceVertex\<close>\<close>
lemma replaceVertex_mergeVertices: "replaceVertex u v g = mergeVertices (\<lambda>w. w = u) v g"
  by (induction g) auto

lemma replaceVertex_removes: "u \<noteq> v \<Longrightarrow> u \<notin> vertexSet (replaceVertex u v g)"
  by (induction g) auto

lemma replaceVertex_id: "u \<notin> vertexSet g \<Longrightarrow> replaceVertex u v g = g"
  by (induction g) auto

lemma replaceVertex_vertexSet:
  shows "u \<in> vertexSet g \<Longrightarrow> vertexSet (replaceVertex u v g) = vertexSet g - {u} \<union> {v}"
    and "u \<notin> vertexSet g \<Longrightarrow> vertexSet (replaceVertex u v g) = vertexSet g"
  by (auto simp: fmap_vertexSet)

lemma replaceVertex_edge_1:
  assumes "(u,w) \<in> edgeSet g" "u \<noteq> w"
  shows "(v,w) \<in> edgeSet (replaceVertex u v g)"
  using assms
  by (induction g) (auto simp: fmap_vertexSet)

lemma replaceVertex_edge_2:
  assumes "(w,u) \<in> edgeSet g" "u \<noteq> w"
  shows "(w,v) \<in> edgeSet (replaceVertex u v g)"
  using assms
  by (induction g) (auto simp: fmap_vertexSet)

lemma replaceVertex_edge_3:
  assumes "(u,u) \<in> edgeSet g"
  shows "(v,v) \<in> edgeSet (replaceVertex u v g)"
  using assms
  by (induction g) (auto simp: fmap_vertexSet)

lemma replaceVertex_edge_4:
  assumes "(s,t) \<in> edgeSet g" "s \<noteq> u" "t \<noteq> u"
  shows "(s,t) \<in> edgeSet (replaceVertex u v g)"
  using assms
  by (induction g) (auto simp: fmap_vertexSet)

lemmas replaceVertex_edge = replaceVertex_edge_1 replaceVertex_edge_2 replaceVertex_edge_3 replaceVertex_edge_4

lemma replaceVertex_edgeSet:
  "edgeSet (replaceVertex u v g) = {(if s = u then v else s, if t = u then v else t)| s t. (s,t) \<in> edgeSet g}"
  by (auto simp: fmap_edgeSet)

subsubsection \<open>\<^term>\<open>mergeVertices\<close>\<close>
lemma mergeVertices_id:
  assumes "\<And>u. u \<in> vertexSet g \<Longrightarrow> \<not> p u"
  shows "mergeVertices p v g = g"
  using assms
  by (induction g) auto

lemma mergeVertices_vertexSet:
  assumes "u \<in> vertexSet g" "u \<noteq> v" "p u"
  shows "v \<in> vertexSet (mergeVertices p v g)" "u \<notin> vertexSet (mergeVertices p v g)"
  using assms
  by (induction g) (auto simp: fmap_vertexSet)

lemma mergeVertices_edge_1:
  assumes "(s,t) \<in> edgeSet g" "p s" "p t"
  shows "(v,v) \<in> edgeSet (mergeVertices p v g)"
  using assms
  by (induction g) (auto simp: fmap_vertexSet)

lemma mergeVertices_edge_2:
  assumes "(s,t) \<in> edgeSet g" "p s" "\<not>p t"
  shows "(v,t) \<in> edgeSet (mergeVertices p v g)"
  using assms
  by (induction g) (auto simp: fmap_vertexSet)

lemma mergeVertices_edge_3:
  assumes "(s,t) \<in> edgeSet g" "\<not>p s" "p t"
  shows "(s,v) \<in> edgeSet (mergeVertices p v g)"
  using assms
  by (induction g) (auto simp: fmap_vertexSet)

lemma mergeVertices_edge_4:
  assumes "(s,t) \<in> edgeSet g" "\<not>p s" "\<not>p t"
  shows "(s,t) \<in> edgeSet (mergeVertices p v g)"
  using assms
  by (induction g) (auto simp: fmap_vertexSet)

lemmas merge_Vertices_edge = mergeVertices_edge_1 mergeVertices_edge_2 mergeVertices_edge_3 mergeVertices_edge_4

lemma mergeVertices_edgeSet:
  "edgeSet (mergeVertices p v g) = {(if p s then v else s, if p t then v else t)| s t. (s,t) \<in> edgeSet g}"
  by (auto simp: fmap_edgeSet)

subsubsection \<open>\<^term>\<open>splitVertex\<close>\<close>
lemma splitVertex_id:
  assumes "u \<notin> vertexSet g"
  shows "splitVertex u vs g = g"
  using assms
  by (induction g) auto

lemma splitVertex_vertexSet':
  "{v. v \<in> vertexSet g \<and> u \<noteq> v} \<subseteq> vertexSet (splitVertex u vs g)"
  by (induction g) auto

lemma splitVertex_vertexSet:
  assumes "u \<in> vertexSet g"
  shows "vertexSet (splitVertex u vs g) = vertexSet g - {u} \<union> set vs"
  using assms splitVertex_vertexSet'
  by (induction g) (fastforce simp: splitVertex_id vertices_vertexSet)+

lemma splitVertex_edge_1:
  assumes "(u,w) \<in> edgeSet g" "u \<noteq> w"
  shows "\<And>v. v \<in> set vs \<Longrightarrow> (v,w) \<in> edgeSet (splitVertex u vs g)"
  using assms splitVertex_vertexSet'
  by (induction g) (fastforce simp: splitVertex_vertexSet)+

lemma splitVertex_edge_2:
  assumes "(w,u) \<in> edgeSet g" "u \<noteq> w"
  shows "\<And>v. v \<in> set vs \<Longrightarrow> (w,v) \<in> edgeSet (splitVertex u vs g)"
  using assms splitVertex_vertexSet'
  by (induction g) (fastforce simp: splitVertex_vertexSet)+

lemma splitVertex_edge_3:
  assumes "(u,u) \<in> edgeSet g"
  shows "\<And>v w. v \<in> set vs \<Longrightarrow> w \<in> set vs \<Longrightarrow> (v,w) \<in> edgeSet (splitVertex u vs g)"
  using assms
  by (induction g) (auto simp: splitVertex_vertexSet)

lemma splitVertex_edge_4:
  assumes "(s,t) \<in> edgeSet g" "s \<noteq> u" "t \<noteq> u"
  shows "(s,t) \<in> edgeSet (splitVertex u vs g)"
  using assms splitVertex_vertexSet'
  by (induction g) (fastforce simp: splitVertex_vertexSet)+

lemmas splitVertex_edge = splitVertex_edge_1 splitVertex_edge_2 splitVertex_edge_3 splitVertex_edge_4

lemma splitVertex_altdef_eq: "splitVertex' u vs g = splitVertex u vs g"
  by (induction g) auto

subsubsection \<open>\<^term>\<open>induce\<close>\<close>
lemma induce_vertexSet: "vertexSet (induce p g) = {u. u \<in> vertexSet g \<and> p u}"
  by (induction g) (auto simp: induce_def)

lemma induce_vertexSet_p: "u \<in> vertexSet (induce p g) \<Longrightarrow> p u"
  by (auto simp only: induce_vertexSet)

lemma induce_remove: "\<not>p u \<Longrightarrow> u \<notin> vertexSet (induce p g)"
  by (induction g) (auto simp: induce_def)

lemma induce_subset: "vertexSet (induce p g) \<subseteq> vertexSet g"
  using induce_vertexSet
  by (metis (no_types, lifting) mem_Collect_eq subsetI)

lemma induce_subset': "u \<in> vertexSet (induce p g) \<Longrightarrow> u \<in> vertexSet g"
  using induce_subset by fast

lemma induce_empty[simp]: "induce p \<epsilon> = \<epsilon>"
  by (simp add: induce_def)

lemma induce_vertex[simp]: "induce p (Vertex u) = (if p u then Vertex u else \<epsilon>)"
  by (simp add: induce_def)

lemma induce_overlay_distr[simp]: "induce p (g1 \<oplus> g2) = induce p g1 \<oplus> induce p g2"
  by (simp add: induce_def)

lemma induce_connect_distr[simp]: "induce p (g1 \<rightarrow> g2) = induce p g1 \<rightarrow> induce p g2"
  by (simp add: induce_def)

lemma in_induced_edgeSet_if: "(u,v) \<in> edgeSet g \<Longrightarrow> p u \<Longrightarrow> p v \<Longrightarrow> (u,v) \<in> edgeSet (induce p g)"
  using induce_vertexSet
  by (induction g) (fastforce simp: induce_def)+


lemma in_induced_edgeSet: "(u,v) \<in> edgeSet (induce p g) \<Longrightarrow> (u,v) \<in> edgeSet g \<and> p u \<and> p v"
  by (induction g)
     (auto dest: induce_vertexSet_p induce_subset' split: if_splits)

lemma induce_edgeSet: "edgeSet (induce p g) = {(u,v)| u v. (u,v) \<in> edgeSet g \<and> p u \<and> p v}"
  by (auto dest: in_induced_edgeSet in_induced_edgeSet_if)

lemma induce_edgeSet_subset: "edgeSet (induce p g) \<subseteq> edgeSet g"
  by (auto dest: in_induced_edgeSet)


subsubsection \<open>\<^term>\<open>simplify\<close>\<close>
lemma simplify_vertexSet: "vertexSet (simplify g) = vertexSet g"
  by (induction g) (auto simp flip: no_vertex_iff_empty)

lemma simplify_edgeSet: "edgeSet (simplify g) = edgeSet g"
  by (induction g) (auto simp: empty_no_edge simplify_vertexSet simp flip: no_vertex_iff_empty)

lemma simplify_size: "size (simplify g) \<le> size g"
  using size_geq_1
  by (induction g) (auto intro: trans_le_add2)

end
