theory Unit_Algebraic_Graph
  imports Algebraic_Graphs_Class
begin

interpretation algebraic_unit_digraph: algebraic_digraph "()" "\<lambda>_. ()" "\<lambda>_ _. ()" "\<lambda>_ _. ()"
  by (unfold_locales) auto


interpretation bogus_digraph: algebraic_digraph True "\<lambda>_. True" "(\<and>)" "(\<and>)"
  by unfold_locales
     auto

end
