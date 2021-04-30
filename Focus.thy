theory Focus
  imports Main
begin

record 'a Focus = 
  ok :: bool
  ins :: "'a list"
  outs :: "'a list"
  verts :: "'a list"

abbreviation Focus :: "bool \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a Focus" where
  "Focus b xs ys zs \<equiv> \<lparr> ok = b, ins = xs, outs = ys, verts = zs \<rparr>"

abbreviation emptyFocus :: "'a Focus" where
  "emptyFocus \<equiv> Focus False [] [] []"

abbreviation vertexFocus :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a Focus" where
  "vertexFocus p x \<equiv> Focus (p x) [] [] [x]"

abbreviation overlayFoci :: "'a Focus \<Rightarrow> 'a Focus \<Rightarrow> 'a Focus" where
  "overlayFoci x y \<equiv> Focus (ok x \<or> ok y) (ins x @ ins y) (outs x @ outs y) (verts x @ verts y)"

fun connectFoci :: "'a Focus \<Rightarrow> 'a Focus \<Rightarrow> 'a Focus" where
  "connectFoci x y = (
    let xs = (if ok y then verts x else ins x);
        ys = (if ok x then verts y else outs y)
    in
      Focus (ok x \<or> ok y) (xs @ ins y) (outs x @ ys) (verts x @ verts y)
  )"

record 'a Context =
  inputs :: "'a list"
  outputs :: "'a list"

end