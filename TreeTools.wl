(* ::Package:: *)

BeginPackage["TreeTools`"];


PruneChildlessNodes
AncestralNestTree


Begin["`Private`"];


PruneChildlessNodes[tree_Tree]:=TreeFold[If[#2=={},Nothing,Tree[##]]&,tree]


AncestralNestTree[f_,tree_Tree]:=
 TreeReplacePart[
  tree,
  Function[
   pos,
   pos:>Tree[
    TreeExtract[tree,pos,TreeData],
    Tree[#,None]&/@f[TreeExtract[tree,Take[pos,#]&/@Range[0,Length@pos],TreeData]]
   ]
  ]/@TreePosition[tree,_,"Leaves"]
 ]


End[];


EndPackage[];
