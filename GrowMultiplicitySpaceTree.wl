(* ::Package:: *)

(* ::Section:: *)
(*Public Functions*)


BeginPackage["GrowMultiplicitySpaceTree`",{"IsotypicDecompositionTools`","CombinatoricsTools`"}];


(* ::Subsection:: *)
(*Public Function Declarations*)


(*SchurS -> Det is the only bottleneck. Symbolic determinant of a matrix with polynomial entries*)
(*We could try an alternative implementation of IsotypicMultiplicitySchurPower: find an explicit expression for the generating function of the number of
semistandard Young tableaux (SSYT) of shape p with powers being the total sum of entries and use Coefficient. Maybe try this for IsotypicMultiplicityExteriorPower
as well for consistency, though tbh it may be slower. Low priority though.*)
GrowMultiplicitySpaceTree::usage="returns the tree"


(* ::Section:: *)
(*Private Functions*)


Begin["`Private`"];


(* ::Subsection:: *)
(*Private Function Implementations*)


MuTuples[\[Lambda]s_List?VectorQ,\[Pi]\[Lambda]s_List,\[Nu]_Integer?NonNegative]:=Select[Tuples@MapThread[IsotypicComponentsSchurPower,{\[Lambda]s,\[Pi]\[Lambda]s}],IsotypicComponentTensorProductQ[#,\[Nu]]&]


PruneChildlessNodes[tree_]:=TreeFold[If[#2=={},Nothing,Tree[##]]&,tree]


(* ::Subsection:: *)
(*Public Function Implementations*)


GrowMultiplicitySpaceTree[\[Lambda]s_,m\[Lambda]s_,\[Nu]_,Ds_]:=
Module[
{tree},

(*Level 1: D*)
tree=Tree[{\[Lambda]s,m\[Lambda]s,\[Nu]},Ds];

(*Level 2: Subscript[(Subscript[d, \[Lambda]]), \[Lambda]]*)
tree=NestTree[StrictCompositions[#,Length[\[Lambda]s]]&,tree];

(*Level 3: Subscript[(Subscript[\[Pi], \[Lambda]]), \[Lambda]]*)
tree=NestTree[Tuples@ThinPartitions[#,\[Lambda]s,m\[Lambda]s]&,tree];

(*Level 4: Subscript[(Subscript[\[Mu], \[Lambda]]), \[Lambda]]*)
tree=NestTree[MuTuples[\[Lambda]s,#,\[Nu]]&,tree];

(*Prune childless nodes for memory efficiency*)
PruneChildlessNodes[tree]
]


End[];


EndPackage[];
