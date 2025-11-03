(* ::Package:: *)

(* ::Section:: *)
(*Public Functions*)


BeginPackage["HarvestMultiplicitySpaceTree`",{"ClebschGordanTools`","IsotypicDecompositionTools`","CombinatoricsTools`"}];


(* ::Subsection:: *)
(*Public Function Declarations*)


HarvestMultiplicitySpaceTree::usage="computes the tensors from the tree";
PathBasisSchurPower;
TensorBasisSchurPower;


(* ::Section:: *)
(*Private Functions*)


Begin["`Private`"];


(* ::Subsection:: *)
(*Private Function Declarations*)


(* ::Subsection:: *)
(*Private Function Attributes*)


SetAttributes[
{
PathBasisExteriorPower,
TensorBasisExteriorPower
},
Listable
]


(* ::Subsection:: *)
(*Private Function Implementations*)


SSYTTensorBasisSchurPower[p_,m_]:=YoungSymmetrize[SymmetrizedArray[#->1,ConstantArray[m,Total[p]]],p]&/@Flatten[SemiStandardYoungTableaux[p,m],{{1},{2,3}}]


PathBasisTensorProduct[\[Lambda]s_,\[Mu]_]:=FoldList[Abs[#1-First[#2]]+Last[#2]-1&,First[\[Lambda]s],Transpose[{Rest[\[Lambda]s],#}]]&/@Position[Fold[IsotypicComponentsTensorProduct,\[Lambda]s],\[Mu]]


TensorBasisTensorProduct[\[Lambda]s_,\[Mu]_]:=ClebschGordanTensor[\[Lambda]s,#]&/@PathBasisTensorProduct[\[Lambda]s,\[Mu]]


PathBasisExteriorPower[\[Lambda]_,d_,\[Mu]_]/;IsotypicMultiplicityExteriorPower[\[Lambda],d,\[Mu]]>0:=
Switch[
d,
0,{{0}},
1,{{\[Lambda]}},
2,{{\[Lambda],\[Mu]}},
3,{{\[Lambda],#+1-Mod[#,2]&@Abs[\[Lambda]-\[Mu]],\[Mu]}}
];


TensorBasisExteriorPower[\[Lambda]_,d_,\[Mu]_]:=AntisymmetrizedClebschGordanTensor/@PathBasisExteriorPower[\[Lambda],d,\[Mu]]


PathBasisSchurPower[\[Lambda]_,p_,\[Mu]_]:=
Module[
{\[Xi]\[Lambda]ps,pathBasisExteriorPower,pathBasisTensorProduct},
\[Xi]\[Lambda]ps=Select[Tuples@IsotypicComponentsExteriorPower[\[Lambda],p],IsotypicComponentTensorProductQ[#,\[Mu]]&];
pathBasisExteriorPower=PathBasisExteriorPower[\[Lambda],p,#]&/@\[Xi]\[Lambda]ps;
pathBasisTensorProduct=PathBasisTensorProduct[#,\[Mu]]&/@\[Xi]\[Lambda]ps;(*For d<=3 we only have to subselect these! Figure out how to subselect here, or just memoize. Let's run a numerical
experiment to see if we can guess which ones we should select like the d=3 alternating power case. Count dimensions too*)
(*
memoize results;
dimension=IsotypicMultiplicitySchurPower[\[Lambda],p,\[Mu]];
span=Select[PathBasisTensorProduct[ConstantArray[\[Lambda],d],\[Mu]],OddQ@#[[2]]&];
While[
Length[basis]<dimension,
keepaddingguysfromspan
]
*)
{pathBasisExteriorPower,pathBasisTensorProduct}
]


TensorBasisSchurPower[\[Lambda]_,p_,\[Mu]_]:=
SymmetrizeColumns[#,p]&/@Join@@Map[
OuterTensorMultiply[TensorBasisExteriorPower[\[Lambda],p,#],TensorBasisTensorProduct[#,\[Mu]]]&,
Select[Tuples@IsotypicComponentsExteriorPower[\[Lambda],p],IsotypicComponentTensorProductQ[#,\[Mu]]&]
]


TensorMultiply[leaf_,root_]:=
Module[
{n=Length[leaf],revLeaf,revRank,revAccRank},
revLeaf=Reverse[leaf];
revRank=TensorRank/@revLeaf;
revAccRank=Accumulate[revRank]+Range[n,-n+2,-2];
Fold[
TensorMultiplyStep,
root,
Transpose[{revLeaf,revRank,revAccRank}]
]
]


TensorMultiplyStep[tensor_,{revLeaf_,revRank_,revAccRank_}]:=TensorContract[TensorProduct[revLeaf,tensor],{{revRank,revAccRank}}]


OuterTensorMultiply[leaves_,roots_]:=Flatten[Outer[TensorMultiply,Tuples[leaves],roots,1],1]


changeBasis[\[Lambda]_Integer?NonNegative]:=
SparseArray@Switch[
\[Lambda],
0,{1},
1,({
 {1/Sqrt[2], 0, -(1/Sqrt[2])},
 {-(I/Sqrt[2]), 0, -(I/Sqrt[2])},
 {0, 1, 0}
}),
_,TensorMultiply[ConstantArray[changeBasis[1],\[Lambda]],ClebschGordanTensor[ConstantArray[1,\[Lambda]],Range[\[Lambda]]]]
]


HarvestPath[{\[Lambda]s_,m\[Lambda]s_,\[Nu]_},{\[Pi]\[Lambda]s_,\[Mu]\[Lambda]s_}]:=
Module[
{e\[Pi]m\[Lambda]Tensors,e\[Pi]h\[Lambda]Tensors,\[Nu]\[Mu]\[Lambda]sTensors,out},

e\[Pi]m\[Lambda]Tensors=MapThread[SSYTTensorBasisSchurPower,{\[Pi]\[Lambda]s,m\[Lambda]s}];

\[Nu]\[Mu]\[Lambda]sTensors=TensorBasisTensorProduct[\[Mu]\[Lambda]s,\[Nu]];

e\[Pi]h\[Lambda]Tensors=MapThread[TensorBasisSchurPower,{\[Lambda]s,\[Pi]\[Lambda]s,\[Mu]\[Lambda]s}];

out=OuterTensorMultiply[e\[Pi]h\[Lambda]Tensors,\[Nu]\[Mu]\[Lambda]sTensors]

(*TensorMultiply[changeBasis/@Flatten[MapThread[Table,{\[Lambda]s,Total/@\[Pi]\[Lambda]s}]],#]&/@out*)
]


AntisymmetrizeRows[tensor_,p_List?VectorQ]:=Symmetrize[tensor,Antisymmetric/@YoungTableau@p]


SymmetrizeColumns[tensor_,p_List?VectorQ]:=Symmetrize[tensor,Symmetric/@ConjugateTableau@YoungTableau@p]


YoungSymmetrize[tensor_,p_List?VectorQ]:=SymmetrizeColumns[AntisymmetrizeRows[tensor,p],p]


(* ::Subsection:: *)
(*Public Function Implementations*)


HarvestMultiplicitySpaceTree[tree_]:=HarvestPath[TreeData[tree],TreeExtract[tree,{Most[#],#},TreeData]]&/@TreePosition[tree,_,"Leaves"]


End[];


EndPackage[];
