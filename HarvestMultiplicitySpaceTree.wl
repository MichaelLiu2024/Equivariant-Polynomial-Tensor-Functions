(* ::Package:: *)

(* ::Section:: *)
(*Public Functions*)


BeginPackage["HarvestMultiplicitySpaceTree`",{"ClebschGordanTools`","IsotypicDecompositionTools`","CombinatoricsTools`"}];


(* ::Subsection:: *)
(*Public Function Declarations*)


HarvestMultiplicitySpaceTree::usage="computes the tensors from the tree"


(* ::Section:: *)
(*Private Functions*)


Begin["`Private`"];


(* ::Subsection:: *)
(*Private Function Declarations*)


(* ::Subsection:: *)
(*Private Function Attributes*)


SetAttributes[
{
TensorBasisExteriorPower
},
Listable
]


(* ::Subsection:: *)
(*Private Function Implementations*)


SSYTTensorBasisSchurPower[p_,m_]:=YoungSymmetrize[SymmetrizedArray[#->1,ConstantArray[m,Total[p]]],p]&/@Flatten[SemiStandardYoungTableaux[p,m],{{1},{2,3}}]


TensorBasisTensorProduct[\[Lambda]s_,\[Mu]_]:=
Module[
{indexBasis,pathBasis,tensorBasis},

indexBasis=Position[Fold[IsotypicComponentsTensorProduct,\[Lambda]s],\[Mu]];
pathBasis=FoldList[Abs[#1-First[#2]]+Last[#2]-1&,First[\[Lambda]s],Transpose[{Rest[\[Lambda]s],#}]]&/@indexBasis;
tensorBasis=ClebschGordanTensor[\[Lambda]s,#]&/@pathBasis
]


(*Make sure you're only passing valid inputs here with nonzero Hom space! IsotypicMultiplicityExteriorPower>0*)
(*Currently we have not accounted for the kernel of Subscript[r, Subscript[\[Pi], \[Lambda]]]: we still need to remove those vectors in the kernel of Subscript[r, Subscript[\[Pi], \[Lambda]]]*)
(*I think we are also assuming that \[Lambda]<=3 for d=3, although this code might work in general. We would need to prove this. It may not be that bad just to stare at the full explicit formula for the CG tensor*)
TensorBasisExteriorPower[\[Lambda]_,d_,\[Mu]_]:=
Module[
{pathBasis,tensorBasis},

pathBasis=
Switch[
d,
0,{{0}},
1,{{\[Lambda]}},
2,{{\[Lambda],\[Mu]}},
3,{{\[Lambda],#+1-Mod[#,2]&@Abs[\[Lambda]-\[Mu]],\[Mu]}},
_,Print["Warning: TensorBasisExteriorPower hit d>3"]
(*
memoize results;
dimension=IsotypicMultiplicityExteriorPower[\[Lambda],d,\[Mu]];
span=Select[PathBasisTensorProduct[ConstantArray[\[Lambda],d],\[Mu]],OddQ@#[[2]]&];
While[
Length[basis]<dimension,
keepaddingguysfromspan
]
*)
];

tensorBasis=AntisymmetrizedClebschGordanTensor/@pathBasis
]


(*We still need to subselect the argument of TensorMultiply to account for kernel of column symmetrizer.*)
TensorBasisSchurPower[\[Lambda]_,p_,\[Mu]_]:=
SymmetrizeColumns[#,p]&/@Flatten[
Map[
OuterTensorMultiply[TensorBasisExteriorPower[\[Lambda],p,#],TensorBasisTensorProduct[#,\[Mu]]]&,
Select[Tuples@IsotypicComponentsExteriorPower[\[Lambda],p],IsotypicComponentTensorProductQ[#,\[Mu]]&]
],
1
]


TensorMultiply[leaf_,root_]:=
Chop@TensorContract[
TensorProduct[Sequence@@leaf,root],
Transpose[{#,Last[#]+Range[Length[leaf]]}]&@Accumulate[TensorRank/@leaf]
]


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
