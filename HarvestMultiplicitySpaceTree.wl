(* ::Package:: *)

(* ::Section:: *)
(*Public Functions*)


BeginPackage["HarvestMultiplicitySpaceTree`",{"ClebschGordanTools`","IsotypicDecompositionTools`","CombinatoricsTools`"}];


(* ::Subsection:: *)
(*Public Function Declarations*)


(*We have to make sure that we are always passing valid inputs to the functions. I don't want to run expensive checks each time the functions are called*)
HarvestMultiplicitySpaceTree::usage="computes the tensors from the tree";


(* ::Section:: *)
(*Private Functions*)


Begin["`Private`"];


(* ::Subsection:: *)
(*Private Function Implementations*)


SSYTTensorBasisSchurPower[p_,m_]:=YoungSymmetrize[SymmetrizedArray[#->1,ConstantArray[m,Total[p]]],p]&/@Flatten[SemiStandardYoungTableaux[p,m],{{1},{2,3}}]


TensorBasisSchurPower[\[Lambda]_,p_,\[Mu]_]:=
SymmetrizeColumns[#,p]&/@Join@@Map[
OuterTensorMultiply[Map[AntisymmetrizedClebschGordanTensor,First[#],{2}],Map[ClebschGordanTensor[ConstantArray[],#]&,Last[#],{1}]]&,
PathBasisSchurPower[\[Lambda],p,\[Mu]]
]


HarvestPath[{{\[Lambda]s_,m\[Lambda]s_,\[Nu]_},D_,d\[Lambda]s_,\[Pi]\[Lambda]s_,\[Mu]\[Lambda]s_}]:=
Module[
{e\[Pi]m\[Lambda]Tensors,e\[Pi]h\[Lambda]Tensors,\[Nu]\[Mu]\[Lambda]sTensors,out},

e\[Pi]m\[Lambda]Tensors=MapThread[SSYTTensorBasisSchurPower,{\[Pi]\[Lambda]s,m\[Lambda]s}];

\[Nu]\[Mu]\[Lambda]sTensors=TensorBasisTensorProduct[\[Mu]\[Lambda]s,\[Nu]];

e\[Pi]h\[Lambda]Tensors=MapThread[TensorBasisSchurPower,{\[Lambda]s,\[Pi]\[Lambda]s,\[Mu]\[Lambda]s}];

out=OuterTensorMultiply[e\[Pi]h\[Lambda]Tensors,\[Nu]\[Mu]\[Lambda]sTensors]

(*TensorMultiply[changeBasis/@Flatten[MapThread[Table,{\[Lambda]s,Total/@\[Pi]\[Lambda]s}]],#]&/@out*)
]


(* ::Subsection:: *)
(*Public Function Implementations*)


HarvestMultiplicitySpaceTree[tree_]:=HarvestPaths[tree,HarvestPath]


End[];


EndPackage[];
