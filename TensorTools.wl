(* ::Package:: *)

(* ::Title:: *)
(*TensorTools*)


(* ::Section:: *)
(*Public Functions*)


BeginPackage["TensorTools`",{"CombinatoricsTools`"}];


(* ::Subsection:: *)
(*Public Function Declarations*)


EvaluateTensorTrain::usage="evaluates the tensor train representation of CG(\[Lambda]s,\[Gamma]s) at the given legs."


EvaluateSymmetrizedTensorTrain::usage="evaluates the symmetrized tensor train representation of CG((\[Lambda],...,\[Lambda]),\[Gamma]s) at the inputs (x,...,x)."


EvaluateTensor::usage="evaluates the tensor CG(\[Lambda]s,\[Gamma]s) at the given legs."


ContractTensorTree


ContractTensorTrain


EvaluateYoungSymmetrizedTensorTree


AntisymmetrizeRows


SymmetrizeColumns


YoungSymmetrize


(* ::Section:: *)
(*Private Functions*)


Begin["`Private`"];


(* ::Subsection:: *)
(*Private Function Implementations*)


ContractLegs[leafVector1_?VectorQ,{leafVector2_List?VectorQ,coreTensor_?ArrayQ}]:=Dot[leafVector2,Dot[leafVector1,coreTensor]]


ContractTensors[leafTensor1_?ArrayQ,{leafTensor2_?ArrayQ,coreTensor_?ArrayQ}]:=
With[
{r2=TensorRank[leafTensor2],r1=TensorRank[leafTensor1]},
TensorContract[TensorProduct[leafTensor1,TensorContract[TensorProduct[leafTensor2,coreTensor],{r2+{0,2}}]],{{r1,r1+r2}}]
]


(* ::Subsection:: *)
(*Public Function Implementations*)


EvaluateTensor[leafVectors_List][coreTensor_?ArrayQ]:=EvaluateTensor[leafVectors,coreTensor]
EvaluateTensor[leafVectors_List,coreTensor_?ArrayQ]:=Normal@Chop@Fold[Dot[#2,#1]&,coreTensor,Take[leafVectors,TensorRank[coreTensor]-1]]


EvaluateTensorTrain[leafVectors_List,coreTensorTrain_List]:=Chop@Fold[ContractLegs,First[leafVectors],Transpose[{Rest[leafVectors],coreTensorTrain}]]


ContractTensorTree[leafTensors_List,coreTensorTrain_List]:=
If[
Length[leafTensors]==1,
Chop@Dot@@Join[leafTensors,coreTensorTrain],
Chop@Fold[ContractTensors,First[leafTensors],Transpose[{Rest[leafTensors],coreTensorTrain}]]
]


ContractTensorTrain[coreTensorTrain_List]:=Chop@Dot@@coreTensorTrain


EvaluateSymmetrizedTensorTrain[leafVector_List?VectorQ,coreTensorTrain_List]:=Chop@Fold[Dot[leafVector,Dot[#1,#2]]&,leafVector,coreTensorTrain]


(*This is really a generalized Tucker format...*)
EvaluateYoungSymmetrizedTensorTree[leafVectors_List,leafTensors_List,coreTensorTrain_List]:=EvaluateTensorTrain[EvaluateTensor[leafVectors]/@leafTensors,coreTensorTrain]


AntisymmetrizeRows[tensor_?ArrayQ,p_List?VectorQ]:=Symmetrize[tensor,Antisymmetric/@YoungTableau@p]


SymmetrizeColumns[p_List?VectorQ][tensor_?ArrayQ]:=SymmetrizeColumns[tensor,p]
SymmetrizeColumns[tensor_?ArrayQ,p_List?VectorQ]:=Symmetrize[tensor,Symmetric/@ConjugateTableau@YoungTableau@p]


YoungSymmetrize[tensor_?ArrayQ,p_List?VectorQ]:=SymmetrizeColumns[AntisymmetrizeRows[tensor,p],p]


End[];


EndPackage[];
